#!/usr/bin/env python3
"""Repository-specific Palomar preflight; not a substitute for kernel checking.

The metadata is JSON-form YAML (valid YAML 1.2), so this check needs only Python's
standard library. --online additionally checks canonical Mathlib ancestry, the
upstream toolchain, and every inherited dependency against its pinned manifest.
"""
from __future__ import annotations
import argparse
import base64
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
MATHLIB = "db584cd6d46c92f209a44c0f1c829460d327499d"
TOOLCHAIN = "leanprover/lean4:v4.33.0"
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
TARGETS = {
    "Sqrt6KissingBound.kissingConfiguration_card_le_sqrt6_pow": "Sqrt6KissingBound/KissingBound.lean",
    "Sqrt6KissingBound.sqrt6_isLeast_universalKissingBase": "Sqrt6KissingBound/Optimality.lean",
    "Sqrt6KissingBound.isUniversalKissingBase_iff": "Sqrt6KissingBound/Optimality.lean",
    "Sqrt6KissingBound.supremum_kissing_roots_eq_sqrt6": "Sqrt6KissingBound/Optimality.lean",
    "Sqrt6KissingBound.Palomar.kissingNumber_exists": "Solution.lean",
    "Sqrt6KissingBound.Palomar.planar_kissingNumber": "Solution.lean",
    "Sqrt6KissingBound.Palomar.kissingNumber_roots": "Solution.lean",
    "Sqrt6KissingBound.Palomar.kissingNumber_universal_base": "Solution.lean",
}
DEFINITIONS = {
    "IsKissingConfiguration": "Sqrt6KissingBound/KissingBound.lean",
    "RealizableKissingCard": "Sqrt6KissingBound/KissingNumber.lean",
    "IsUniversalKissingBase": "Sqrt6KissingBound/Optimality.lean",
}


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def text(path: str) -> str:
    p = ROOT / path
    require(p.is_file() and not p.is_symlink(), f"Missing/nonregular file: {path}")
    return p.read_text(encoding="utf-8")


def uncomment(s: str) -> str:
    """Remove Lean line and nested block comments, retaining line breaks."""
    out: list[str] = []
    i = depth = 0
    quoted = False
    while i < len(s):
        if depth:
            if s.startswith("/-", i):
                depth += 1; out.extend("  "); i += 2
            elif s.startswith("-/", i):
                depth -= 1; out.extend("  "); i += 2
            else:
                out.append("\n" if s[i] == "\n" else " "); i += 1
        elif quoted:
            out.append(s[i])
            if s[i] == "\\" and i + 1 < len(s):
                out.append(s[i + 1]); i += 2
            else:
                if s[i] == '"': quoted = False
                i += 1
        elif s.startswith("/-", i):
            depth = 1; out.extend("  "); i += 2
        elif s.startswith("--", i):
            j = s.find("\n", i)
            if j < 0: j = len(s)
            out.append(" " * (j - i)); i = j
        else:
            if s[i] == '"': quoted = True
            out.append(s[i]); i += 1
    require(depth == 0, "Unterminated Lean block comment")
    return "".join(out)


def normalized(s: str) -> str:
    return " ".join(s.split())


def theorem_signature(s: str, short_name: str) -> str:
    matches = re.findall(r"\btheorem\s+" + re.escape(short_name) + r"\b(.*?)\s*:=", s, re.S)
    require(len(matches) == 1, f"Expected one theorem named {short_name}")
    return normalized(matches[0])


def definition(s: str, name: str) -> str:
    pattern = (r"^\s*def\s+" + re.escape(name) + r"\b(.*?)"
               r"(?=^\s*(?:def|lemma|theorem|namespace|end|noncomputable|private|protected)\b|\Z)")
    found = re.findall(pattern, s, re.M | re.S)
    require(len(found) == 1, f"Expected one definition named {name}")
    return normalized(found[0])


def api(path: str) -> dict:
    headers = {"Accept": "application/vnd.github+json", "User-Agent": "sqrt6-palomar-preflight"}
    token = os.environ.get("GITHUB_TOKEN")
    if token:
        headers["Authorization"] = "Bearer " + token
    request = urllib.request.Request("https://api.github.com/repos/leanprover-community/mathlib4/" + path,
                                     headers=headers)
    with urllib.request.urlopen(request, timeout=60) as response:
        return json.load(response)


def upstream_file(path: str) -> str:
    obj = api(f"contents/{path}?ref={MATHLIB}")
    return base64.b64decode(obj["content"]).decode("utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--online", action="store_true")
    args = parser.parse_args()
    cfg = json.loads(text("comparator.json"))
    require(set(cfg) == {"challenge_module", "solution_module", "theorem_names", "definition_names",
                         "permitted_axioms", "enable_nanoda"}, "Unexpected Comparator configuration keys")
    require(cfg["challenge_module"] == "Challenge" and cfg["solution_module"] == "Solution", "Wrong modules")
    require(cfg["theorem_names"] == list(TARGETS), "The eight expected Comparator targets must be selected")
    require(cfg["definition_names"] == [], "Definitions must have explicit values in the Challenge")
    require(set(cfg["permitted_axioms"]) == AXIOMS and len(cfg["permitted_axioms"]) == 3, "Wrong axiom allowlist")
    require(cfg["enable_nanoda"] is True, "Local Comparator must enable NanoDa")
    raw = text("Challenge.lean")
    require(len(raw.encode()) <= 32 * 1024 and len(raw.splitlines()) <= 300, "Challenge exceeds preferred size")
    ch = uncomment(raw)
    require(re.findall(r"^\s*import\s+(\S+)", ch, re.M) == ["Mathlib"], "Challenge must import only Mathlib")
    require(len(re.findall(r"\bsorry\b", ch)) == 8, "Challenge should have exactly eight statement placeholders")
    require(not re.search(r"\b(?:axiom|admit|native_decide)\b", ch), "Unexpected Challenge construct")
    require("Fintype.card" not in ch and "kissingNumberCeiling" not in ch and "findGreatest" not in ch,
            "Challenge must not use a local cardinality instance or a bound-dependent maximum")
    for name, path in DEFINITIONS.items():
        require(definition(ch, name) == definition(uncomment(text(path)), name), f"Definition drift: {name}")
    for name, path in TARGETS.items():
        short = name.rsplit(".", 1)[-1]
        require(theorem_signature(ch, short) == theorem_signature(uncomment(text(path)), short),
                f"Challenge/Solution signature drift: {name}")
    proof_paths = ["Sqrt6KissingBound.lean", "Solution.lean", "Axioms.lean"] + [
        str(p.relative_to(ROOT)) for p in (ROOT / "Sqrt6KissingBound").rglob("*.lean")]
    for path in proof_paths:
        # Diagnostic strings may say "axiom" without declaring one.
        source = re.sub(r'"(?:\\.|[^"\\])*"', '""', uncomment(text(path)))
        require(not re.search(r"\b(?:sorry|admit|axiom|native_decide|sorryAx|ofReduceBool)\b", source),
                f"Forbidden proof hole/axiom/evaluation shortcut: {path}")
        require(not re.search(r"^\s*import\s+.*\bChallenge\b", source, re.M), f"Proof imports Challenge: {path}")
    require(re.search(r"^import Solution$", text("Axioms.lean"), re.M) is not None, "Axiom audit must import Solution")
    require(text("lean-toolchain").strip() == TOOLCHAIN, "Wrong Lean toolchain")
    lake = text("lakefile.lean")
    require(MATHLIB in lake, "Lakefile must pin canonical Mathlib")
    require(not (ROOT / "lakefile.toml").exists(), "Exactly one Lakefile is permitted")
    for module in ("Challenge", "Solution"):
        require(f"lean_lib {module} where" in lake and f"roots := #[`{module}]" in lake, f"Missing Lake root: {module}")
    manifest = json.loads(text("lake-manifest.json"))
    packages = manifest["packages"]
    require(len({p["name"] for p in packages}) == len(packages), "Duplicate dependency names")
    for p in packages:
        require(p["type"] == "git" and re.fullmatch(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", p["url"]) is not None,
                f"Noncanonical dependency URL: {p['name']}")
        require(re.fullmatch(r"[0-9a-f]{40}", p["rev"]) is not None, f"Unpinned dependency: {p['name']}")
    ml = [p for p in packages if p["name"] == "mathlib"]
    require(len(ml) == 1 and ml[0]["rev"] == ml[0]["inputRev"] == MATHLIB, "Inconsistent Mathlib lock")
    metadata = json.loads(text("formalization.yaml"))  # JSON is a strict subset of YAML 1.2.
    require(metadata["version"] == "v0.4", "Wrong metadata format")
    project = metadata["project"]
    require(isinstance(project["name"], str) and 0 < len(project["name"]) <= 300, "Invalid title")
    require(isinstance(project["description"], str) and 0 < len(project["description"]) <= 10000, "Invalid abstract")
    for field in ("authors", "responsible_maintainers"):
        require(project[field] == ["Sébastien Palcoux"], f"Unexpected human responsibility field: {field}")
    require(project["license"] == "Apache-2.0", "Wrong declared license")
    require("Apache License" in text("LICENSE") and "Version 2.0, January 2004" in text("LICENSE"), "Wrong root license")
    license_names = {"license", "licence", "copying", "unlicense", "ofl"}
    licenses = [p for p in ROOT.iterdir() if p.name.lower().split('.')[0] in license_names]
    require(len(licenses) == 1, "Repository must contain exactly one conventional root license file")
    require(metadata["classification"] == {"arxiv": ["math.MG", "math.CO"], "msc2020": ["52C17", "52C35"]}, "Wrong classifications")
    sources = metadata["sources"]
    require(bool(sources) and any(s["relationship"] in {"formalizes", "adapts", "independently-proves"} for s in sources), "Missing substantive mathematical source")
    for s in sources:
        require(bool(s["title"]) and s["relationship"] in {"formalizes", "adapts", "independently-proves", "background", "other"}, "Invalid source")
        require(s.get("type") in {"paper", "book", "web discussion", "folklore", "other"}, "Invalid source type/origin")
    require("repository" not in metadata, "This is the substantive repository, not a thin wrapper")
    require(bool(metadata["automation"]["methods"]) and all(m.get("method") for m in metadata["automation"]["methods"]), "Missing automation disclosure")
    require(bool(metadata["review"]["status"]) and bool(metadata["status"]["scope"]), "Missing review/scope disclosure")
    tracked = subprocess.run(["git", "ls-files", "-z"], cwd=ROOT, capture_output=True, text=True)
    if tracked.returncode == 0:
        paths = [ROOT / s for s in tracked.stdout.split('\0') if s]
        require(not any(p.is_symlink() for p in paths), "Tracked symlink detected")
        require(not any(p.name == '.gitmodules' for p in paths), "Git submodules are not permitted")
        compiled = {'.olean', '.ilean', '.a', '.bc', '.dll', '.dylib', '.o', '.obj', '.so', '.trace'}
        require(not any(p.suffix in compiled and '.lake' not in p.parts for p in paths), "Tracked compiled artifact")
        files = [p for p in paths if p.is_file()]
        require(sum(p.stat().st_size for p in files) <= 500 * 1024 ** 2, "Repository exceeds 500 MiB")
        for p in files:
            with p.open('rb') as stream:
                require(not stream.read(80).startswith(b'version https://git-lfs.github.com/spec/v1'), f"Git LFS pointer: {p}")
    if args.online:
        comparison = api(f"compare/{MATHLIB}...master")
        require(comparison.get("status") in {"ahead", "identical"}, "Mathlib pin is not in canonical master ancestry")
        require(upstream_file("lean-toolchain").strip() == TOOLCHAIN, "Upstream Mathlib toolchain mismatch")
        canonical = json.loads(upstream_file("lake-manifest.json"))["packages"]
        key = lambda p: (p["name"], p["url"].removesuffix('.git'), p["rev"])
        require({key(p) for p in packages if p["name"] != "mathlib"} == {key(p) for p in canonical}, "Inherited dependency lock differs from canonical Mathlib")
        print("Canonical Mathlib ancestry, toolchain, and inherited dependency lock verified.")
    print(f"Palomar static preflight passed: {len(raw.splitlines())} Challenge lines, {len(raw.encode())} bytes, {len(TARGETS)} theorem targets.")
    print("This checks packaging and source signatures, not Lean elaboration or kernel acceptance.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        sys.exit(1)
