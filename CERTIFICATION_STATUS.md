# Verification

The substantive certificate contains the Euclidean-volume proof presented in
the manuscript, the existence of attained kissing numbers, the value tau_2 = 6,
and optimality of the universal base. The Palomar interface adds four proved
adapters but changes no substantive mathematical proof module.

## Environment and checks

- Lean: `leanprover/lean4:v4.33.0`.
- Canonical Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Exact dependency lock: `lake-manifest.json`.
- Source fingerprints: `SOURCE_SHA256SUMS`.

```bash
python3 scripts/palomar_static_check.py --online
lake exe cache get
bash scripts/check.sh
bash scripts/verify-comparator.sh
```

The preflight checks packaging, the three public definitions, all eight theorem
signatures, canonical Mathlib ancestry, and inherited dependency revisions. It
is not a Lean proof check. `check.sh` builds the proof and the two isolated
interface modules, verifies fingerprints, and runs the all-project axiom audit.
`verify-comparator.sh` checks exported Challenge/Solution equality and replays
the proofs with Lean and the independent NanoDa kernel. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed in the proved development.

The eight deliberate `sorry` placeholders in `Challenge.lean` state the
independent challenges; they are never imported by the solution. There are no
permitted proof holes in Solution or the substantive development.

## Reading the status correctly

The result of each run belongs to its exact Git commit. Consult the
[GitHub Actions runs](https://github.com/sebastienpalcoux/sqrt6-kissing-bound/actions)
for that commit and require all three verification jobs to pass. A successful
older run is not evidence for a later edit. A queued or running Comparator job
is not a successful independent check.

## Completed Palomar registration

[PALOMAR-2026-09-05-000002, version 1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-09-05-000002&version=1)
was registered on 5 September 2026 for repository commit
`cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9`, using the root `comparator.json`.
All eight selected declarations passed Comparator, Lean kernel checking, and
independent NanoDa replay in
[Palomar's verification run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/33941141603).
The automated editorial review identified no problems. The submitter then
authorized permanent registration, and the public record and source-preservation
receipt are available at the entry above.

The current disclosure and manuscript revision postdates the registered
snapshot. It updates the AI attribution and registration account; the Lean
source, Comparator configuration, and dependency pins remain those registered.
Palomar version 1 preserves its original metadata and manuscript. Registration
does not constitute human peer review or a novelty certificate. No independent
human mathematical review is recorded.
