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

The pre-packaging proof snapshot recorded a successful build and an axiom audit
of 274 project declarations. That record is not presented as validation of the
new interface or repinned environment; those have their own CI gate. The
manuscript's environment note describes that original proof build; the current
registration pins are the ones above and in the committed Lake files.

No Palomar identifier or registration outcome is asserted here. Registration
requires Palomar's own mechanical verification and automated review, followed
by the submitter's decision to make the result and review public. No
independent human mathematical review is recorded.
