# Verification record

Local checks of this extension passed with Lean v4.35.0-rc3 and pinned Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`:

- `lake build --wfail`: success, including all three library modules and Solution.
- `lake build Challenge`: success; eight expected theorem-placeholder warnings.
- `lake env lean Audit.lean`: all eight public results use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- `lake comparator --config comparator.json`: all eight Challenge/Solution types match;
  both the NanoDa kernel and Lean's default kernel accept the solution.

`Audit.lean` also checks K₂ as a counterexample to omitting the order assumption, K₄
as an equality case of the K₅-minor-free bound, and the density theorem applied to K₅.
These finite calculations use kernel-reduced `decide`, not `native_decide`.

The Challenge is independently compiled and repeats the branch-set definition rather
than importing Solution or project proof modules. Its eight `sorry` placeholders occur
only in selected theorem statements. Definitions contain no placeholders. Comparator
permits only the three standard axioms listed above and enables NanoDa.

Logs from the successful local run are in `verification/`. The PR's two Actions checks
provide remote verification of the uploaded source. The Palomar workflow uses the
official full pipeline pinned at `c02bbeaed888df45c4e28c4e99dba540ad21552a` and
`palomar-standard-v1`. A successful preflight is mechanical evidence, not registry
submission, acceptance, or independent human mathematical review.
