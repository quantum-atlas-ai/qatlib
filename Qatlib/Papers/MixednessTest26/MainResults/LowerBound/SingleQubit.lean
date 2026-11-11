/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MixednessTest26.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Adaptive single-qubit lower bound (Theorem 1.2)

Paper: arXiv:2608.18839v3, Theorem 1.2 (page 2 of the PDF):

> The total number of copies needed for adaptive single-qubit mixedness testing
> is `n = Ω̃(√(10^N)/ε²)`.

"Adaptive single-qubit" means that every copy is measured by a product
single-qubit (binary POVM per wire) measurement, and the choice for the next
copy may depend on all previous outcomes (copy-wise adaptivity).  The model is
`SingleQubitProtocol N n` from `Model/SourceModel.lean`, whose transcript mass is
defined through the Born rule for product effects.

The `Ω̃` hides a polynomial factor in `N`; the statement therefore asserts the
existence of a positive constant and a polynomial loss `(N+1)^j`, valid for all
sufficiently large `N` and all `ε > 0`.

## Proof status (scaffolds removed; statements in branch history c93d182c6)

* Fixed source: arXiv:2608.18839v3, Theorem 1.2, §5 (proof of the lower bound),
  using [LiuAcharya2024a] and the measurement information channel.
* Key proof route: (i) build the hard-instance ensemble of Definition 5.2 with
  `ℓ = Θ(N)`-bit perturbations along single-qubit Pauli directions; (ii) the MIC
  of product single-qubit measurements has
  `‖L_M‖_op ‖L_M‖_1 = Θ(10^N·poly(N))`; (iii) Theorem 1.3 then gives
  `n = Ω(4^N/(ε²√(‖L‖_op‖L‖_1))) = Ω̃(√(10^N)/ε²)`, using
  `4^N/√(10^N·poly) = √(10^N)/poly` up to `poly(N)` factors.
* Lean gap: the two-way relation between the MIC spectral norms of product
  single-qubit measurements and `√(10^N)` (Theorem 5.7 / §5.2) is not
  formalized, nor is the reduction from Theorem 1.3 to this statement.  The
  present declaration records the faithful lower-bound shape for the
  paper-local protocol model.
* Reusable dependencies: `SourceModel.singleQubitAcceptProb`,
  `IsSingleQubitMixednessTester`, `MeasurementModel.micLop/micL1/micScale`,
  `hardInstanceDelta`, `hardInstanceState`, and the (removed scaffold)
  `LowerBound/Framework.lean` Theorem 1.3 statement.
* Suggested tactics: instantiate Theorem 1.3 with the family of product
  single-qubit measurements, then bound `micScale` via the eigenvalue
  computation of Theorem 5.7 (`Matrix.PosSemidef` spectral calculus,
  `Finset.sum` over Pauli strings), and finish with `Nat.cast`/`nlinarith`
  asymptotics.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MixednessTest26.MainResults.LowerBound


end Qatlib.Papers.MixednessTest26.MainResults.LowerBound
