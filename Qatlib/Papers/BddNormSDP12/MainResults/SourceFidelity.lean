/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.StrongDuality.SdpDuality
import Qatlib.Concepts.DyadicFloor.FloorRounding.SdpDualityDefs

set_option backward.isDefEq.respectTransparency false

/-!
# `SourceFidelity` — §2.1 fidelity SDP optimal value (claim c003)

Watrous, *Simpler semidefinite programs for completely bounded norms*,
fixed arXiv:1207.5726v2 (2012), §2.1 "Optimal value", pp.5–6.

The fidelity program has primal variable `X ∈ L(X)` subject to the block
constraint `[[P, X], [X*, Q]] ⪰ 0` and objective `½Tr(X) + ½Tr(X*) = Re Tr X`.
The paper proves (via Lemma 2 and Theorem 3) that its optimal value equals the
fidelity `F(P, Q) = ‖√P√Q‖₁`.

Reuses `fidelity_source_rootFidelity`: for PSD `P, Q` the literal primal values
have LUB `rootFidelity P Q = ‖√P√Q‖₁`, the literal dual values have GLB the same
value, and an actual cross block `X` attains the primal optimum. This is exactly
"the optimal value of the semidefinite program equals `F(P,Q)`".
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped ComplexOrder

namespace Qatlib.Papers.BddNormSDP12.MainResults.SourceFidelity

open Qatlib.Concepts.SdpDuality.StrongDuality
open Qatlib.Concepts.DyadicFloor.FloorRounding

/-- Fixed arXiv:1207.5726v2 §2.1 "Optimal value", pp.5–6. For PSD `P, Q`, the
fidelity semidefinite program over the block `[[P, X], [X*, Q]] ⪰ 0` with
objective `Re Tr X` has optimal value `F(P,Q) = ‖√P√Q‖₁ = rootFidelity P Q`;
the primal supremum and dual infimum coincide and the primal optimum is attained
by an actual cross block. Reuses `fidelity_source_rootFidelity`. -/
theorem fidelity_sdp_optimal_value {I : Type*} [Fintype I] [DecidableEq I]
    {P Q : HermitianMat I ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    IsLUB (fidelityPrimalValues P Q) (rootFidelity P Q) ∧
      IsGLB (fidelityDualValues P Q) (rootFidelity P Q) ∧
      ∃ X : Matrix I I ℂ, (Matrix.fromBlocks P.mat X Xᴴ Q.mat).PosSemidef ∧
        (Matrix.trace X).re = rootFidelity P Q :=
  fidelity_source_rootFidelity hP hQ

end Qatlib.Papers.BddNormSDP12.MainResults.SourceFidelity
