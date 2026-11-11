/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GenerativeAdv25.MainResults.Model.ParameterizedSwap
import Qatlib.Papers.GenerativeAdv25.MainResults.Model.LossLandscape
import Qatlib.Papers.GenerativeAdv25.MainResults.Model.Complexity

set_option backward.isDefEq.respectTransparency false

/-!
# GenerativeAdv25 — fully proved claims (Proposition 2, Theorem 10, Corollary 1)

Fixed paper version: arXiv:2509.09033v1.

This file re-exports, under claim-numbered names, the three claims whose paper proofs are
fully formalized in the model layer:

* `c012_proposition2` — Proposition 2 (Eqs. (S.1.3)–(S.1.11), page 36–37),
  from `Model/ParameterizedSwap.lean`;
* `c014_theorem10` — Theorem 10 strong convexity (Eqs. (S.2.36)–(S.2.37), page 39),
  from `Model/LossLandscape.lean`;
* `c015_corollary1` — Corollary 1 global optimality of local minima (page 40), from the
  same file.

Each bridge is a direct citation of the corresponding proved model theorem; no unverified
conclusion is assumed.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

open Qatlib.Papers.GenerativeAdv25.MainResults

namespace Qatlib.Papers.GenerativeAdv25.MainResults.Source

/-- **Claim c012 = Proposition 2** (arXiv:2509.09033v1, Eqs. (S.1.3)–(S.1.11), pages
36–37): for any `Nodup` list `S` of block indices, there is a parameter configuration `θ`
such that the three-layer parameterized SWAP circuit implements the target unitary
`U_S = ∏_{j∈S} SWAP_{4j+1,4j+4}`, up to the unit-modulus global phase `I^(5|S|)` generated
by the five `e^{i(π/2) SWAP}` gates per block.  Proved in
`Model/ParameterizedSwap.lean` as `proposition2_implementation`. -/
theorem c012_proposition2 (n : ℕ) (S : List (Fin (n / 4))) (hS : S.Nodup) :
    ∃ θ : Fin (n / 4) → Fin 5 → ℝ,
      multiBlockCircuit n S θ = (Complex.I ^ (5 * S.length)) • targetUnitary n S :=
  proposition2_implementation n S hS

/-- **Claim c014 = Theorem 10** (arXiv:2509.09033v1, Appendix G.2.a, Eqs. (S.2.36)–(S.2.37),
page 39): the least-squares Pauli-coefficient loss `ℒ(α) = (1/N)∑_ℓ ‖α − d_ℓ‖²` is
2-strongly convex in the parameter space (its Hessian is `2I`).  Proved in
`Model/LossLandscape.lean` as `theorem10_strong_convexity` via the decomposition
`ℒ(α) = ‖α − α*‖² + ℒ(α*)`. -/
theorem c014_theorem10 {M N : ℕ} (d : Fin N → ParamVec M) (hN : (N : ℝ) ≠ 0) :
    StronglyConvex2 (lsLoss d) :=
  theorem10_strong_convexity d hN

/-- **Claim c015 (1) = Corollary 1** (arXiv:2509.09033v1, page 40): `ℒ` has the unique
global minimum `α* = meanData d`.  Proved in `Model/LossLandscape.lean` as
`corollary1_global_min`. -/
theorem c015_corollary1_unique_global_min {M N : ℕ} (d : Fin N → ParamVec M)
    (hN : (N : ℝ) ≠ 0) : IsUniqueGlobalMin (lsLoss d) (meanData d) :=
  corollary1_global_min d hN

/-- **Claim c015 (2) = Corollary 1** (arXiv:2509.09033v1, page 40): every local minimum of
`ℒ` is global.  Proved in `Model/LossLandscape.lean` as `corollary1_local_min_global`. -/
theorem c015_corollary1_local_min_global {M N : ℕ} (d : Fin N → ParamVec M)
    (hN : (N : ℝ) ≠ 0) :
    ∀ x, IsLocalMin (lsLoss d) x → ∀ y, lsLoss d x ≤ lsLoss d y :=
  corollary1_local_min_global d hN

/-- **Claim c015 (3) = Corollary 1** (arXiv:2509.09033v1, page 40): every critical point of
`ℒ` equals `α*`.  Proved in `Model/LossLandscape.lean` as `corollary1_critical_point`. -/
theorem c015_corollary1_critical_point {M N : ℕ} (d : Fin N → ParamVec M)
    (hN : (N : ℝ) ≠ 0) :
    ∀ x, IsCriticalPoint (lsLoss d) x → x = meanData d :=
  corollary1_critical_point d hN

end Qatlib.Papers.GenerativeAdv25.MainResults.Source
