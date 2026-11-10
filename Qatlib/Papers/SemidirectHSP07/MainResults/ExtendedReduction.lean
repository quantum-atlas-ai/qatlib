/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemidirectHSP07.MainResults.ReductionSource
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Commutator.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP07.MainResults

open scoped commutatorElement

theorem classOne_quotient_commutative (p r : ℕ) (hp : p.Prime) (hr : 2 ≤ r)
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) (hφ : ClassOne p r φ) :
    letI : (Subgroup.zpowers (xGen p r φ ^ p ^ (r - 2))).Normal := K0_normal p r hp φ hφ
    IsMulCommutative (SDG p r φ ⧸ Subgroup.zpowers (xGen p r φ ^ p ^ (r - 2))) := by
  letI : (Subgroup.zpowers (xGen p r φ ^ p ^ (r - 2))).Normal := K0_normal p r hp φ hφ
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    (classOne_commutator_le p r hp hr φ hφ)

theorem K0_le_cyclic_square (p r : ℕ) (hp : p.Prime) (hr4 : 4 ≤ r)
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) :
    Subgroup.zpowers (xGen p r φ ^ p ^ (r - 2)) ≤
      Subgroup.zpowers (xGen p r φ ^ p ^ 2) := by
  rw [Subgroup.zpowers_le]
  have h : p ^ (r - 2) = p ^ 2 * p ^ (r - 4) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h, pow_mul]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

theorem candidate_square_normal (p r : ℕ) (hp : p.Prime) (hr4 : 4 ≤ r)
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) (hφ : ClassOne p r φ) :
    (Subgroup.zpowers (xGen p r φ ^ p ^ 2)).Normal :=
  normal_of_contains_commutator p r hp (by omega) φ hφ _
    (K0_le_cyclic_square p r hp hr4 φ)

theorem candidate_form2_two_two_normal (p r : ℕ) (hp : p.Prime) (hr4 : 4 ≤ r)
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) (hφ : ClassOne p r φ) :
    (form2 p r φ 2 2).Normal := by
  refine normal_of_contains_commutator p r hp (by omega) φ hφ _ ?_
  refine le_trans (K0_le_cyclic_square p r hp hr4 φ) ?_
  rw [Subgroup.zpowers_le]
  change xGen p r φ ^ p ^ 2 ∈
    Subgroup.closure ({xGen p r φ ^ p ^ 2, yGen p r φ ^ p ^ 2} : Set (SDG p r φ))
  exact Subgroup.subset_closure (by simp)

end Qatlib.Papers.SemidirectHSP07.MainResults
