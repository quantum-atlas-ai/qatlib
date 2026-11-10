/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteStats.BornEstimator.BornLaw
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.FiniteStats.BornEstimator
open scoped Classical BigOperators
variable {V K : Type*} [Fintype V] [DecidableEq V] [Fintype K]

def contextOverlap (C : K → Finset V) (q : K → ℝ) : Matrix V V ℝ :=
  fun i j => ∑ k,q k*(if i∈C k then 1 else 0)*(if j∈C k then 1 else 0)

theorem contextOverlap_psd (C : K → Finset V) (q : K → ℝ) (hq : ∀ k,0 ≤ q k) :
    (contextOverlap C q).PosSemidef := by
  have h := Matrix.posSemidef_sum Finset.univ (fun k _ =>
    (Matrix.posSemidef_vecMulVec_self_star (fun i : V => if i∈C k then (1:ℝ) else 0)).smul (hq k))
  convert h using 1
  ext i j
  simp [contextOverlap,Matrix.sum_apply,Matrix.vecMulVec_apply]

theorem weighted_contextOverlap_psd (C : K → Finset V) (q : K → ℝ) (hq : ∀ k,0 ≤ q k) (a : V → ℝ) :
    (Matrix.of (fun i j => a i*a j*contextOverlap C q i j)).PosSemidef := by
  have h := Matrix.posSemidef_sum Finset.univ (fun k _ =>
    (Matrix.posSemidef_vecMulVec_self_star (fun i : V => a i*(if i∈C k then (1:ℝ) else 0))).smul (hq k))
  convert h using 1
  ext i j
  simp only [contextOverlap,Finset.mul_sum,Matrix.sum_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,
    star_trivial,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

end Qatlib.Foundations.FiniteStats.BornEstimator
