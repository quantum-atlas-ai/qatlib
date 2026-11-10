/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalCircuits.LocalGateCosts.Costs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.LocalCircuits.LocalGateCosts
open Matrix

namespace Qatlib.Papers.QCircApprox95.MainResults

def sourceU4Params : ℕ := 16

def sourceU2Params : ℕ := 4

theorem phase_parameter_arithmetic : sourceU4Params - 1 ≤ 15 := by
  norm_num [sourceU4Params]

theorem one_input_parameter_arithmetic : sourceU4Params - 1 - (sourceU2Params - 1) ≤ 12 := by
  norm_num [sourceU4Params, sourceU2Params]

theorem two_input_parameter_arithmetic :
    sourceU4Params - 1 - 2 * (sourceU2Params - 1) ≤ 9 := by
  norm_num [sourceU4Params, sourceU2Params]

def prefixProjection (k m : ℕ) : Matrix (Fin k) (Fin m) ℂ :=
  fun i j => if (j : ℕ) = (i : ℕ) then 1 else 0

theorem lemma_three_two_nullity (k m : ℕ) (hk : k ≤ m)
    (V : Matrix (Fin k) (Fin m) ℂ) :
    m - k ≤ Module.finrank ℂ
      (LinearMap.ker (V - prefixProjection k m).mulVecLin) := by
  set W := V - prefixProjection k m with hW
  have h := LinearMap.finrank_range_add_finrank_ker (f := W.mulVecLin)
  have hm : Module.finrank ℂ (Fin m → ℂ) = m := by simp
  have hk' : Module.finrank ℂ (Fin k → ℂ) = k := by simp
  have hle : Module.finrank ℂ (LinearMap.range W.mulVecLin) ≤ k := by
    have hr := Submodule.finrank_le (LinearMap.range W.mulVecLin)
    rw [hk'] at hr
    exact hr
  have hker_eq : Module.finrank ℂ (LinearMap.ker W.mulVecLin)
      = m - Module.finrank ℂ (LinearMap.range W.mulVecLin) := by
    rw [hm] at h
    omega
  rw [hker_eq]
  omega

theorem sub_prefixProjection_mul_eq_zero_iff (k m r : ℕ)
    (V : Matrix (Fin k) (Fin m) ℂ) (X : Matrix (Fin m) (Fin r) ℂ) :
    (V - prefixProjection k m) * X = 0 ↔ V * X = prefixProjection k m * X := by
  rw [Matrix.sub_mul, sub_eq_zero]

theorem prefixProjection_mul_apply (k m r : ℕ) (hk : k ≤ m)
    (X : Matrix (Fin m) (Fin r) ℂ) (i : Fin k) (j : Fin r) :
    (prefixProjection k m * X) i j = X ⟨i.1, lt_of_lt_of_le i.2 hk⟩ j := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single ⟨i.1, lt_of_lt_of_le i.2 hk⟩]
  · simp [prefixProjection]
  · intro a _ ha
    have hv : ¬ ((a : ℕ) = (i : ℕ)) := by
      intro h
      exact ha (Fin.ext h)
    simp [prefixProjection, hv]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem lemma_three_two_first_rows (k m r : ℕ) (hk : k ≤ m)
    (V : Matrix (Fin k) (Fin m) ℂ) (X : Matrix (Fin m) (Fin r) ℂ)
    (hX : V * X = prefixProjection k m * X) (i : Fin k) (j : Fin r) :
    (V * X) i j = X ⟨i.1, lt_of_lt_of_le i.2 hk⟩ j := by
  rw [hX, prefixProjection_mul_apply k m r hk X i j]

end Qatlib.Papers.QCircApprox95.MainResults
