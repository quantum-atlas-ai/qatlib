/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Qatlib.Foundations.PureStateMath.Qubit
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Pi

@[expose] public section


/-! # Finite complex separation by an actual amplitude vector

The algebraic separating functional is represented in the same finite complex
coordinates as the caller. No inner-product conclusion is assumed as an input.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Foundations.PureStateMath.DualSep

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The amplitude vector representing a complex linear functional in its second slot. -/
def dualVector (f : (I → ℂ) →ₗ[ℂ] ℂ) : I → ℂ :=
  fun i => star (f (Pi.single i 1))

/-- Pairing with the representing vector is the conjugate of the functional value. -/
theorem dualPair (f : (I → ℂ) →ₗ[ℂ] ℂ) (v : I → ℂ) :
    Inner v (dualVector f) = star (f v) := by
  have hexp : f v = ∑ i, v i * f (Pi.single i 1) := by
    calc
      f v = f (∑ i, Pi.single i (v i)) :=
        congrArg f (LinearMap.sum_single_apply (fun _ : I => ℂ) v).symm
      _ = ∑ i, v i * f (Pi.single i 1) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        have hs : Pi.single i (v i) = v i • (Pi.single i (1 : ℂ) : I → ℂ) := by
          ext j
          by_cases h : j = i <;> simp [h]
        rw [hs, map_smul, smul_eq_mul]
  rw [hexp]
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply,
    dualVector, star_sum, star_mul, mul_comm]

/-- A vector outside a complex subspace has a nonzero pairing with a vector
orthogonal to the entire subspace, including in zero-dimensional edge cases. -/
theorem orthogSep (S : Submodule ℂ (I → ℂ)) (v : I → ℂ) (hv : v ∉ S) :
    ∃ w : I → ℂ, Inner v w ≠ 0 ∧ ∀ u ∈ S, Inner u w = 0 := by
  obtain ⟨f, hfv, hfS⟩ := S.exists_dual_map_eq_bot_of_notMem hv inferInstance
  refine ⟨dualVector f, ?_, ?_⟩
  · rw [dualPair]
    simpa only [ne_eq, star_eq_zero] using hfv
  · intro u hu
    have hzero : f u = 0 := by
      have hm : f u ∈ S.map f := Submodule.mem_map.mpr ⟨u, hu, rfl⟩
      rwa [hfS, Submodule.mem_bot] at hm
    rw [dualPair, hzero, star_zero]

end Qatlib.Foundations.PureStateMath.DualSep
