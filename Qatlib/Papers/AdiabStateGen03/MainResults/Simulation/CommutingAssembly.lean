/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Defs
import Qatlib.Papers.AdiabStateGen03.MainResults.Simulation.CircuitCalculus
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Simulation of commuting Hamiltonian sums

This module factors the evolution of commuting Hamiltonians with `timeEvolution_add_of_commute`
and combines their approximating circuits. Operator norm and accuracy-rescaling estimates
support `simulatable_add_of_commute`, which proves that a commuting sum of simulatable
Hamiltonians is simulatable. The mathematical context is [AharonovTaShma2007].

## Main statements

* `timeEvolution_add_of_commute`: The evolution of a sum of commuting Hamiltonians equals the
  product of their evolutions at the same time.
* `simulatable_add_of_commute`: The sum of two commuting simulatable Hamiltonians is
  simulatable.

## References

* [Aharonov and Ta‐Shma, 2007][AharonovTaShma2007]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace BigOperators

namespace Qatlib.Papers.AdiabStateGen03.MainResults.Simulation

open Qatlib.Papers.AdiabStateGen03.MainResults

variable {n : ℕ}

/-- The operator of a circuit has norm at most one. -/
theorem Circuit.norm_unitary_le_one (C : Circuit n) : ‖C.unitary‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro ψ
  simpa using C.contract ψ

/-- Commuting Hamiltonian matrices induce commuting operators. -/
theorem commute_toOp_of_mul_comm (H₁ H₂ : Ham n) (h : H₁ * H₂ = H₂ * H₁) :
    Commute (toOp H₁) (toOp H₂) := by
  have hmap : Matrix.toEuclideanCLM (n := Dim n) (𝕜 := ℂ) (H₁ * H₂)
      = Matrix.toEuclideanCLM (n := Dim n) (𝕜 := ℂ) H₁
        * Matrix.toEuclideanCLM (n := Dim n) (𝕜 := ℂ) H₂ := map_mul _ _ _
  have hmap' : Matrix.toEuclideanCLM (n := Dim n) (𝕜 := ℂ) (H₂ * H₁)
      = Matrix.toEuclideanCLM (n := Dim n) (𝕜 := ℂ) H₂
        * Matrix.toEuclideanCLM (n := Dim n) (𝕜 := ℂ) H₁ := map_mul _ _ _
  show toOp H₁ * toOp H₂ = toOp H₂ * toOp H₁
  simp only [toOp]
  rw [← hmap, h]
  exact hmap'

/-- Multiplying two commuting operators by the same complex scalar preserves commutation. -/
theorem commute_smul_of_commute {A B : Op n} (c : ℂ) (h : A * B = B * A) :
    Commute (c • A) (c • B) := by
  show (c • A) * (c • B) = (c • B) * (c • A)
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul,
    smul_smul]
  have hx : A (B x) = B (A x) := by
    have h' := congrArg (fun f : Op n => f x) h
    simpa only [ContinuousLinearMap.mul_apply] using h'
  rw [hx]

/-- Real scalar multiplication of a complex operator agrees with multiplication by the
corresponding complex scalar. -/
@[simp] theorem real_smul_op (r : ℝ) (X : Op n) : r • X = ((r : ℂ)) • X := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.smul_apply]
  simp

/-- The evolution of a sum of commuting Hamiltonians equals the product of their evolutions at
the same time [AharonovTaShma2007]. -/
theorem timeEvolution_add_of_commute (H₁ H₂ : Ham n) (h : H₁ * H₂ = H₂ * H₁) (t : ℝ) :
    timeEvolution (H₁ + H₂) t = timeEvolution H₁ t * timeEvolution H₂ t := by
  have hc : Commute (toOp H₁) (toOp H₂) := commute_toOp_of_mul_comm H₁ H₂ h
  have hcI : Commute (Complex.I • toOp H₁) (Complex.I • toOp H₂) :=
    commute_smul_of_commute Complex.I hc
  have hct : Commute ((((-t : ℝ) : ℂ)) • (Complex.I • toOp H₁))
      ((((-t : ℝ) : ℂ)) • (Complex.I • toOp H₂)) :=
    commute_smul_of_commute (((-t : ℝ) : ℂ)) hcI
  unfold timeEvolution
  have hm : toOp (H₁ + H₂) = toOp H₁ + toOp H₂ := map_add _ _ _
  have hsplit : (-t : ℝ) • (Complex.I • toOp (H₁ + H₂))
      = (-t : ℝ) • (Complex.I • toOp H₁) + (-t : ℝ) • (Complex.I • toOp H₂) := by
    rw [hm, smul_add, smul_add]
  rw [hsplit]
  rw [real_smul_op (-t) (Complex.I • toOp H₁),
      real_smul_op (-t) (Complex.I • toOp H₂)]
  exact NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hct
    ((NormedSpace.expSeries_radius_eq_top ℂ (Op n)).symm ▸ edist_lt_top _ _)
    ((NormedSpace.expSeries_radius_eq_top ℂ (Op n)).symm ▸ edist_lt_top _ _)

/-- A `PolySize3` bound at accuracy `α / 4` yields a `PolySize3` bound at positive accuracy `α`
and positive time. -/
theorem PolySize3.accuracy_scale_four {C : Circuit n} {t α : ℝ}
    (ht : 0 < t) (hα : 0 < α) (h : PolySize3 n t (α / 4) C) : PolySize3 n t α C := by
  obtain ⟨c, k, hc⟩ := h
  have hinv : 1 / (α / 4) = 4 * (1 / α) := by
    field_simp
  have hB' : (n : ℝ) + t + 1 / (α / 4) + 1
      ≤ 8 * ((n : ℝ) + t + 1 / α + 1) := by
    rw [hinv]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hinvpos : 0 < 1 / α := by positivity
    nlinarith
  have hmono : ((n : ℝ) + t + 1 / (α / 4) + 1) ^ k
      ≤ (8 : ℝ) ^ k * ((n : ℝ) + t + 1 / α + 1) ^ k := by
    calc ((n : ℝ) + t + 1 / (α / 4) + 1) ^ k
        ≤ (8 * ((n : ℝ) + t + 1 / α + 1)) ^ k :=
          pow_le_pow_left₀ (by positivity) hB' k
      _ = (8 : ℝ) ^ k * ((n : ℝ) + t + 1 / α + 1) ^ k := by rw [mul_pow]
  refine ⟨c * 8 ^ k + c, k, ?_⟩
  have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  have hstep : (c : ℝ) * ((n : ℝ) + t + 1 / (α / 4) + 1) ^ k + (c : ℝ)
      ≤ (c : ℝ) * (8 : ℝ) ^ k * ((n : ℝ) + t + 1 / α + 1) ^ k + (c : ℝ) := by
    have := mul_le_mul_of_nonneg_left hmono hc0
    nlinarith
  have hBnn : (0 : ℝ) ≤ ((n : ℝ) + t + 1 / α + 1) ^ k := by
    have : (0 : ℝ) ≤ (n : ℝ) + t + 1 / α + 1 := by positivity
    exact pow_nonneg this k
  push_cast
  nlinarith [hc, hstep, hBnn, pow_nonneg (show (0 : ℝ) ≤ 8 by norm_num) k, hc0]

/-- The sum of two commuting simulatable Hamiltonians is simulatable. -/
theorem simulatable_add_of_commute {H₁ H₂ : Ham n}
    (h : H₁ * H₂ = H₂ * H₁) (h₁ : Simulatable H₁) (h₂ : Simulatable H₂) :
    Simulatable (H₁ + H₂) := by
  intro t ht α hα hα1
  have hquarter : 0 < α / 4 := by linarith
  have hquarter1 : α / 4 < 1 := by linarith
  obtain ⟨C₁, hp₁, hd₁⟩ := h₁ t ht (α / 4) hquarter hquarter1
  obtain ⟨C₂, hp₂, hd₂⟩ := h₂ t ht (α / 4) hquarter hquarter1
  refine ⟨circComp C₁ C₂,
      PolySize3.accuracy_scale_four ht hα (PolySize3.circComp ht hquarter hp₁ hp₂), ?_⟩
  rw [circComp_unitary, timeEvolution_add_of_commute H₁ H₂ h t]
  have hsplit : C₁.unitary.comp C₂.unitary
        - timeEvolution H₁ t * timeEvolution H₂ t
      = (C₁.unitary - timeEvolution H₁ t).comp C₂.unitary
        + C₁.unitary.comp (C₂.unitary - timeEvolution H₂ t)
        + (timeEvolution H₁ t - C₁.unitary).comp
            (C₂.unitary - timeEvolution H₂ t) := by
    ext ψ
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, map_sub]
    abel
  rw [hsplit]
  have hC₁ : ‖C₁.unitary‖ ≤ 1 := Circuit.norm_unitary_le_one C₁
  have hC₂ : ‖C₂.unitary‖ ≤ 1 := Circuit.norm_unitary_le_one C₂
  have hE₁ : ‖timeEvolution H₁ t - C₁.unitary‖ ≤ α / 4 := by
    rw [norm_sub_rev]
    exact hd₁
  have hcomp₁ : ‖(C₁.unitary - timeEvolution H₁ t).comp C₂.unitary‖ ≤ α / 4 := by
    calc ‖(C₁.unitary - timeEvolution H₁ t).comp C₂.unitary‖
        ≤ ‖C₁.unitary - timeEvolution H₁ t‖ * ‖C₂.unitary‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (α / 4) * 1 := by
          exact mul_le_mul hd₁ hC₂ (norm_nonneg _) (by linarith)
      _ = α / 4 := mul_one _
  have hcomp₂ : ‖C₁.unitary.comp (C₂.unitary - timeEvolution H₂ t)‖ ≤ α / 4 := by
    calc ‖C₁.unitary.comp (C₂.unitary - timeEvolution H₂ t)‖
        ≤ ‖C₁.unitary‖ * ‖C₂.unitary - timeEvolution H₂ t‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (α / 4) := by
          exact mul_le_mul hC₁ hd₂ (norm_nonneg _) (by norm_num)
      _ = α / 4 := one_mul _
  have hcomp₃ : ‖(timeEvolution H₁ t - C₁.unitary).comp
        (C₂.unitary - timeEvolution H₂ t)‖ ≤ (α / 4) * (α / 4) := by
    calc ‖(timeEvolution H₁ t - C₁.unitary).comp
          (C₂.unitary - timeEvolution H₂ t)‖
        ≤ ‖timeEvolution H₁ t - C₁.unitary‖
            * ‖C₂.unitary - timeEvolution H₂ t‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (α / 4) * (α / 4) := by
          exact mul_le_mul hE₁ hd₂ (norm_nonneg _) (by linarith)
  calc ‖(C₁.unitary - timeEvolution H₁ t).comp C₂.unitary
        + C₁.unitary.comp (C₂.unitary - timeEvolution H₂ t)
        + (timeEvolution H₁ t - C₁.unitary).comp
            (C₂.unitary - timeEvolution H₂ t)‖
      ≤ ‖(C₁.unitary - timeEvolution H₁ t).comp C₂.unitary
          + C₁.unitary.comp (C₂.unitary - timeEvolution H₂ t)‖
        + ‖(timeEvolution H₁ t - C₁.unitary).comp
            (C₂.unitary - timeEvolution H₂ t)‖ := norm_add_le _ _
    _ ≤ (‖(C₁.unitary - timeEvolution H₁ t).comp C₂.unitary‖
          + ‖C₁.unitary.comp (C₂.unitary - timeEvolution H₂ t)‖)
        + ‖(timeEvolution H₁ t - C₁.unitary).comp
            (C₂.unitary - timeEvolution H₂ t)‖ := by
        have := norm_add_le ((C₁.unitary - timeEvolution H₁ t).comp C₂.unitary)
          (C₁.unitary.comp (C₂.unitary - timeEvolution H₂ t))
        linarith
    _ ≤ (α / 4 + α / 4) + (α / 4) * (α / 4) := by
        have := add_le_add (add_le_add hcomp₁ hcomp₂) hcomp₃
        linarith
    _ ≤ α := by
        have hαsq : α ^ 2 < α := by nlinarith [mul_lt_mul_of_pos_left hα1 hα]
        nlinarith

end Qatlib.Papers.AdiabStateGen03.MainResults.Simulation
