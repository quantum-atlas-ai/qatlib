/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Qatlib.Concepts.SqEstimation.TraceBilinear
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SqEstimation.InnerProduct
open Qatlib.Concepts.SqEstimation.TraceBilinear

namespace Qatlib.Papers.AnyonicSpin06.MainResults.ColoredJonesWRT

def rootA (r : ℕ) : ℂ :=
  Complex.exp (Complex.I * ((Real.pi / (2 * (r : ℝ)) : ℝ) : ℂ))

theorem norm_rootA (r : ℕ) : ‖rootA r‖ = 1 := by
  unfold rootA
  rw [Complex.norm_exp]
  have h : (Complex.I * ((Real.pi / (2 * (r : ℝ)) : ℝ) : ℂ)).re
      = - ((Real.pi / (2 * (r : ℝ)) : ℝ) : ℂ).im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [h, Complex.ofReal_im]
  simp

def fibonacciA : ℂ := Complex.exp (Complex.I * ((3 * Real.pi / 5 : ℝ) : ℂ))

theorem norm_fibonacciA : ‖fibonacciA‖ = 1 := by
  unfold fibonacciA
  rw [Complex.norm_exp]
  have h : (Complex.I * ((3 * Real.pi / 5 : ℝ) : ℂ)).re
      = - ((3 * Real.pi / 5 : ℝ) : ℂ).im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [h, Complex.ofReal_im]
  simp

def WRT (r : ℕ) (Delta bracket : ℕ → ℂ) : ℂ :=
  ∑ a ∈ Finset.range (r - 1), Delta a * bracket a

theorem WRT_eq_finite_sum (r : ℕ) (Delta bracket : ℕ → ℂ) :
    WRT r Delta bracket = ∑ a ∈ Finset.range (r - 1), Delta a * bracket a := rfl

theorem WRT_error_bound {r : ℕ} (Delta bracket est : ℕ → ℂ) {D δ : ℝ}
    (hD : ∀ a, ‖Delta a‖ ≤ D) (hδ : ∀ a, ‖bracket a - est a‖ ≤ δ) :
    ‖WRT r Delta bracket - WRT r Delta est‖ ≤ ((r - 1 : ℕ) : ℝ) * D * δ := by
  unfold WRT
  rw [← Finset.sum_sub_distrib]
  calc ‖∑ a ∈ Finset.range (r - 1), (Delta a * bracket a - Delta a * est a)‖
      ≤ ∑ a ∈ Finset.range (r - 1), ‖Delta a * bracket a - Delta a * est a‖ :=
        norm_sum_le _ _
    _ = ∑ a ∈ Finset.range (r - 1), ‖Delta a‖ * ‖bracket a - est a‖ := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← mul_sub, norm_mul]
    _ ≤ ∑ a ∈ Finset.range (r - 1), D * δ := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul (hD a) (hδ a) (norm_nonneg _) (le_trans (norm_nonneg _) (hD a))
    _ = ((r - 1 : ℕ) : ℝ) * D * δ := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

theorem matrix_element_is_sqInnerTarget {n : ℕ}
    (a : FiniteSQInput (Fin n × Fin n)) (A : Operator n)
    (hA : ∀ p, a.target p = A p.1 p.2) (x y : Fin n → ℂ) :
    sqInnerTarget a.target (fun p => x p.1 * star (y p.2)) =
      star (∑ i, ∑ j, star (x i) * A i j * y j) :=
  sqInnerTarget_bilinear a A hA x y

theorem trace_is_sqInnerTarget {n : ℕ} (a : FiniteSQInput (Fin n × Fin n))
    (A : Operator n) (hz : ∀ p, a.target p = (1 : Operator n) p.1 p.2) :
    sqInnerTarget a.target (fun p => A p.1 p.2) = Matrix.trace A := by
  simpa using! sqInnerTarget_matrix_trace a A 1 hz

theorem recoupling_sum_collapse {ι : Type*} [DecidableEq ι] (s : Finset ι) (x₀ : ι)
    (B : ι → ℂ) (D : ℂ) :
    ∑ x ∈ s, B x * (if x = x₀ then D else 0) = if x₀ ∈ s then B x₀ * D else 0 := by
  by_cases h : x₀ ∈ s
  · rw [if_pos h, Finset.sum_eq_single x₀]
    · simp
    · intro b hb hbne
      simp [hbne]
    · intro hx
      exact absurd h hx
  · rw [if_neg h, Finset.sum_eq_zero]
    intro x hx
    have hne : x ≠ x₀ := by rintro rfl; exact h hx
    simp [hne]

theorem closed_bracket_single_term {ι : Type*} [DecidableEq ι] [Zero ι]
    (s : Finset ι) (B : ι → ℂ) (D : ℂ) :
    ∑ x ∈ s, B x * (if x = 0 then D else 0) = if (0 : ι) ∈ s then B 0 * D else 0 :=
  recoupling_sum_collapse s 0 B D

theorem WRT_add {r : ℕ} (Delta b1 b2 : ℕ → ℂ) :
    WRT r Delta (fun a => b1 a + b2 a) = WRT r Delta b1 + WRT r Delta b2 := by
  unfold WRT
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem WRT_single {r : ℕ} (Delta : ℕ → ℂ) (x₀ : ℕ) (D : ℂ) :
    WRT r Delta (fun a => if a = x₀ then D else 0)
      = if x₀ ∈ Finset.range (r - 1) then Delta x₀ * D else 0 := by
  unfold WRT
  exact recoupling_sum_collapse (Finset.range (r - 1)) x₀ Delta D

theorem WRT_zero_bracket (r : ℕ) (Delta : ℕ → ℂ) :
    WRT r Delta (fun _ => 0) = 0 := by
  unfold WRT
  simp

end Qatlib.Papers.AnyonicSpin06.MainResults.ColoredJonesWRT
