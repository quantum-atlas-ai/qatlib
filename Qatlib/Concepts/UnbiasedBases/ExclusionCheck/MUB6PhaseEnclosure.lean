/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.Qubit
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.GCongr

@[expose] public section
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Concepts.UnbiasedBases.ExclusionCheck

noncomputable def phase (x : ℝ) : ℂ := Complex.exp (Complex.I * (x : ℂ))
noncomputable def polynomial32 (x : ℝ) : ℂ :=
  ∑ m ∈ Finset.range 33, (Complex.I * (x : ℂ)) ^ m / (m.factorial : ℂ)

/-- Shows that every complex phase has norm one. -/
theorem phase_norm (x : ℝ) : ‖phase x‖ = 1 := by
  simp [phase, Complex.norm_exp]

/-- Bounds the degree-thirty-two polynomial phase approximation error by one over one hundred
million for arguments of absolute value at most seven. -/
theorem phase_polynomial_error (x : ℝ) (hx : |x| ≤ 7) :
    ‖phase x - polynomial32 x‖ ≤ (1 : ℝ) / 100000000 := by
  have hn : ‖Complex.I * (x : ℂ)‖ ≤ 7 := by simpa using hx
  have h := Complex.exp_bound' (x := Complex.I * (x : ℂ)) (n := 33)
    (show ‖Complex.I * (x : ℂ)‖ / (33 + 1 : ℕ) ≤ (1 : ℝ)/2 by norm_num; linarith)
  change ‖phase x - polynomial32 x‖ ≤ _ at h
  calc
    _ ≤ ‖Complex.I * (x : ℂ)‖ ^ 33 / (Nat.factorial 33 : ℝ) * 2 := h
    _ ≤ 7 ^ 33 / (Nat.factorial 33 : ℝ) * 2 := by gcongr
    _ ≤ _ := by norm_num

/-- Shows that the complex phase map is Lipschitz with constant one. -/
theorem phase_distance (x y : ℝ) : ‖phase x - phase y‖ ≤ |x-y| := by
  have he : phase x - phase y = phase y * (phase (x-y) - 1) := by
    unfold phase
    rw [mul_sub, mul_one, ← Complex.exp_add]
    have harg : Complex.I * (y : ℂ) + Complex.I * ((x-y : ℝ) : ℂ) =
        Complex.I * (x : ℂ) := by push_cast; ring
    rw [harg]
  rw [he, norm_mul, phase_norm, one_mul]
  simpa [phase, Real.norm_eq_abs] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x-y))

noncomputable def phaseVector (θ : Fin 5 → ℝ) : QState (Fin 6) :=
  Fin.cases 1 (fun j => phase (θ j))

/-- Expresses the inner product of phase vectors as one plus the sum of their relative phases. -/
theorem phase_inner (α β : Fin 5 → ℝ) :
    Inner (phaseVector α) (phaseVector β) = 1 + ∑ j : Fin 5, phase (β j - α j) := by
  rw [inner_apply, Fin.sum_univ_succ]
  simp only [phaseVector, Fin.cases_zero, Fin.cases_succ, map_one, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  unfold phase
  rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

noncomputable def polynomialOverlap (a b : Fin 5 → ℝ) : ℂ :=
  1 + ∑ j : Fin 5, polynomial32 (b j - a j)

/-- Bounds the error between a phase-vector inner product and its polynomial overlap by the
total coordinate uncertainty plus the polynomial approximation error. -/
theorem pair_enclosure (α β a b r s : Fin 5 → ℝ)
    (hα : ∀ j, |α j - a j| ≤ r j) (hβ : ∀ j, |β j - b j| ≤ s j)
    (hc : ∀ j, |b j - a j| ≤ 7) :
    ‖Inner (phaseVector α) (phaseVector β) - polynomialOverlap a b‖ ≤
      (∑ j : Fin 5, (r j + s j)) + (5 : ℝ) / 100000000 := by
  have each (j : Fin 5) :
      ‖phase (β j - α j) - polynomial32 (b j - a j)‖ ≤
        r j + s j + (1 : ℝ) / 100000000 := by
    have hd : |(β j - α j) - (b j - a j)| ≤ r j + s j := by
      have he : (β j - α j) - (b j - a j) = (β j - b j) - (α j - a j) := by ring
      rw [he]
      have ht := abs_add_le (β j - b j) (-(α j - a j))
      rw [abs_neg] at ht
      have habs : |(β j - b j) - (α j - a j)| ≤ |β j - b j| + |α j - a j| := by
        simpa only [sub_eq_add_neg] using ht
      linarith [hα j, hβ j]
    calc
      _ = ‖(phase (β j - α j) - phase (b j - a j)) +
          (phase (b j - a j) - polynomial32 (b j - a j))‖ := by congr 1; ring
      _ ≤ ‖phase (β j - α j) - phase (b j - a j)‖ +
          ‖phase (b j - a j) - polynomial32 (b j - a j)‖ := norm_add_le _ _
      _ ≤ (r j + s j) + (1 : ℝ) / 100000000 :=
        add_le_add ((phase_distance _ _).trans hd) (phase_polynomial_error _ (hc j))
  rw [phase_inner, polynomialOverlap, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin 5, ‖phase (β j - α j) - polynomial32 (b j - a j)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 5, (r j + s j + (1 : ℝ)/100000000) := Finset.sum_le_sum (fun j _ => each j)
    _ = _ := by simp [Finset.sum_add_distrib, div_eq_mul_inv]

end Qatlib.Concepts.UnbiasedBases.ExclusionCheck
