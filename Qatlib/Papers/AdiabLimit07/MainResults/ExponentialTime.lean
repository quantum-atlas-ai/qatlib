/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabLimit07.MainResults.ProbabilityFlow

/-!
# Probability bounds for a diagonal binary driver

Defines the scaled complement projector `finalProjector` and its interpolation with a diagonal
driver. The module proves that computational basis probabilities have zero derivative for this
diagonal evolution and derives the stated finite-time bounds using a derivative estimate and a
bound on two basis probabilities. See [IoannouMosca2008].

## Main statements

* `beta0_deriv_zero`: Every computational basis probability is constant to first order along the
  diagonal evolution.
* `beta0_lower_bound`: An initially unit basis probability satisfies a finite-time lower bound.
* `exponential_time_eq30`: Combines the flow and overlap estimates into the target probability
  bound.

## References

* [Ioannou and Mosca, 2008][IoannouMosca2008]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AdiabLimit07.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath
open scoped BigOperators Matrix

variable {n : ℕ}

/-- The scaled complement of the computational basis projector at `w`, equal to `E1` times `I -
|w⟩⟨w|`. -/
def finalProjector (E1 : ℝ) (w : Reg n) : Matrix (Reg n) (Reg n) ℂ :=
  (E1 : ℂ) • (1 - Matrix.of (fun x y => if x = w ∧ y = w then (1 : ℂ) else 0))

/-- The affine interpolation between the diagonal energies `Fdiag` and `finalProjector E1 w`. -/
def binaryDriver (Fdiag : Reg n → ℝ) (E1 : ℝ) (w : Reg n) (s : ℝ) :
    Matrix (Reg n) (Reg n) ℂ :=
  (1 - s) • Matrix.diagonal (fun z => (Fdiag z : ℂ)) + s • finalProjector E1 w

/-- An entry of the final projector is `E1` times the identity entry minus the projector entry
at `w`. -/
theorem finalProjector_apply (E1 : ℝ) (w x y : Reg n) :
    finalProjector E1 w x y
      = (E1 : ℂ) * ((if x = y then (1 : ℂ) else 0)
          - (if x = w ∧ y = w then (1 : ℂ) else 0)) := by
  unfold finalProjector
  simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply]

/-- Every entry of the final projector has zero imaginary part. -/
theorem finalProjector_im (E1 : ℝ) (w x y : Reg n) :
    (finalProjector E1 w x y).im = 0 := by
  rw [finalProjector_apply]
  split_ifs <;> simp

/-- Every off-diagonal entry of the final projector is zero. -/
theorem finalProjector_offdiag {E1 : ℝ} {w : Reg n} {x y : Reg n} (hxy : x ≠ y) :
    finalProjector E1 w x y = 0 := by
  rw [finalProjector_apply, if_neg hxy]
  have hconj : ¬ (x = w ∧ y = w) := fun h => hxy (h.1.trans h.2.symm)
  rw [if_neg hconj]
  ring

/-- Every off-diagonal entry of the binary driver is zero. -/
theorem binaryDriver_offdiag (Fdiag : Reg n → ℝ) (E1 : ℝ) (w : Reg n) (s : ℝ)
    {x y : Reg n} (hxy : x ≠ y) :
    binaryDriver Fdiag E1 w s x y = 0 := by
  unfold binaryDriver
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply]
  have h1 : Matrix.diagonal (fun z => (Fdiag z : ℂ)) x y = 0 := by
    rw [Matrix.diagonal_apply, if_neg hxy]
  rw [h1, finalProjector_offdiag (E1 := E1) (w := w) hxy]
  simp

/-- Every entry of the binary driver has zero imaginary part. -/
theorem binaryDriver_im (Fdiag : Reg n → ℝ) (E1 : ℝ) (w : Reg n) (s : ℝ) (x y : Reg n) :
    (binaryDriver Fdiag E1 w s x y).im = 0 := by
  unfold binaryDriver
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Complex.add_im,
    Complex.smul_im, Complex.smul_im]
  have h1 : (Matrix.diagonal (fun z => (Fdiag z : ℂ)) x y).im = 0 := by
    rw [Matrix.diagonal_apply]
    split_ifs <;> simp
  have h2 : (finalProjector E1 w x y).im = 0 := finalProjector_im E1 w x y
  rw [h1, h2]
  simp

/-- Multiplication by the binary driver acts coordinatewise by its diagonal entries. -/
theorem binaryDriver_mulVec_diag (Fdiag : Reg n → ℝ) (E1 : ℝ) (w : Reg n) (s : ℝ)
    (γ : QState (Reg n)) (x : Reg n) :
    (binaryDriver Fdiag E1 w s).mulVec γ x
      = (binaryDriver Fdiag E1 w s x x) * γ x := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single x]
  · intro y _ hy
    rw [binaryDriver_offdiag Fdiag E1 w s (Ne.symm hy), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- A differentiable real function whose derivative has absolute value at most `B` on `[0,T]`
satisfies `|p T - p 0| ≤ B * T` for nonnegative `T`. -/
theorem abs_sub_le_of_deriv_bound {p : ℝ → ℝ} {T B : ℝ} (hT : 0 ≤ T)
    (hdiff : ∀ t ∈ Set.Icc 0 T, DifferentiableAt ℝ p t)
    (hbound : ∀ t ∈ Set.Icc 0 T, |deriv p t| ≤ B) :
    |p T - p 0| ≤ B * T := by
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) T) := convex_Icc _ _
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Icc (0 : ℝ) T)
    (f := p) (C := B) hdiff
    (fun t ht => by rw [Real.norm_eq_abs]; exact hbound t ht) hconv
    (Set.left_mem_Icc.mpr hT) (Set.right_mem_Icc.mpr hT)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg hT] at h
  exact h

/-- The assumed lower bound at `u`, two-probability inequality, and basis overlap formula imply
the upper bound `(2 * E1 * T + 1) / sqrt (2 ^ n)` at `w`. -/
theorem eq30_from_28_29 {E1 T : ℝ} (ψ : QState (Reg n)) (w u : Reg n)
    (hE1 : 0 ≤ E1) (hT : 0 ≤ T)
    (h28 : 1 - 2 * E1 * T / Real.sqrt (((2 : ℕ) ^ n : ℝ))
              ≤ BornProb ψ u)
    (h29 : BornProb ψ w + BornProb ψ u
              ≤ 1 + ‖Qatlib.Foundations.PureStateMath.Inner (Ket u) (Ket w)‖)
    (hinner : ‖Qatlib.Foundations.PureStateMath.Inner (Ket u) (Ket w)‖ = 1 / Real.sqrt (((2 : ℕ) ^ n : ℝ))) :
    BornProb ψ w ≤ 2 * E1 * T / Real.sqrt (((2 : ℕ) ^ n : ℝ))
                      + 1 / Real.sqrt (((2 : ℕ) ^ n : ℝ)) := by
  have := h28
  have h29' := h29
  rw [hinner] at h29'
  linarith

/-- Under coordinatewise Schrödinger evolution with the diagonal binary driver, the derivative
of every computational basis Born probability is zero. -/
theorem beta0_deriv_zero {Fdiag : Reg n → ℝ} {E1 : ℝ} {w u : Reg n}
    {s : ℝ → ℝ} {ψ : ℝ → QState (Reg n)} {T : ℝ}
    (hSchrod : SchrodingerIVP (fun t => binaryDriver Fdiag E1 w (s t)) ψ T)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    deriv (fun τ => BornProb (ψ τ) u) t = 0 := by
  rw [(hasDerivAt_bornProb hSchrod ht u).deriv]
  have hmv := binaryDriver_mulVec_diag Fdiag E1 w (s t) (ψ t) u
  rw [hmv]
  have hc : (binaryDriver Fdiag E1 w (s t) u u).im = 0 := binaryDriver_im Fdiag E1 w (s t) u u
  rw [re_mul_neg_I_im]
  have hX : (starRingEnd ℂ (ψ t u)
        * ((binaryDriver Fdiag E1 w (s t) u u) * ψ t u)).im = 0 := by
    have hre : starRingEnd ℂ (ψ t u) * ((binaryDriver Fdiag E1 w (s t) u u) * ψ t u)
        = (binaryDriver Fdiag E1 w (s t) u u)
            * (starRingEnd ℂ (ψ t u) * ψ t u) := by ring
    rw [hre]
    have hnorm : starRingEnd ℂ (ψ t u) * ψ t u
        = ((Complex.normSq (ψ t u) : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]
    rw [hnorm, Complex.mul_im, hc]
    simp
  rw [hX]
  ring

/-- For the binary driver with `E1 ≥ 0` and schedule in `[0,1]`, the absolute derivative of each
basis probability is at most `2 * E1 / sqrt (2 ^ n)`. -/
theorem beta0_flow_bound {Fdiag : Reg n → ℝ} {E1 : ℝ} (w u : Reg n)
    (s : ℝ → ℝ) (hE1 : 0 ≤ E1)
    (ψ : ℝ → QState (Reg n)) (T : ℝ)
    (hSchrod : SchrodingerIVP (fun t => binaryDriver Fdiag E1 w (s t)) ψ T)
    (hs0 : ∀ t, 0 ≤ s t) (hs1 : ∀ t, s t ≤ 1) :
    ∀ t ∈ Set.Icc 0 T,
      |deriv (fun τ => BornProb (ψ τ) u) t| ≤ 2 * E1 / Real.sqrt (((2 : ℕ) ^ n : ℝ)) := by
  intro t ht
  rw [beta0_deriv_zero hSchrod ht, abs_zero]
  exact div_nonneg (by positivity) (Real.sqrt_nonneg _)

/-- An initially unit basis probability is at least `1 - 2 * E1 * T / sqrt (2 ^ n)` after
nonnegative time `T`. -/
theorem beta0_lower_bound {Fdiag : Reg n → ℝ} {E1 : ℝ} (w u : Reg n)
    (s : ℝ → ℝ) (hE1 : 0 ≤ E1)
    (ψ : ℝ → QState (Reg n)) (T : ℝ)
    (hSchrod : SchrodingerIVP (fun t => binaryDriver Fdiag E1 w (s t)) ψ T)
    (hs0 : ∀ t, 0 ≤ s t) (hs1 : ∀ t, s t ≤ 1)
    (hT : 0 ≤ T)
    (hinit : BornProb (ψ 0) u = 1) :
    1 - 2 * E1 * T / Real.sqrt (((2 : ℕ) ^ n : ℝ)) ≤ BornProb (ψ T) u := by
  have hdiff : ∀ t ∈ Set.Icc 0 T, DifferentiableAt ℝ (fun τ => BornProb (ψ τ) u) t :=
    fun t ht => (hasDerivAt_bornProb hSchrod ht u).differentiableAt
  have hbound : ∀ t ∈ Set.Icc 0 T, |deriv (fun τ => BornProb (ψ τ) u) t| ≤ 0 := by
    intro t ht
    rw [beta0_deriv_zero hSchrod ht, abs_zero]
  have habs := abs_sub_le_of_deriv_bound hT hdiff hbound
  rw [zero_mul] at habs
  have heq : BornProb (ψ T) u = BornProb (ψ 0) u := by
    have hzero : |BornProb (ψ T) u - BornProb (ψ 0) u| = 0 :=
      le_antisymm habs (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp hzero)
  rw [heq, hinit]
  have hnonneg : 0 ≤ 2 * E1 * T / Real.sqrt (((2 : ℕ) ^ n : ℝ)) := by
    apply div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hE1) hT)
    exact Real.sqrt_nonneg _
  linarith

/-- For a normalized state, the sum of the Born probabilities at `w` and `u` is at most one plus
the norm of their basis-vector inner product. -/
theorem orthogonality_ineq (ψ : QState (Reg n)) (w u : Reg n) (hψ : Normalized ψ) :
    BornProb ψ w + BornProb ψ u
      ≤ 1 + ‖Qatlib.Foundations.PureStateMath.Inner
              (Ket u) (Ket w)‖ := by
  have htot : (∑ z : Reg n, BornProb ψ z) = 1 := by
    simpa [BornProb] using! hψ
  by_cases huw : u = w
  · rw [huw, inner_ket_ket, if_pos rfl]
    have hw : BornProb ψ w ≤ 1 := by
      have hle : BornProb ψ w ≤ ∑ z : Reg n, BornProb ψ z :=
        Finset.single_le_sum (f := fun z => BornProb ψ z)
          (fun i _ => bornProb_nonneg ψ i) (Finset.mem_univ w)
      linarith [htot]
    have hone : ‖(1 : ℂ)‖ = 1 := by simp
    rw [hone]
    nlinarith [hw, bornProb_nonneg ψ w]
  · rw [inner_ket_ket, if_neg huw]
    simp only [norm_zero, add_zero]
    have hpair : BornProb ψ w + BornProb ψ u
        = ∑ z ∈ ({w, u} : Finset (Reg n)), BornProb ψ z := by
      rw [Finset.sum_insert (by simp [Ne.symm huw])]
      simp
    have hsub : (∑ z ∈ ({w, u} : Finset (Reg n)), BornProb ψ z)
        ≤ ∑ z : Reg n, BornProb ψ z :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun z _ _ => bornProb_nonneg ψ z)
    linarith [htot]

/-- Under the stated evolution, initialization, normalization, and overlap hypotheses, the final
probability at `w` is at most `(2 * E1 * T + 1) / sqrt (2 ^ n)`. -/
theorem exponential_time_eq30 {Fdiag : Reg n → ℝ} {E1 : ℝ} (w u : Reg n)
    (s : ℝ → ℝ) (hE1 : 0 ≤ E1)
    (ψ : ℝ → QState (Reg n)) (T : ℝ)
    (hSchrod : SchrodingerIVP (fun t => binaryDriver Fdiag E1 w (s t)) ψ T)
    (hs0 : ∀ t, 0 ≤ s t) (hs1 : ∀ t, s t ≤ 1)
    (hT : 0 ≤ T)
    (hinit : BornProb (ψ 0) u = 1)
    (hψnorm : Normalized (ψ T))
    (hinner : ‖Qatlib.Foundations.PureStateMath.Inner (Ket u) (Ket w)‖ = 1 / Real.sqrt (((2 : ℕ) ^ n : ℝ))) :
    BornProb (ψ T) w ≤ 2 * E1 * T / Real.sqrt (((2 : ℕ) ^ n : ℝ))
                        + 1 / Real.sqrt (((2 : ℕ) ^ n : ℝ)) := by
  exact eq30_from_28_29 (ψ T) w u hE1 hT
    (beta0_lower_bound w u s hE1 ψ T hSchrod hs0 hs1 hT hinit)
    (orthogonality_ineq (ψ T) w u hψnorm) hinner

end Qatlib.Papers.AdiabLimit07.MainResults
