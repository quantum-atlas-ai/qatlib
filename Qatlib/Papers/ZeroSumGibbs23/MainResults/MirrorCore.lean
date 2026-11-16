/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ZeroSumGibbs23.MainResults.Model.SourceModel
public import Qatlib.Papers.ZeroSumGibbs23.MainResults.GibbsStability.SourceGibbsStability

@[expose] public section


/-!
# MirrorCore deterministic core

This module preserves closed algebraic and finite-dimensional source results
from arXiv:2301.03763v1. It does not assert a circuit implementation, concentration
bound, or end-to-end algorithmic complexity.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Matrix
namespace Qatlib.Papers.ZeroSumGibbs23.MainResults.MirrorCore
open Qatlib.Papers.ZeroSumGibbs23.MainResults.Model
open Qatlib.Papers.ZeroSumGibbs23.MainResults.GibbsStability
variable {m n N : ℕ}

/-- **Lemma 5**, printed p.19. If `u, ũ ∈ Δ_m` with `‖u − ũ‖₁ ≤ δ` and
`g̃ := A_{i:}` for `i ∼ ũ` (so `E g̃ = Aᵀũ`), while `g := Aᵀu`, then
`‖g − E g̃‖_∞ ≤ δ`. Componentwise: `|(Aᵀu)_j − (Aᵀũ)_j| ≤ δ`. -/
theorem gradient_error (A : Matrix (Fin m) (Fin n) ℝ) (hA : MaxEntryBound A 1)
    (u u' : Fin m → ℝ) {δ : ℝ} (hδ : l1Norm (fun i => u i - u' i) ≤ δ) (j : Fin n) :
    |colSum A u j - colSum A u' j| ≤ δ := by
  exact le_trans (abs_colSum_diff_le A hA u' u j) hδ

/-! ### Averaging iterates -/

/-- The average of a finite family of vectors. -/
def avgVec {T n : ℕ} (x : Fin T → Fin n → ℝ) : Fin n → ℝ :=
  fun i => (∑ t, x t i) / T

/-- An average of simplex points is a simplex point. -/
theorem isDist_avg {T n : ℕ} (hT : 0 < T) {x : Fin T → Fin n → ℝ}
    (hx : ∀ t, IsDist (x t)) : IsDist (avgVec x) := by
  constructor
  · intro i
    unfold avgVec
    exact div_nonneg (Finset.sum_nonneg fun t _ => (hx t).1 i) (Nat.cast_nonneg T)
  · unfold avgVec
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, Finset.sum_comm]
    have hinner : ∀ t : Fin T, (∑ i : Fin n, x t i) = 1 := fun t => (hx t).2
    simp only [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    exact mul_inv_cancel₀ (by exact_mod_cast Nat.pos_iff_ne_zero.mp hT)

/-- Convexity of the ℓ1 norm: the average of vectors each `δ`-close is
`δ`-close. This is the first step of the proof of Lemma 6 (p.21). -/
theorem average_close {T n : ℕ} (hT : 0 < T) (u ũ : Fin T → Fin n → ℝ) {δ : ℝ}
    (h : ∀ t, l1Norm (fun i => ũ t i - u t i) ≤ δ) :
    l1Norm (fun i => avgVec ũ i - avgVec u i) ≤ δ := by
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hdiff : (fun i => avgVec ũ i - avgVec u i) =
      fun i => (∑ t, (ũ t i - u t i)) / T := by
    funext i
    unfold avgVec
    rw [← sub_div, ← Finset.sum_sub_distrib]
  rw [hdiff]
  have h1 : l1Norm (fun i => (∑ t, (ũ t i - u t i)) / T) =
      (1 / T) * ∑ i, |∑ t, (ũ t i - u t i)| := by
    unfold l1Norm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_div, abs_of_pos hTR, div_eq_mul_inv]
    ring
  have h2 : (∑ i, |∑ t, (ũ t i - u t i)|) ≤ ∑ t, l1Norm (fun i => ũ t i - u t i) := by
    calc
      ∑ i, |∑ t, (ũ t i - u t i)| ≤ ∑ i, ∑ t, |ũ t i - u t i| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ = ∑ t, ∑ i, |ũ t i - u t i| := Finset.sum_comm
      _ = ∑ t, l1Norm (fun i => ũ t i - u t i) := rfl
  have h3 : (∑ t : Fin T, l1Norm (fun i => ũ t i - u t i)) ≤ ∑ _t : Fin T, δ :=
    Finset.sum_le_sum fun t _ => h t
  have h4 : (∑ _t : Fin T, δ) = (T : ℝ) * δ := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hsum : (∑ i, |∑ t, (ũ t i - u t i)|) ≤ (T : ℝ) * δ := by
    calc
      ∑ i, |∑ t, (ũ t i - u t i)| ≤ ∑ t, l1Norm (fun i => ũ t i - u t i) := h2
      _ ≤ (T : ℝ) * δ := le_trans h3 (le_of_eq h4)
  rw [h1]
  calc
    (1 / T) * ∑ i, |∑ t, (ũ t i - u t i)| ≤ (1 / T) * ((T : ℝ) * δ) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = δ := by
      have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTR
      rw [div_eq_mul_inv, one_mul, ← mul_assoc, inv_mul_cancel₀ hTne, one_mul]

/-! ### Payoff Lipschitz bounds -/

/-- A row combination against a simplex point has entries in `[-1, 1]` when
`‖A‖_max ≤ 1`. -/
theorem row_abs_le_one (A : Matrix (Fin m) (Fin n) ℝ) (hA : MaxEntryBound A 1)
    {v : Fin n → ℝ} (hv : IsDist v) (i : Fin m) : |rowSum A v i| ≤ 1 := by
  unfold rowSum
  calc
    |∑ j, A i j * v j| ≤ ∑ j, |A i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |A i j| * |v j| := by simp [abs_mul]
    _ ≤ ∑ j, 1 * v j := by
      refine Finset.sum_le_sum fun j _ => ?_
      rw [abs_of_nonneg (hv.1 j)]
      exact mul_le_mul_of_nonneg_right (hA i j) (hv.1 j)
    _ = 1 := by
      rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => one_mul (v j)), hv.2]

/-- Payoff is `‖·‖₁`-Lipschitz in the maximiser against any simplex point. -/
theorem payoff_lipsch_u (A : Matrix (Fin m) (Fin n) ℝ) (hA : MaxEntryBound A 1)
    {u u' : Fin m → ℝ} {v : Fin n → ℝ} (hv : IsDist v) :
    |payoff A u v - payoff A u' v| ≤ l1Norm (fun i => u i - u' i) := by
  have hsplit : payoff A u v - payoff A u' v = ∑ i, (u i - u' i) * rowSum A v i := by
    rw [payoff_eq_sum_mul_row, payoff_eq_sum_mul_row, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  calc
    |payoff A u v - payoff A u' v| = |∑ i, (u i - u' i) * rowSum A v i| := by rw [hsplit]
    _ ≤ ∑ i, |(u i - u' i) * rowSum A v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |u i - u' i| * |rowSum A v i| := by simp [abs_mul]
    _ ≤ ∑ i, |u i - u' i| * 1 :=
      Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (row_abs_le_one A hA hv i) (abs_nonneg _)
    _ = l1Norm (fun i => u i - u' i) := by simp [l1Norm]

/-- Payoff is `‖·‖₁`-Lipschitz in the minimiser against any simplex point. -/
theorem payoff_lipsch_v (A : Matrix (Fin m) (Fin n) ℝ) (hA : MaxEntryBound A 1)
    {u : Fin m → ℝ} {v v' : Fin n → ℝ} (hu : IsDist u) :
    |payoff A u v - payoff A u v'| ≤ l1Norm (fun j => v j - v' j) := by
  have hsplit : payoff A u v - payoff A u v' = ∑ j, (v j - v' j) * colSum A u j := by
    rw [payoff_eq_sum_mul_col, payoff_eq_sum_mul_col, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hcol : ∀ j, |colSum A u j| ≤ 1 := by
    intro j
    unfold colSum
    calc
      |∑ i, A i j * u i| ≤ ∑ i, |A i j * u i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |A i j| * |u i| := by simp [abs_mul]
      _ ≤ ∑ i, 1 * u i := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_of_nonneg (hu.1 i)]
        exact mul_le_mul_of_nonneg_right (hA i j) (hu.1 i)
      _ = 1 := by
        rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => one_mul (u i)), hu.2]
  calc
    |payoff A u v - payoff A u v'| = |∑ j, (v j - v' j) * colSum A u j| := by rw [hsplit]
    _ ≤ ∑ j, |(v j - v' j) * colSum A u j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |v j - v' j| * |colSum A u j| := by simp [abs_mul]
    _ ≤ ∑ j, |v j - v' j| * 1 :=
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hcol j) (abs_nonneg _)
    _ = l1Norm (fun j => v j - v' j) := by simp [l1Norm]

/-- Deterministic core of **Lemma 6** (p.21): if the averages `(ū, v̄)` are an
`ε`-approximate NE and the substitute averages `(û, v̂)` are `δ`-close in ℓ1,
then `(û, v̂)` has duality gap at most `ε + 2δ`. -/
theorem replace_ne (A : Matrix (Fin m) (Fin n) ℝ) (hA : MaxEntryBound A 1)
    {ε δ : ℝ} {ubar uhat : Fin m → ℝ} {vbar vhat : Fin n → ℝ}
    (hNE : ∀ (u' : Fin m → ℝ) (v' : Fin n → ℝ), IsDist u' → IsDist v' →
      payoff A u' vbar - payoff A ubar v' ≤ ε)
    (hdu : l1Norm (fun i => uhat i - ubar i) ≤ δ)
    (hdv : l1Norm (fun j => vhat j - vbar j) ≤ δ) :
    ∀ (u' : Fin m → ℝ) (v' : Fin n → ℝ), IsDist u' → IsDist v' →
      payoff A u' vhat - payoff A uhat v' ≤ ε + 2 * δ := by
  intro u' v' hu' hv'
  have h1 : payoff A u' vhat - payoff A u' vbar ≤ δ := by
    have habs := payoff_lipsch_v A hA (u := u') (v := vhat) (v' := vbar) hu'
    linarith [(abs_le.mp habs).2, hdv]
  have h2 : payoff A ubar v' - payoff A uhat v' ≤ δ := by
    have habs := payoff_lipsch_u A hA (u := ubar) (u' := uhat) (v := v') hv'
    have hsym : l1Norm (fun i => ubar i - uhat i) = l1Norm (fun i => uhat i - ubar i) := by
      unfold l1Norm
      exact Finset.sum_congr rfl fun i _ => by rw [abs_sub_comm]
    have hdu' : l1Norm (fun i => ubar i - uhat i) ≤ δ := by rw [hsym]; exact hdu
    linarith [(abs_le.mp habs).2, hdu']
  have hmid := hNE u' v' hu' hv'
  linarith [h1, h2, hmid]

/-! ### Proposition 3 and its arithmetic -/

/-- Expectation over a finite probability space. -/
def expectedValue (P : FinProbSpace) (f : P.Ω → ℝ) : ℝ := ∑ ω, P.prob ω * f ω

/-- The final numerical step of the proof of **Proposition 3** (p.20): with
`δ ≤ ε/20`, `η = ε/15` and `T ≥ 6 log(mn)/(ηε)`, the error budget
`2 log(mn)/(ηT) + 5η + 4δ` is at most `ε`. -/
theorem prop3_arith (m n : ℕ) (ε η δ : ℝ) (T : ℕ)
    (hε : 0 < ε) (hη : η = ε / 15) (hδ : δ ≤ ε / 20)
    (hTpos : 0 < T) (hT : 6 * Real.log ((m : ℝ) * (n : ℝ)) / (η * ε) ≤ (T : ℝ)) :
    2 * Real.log ((m : ℝ) * (n : ℝ)) / (η * (T : ℝ)) + 5 * η + 4 * δ ≤ ε := by
  have hηpos : 0 < η := by rw [hη]; positivity
  have hTposR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hTpos
  have hηε : 0 < η * ε := mul_pos hηpos hε
  have hstep1 : 6 * Real.log ((m : ℝ) * (n : ℝ)) ≤ (T : ℝ) * (η * ε) := by
    have h := (div_le_iff₀ hηε).mp hT
    simpa [mul_comm, mul_assoc, mul_left_comm] using h
  have hstep2 : 2 * Real.log ((m : ℝ) * (n : ℝ)) / (η * (T : ℝ)) ≤ ε / 3 := by
    rw [div_le_iff₀ (mul_pos hηpos hTposR)]
    nlinarith [hstep1]
  have h5 : 5 * η = ε / 3 := by rw [hη]; ring
  have h4 : 4 * δ ≤ ε / 5 := by nlinarith [hδ]
  nlinarith [hstep2, h5, h4]

/-- The numerical step of **Corollary 3** (p.20): under
`T ≥ 8 log(mn)/(ηε) + 2048 log(1/α)/ε²`, `η = ε/20`, `δ ≤ ε/20`, the full
error budget including the martingale term is at most `ε`. -/
theorem cor3_arithmetic (m n : ℕ) (ε η δ α : ℝ) (T : ℕ)
    (hε : 0 < ε) (hα0 : 0 < α) (hα1 : α < 1) (hη : η = ε / 20) (hδ : δ ≤ ε / 20)
    (hTpos : 0 < T)
    (hT : 8 * Real.log ((m : ℝ) * (n : ℝ)) / (η * ε)
        + 2048 * Real.log (1 / α) / ε ^ 2 ≤ (T : ℝ))
    (hL : 0 ≤ Real.log ((m : ℝ) * (n : ℝ))) :
    2 * Real.log ((m : ℝ) * (n : ℝ)) / (η * (T : ℝ)) + 5 * η + 4 * δ
      + Real.sqrt (128 * Real.log (1 / α) / (T : ℝ)) ≤ ε := by
  have hηpos : 0 < η := by rw [hη]; positivity
  have hTposR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hTpos
  have hηε : 0 < η * ε := mul_pos hηpos hε
  have hlog : 0 < Real.log (1 / α) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hα0]
    simpa using hα1
  have hterm_nonneg : 0 ≤ 2048 * Real.log (1 / α) / ε ^ 2 := by positivity
  have hterm_nonneg2 : 0 ≤ 8 * Real.log ((m : ℝ) * (n : ℝ)) / (η * ε) := by positivity
  have hstep1 : 8 * Real.log ((m : ℝ) * (n : ℝ)) ≤ (T : ℝ) * (η * ε) := by
    have h8 : 8 * Real.log ((m : ℝ) * (n : ℝ)) / (η * ε) ≤ (T : ℝ) :=
      le_trans (le_add_of_nonneg_right hterm_nonneg) hT
    have := (div_le_iff₀ hηε).mp h8
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  have hstep2 : 2 * Real.log ((m : ℝ) * (n : ℝ)) / (η * (T : ℝ)) ≤ ε / 4 := by
    rw [div_le_iff₀ (mul_pos hηpos hTposR)]
    nlinarith [hstep1]
  have h5 : 5 * η = ε / 4 := by rw [hη]; ring
  have h4 : 4 * δ ≤ ε / 5 := by nlinarith [hδ]
  have hT2 : 2048 * Real.log (1 / α) / ε ^ 2 ≤ (T : ℝ) := by
    have := le_trans (le_add_of_nonneg_left hterm_nonneg2) hT
    linarith
  have hsq : 128 * Real.log (1 / α) / (T : ℝ) ≤ (ε / 4) ^ 2 := by
    rw [div_le_iff₀ hTposR]
    -- 128 log(1/α) ≤ (ε/4)^2 * T
    have hbound : 128 * Real.log (1 / α) ≤ (ε ^ 2 / 16) * (T : ℝ) := by
      have : 128 * Real.log (1 / α) = (ε ^ 2 / 16) * (2048 * Real.log (1 / α) / ε ^ 2) := by
        field_simp
        ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hT2 (by positivity)
    calc
      128 * Real.log (1 / α) ≤ (ε ^ 2 / 16) * (T : ℝ) := hbound
      _ = (ε / 4) ^ 2 * (T : ℝ) := by ring
  have hsqrt : Real.sqrt (128 * Real.log (1 / α) / (T : ℝ)) ≤ ε / 4 := by
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity)] at this
  nlinarith [hstep2, h5, h4, hsqrt]

end Qatlib.Papers.ZeroSumGibbs23.MainResults.MirrorCore
