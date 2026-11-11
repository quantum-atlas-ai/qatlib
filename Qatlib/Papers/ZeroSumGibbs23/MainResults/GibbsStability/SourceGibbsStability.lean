/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZeroSumGibbs23.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# ZeroSumGibbs23 — Lemma 2 (Gibbs stability inside a phase)

Fixed arXiv:2301.03763v1, Lemma 2, printed p.12 (Section 4.1).

The source lemma: for all `s ∈ [⌈1/η⌉]`,

  `Z_{τ+s} ∈ [Z_τ/3, 3Z_τ]`, and `p_{τ+s} ∈ [p_τ/9, 9p_τ]` entrywise.

The proof observes `ν_{τ+s,j}/ν_{τ,j} = exp((Aᵀ(x_{τ+s}-x_τ))_j) ∈ [exp(-ηs), exp(ηs)]`
(since `‖A‖_max ≤ 1` and each of the `s` updates adds `η` to one nonnegative
coordinate), and `exp(ηs) ≤ 3` in the paper's parameter regime (`η = ε/60`).
We split this into the general exponential bound (`gibbs_stability_exp`, valid
for every step size) and the printed constants `1/3, 3, 1/9, 9`
(`lemma2_gibbs_stability`), which additionally assumes `exp (η s) ≤ 3` — the
implicit small-step regime of the paper (`s ≤ ⌈1/η⌉` alone only gives
`exp (η s) ≤ exp (1 + η)`).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZeroSumGibbs23.MainResults.GibbsStability

open Qatlib.Papers.ZeroSumGibbs23.MainResults.Model

variable {m n : ℕ}

/-- Entrywise logit difference bound: one Update step changes `Aᵀx` by at most
`η` in each coordinate, hence `s` steps change it by at most `‖x' - x‖₁`.
This is the inequality `|[Aᵀ(x_{τ+s}-x_τ)]_j| ≤ ‖A‖_max ‖x_{τ+s}-x_τ‖₁` used in
the proof of Lemma 2 (p.12). -/
theorem abs_colSum_diff_le (A : Matrix (Fin m) (Fin n) ℝ) (hA : MaxEntryBound A 1)
    (x x' : Fin m → ℝ) (j : Fin n) :
    |colSum A x' j - colSum A x j| ≤ l1Norm (fun i => x' i - x i) := by
  have hsplit : colSum A x' j - colSum A x j = ∑ i, A i j * (x' i - x i) := by
    unfold colSum
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit]
  calc
    |∑ i, A i j * (x' i - x i)| ≤ ∑ i, |A i j * (x' i - x i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |A i j| * |x' i - x i| := by simp [abs_mul]
    _ ≤ ∑ i, 1 * |x' i - x i| :=
      Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (hA i j) (abs_nonneg (x' i - x i))
    _ = l1Norm (fun i => x' i - x i) := by simp [l1Norm]

/-- Upper exponential bound for the partition function: if every logit increases
by at most `d`, then `Z' ≤ exp d · Z`. This is the `exp(ηs)` half of Lemma 2. -/
theorem gibbsZ_upper (w w' : Fin n → ℝ) {d : ℝ} (h : ∀ j, w' j - w j ≤ d) :
    gibbsZ w' ≤ Real.exp d * gibbsZ w := by
  unfold gibbsZ
  calc
    ∑ j, Real.exp (w' j) ≤ ∑ j, Real.exp (w j) * Real.exp d := by
      refine Finset.sum_le_sum fun j _ => ?_
      have hw : Real.exp (w' j) = Real.exp (w j) * Real.exp (w' j - w j) := by
        conv_lhs => rw [show w' j = w j + (w' j - w j) by ring]
        rw [Real.exp_add]
      rw [hw]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (h j)) (Real.exp_pos (w j)).le
    _ = Real.exp d * ∑ j, Real.exp (w j) := by
      rw [← Finset.sum_mul, mul_comm]

/-- Lower exponential bound for the partition function: if every logit decreases
by at most `d`, then `exp(-d) · Z ≤ Z'`. -/
theorem gibbsZ_lower (w w' : Fin n → ℝ) {d : ℝ} (h : ∀ j, -d ≤ w' j - w j) :
    Real.exp (-d) * gibbsZ w ≤ gibbsZ w' := by
  unfold gibbsZ
  calc
    Real.exp (-d) * ∑ j, Real.exp (w j) = ∑ j, Real.exp (-d) * Real.exp (w j) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ j, Real.exp (w' j) := by
      refine Finset.sum_le_sum fun j _ => ?_
      have hw : Real.exp (-d) * Real.exp (w j) = Real.exp (-d + w j) :=
        (Real.exp_add (-d) (w j)).symm
      rw [hw]
      exact Real.exp_le_exp.mpr (by linarith [h j])

/-- From bounded multiplicative changes of both `exp(w_j)` and `Z`, the Gibbs
probabilities change by at most the square of the same factor:
`p'_j ≤ B² p_j`. This is the `p_{τ+s} ∈ [p_τ/9, 9p_τ]` step of Lemma 2 with
`B = exp(ηs)`. -/
theorem gibbsP_le_sq_mul {w w' : Fin n → ℝ} (hn : 0 < n) {B : ℝ} (hB : 0 < B)
    (hW : ∀ j, Real.exp (w' j) ≤ B * Real.exp (w j))
    (hZ : gibbsZ w ≤ B * gibbsZ w') (j : Fin n) :
    gibbsP w' j ≤ B ^ 2 * gibbsP w j := by
  have hZpos : 0 < gibbsZ w := gibbsZ_pos w hn
  have hZ'pos : 0 < gibbsZ w' := gibbsZ_pos w' hn
  have he := hW j
  have h1 : Real.exp (w' j) * gibbsZ w ≤ (B * Real.exp (w j)) * gibbsZ w :=
    mul_le_mul_of_nonneg_right he hZpos.le
  have h2 : (B * Real.exp (w j)) * gibbsZ w ≤ (B * Real.exp (w j)) * (B * gibbsZ w') :=
    mul_le_mul_of_nonneg_left hZ (mul_pos hB (Real.exp_pos (w j))).le
  have hmain : Real.exp (w' j) * gibbsZ w ≤ B ^ 2 * Real.exp (w j) * gibbsZ w' := by
    calc
      Real.exp (w' j) * gibbsZ w ≤ (B * Real.exp (w j)) * gibbsZ w := h1
      _ ≤ (B * Real.exp (w j)) * (B * gibbsZ w') := h2
      _ = B ^ 2 * Real.exp (w j) * gibbsZ w' := by ring
  unfold gibbsP
  rw [show B ^ 2 * (Real.exp (w j) / gibbsZ w) = (B ^ 2 * Real.exp (w j)) / gibbsZ w from
    (mul_div_assoc _ _ _).symm]
  rw [div_le_div_iff₀ hZ'pos hZpos]
  exact hmain

/-- **Lemma 2**, general exponential form (Printed p.12, Section 4.1): after
`s` Update steps of size `η` with `‖A‖_max ≤ 1`, the partition function is
within `[exp(-ηs) Z, exp(ηs) Z]` and every Gibbs probability is within
`[exp(-2ηs) p_j, exp(2ηs) p_j]`. -/
theorem gibbs_stability_exp (A : Matrix (Fin m) (Fin n) ℝ) (hA : MaxEntryBound A 1)
    (x x' : Fin m → ℝ) (η : ℝ) (s : ℕ) (hn : 0 < n)
    (hstep : l1Norm (fun i => x' i - x i) ≤ η * (s : ℝ)) :
    gibbsZ (gibbsLogit A x') ≤ Real.exp (η * s) * gibbsZ (gibbsLogit A x) ∧
    Real.exp (-(η * s)) * gibbsZ (gibbsLogit A x) ≤ gibbsZ (gibbsLogit A x') ∧
    (∀ j, gibbsP (gibbsLogit A x') j ≤
      Real.exp (2 * (η * s)) * gibbsP (gibbsLogit A x) j) ∧
    (∀ j, gibbsP (gibbsLogit A x) j ≤
      Real.exp (2 * (η * s)) * gibbsP (gibbsLogit A x') j) := by
  have hdiff : ∀ j, |gibbsLogit A x' j - gibbsLogit A x j| ≤ η * (s : ℝ) := by
    intro j
    have h := abs_colSum_diff_le A hA x x' j
    have hw : gibbsLogit A x' j - gibbsLogit A x j = colSum A x' j - colSum A x j := rfl
    rw [hw]
    exact le_trans h hstep
  have hup : ∀ j, gibbsLogit A x' j - gibbsLogit A x j ≤ η * (s : ℝ) :=
    fun j => (abs_le.mp (hdiff j)).2
  have hlow : ∀ j, -(η * (s : ℝ)) ≤ gibbsLogit A x' j - gibbsLogit A x j :=
    fun j => (abs_le.mp (hdiff j)).1
  have hZup := gibbsZ_upper (gibbsLogit A x) (gibbsLogit A x') hup
  have hZlow := gibbsZ_lower (gibbsLogit A x) (gibbsLogit A x') hlow
  have hZmul : gibbsZ (gibbsLogit A x) ≤
      Real.exp (η * s) * gibbsZ (gibbsLogit A x') := by
    have h3 : Real.exp (-(η * s)) = (Real.exp (η * s))⁻¹ := Real.exp_neg _
    have hlow' : (Real.exp (η * s))⁻¹ * gibbsZ (gibbsLogit A x) ≤
        gibbsZ (gibbsLogit A x') := by
      rw [← h3]
      exact hZlow
    have h2 := mul_le_mul_of_nonneg_left hlow' (Real.exp_pos (η * s)).le
    calc gibbsZ (gibbsLogit A x) =
        Real.exp (η * s) * ((Real.exp (η * s))⁻¹ * gibbsZ (gibbsLogit A x)) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.exp_pos _)), one_mul]
      _ ≤ Real.exp (η * s) * gibbsZ (gibbsLogit A x') := h2
  have hB : 0 < Real.exp (η * s) := Real.exp_pos _
  have hsq : Real.exp (2 * (η * s)) = Real.exp (η * s) ^ 2 := by
    rw [show 2 * (η * s) = η * s + η * s by ring, Real.exp_add]
    ring
  refine ⟨hZup, hZlow, ?_, ?_⟩
  · intro j
    rw [hsq]
    exact gibbsP_le_sq_mul hn hB
      (fun j => by
        calc Real.exp (gibbsLogit A x' j) =
            Real.exp (gibbsLogit A x j) *
              Real.exp (gibbsLogit A x' j - gibbsLogit A x j) := by
              conv_lhs =>
                rw [show gibbsLogit A x' j =
                  gibbsLogit A x j + (gibbsLogit A x' j - gibbsLogit A x j) by ring]
              rw [Real.exp_add]
          _ ≤ Real.exp (gibbsLogit A x j) * Real.exp (η * s) :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hup j)) (Real.exp_pos _).le
          _ = Real.exp (η * s) * Real.exp (gibbsLogit A x j) := by ring)
      hZmul j
  · intro j
    rw [hsq]
    exact gibbsP_le_sq_mul hn hB
      (fun j => by
        calc Real.exp (gibbsLogit A x j) =
            Real.exp (gibbsLogit A x' j) *
              Real.exp (gibbsLogit A x j - gibbsLogit A x' j) := by
              conv_lhs =>
                rw [show gibbsLogit A x j =
                  gibbsLogit A x' j + (gibbsLogit A x j - gibbsLogit A x' j) by ring]
              rw [Real.exp_add]
          _ ≤ Real.exp (gibbsLogit A x' j) * Real.exp (η * s) := by
              refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
              apply Real.exp_le_exp.mpr
              linarith only [hlow j]
          _ = Real.exp (η * s) * Real.exp (gibbsLogit A x' j) := by ring)
      hZup j

/-- **Lemma 2** (Printed p.12, Section 4.1), printed constants:
`Z_{τ+s} ∈ [Z_τ/3, 3Z_τ]` and `p_{τ+s} ∈ [p_τ/9, 9p_τ]` entrywise, under the
paper's small-step regime `exp (η s) ≤ 3` (satisfied for `s ≤ ⌈1/η⌉` and
`η ≤ 1/12`; in the applications `η = ε/60 < 1/12`). -/
theorem lemma2_gibbs_stability (A : Matrix (Fin m) (Fin n) ℝ) (hA : MaxEntryBound A 1)
    (x x' : Fin m → ℝ) (η : ℝ) (s : ℕ) (hn : 0 < n)
    (hstep : l1Norm (fun i => x' i - x i) ≤ η * (s : ℝ))
    (hreg : Real.exp (η * (s : ℝ)) ≤ 3) :
    gibbsZ (gibbsLogit A x') ≤ 3 * gibbsZ (gibbsLogit A x) ∧
    (1 / 3) * gibbsZ (gibbsLogit A x) ≤ gibbsZ (gibbsLogit A x') ∧
    (∀ j, gibbsP (gibbsLogit A x') j ≤ 9 * gibbsP (gibbsLogit A x) j) ∧
    (∀ j, gibbsP (gibbsLogit A x) j ≤ 9 * gibbsP (gibbsLogit A x') j) := by
  obtain ⟨hZup, hZlow, hpup, hplow⟩ := gibbs_stability_exp A hA x x' η s hn hstep
  have hexp_pos : 0 < Real.exp (η * (s : ℝ)) := Real.exp_pos _
  have hthird : (1 / 3 : ℝ) ≤ Real.exp (-(η * (s : ℝ))) := by
    rw [Real.exp_neg]
    have h3 : (1 / 3 : ℝ) = (3 : ℝ)⁻¹ := by norm_num
    rw [h3]
    exact inv_anti₀ hexp_pos hreg
  have hsquare : Real.exp (2 * (η * (s : ℝ))) ≤ 9 := by
    have h9 : (9 : ℝ) = 3 * 3 := by norm_num
    rw [h9]
    rw [show 2 * (η * (s : ℝ)) = η * (s : ℝ) + η * (s : ℝ) by ring, Real.exp_add]
    exact mul_le_mul hreg hreg hexp_pos.le (by norm_num)
  have hZ3 : Real.exp (η * (s : ℝ)) * gibbsZ (gibbsLogit A x) ≤
      3 * gibbsZ (gibbsLogit A x) :=
    mul_le_mul_of_nonneg_right hreg (le_of_lt (gibbsZ_pos _ hn))
  refine ⟨le_trans hZup hZ3, ?_, ?_, ?_⟩
  · calc (1 / 3) * gibbsZ (gibbsLogit A x) ≤
        Real.exp (-(η * (s : ℝ))) * gibbsZ (gibbsLogit A x) :=
          mul_le_mul_of_nonneg_right hthird (gibbsZ_pos _ hn).le
      _ ≤ gibbsZ (gibbsLogit A x') := hZlow
  · intro j
    calc gibbsP (gibbsLogit A x') j ≤
        Real.exp (2 * (η * (s : ℝ))) * gibbsP (gibbsLogit A x) j := hpup j
      _ ≤ 9 * gibbsP (gibbsLogit A x) j :=
          mul_le_mul_of_nonneg_right hsquare (gibbsP_nonneg _ hn j)
  · intro j
    calc gibbsP (gibbsLogit A x) j ≤
        Real.exp (2 * (η * (s : ℝ))) * gibbsP (gibbsLogit A x') j := hplow j
      _ ≤ 9 * gibbsP (gibbsLogit A x') j :=
          mul_le_mul_of_nonneg_right hsquare (gibbsP_nonneg _ hn j)

end Qatlib.Papers.ZeroSumGibbs23.MainResults.GibbsStability
