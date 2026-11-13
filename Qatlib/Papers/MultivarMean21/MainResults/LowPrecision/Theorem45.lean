/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultivarMean21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Mean-estimation specification and proved norm comparisons

The box bounds and finite-dimensional norm comparisons below are proved.
`theorem4_5_statement` is an unproved output-error/resource specification
corresponding to Theorem 4.5 of Cornelissen and Jerbi (arXiv:2111.09787).
**Statement only — not proved in Qatlib.** The estimator's oracle implementation
is an explicit predicate parameter; no sampling or quantum algorithm is constructed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.MultivarMean21.MainResults.LowPrecision
open Qatlib.Papers.MultivarMean21.MainResults


/-- Elementary bound behind the trivial branch of Theorem 4.5 (p. 23): if `X` takes values in
`[−B, B]^d`, then every coordinate of the mean `E[X]` satisfies `|E[X]_i| ≤ B`. -/
theorem abs_mean_le_of_inBox {d : ℕ} (r : FinRV d) (B : ℝ) (hB : 0 ≤ B) (h : r.InBox B) :
    ∀ i, |r.mean i| ≤ B := by
  classical
  by_cases _htriv : 0 ≤ B
  swap
  · exact False.elim (_htriv hB)
  intro i
  have hmean : r.mean i = ∑ ω, r.P ω * r.X ω i := rfl
  rw [hmean]
  calc
    |∑ ω, r.P ω * r.X ω i| ≤ ∑ ω, |r.P ω * r.X ω i| :=
      Finset.abs_sum_le_sum_abs (fun ω => r.P ω * r.X ω i) Finset.univ
    _ = ∑ ω, r.P ω * |r.X ω i| := by
      refine Finset.sum_congr rfl ?_
      intro ω _
      rw [abs_mul, abs_of_nonneg (r.P_nonneg ω)]
    _ ≤ ∑ ω, r.P ω * B := by
      refine Finset.sum_le_sum ?_
      intro ω _
      exact mul_le_mul_of_nonneg_left (h ω i) (r.P_nonneg ω)
    _ = B := by
      rw [← Finset.sum_mul]
      simp [r.P_sum]

/-- The `ℓ∞` form of `abs_mean_le_of_inBox`: a variable with values in `[−B, B]^d` has its mean
in the same box, so `‖E[X]‖∞ ≤ B`.  This is the "trivial branch" of Theorem 4.5 (`n' < d`), where
the all-zeros output is optimal up to constants. -/
theorem linf_mean_le_of_inBox {d : ℕ} (r : FinRV d) (B : ℝ) (hB : 0 ≤ B) (h : r.InBox B) :
    linf r.mean ≤ B := by
  simp only [linf]
  rw [Finset.fold_max_le]
  exact ⟨hB, fun i _ => abs_mean_le_of_inBox r B hB h i⟩

/-- The norm conversion used in the last sentence of Theorem 4.5 (p. 23):
`‖x‖_p ≤ d^{1/p} ‖x‖∞` for `p ∈ [1,∞)`.

This is the finite counting-measure norm comparison
`(∑ᵢ |xᵢ|^p)^{1/p} ≤ d^{1/p} maxᵢ |xᵢ|`, also obtainable from Hölder's
inequality. The proof bounds each `|v i| ^ p` by `linf v ^ p`, sums to obtain
`∑ i, |v i| ^ p ≤ d * linf v ^ p`, and takes the monotone `1/p` power. -/
theorem norm_le_rpow_linf {d : ℕ} (p : ℝ) (hp : 1 ≤ p) (v : Vec d) :
    lpNat p v ≤ (d : ℝ) ^ (1 / p) * linf v := by
  have hp0 : 0 < p := by linarith
  have hpinv_ne : 1 / p ≠ 0 := one_div_ne_zero hp0.ne'
  have hpinv_nn : 0 ≤ 1 / p := by positivity
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [lpNat, Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero]
    rw [Real.zero_rpow hpinv_ne, zero_mul]
  · have hd0 : 0 ≤ (d : ℝ) := (Nat.cast_pos.mpr hd).le
    have hlinf0 : 0 ≤ linf v :=
      (Finset.le_fold_max 0).2 (Or.inl le_rfl)
    have hcoord (i : Fin d) : |v i| ^ p ≤ (linf v) ^ p := by
      apply Real.rpow_le_rpow (abs_nonneg _) _ hp0.le
      exact (Finset.le_fold_max |v i|).2 (Or.inr ⟨i, Finset.mem_univ i, le_rfl⟩)
    have hsum : ∑ i : Fin d, |v i| ^ p ≤ (d : ℝ) * (linf v) ^ p := by
      calc
        ∑ i : Fin d, |v i| ^ p ≤ ∑ _i : Fin d, (linf v) ^ p :=
          Finset.sum_le_sum (fun i _ => hcoord i)
        _ = (d : ℝ) * (linf v) ^ p := by simp
    calc
      lpNat p v ≤ ((d : ℝ) * (linf v) ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow
          (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) hsum hpinv_nn
      _ = (d : ℝ) ^ (1 / p) * ((linf v) ^ p) ^ (1 / p) :=
        Real.mul_rpow hd0 (Real.rpow_nonneg hlinf0 p)
      _ = (d : ℝ) ^ (1 / p) * linf v := by
        rw [← Real.rpow_mul hlinf0, mul_one_div_cancel hp0.ne', Real.rpow_one]

/-- Theorem 4.5 (p. 23), last sentence: the `ℓp` error is at most `d^{1/p}` times the `ℓ∞`
error, for all `p ∈ [1,∞)`.  This is the exact conversion stated in the paper, derived here
from `norm_le_rpow_linf`. -/
theorem theorem4_5_lp {d : ℕ} (p : ℝ) (hp : 1 ≤ p) (v w : Vec d) :
    lpNat p (fun i => v i - w i) ≤ (d : ℝ) ^ (1 / p) * linfErr v w := by
  simpa [lpNat, linfErr] using norm_le_rpow_linf p hp (fun i => v i - w i)

/-- **Statement only — not proved in Qatlib.**
Three-regime output-error and resource specification of Theorem 4.5.
`Implemented` must certify an oracle implementation, including its output law
and resource accounting. No implementation or existence proof is supplied. -/
def theorem4_5_statement (d : ℕ)
    (Implemented : Estimator d PhaseParams → Prop) : Prop :=
    ∃ E : Estimator d PhaseParams,
      Implemented E ∧
      ∀ (p : PhaseParams) (r : FinRV d),
        0 < p.δ → p.δ < 1 → r.InBox (1 / 4) →
        E.failProb r p (fun v =>
            linfErr v r.mean ≤
              if p.n' < d then 1
              else if (p.n : ℝ) < (d : ℝ) then
                max (1 / Real.sqrt (p.n : ℝ)) ((d : ℝ) / (p.n' : ℝ)) *
                  Real.log ((d : ℝ) / p.δ)
              else
                max (Real.sqrt (d : ℝ) / (p.n : ℝ)) ((d : ℝ) / (p.n' : ℝ)) *
                  Real.log ((d : ℝ) / p.δ)) ≤ p.δ ∧
        SoftOLe ((E.cost p).experiments : ℝ) (p.n : ℝ) ((d : ℝ) / p.δ) ∧
        SoftOLe ((E.cost p).queries : ℝ) (p.n' : ℝ) ((d : ℝ) / p.δ)

end Qatlib.Papers.MultivarMean21.MainResults.LowPrecision
