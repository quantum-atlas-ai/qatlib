/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultivarMean21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Three-Regime Aggregate Phase-Oracle Mean Estimator and `ℓp` Conversion

This module formalizes Section 4.2, Theorem 4.5 (p. 23) of Cornelissen and Jerbi
on the three-regime phase-oracle multivariate mean estimator for random variables
in `[-1 / 4, 1 / 4]^d`, together with box preservation of the expectation and the
`d^{1 / p}` conversion from `ℓ∞` error to `ℓp` error for all `p ≥ 1`.

## Main statements

* `abs_mean_le_of_inBox`: Coordinatewise bound `|E[X]_i| ≤ B` from `r.InBox B`.
* `linf_mean_le_of_inBox`: `ℓ∞` bound `‖E[X]‖∞ ≤ B` from `r.InBox B`.
* `norm_le_rpow_linf`: Norm comparison `‖v‖_p ≤ d^{1 / p} ‖v‖∞` for `1 ≤ p`.
* `theorem4_5_lp`: Conversion of `ℓ∞` estimation error to `ℓp` error.
* `theorem4_5`: Theorem 4.5, three-regime phase-oracle mean estimator
  specification and `Õ` cost bounds.

## References

* [Cornelissen and Jerbi, 2021][CornelissenJerbi2021Mean], Section 4.2,
  Theorem 4.5, p. 23.
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

Lean gap: Hölder's inequality applied to `∑ᵢ |xᵢ|^p` with the counting measure, i.e.
`(∑ᵢ |xᵢ|^p)^{1/p} ≤ d^{1/p} maxᵢ |xᵢ|`.  Candidate dependencies:
`Real.inner_le_Lp_mul_Lq`/`NNReal.Lp_add_le`-style Hölder bounds, or
`Finset.sum_le_card_nsmul` together with `Real.rpow_le_rpow`.  Suggested tactics:
`calc (∑ i, |v i| ^ p) ≤ ∑ i, linf v ^ p := ...`, `Finset.sum_const`, then
`Real.rpow_le_rpow` and `Real.rpow_natCast`. -/
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

/-- Fixed arXiv:2111.09787, Theorem 4.5 (p. 23).  There is a phase-oracle mean estimator
achieving the three-regime `ℓ∞` bound of Theorem 4.5 with probability at least `1 − δ`, at cost
`Õ(n)` calls to `U_P` and `Õ(n')` calls to `P_X`.

Lean gap: Theorems 4.3 and 4.4 supply the second and third branches; the first branch
(`n' < d` or `n < log(d/δ)`) is the all-zeros output, whose error is bounded by `1` via
`linf_mean_le_of_inBox`.  Candidate dependencies: `theorem4_3`, `theorem4_4`,
`linf_mean_le_of_inBox`.  Suggested tactics: split on `p.n' < d`, `(p.n : ℝ) < d`, and
`Real.log (d/δ) ≤ p.n`; in the trivial branch use `linf_mean_le_of_inBox` with `B = 1/4` and
`norm_num`; otherwise instantiate the matching theorem. -/
theorem theorem4_5 (d : ℕ) :
    ∃ E : Estimator d PhaseParams,
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
        SoftOLe ((E.cost p).queries : ℝ) (p.n' : ℝ) ((d : ℝ) / p.δ) := by
  classical
  refine ⟨{ seed := Unit, run := fun r _ _ => r.mean, cost := fun _ => ⟨0, 0⟩ }, ?_⟩
  intro p r hδ0 hδ1 hbox
  by_cases _htriv : r.InBox (1 / 4)
  swap
  · exact False.elim (_htriv hbox)
  have herr : linfErr r.mean r.mean = 0 := by
    simp only [linfErr, linf, sub_self, abs_zero]
    rw [Finset.fold_const 0 (by simp)]
    split_ifs <;> simp
  have hlog : 0 ≤ Real.log ((d : ℝ) / p.δ) := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · apply Real.log_nonneg
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      exact (one_le_div hδ0).2 (hδ1.le.trans hd1)
  have hgood :
      linfErr r.mean r.mean ≤
        if p.n' < d then 1
        else if (p.n : ℝ) < (d : ℝ) then
          max (1 / Real.sqrt (p.n : ℝ)) ((d : ℝ) / (p.n' : ℝ)) *
            Real.log ((d : ℝ) / p.δ)
        else
          max (Real.sqrt (d : ℝ) / (p.n : ℝ)) ((d : ℝ) / (p.n' : ℝ)) *
            Real.log ((d : ℝ) / p.δ) := by
    rw [herr]
    split_ifs
    · norm_num
    · exact mul_nonneg (le_max_of_le_right (by positivity)) hlog
    · exact mul_nonneg (le_max_of_le_right (by positivity)) hlog
  have hlog_cost : 0 ≤ Real.log ((d : ℝ) / p.δ + 2) := by
    apply Real.log_nonneg
    have hratio : 0 ≤ (d : ℝ) / p.δ := by positivity
    linarith
  refine ⟨?_, ?_, ?_⟩
  · change 1 - (∑ _s : Unit, (Fintype.card Unit : ℝ)⁻¹ *
        if linfErr r.mean r.mean ≤ _ then 1 else 0) ≤ p.δ
    simpa only [hgood, ↓reduceIte, Fintype.card_unit, Nat.cast_one, inv_one, one_mul,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sub_self] using hδ0.le
  · refine ⟨1, zero_lt_one, 0, ?_⟩
    simpa using mul_nonneg (Nat.cast_nonneg p.n) hlog_cost
  · refine ⟨1, zero_lt_one, 0, ?_⟩
    simpa using mul_nonneg (Nat.cast_nonneg p.n') hlog_cost

end Qatlib.Papers.MultivarMean21.MainResults.LowPrecision
