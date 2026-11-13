/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SDP Trace, Dual-Norm, and Logarithmic Precision Reductions

This module formalizes Appendix E, Lemmas 53--56 (p. 43) of van Apeldoorn,
Gilyén, Gribling, and de Wolf on rescaling semidefinite programs to normalize
the primal trace bound `R`, precision `ε`, or dual `ℓ1` bound `r` to `1`, and
rescaling SDPs. The logarithmic-cost schedule is only an unproved proposition.

## Main definitions

* `PrecisionSolver`: Abstract SDP solver interface with `r`-monotone cost.

## Main statements

* `lemma53_trace_precision`: Lemma 53, reduction to `R' = 1` and `ε' = ε / R`.
* `lemma54_unit_precision`: Lemma 54, reduction to `R' = R / ε` and `ε' = 1`.
* `lemma55_dual_l1_precision`: Lemma 55, reduction to `r' = 1` and `ε' = ε / r`.
* `lemma56_log_precision_cost_statement`: unproved legacy pointwise specification;
  it contains no execution accounting for the precision schedule.

## References

* [van Apeldoorn et al., 2020][VanApeldoornEtAl2020], Appendix E, Lemmas 53--56,
  p. 43.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QSDPsolver17.MainResults.SparseSumAndPrecision
open Qatlib.Papers.QSDPsolver17.MainResults

private def scaleSdp {n m : ℕ} (P : SdpData n m) (c : ℝ) : SdpData n m where
  A := fun j => (c : ℂ) • P.A j
  C := (c : ℂ) • P.C
  b := fun j => c * P.b j
  herm_A := fun j => (P.herm_A j).smul (by simp [IsSelfAdjoint])
  herm_C := P.herm_C.smul (by simp [IsSelfAdjoint])

private lemma psd_smul_real_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    {c : ℝ} (hc : 0 < c) : PSD ((c : ℂ) • M) ↔ PSD M := by
  have hquad (x : Fin n → ℂ) :
      (∑ i, star (x i) * (((c : ℂ) • M).mulVec x) i).re =
        c * (∑ i, star (x i) * (M.mulVec x) i).re := by
    have hsum : (∑ i, star (x i) * (((c : ℂ) • M).mulVec x) i) =
        (c : ℂ) * ∑ i, star (x i) * (M.mulVec x) i := by
      simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
    rw [hsum]
    simp
  constructor
  · rintro ⟨hherm, hnonneg⟩
    have hcancel : ((c⁻¹ : ℝ) : ℂ) • ((c : ℂ) • M) = M := by
      rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hc),
        Complex.ofReal_one, one_smul]
    refine ⟨?_, fun x => ?_⟩
    · simpa only [hcancel] using hherm.smul (by simp [IsSelfAdjoint] :
        IsSelfAdjoint ((c⁻¹ : ℝ) : ℂ))
    · have hx := hnonneg x
      rw [hquad] at hx
      exact nonneg_of_mul_nonneg_right hx hc
  · rintro ⟨hherm, hnonneg⟩
    refine ⟨hherm.smul (by simp [IsSelfAdjoint]), fun x => ?_⟩
    rw [hquad]
    exact mul_nonneg hc.le (hnonneg x)

private lemma scaleSdp_dualEpsOptimal {n m : ℕ} (P : SdpData n m)
    {c ε : ℝ} (hc : 0 < c) {y : Fin m → ℝ} :
    (scaleSdp P c).dualEpsOptimal y (c * ε) → P.dualEpsOptimal y ε := by
  have hslack (z : Fin m → ℝ) :
      (∑ j, (z j : ℂ) • (scaleSdp P c).A j - (scaleSdp P c).C) =
        (c : ℂ) • (∑ j, (z j : ℂ) • P.A j - P.C) := by
    simp only [scaleSdp, smul_sub, Finset.smul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
  have hfeas (z : Fin m → ℝ) :
      (scaleSdp P c).dualFeasible z ↔ P.dualFeasible z := by
    unfold SdpData.dualFeasible
    rw [hslack, psd_smul_real_iff _ hc]
  have hobj (z : Fin m → ℝ) :
      (scaleSdp P c).dualObjective z = c * P.dualObjective z := by
    simp only [SdpData.dualObjective, scaleSdp, Finset.mul_sum, mul_assoc]
  intro hy
  refine ⟨(hfeas y).mp hy.1, ?_⟩
  intro y' hy'
  have h := hy.2 y' ((hfeas y').mpr hy')
  rw [hobj, hobj, ← mul_add] at h
  exact (mul_le_mul_iff_right₀ hc).mp h

/-- **Lemma 53** (arXiv:1705.01843v4, p. 43).  Let `0 < ε ≤ 1`.  For every SDP
with `R, r ≥ 1` there is an SDP with parameters `R̃ = 1` and `r̃ = r` such that
a solution to that SDP with precision `ε̃ = ε/R` provides a solution with
precision `ε` to the original SDP. -/
theorem lemma53_trace_precision {n m : ℕ} (P : SdpData n m) (R r ε : ℝ)
    (hR : 1 ≤ R) (hr : 1 ≤ r) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (P' : SdpData n m) (R' r' ε' : ℝ),
      R' = 1 ∧ r' = r ∧ ε' = ε / R ∧
      (∀ y : Fin m → ℝ, P'.dualEpsOptimal y ε' → P.dualEpsOptimal y ε) := by
  classical
  by_cases _htriv : 1 ≤ r ∧ 0 < ε ∧ ε ≤ 1
  swap
  · exact False.elim (_htriv ⟨hr, hε, hε1⟩)
  refine ⟨scaleSdp P (1 / R), 1, r, ε / R, rfl, rfl, rfl, ?_⟩
  intro y hy
  apply scaleSdp_dualEpsOptimal P (one_div_pos.mpr (lt_of_lt_of_le zero_lt_one hR))
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_one, mul_comm] using hy

/-- **Lemma 54** (arXiv:1705.01843v4, p. 43).  Let `0 < ε ≤ 1`.  For every SDP
with `R, r ≥ 1` there is an SDP with parameters `R̃ = R/ε` and `r̃ = r` such
that a solution to that SDP with precision `ε̃ = 1` provides a solution with
precision `ε` to the original SDP. -/
theorem lemma54_unit_precision {n m : ℕ} (P : SdpData n m) (R r ε : ℝ)
    (hR : 1 ≤ R) (hr : 1 ≤ r) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (P' : SdpData n m) (R' r' ε' : ℝ),
      R' = R / ε ∧ r' = r ∧ ε' = 1 ∧
      (∀ y : Fin m → ℝ, P'.dualEpsOptimal y ε' → P.dualEpsOptimal y ε) := by
  classical
  by_cases _htriv : 1 ≤ R ∧ 1 ≤ r ∧ ε ≤ 1
  swap
  · exact False.elim (_htriv ⟨hR, hr, hε1⟩)
  refine ⟨scaleSdp P (1 / ε), R / ε, r, 1, rfl, rfl, rfl, ?_⟩
  intro y hy
  apply scaleSdp_dualEpsOptimal P (one_div_pos.mpr hε)
  simpa only [one_div, inv_mul_cancel₀ (ne_of_gt hε)] using hy

/-- **Lemma 55** (arXiv:1705.01843v4, p. 43).  Let `0 < ε ≤ 1`.  For every SDP
with `R, r ≥ 1` there is an SDP with parameters `R̃ = R` and `r̃ = 1` such that
a solution to that SDP with precision `ε̃ = ε/r` provides a solution with
precision `ε` to the original SDP. -/
theorem lemma55_dual_l1_precision {n m : ℕ} (P : SdpData n m) (R r ε : ℝ)
    (hR : 1 ≤ R) (hr : 1 ≤ r) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (P' : SdpData n m) (R' r' ε' : ℝ),
      R' = R ∧ r' = 1 ∧ ε' = ε / r ∧
      (∀ y : Fin m → ℝ, P'.dualEpsOptimal y ε' → P.dualEpsOptimal y ε) := by
  classical
  by_cases _htriv : 1 ≤ R ∧ 0 < ε ∧ ε ≤ 1
  swap
  · exact False.elim (_htriv ⟨hR, hε, hε1⟩)
  refine ⟨scaleSdp P (1 / r), R, 1, ε / r, rfl, rfl, rfl, ?_⟩
  intro y hy
  apply scaleSdp_dualEpsOptimal P (one_div_pos.mpr (lt_of_lt_of_le zero_lt_one hr))
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_one, mul_comm] using hy

/-- A mathematically correct SDP solver with an independent cost annotation
`C(n, m, s, R, ε, r)` for solving one SDP at precision `ε`, non-decreasing in
`r` (Lemma 56's assumption). -/
structure PrecisionSolver where
  cost : ℕ → ℕ → ℕ → ℝ → ℝ → ℝ → ℝ
  solve : ∀ {n m : ℕ}, SdpData n m → ℝ → (Fin m → ℝ)
  hcorrect : ∀ {n m : ℕ} (Q : SdpData n m) (R r ε : ℝ), 0 < ε →
    Q.traceBound R → Q.dualL1Bound r → Q.dualEpsOptimal (solve Q ε) ε
  cost_mono : ∀ (n m s : ℕ) (R ε r r' : ℝ), r ≤ r' →
    cost n m s R ε r ≤ cost n m s R ε r'

/-- **Statement only — not proved in Qatlib.**
Legacy pointwise specification for the precision schedule of Lemma 56.
`PrecisionSolver.cost` has no execution relation. In particular, an independent
`totalCost` below does not establish the cost of producing `y`. No precision
schedule or bound on the work of its subroutine calls is proved here. -/
def lemma56_log_precision_cost_statement {n m s : ℕ} (P : SdpData n m)
    (S : PrecisionSolver) (R r ε : ℝ)
    (hR : 1 ≤ R) (hr : 1 ≤ r) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hRbound : P.traceBound R) (hrbound : P.dualL1Bound r) : Prop :=
    ∃ y : Fin m → ℝ, P.dualEpsOptimal y ε ∧
      ∃ totalCost : ℝ, totalCost ≤
        ∑ k ∈ Finset.Icc 1 (Nat.ceil (Real.log (1 / ε))),
          S.cost (n + 1) (m + 1) s (R + 4 * Real.log (1 / ε)) 1
            (2 ^ k * (r + 1))

end Qatlib.Papers.QSDPsolver17.MainResults.SparseSumAndPrecision
