/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.HamiltonianSim.SimulationCostEquationStat

/-!
# Existence and uniqueness of simulation cost

This module proves `SimulationCostEquation`, establishing a unique real cost parameter above `t`
for the equation `(t / r) ^ r = ε`. Its auxiliary lemmas express the logarithm of the left side
through the strictly increasing function `x * log x` on `[1, ∞)`. The mathematical background is
developed in [GilyenSuLowWiebe2019].

## Main statements

* `simulationCostEquation_answer`: existence and uniqueness of the cost parameter.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

namespace Qatlib.Concepts.QsvtCore.HamiltonianSim

open Real

/-- The function `x * log x` is strictly increasing for real arguments at least one. -/
theorem sim157_log_mul_strictMono {x y : ℝ} (hx : 1 ≤ x) (hxy : x < y) :
    x * Real.log x < y * Real.log y := by
  have hx0 : (0:ℝ) ≤ Real.log x := Real.log_nonneg hx
  have h1 : x * Real.log x ≤ y * Real.log x :=
    mul_le_mul_of_nonneg_right hxy.le hx0
  have h2 : y * Real.log x < y * Real.log y :=
    mul_lt_mul_of_pos_left
      ((Real.log_lt_log_iff (by linarith : (0:ℝ) < x) (by linarith : (0:ℝ) < y)).mpr hxy)
      (by linarith : (0:ℝ) < y)
  linarith

/-- For positive `t` and `z`, `z * log (t / z)` equals `-t * ((z / t) * log (z / t))`. -/
theorem sim157_flip {t z : ℝ} (ht : 0 < t) (hz : 0 < z) :
    z * Real.log (t/z) = -t * ((z/t) * Real.log (z/t)) := by
  rw [Real.log_div (ne_of_gt ht) (ne_of_gt hz),
    Real.log_div (ne_of_gt hz) (ne_of_gt ht)]
  field_simp
  ring

set_option maxHeartbeats 400000 in

/-- For positive `t` and `0 < ε < 1`, there is a unique `r ≥ t` solving `(t / r) ^ r = ε`; see
[Gilyén et al., Lemma 59][GilyenSuLowWiebe2019]. -/
theorem simulationCostEquation_answer : SimulationCostEquation := by
  intro t ε ht hε hε1
  have hε0 : (0:ℝ) < ε := hε
  have h1ε : (1:ℝ) < 1/ε := by
    rw [lt_div_iff₀ hε0]
    norm_num
    linarith
  have hLpos : (0:ℝ) < Real.log (1/ε) := Real.log_pos h1ε
  have hLneg : Real.log ε = -(Real.log (1/ε)) := by
    rw [one_div, Real.log_inv ε, neg_neg]
  have hE1 : (1:ℝ) ≤ Real.exp ((Real.log (1/ε) + 1)/t) := by
    have h1 := Real.add_one_le_exp ((Real.log (1/ε) + 1)/t)
    have h2 : (0:ℝ) ≤ (Real.log (1/ε) + 1)/t := by
      apply div_nonneg _ (le_of_lt ht)
      linarith
    linarith
  have hRge : t ≤ t * Real.exp ((Real.log (1/ε) + 1)/t) := by
    have h1 : (1:ℝ) + (Real.log (1/ε) + 1)/t
        ≤ Real.exp ((Real.log (1/ε) + 1)/t) := by
      have h := Real.add_one_le_exp ((Real.log (1/ε) + 1)/t)
      linarith
    have h1' : t * (1 + (Real.log (1/ε) + 1)/t)
        ≤ t * Real.exp ((Real.log (1/ε) + 1)/t) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt ht)
    have h2 : t * ((Real.log (1/ε) + 1)/t) = Real.log (1/ε) + 1 := by field_simp
    have h3 : t * (1 + (Real.log (1/ε) + 1)/t)
        = t + t * ((Real.log (1/ε) + 1)/t) := by ring
    linarith
  have hcont : ContinuousOn (fun r : ℝ => r * Real.log (t/r))
      (Set.Icc t (t * Real.exp ((Real.log (1/ε) + 1)/t))) := by
    have hd : ContinuousOn (fun r : ℝ => t / r)
        (Set.Icc t (t * Real.exp ((Real.log (1/ε) + 1)/t))) := by
      apply ContinuousOn.div continuousOn_const continuousOn_id
      intro r hr
      have hrp : (0:ℝ) < r := by have h := hr.1; linarith
      exact ne_of_gt hrp
    apply ContinuousOn.mul continuousOn_id
    apply ContinuousOn.log hd
    intro r hr
    have hrp : (0:ℝ) < r := by have h := hr.1; linarith
    exact ne_of_gt (div_pos ht hrp)
  have hvalt : Real.log ε ≤ t * Real.log (t/t) := by
    have h1 : t * Real.log (t/t) = 0 := by
      rw [div_self (ne_of_gt ht), Real.log_one, mul_zero]
    rw [h1, hLneg]
    linarith
  have hvalR : t * Real.exp ((Real.log (1/ε) + 1)/t) *
      Real.log (t / (t * Real.exp ((Real.log (1/ε) + 1)/t))) ≤ Real.log ε := by
    have ha : (0:ℝ) < Real.exp ((Real.log (1/ε) + 1)/t) := Real.exp_pos _
    have hdiv : t / (t * Real.exp ((Real.log (1/ε) + 1)/t))
        = (Real.exp ((Real.log (1/ε) + 1)/t))⁻¹ := by
      field_simp
    rw [hdiv, Real.log_inv (Real.exp ((Real.log (1/ε) + 1)/t)),
      Real.log_exp ((Real.log (1/ε) + 1)/t)]
    rw [hLneg]
    have hkey : (Real.log (1/ε) + 1) * Real.exp ((Real.log (1/ε) + 1)/t)
        ≥ Real.log (1/ε) := by
      have hL1 : (0:ℝ) ≤ Real.log (1/ε) + 1 := by linarith
      nlinarith [hE1, hL1]
    have hexp : t * Real.exp ((Real.log (1/ε) + 1)/t) * ((Real.log (1/ε) + 1)/t)
        = (Real.log (1/ε) + 1) * Real.exp ((Real.log (1/ε) + 1)/t) := by
      have h2 : t * ((Real.log (1/ε) + 1)/t) = Real.log (1/ε) + 1 := by field_simp
      calc t * Real.exp ((Real.log (1/ε) + 1)/t) * ((Real.log (1/ε) + 1)/t)
          = Real.exp ((Real.log (1/ε) + 1)/t) * (t * ((Real.log (1/ε) + 1)/t)) := by ring
        _ = Real.exp ((Real.log (1/ε) + 1)/t) * (Real.log (1/ε) + 1) := by rw [h2]
        _ = (Real.log (1/ε) + 1) * Real.exp ((Real.log (1/ε) + 1)/t) := by ring
    linarith
  obtain ⟨r, hrIcc, hreq0⟩ :=
    (isPreconnected_Icc (a := t) (b := t * Real.exp ((Real.log (1/ε) + 1)/t))).intermediate_value₂
      (Set.mem_Icc.mpr ⟨le_refl t, hRge⟩)
      (Set.mem_Icc.mpr ⟨hRge, le_refl _⟩)
      (f := fun _ : ℝ => Real.log ε) (g := fun r : ℝ => r * Real.log (t/r))
      continuousOn_const hcont hvalt hvalR
  have hr0 : (0:ℝ) < r := by have := hrIcc.1; linarith
  have hrpos : (0:ℝ) < t/r := div_pos ht hr0
  have heqr : (t/r)^r = ε := by
    rw [Real.rpow_def_of_pos hrpos, mul_comm, ← hreq0, Real.exp_log hε0]
  refine ⟨r, hrIcc.1, heqr, ?_⟩
  intro s hts hsol
  have hs0 : (0:ℝ) < s := by have := hts; linarith
  have hspos : (0:ℝ) < t/s := div_pos ht hs0
  have hs' : s * Real.log (t/s) = Real.log ε := by
    apply Real.exp_injective
    rw [Real.rpow_def_of_pos hspos, mul_comm] at hsol
    rw [hsol, Real.exp_log hε0]
  have hr' : r * Real.log (t/r) = Real.log ε := by
    apply Real.exp_injective
    rw [Real.exp_log hε0, ← heqr, Real.rpow_def_of_pos hrpos]
    congr 1
    ring
  have hxs : (1:ℝ) ≤ s/t := by rw [le_div_iff₀ ht]; linarith
  have hxr : (1:ℝ) ≤ r/t := by
    rw [le_div_iff₀ ht]
    have h := hrIcc.1
    linarith
  rw [sim157_flip ht hs0, neg_mul] at hs'
  rw [sim157_flip ht hr0, neg_mul] at hr'
  have h5 : t * ((s/t) * Real.log (s/t)) = t * ((r/t) * Real.log (r/t)) :=
    neg_injective (by rw [hs', hr'])
  have h6 : (s/t) * Real.log (s/t) = (r/t) * Real.log (r/t) :=
    mul_left_cancel₀ (ne_of_gt ht) h5
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h7 := sim157_log_mul_strictMono hxs
      ((div_lt_div_iff₀ ht ht).mpr (mul_lt_mul_of_pos_right hlt ht))
    linarith
  · have h7 := sim157_log_mul_strictMono hxr
      ((div_lt_div_iff₀ ht ht).mpr (mul_lt_mul_of_pos_right hlt ht))
    linarith

end Qatlib.Concepts.QsvtCore.HamiltonianSim
