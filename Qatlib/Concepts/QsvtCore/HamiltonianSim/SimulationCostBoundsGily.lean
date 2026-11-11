/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.HamiltonianSim.SimulationCostBoundsStat
import Qatlib.Concepts.QsvtCore.HamiltonianSim.SimulationCostEquationGily

/-!
# Bounds for the simulation cost equation

This module proves `SimulationCostBounds` using monotonicity estimates for real logarithms. The
bounds control a solution of `(t / r) ^ r = ε` in two parameter regimes and give a family of
upper bounds indexed by positive `q`. The mathematical background is developed in
[GilyenSuLowWiebe2019].

## Main statements

* `simulationCostBounds_answer`: logarithmic and linear estimates for the simulation cost
  parameter.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false

namespace Qatlib.Concepts.QsvtCore.HamiltonianSim

open Real

/-- For `x` and `y` at least one, the inequality `x * log x ≤ y * log y` implies `x ≤ y`. -/
theorem sim157_log_mul_le_of_le {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h : x * Real.log x ≤ y * Real.log y) : x ≤ y := by
  by_contra hne
  have hlt : y < x := lt_of_not_ge hne
  have h7 := sim157_log_mul_strictMono hy hlt
  linarith

/-- For `w ≥ 1`, twice the natural logarithm of `w` is at most `w`. -/
theorem sim157_two_log_le {w : ℝ} (hw : 1 ≤ w) : 2 * Real.log w ≤ w := by
  by_cases hw2 : w ≤ 2
  · have h1 : Real.log w ≤ w - 1 := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < w)
    linarith
  · have h1 : Real.log (w/2) ≤ w/2 - 1 :=
      Real.log_le_sub_one_of_pos (by have := lt_of_not_ge hw2; linarith : (0:ℝ) < w/2)
    have h2 : Real.log w = Real.log (w/2) + Real.log 2 := by
      rw [← Real.log_mul (ne_of_gt (by have := lt_of_not_ge hw2; linarith : (0:ℝ) < w/2))
        two_ne_zero]
      field_simp
    have h3 : Real.log 2 ≤ 1 := by
      have h4 : (2:ℝ) ≤ Real.exp 1 := by
        have h5 := Real.add_one_le_exp 1
        linarith
      calc Real.log 2 ≤ Real.log (Real.exp 1) :=
          (Real.log_le_log_iff (by norm_num : (0:ℝ) < 2) (Real.exp_pos 1)).mpr h4
        _ = 1 := Real.log_exp 1
    linarith

/-- For positive `t`, the expression `r * log (t / r)` strictly decreases as `r` increases above
`t`. -/
theorem sim157_g_antimono {t a b : ℝ} (ht : 0 < t) (ha : t ≤ a) (hab : a < b) :
    b * Real.log (t/b) < a * Real.log (t/a) := by
  have ha0 : (0:ℝ) < a := by have := ha; linarith
  have hb0 : (0:ℝ) < b := by linarith
  have hxa : (1:ℝ) ≤ a/t := by rw [le_div_iff₀ ht]; linarith
  have hxb : (1:ℝ) ≤ b/t := by rw [le_div_iff₀ ht]; linarith
  have hlt : a/t < b/t := (div_lt_div_iff₀ ht ht).mpr (mul_lt_mul_of_pos_right hab ht)
  have h7 := sim157_log_mul_strictMono hxa hlt
  rw [sim157_flip ht ha0, sim157_flip ht hb0, neg_mul, neg_mul]
  nlinarith [h7, ht]

set_option maxHeartbeats 400000 in

/-- Solutions of the simulation cost equation satisfy `SimulationCostBounds`, corresponding to
[Gilyén et al., Lemma 59][GilyenSuLowWiebe2019]. -/
theorem simulationCostBounds_answer : SimulationCostBounds := by
  intro t ε r ht hε hε1 htr hreq
  have hε0 : (0:ℝ) < ε := hε
  have h1ε : (1:ℝ) < 1/ε := by
    rw [lt_div_iff₀ hε0]
    norm_num
    linarith
  have hLpos : (0:ℝ) < Real.log (1/ε) := Real.log_pos h1ε
  have hLneg : Real.log ε = -(Real.log (1/ε)) := by
    rw [one_div, Real.log_inv ε, neg_neg]
  have he1 : (1:ℝ) ≤ Real.exp 1 := by
    have h := Real.exp_le_exp.mpr (by norm_num : (0:ℝ) ≤ 1)
    rwa [Real.exp_zero] at h
  have hr0 : (0:ℝ) < r := by have := htr; linarith
  have hrpos : (0:ℝ) < t/r := div_pos ht hr0
  have hreq2 : r * Real.log (t/r) = Real.log ε := by
    apply Real.exp_injective
    rw [Real.rpow_def_of_pos hrpos, mul_comm] at hreq
    rw [hreq, Real.exp_log hε0]
  have hrlogA : r * Real.log (t/r) = -(Real.log (1/ε)) := by
    rw [← hLneg]
    exact hreq2
  have hrlogB : r * Real.log (t/r) = -(Real.log (1/ε)) := by
    rw [← hLneg]
    exact hreq2
  rw [sim157_flip ht hr0, neg_mul] at hrlogB
  have hxr1 : (1:ℝ) ≤ r/t := by
    rw [le_div_iff₀ ht]
    linarith
  have hnorm : (r/t) * Real.log (r/t) = (Real.log (1/ε))/t := by
    have h1 : t * ((r/t) * Real.log (r/t)) = Real.log (1/ε) := neg_injective hrlogB
    exact (eq_div_iff (ne_of_gt ht)).mpr (by rw [mul_comm]; exact h1)
  refine ⟨?_, ?_, ?_⟩
  · intro hreg
    have hce : (Real.exp 1 : ℝ) ≤ (Real.log (1/ε))/t := by
      rw [le_div_iff₀ (Real.exp_pos 1)] at hreg
      rw [le_div_iff₀ ht]
      rw [mul_comm]
      linarith
    set c := (Real.log (1/ε))/t with hcde
    have hc1 : (1:ℝ) ≤ c := le_trans he1 hce
    have hcpos : (0:ℝ) < c := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hc1
    have hEpos : (0:ℝ) < (Real.exp 1 : ℝ) + c := by positivity
    have hDpos : (0:ℝ) < Real.log ((Real.exp 1 : ℝ) + c) :=
      Real.log_pos (by have := he1; have := hc1; linarith : (1:ℝ) < (Real.exp 1 : ℝ) + c)
    have hD1 : (1:ℝ) ≤ Real.log ((Real.exp 1 : ℝ) + c) := by
      have hDE : Real.log ((Real.exp 1 : ℝ)) ≤ Real.log ((Real.exp 1 : ℝ) + c) :=
        (Real.log_le_log_iff (Real.exp_pos 1) hEpos).mpr
          (by linarith : (Real.exp 1 : ℝ) ≤ (Real.exp 1 : ℝ) + c)
      rwa [Real.log_exp] at hDE
    have hlogcD : Real.log c ≤ Real.log ((Real.exp 1 : ℝ) + c) :=
      (Real.log_le_log_iff hcpos hEpos).mpr (by linarith : c ≤ (Real.exp 1 : ℝ) + c)
    have hwpos : (0:ℝ) < Real.log (2*c) :=
      Real.log_pos (by nlinarith [hc1] : (1:ℝ) < 2*c)
    have hDw : Real.log ((Real.exp 1 : ℝ) + c) ≤ Real.log (2*c) :=
      (Real.log_le_log_iff hEpos (by positivity : (0:ℝ) < 2*c)).mpr
        (by have := hce; nlinarith : (Real.exp 1 : ℝ) + c ≤ 2*c)
    have hw1 : (1:ℝ) ≤ Real.log (2*c) := le_trans hD1 hDw
    have hkey := sim157_two_log_le hw1
    have hlogDw : Real.log (Real.log ((Real.exp 1 : ℝ) + c)) ≤ Real.log (Real.log (2*c)) :=
      (Real.log_le_log_iff (by linarith : (0:ℝ) < Real.log ((Real.exp 1 : ℝ) + c)) hwpos).mpr hDw
    have hchain : Real.log ((Real.exp 1 : ℝ) + c)
        ≤ 2 * (Real.log (2*c) - Real.log (Real.log ((Real.exp 1 : ℝ) + c))) := by
      have a4 : 2 * (Real.log (2*c) - Real.log (Real.log ((Real.exp 1 : ℝ) + c)))
          ≥ 2 * (Real.log (2*c) - Real.log (Real.log (2*c))) := by linarith
      have a2 : 2 * (Real.log (2*c) - Real.log (Real.log (2*c))) ≥ Real.log (2*c) := by
        linarith
      linarith
    have hbot : (c / Real.log ((Real.exp 1 : ℝ) + c)) *
        Real.log (c / Real.log ((Real.exp 1 : ℝ) + c)) ≤ c := by
      have hld' : Real.log (c / Real.log ((Real.exp 1 : ℝ) + c))
          = Real.log c - Real.log (Real.log ((Real.exp 1 : ℝ) + c)) :=
        Real.log_div (ne_of_gt hcpos) (ne_of_gt hDpos)
      have hlogD0 : (0:ℝ) ≤ Real.log (Real.log ((Real.exp 1 : ℝ) + c)) :=
        Real.log_nonneg hD1
      have hmid : Real.log (c / Real.log ((Real.exp 1 : ℝ) + c))
          ≤ Real.log ((Real.exp 1 : ℝ) + c) := by
        rw [hld']
        linarith
      have hnn' : (0:ℝ) ≤ c / Real.log ((Real.exp 1 : ℝ) + c) :=
        div_nonneg (le_of_lt hcpos) (le_of_lt hDpos)
      calc (c / Real.log ((Real.exp 1 : ℝ) + c)) *
          Real.log (c / Real.log ((Real.exp 1 : ℝ) + c))
          ≤ (c / Real.log ((Real.exp 1 : ℝ) + c)) * Real.log ((Real.exp 1 : ℝ) + c) :=
            mul_le_mul_of_nonneg_left hmid hnn'
        _ = c := by field_simp
    have hge : c / Real.log ((Real.exp 1 : ℝ) + c) ≤ r/t := by
      by_cases hx01 : c / Real.log ((Real.exp 1 : ℝ) + c) ≤ 1
      · calc c / Real.log ((Real.exp 1 : ℝ) + c) ≤ 1 := hx01
          _ ≤ r/t := hxr1
      · have hx0 : (1:ℝ) ≤ c / Real.log ((Real.exp 1 : ℝ) + c) :=
          lt_of_not_ge (by simpa using hx01) |> le_of_lt
        refine sim157_log_mul_le_of_le hx0 hxr1 (le_trans hbot ?_)
        rw [hnorm]
    have hLD : Real.log (1/ε) / Real.log ((Real.exp 1 : ℝ) + c) ≤ r := by
      have h1 : Real.log (1/ε) / Real.log ((Real.exp 1 : ℝ) + c)
          = t * (c / Real.log ((Real.exp 1 : ℝ) + c)) := by
        rw [hcde]
        field_simp
      have h2 : t * (c / Real.log ((Real.exp 1 : ℝ) + c))
          ≤ t * (r/t) := mul_le_mul_of_nonneg_left hge (le_of_lt ht)
      have h3 : t * (r/t) = r := by field_simp
      calc Real.log (1/ε) / Real.log ((Real.exp 1 : ℝ) + c)
          = t * (c / Real.log ((Real.exp 1 : ℝ) + c)) := h1
        _ ≤ t * (r/t) := h2
        _ = r := h3
    have hhalf : Real.log (2*c) - Real.log (Real.log ((Real.exp 1 : ℝ) + c))
        ≥ (Real.log ((Real.exp 1 : ℝ) + c)) / 2 := by linarith
    have hnn2 : (0:ℝ) ≤ 2*c / Real.log ((Real.exp 1 : ℝ) + c) :=
      div_nonneg (by positivity : (0:ℝ) ≤ 2*c) (le_of_lt hDpos)
    have htop : c ≤ (2*c / Real.log ((Real.exp 1 : ℝ) + c)) *
        Real.log (2*c / Real.log ((Real.exp 1 : ℝ) + c)) := by
      have hld : Real.log (2*c / Real.log ((Real.exp 1 : ℝ) + c))
          = Real.log (2*c) - Real.log (Real.log ((Real.exp 1 : ℝ) + c)) :=
        Real.log_div (by positivity : (2:ℝ)*c ≠ 0) (ne_of_gt hDpos)
      rw [hld]
      calc c = (2*c / Real.log ((Real.exp 1 : ℝ) + c)) *
          ((Real.log ((Real.exp 1 : ℝ) + c)) / 2) := by field_simp
        _ ≤ (2*c / Real.log ((Real.exp 1 : ℝ) + c)) *
            (Real.log (2*c) - Real.log (Real.log ((Real.exp 1 : ℝ) + c))) :=
              mul_le_mul_of_nonneg_left hhalf hnn2
    have h21 : (1:ℝ) ≤ 2*c / Real.log ((Real.exp 1 : ℝ) + c) := by
      have hD2c : Real.log ((Real.exp 1 : ℝ) + c) ≤ 2*c := by
        have h1 : Real.log ((Real.exp 1 : ℝ) + c) ≤ (Real.exp 1 : ℝ) + c - 1 :=
          Real.log_le_sub_one_of_pos hEpos
        have h2 : (Real.exp 1 : ℝ) + c - 1 ≤ 2*c := by have := hce; linarith
        linarith
      rw [le_div_iff₀ hDpos, one_mul]
      exact hD2c
    have hle2 : r/t ≤ 2*c / Real.log ((Real.exp 1 : ℝ) + c) :=
      sim157_log_mul_le_of_le hxr1 h21 (le_trans hnorm.le htop)
    have hUP : r ≤ 4 * Real.log (1/ε) / Real.log ((Real.exp 1 : ℝ) + c) := by
      have h1 : r = t * (r/t) := by field_simp
      have h2 : t * (r/t) ≤ t * (2*c / Real.log ((Real.exp 1 : ℝ) + c)) :=
        mul_le_mul_of_nonneg_left hle2 (le_of_lt ht)
      have h3 : t * (2*c / Real.log ((Real.exp 1 : ℝ) + c))
          = 2 * Real.log (1/ε) / Real.log ((Real.exp 1 : ℝ) + c) := by
        rw [hcde]
        field_simp
      have h4 : (0:ℝ) ≤ Real.log (1/ε) / Real.log ((Real.exp 1 : ℝ) + c) :=
        div_nonneg (le_of_lt hLpos) (le_of_lt hDpos)
      have h5 : 2 * Real.log (1/ε) / Real.log ((Real.exp 1 : ℝ) + c)
          ≤ 4 * Real.log (1/ε) / Real.log ((Real.exp 1 : ℝ) + c) := by
        rw [mul_div_assoc, mul_div_assoc]
        linarith [h4]
      calc r = t * (r/t) := h1
        _ ≤ t * (2*c / Real.log ((Real.exp 1 : ℝ) + c)) := h2
        _ = 2 * Real.log (1/ε) / Real.log ((Real.exp 1 : ℝ) + c) := h3
        _ ≤ 4 * Real.log (1/ε) / Real.log ((Real.exp 1 : ℝ) + c) := h5
    exact ⟨hLD, hUP⟩
  · intro hreg
    have hc_le : (Real.log (1/ε))/t ≤ Real.exp 1 := by
      rw [div_le_iff₀ (Real.exp_pos 1)] at hreg
      rw [div_le_iff₀ ht, mul_comm]
      linarith
    have hval : (Real.log (1/ε))/t ≤ (Real.exp 1 : ℝ) * Real.log (Real.exp 1) := by
      rw [Real.log_exp, mul_one]
      exact hc_le
    have hx1 : r/t ≤ Real.exp 1 := by
      refine sim157_log_mul_le_of_le hxr1 he1 ?_
      rw [hnorm]
      exact hval
    have h1 : r = t * (r/t) := by field_simp
    have h2 : t * (r/t) ≤ t * (Real.exp 1) :=
      mul_le_mul_of_nonneg_left hx1 (le_of_lt ht)
    calc r = t * (r/t) := h1
      _ ≤ t * (Real.exp 1) := h2
      _ = (Real.exp 1) * t := mul_comm _ _
  · intro q hq
    have heq1 : (1:ℝ) ≤ Real.exp q := by
      have h := Real.exp_le_exp.mpr (le_of_lt hq)
      rwa [Real.exp_zero] at h
    set rq := (Real.exp q) * t + (Real.log (1/ε))/q with hrqd
    have hrq0 : (0:ℝ) < rq :=
      add_pos (mul_pos (Real.exp_pos q) ht) (div_pos hLpos hq)
    have hrq_t : t ≤ rq := by
      have h1 : t ≤ Real.exp q * t := le_mul_of_one_le_left (le_of_lt ht) heq1
      have h2 : (0:ℝ) ≤ (Real.log (1/ε))/q := (div_pos hLpos hq).le
      rw [hrqd]
      linarith
    have hprod : (Real.exp q) * t ≤ rq := by
      rw [hrqd]
      exact le_add_of_nonneg_right (div_pos hLpos hq).le
    have hle : t / rq ≤ (Real.exp q)⁻¹ := by
      rw [div_le_iff₀ hrq0]
      calc t = (Real.exp q)⁻¹ * ((Real.exp q) * t) := by field_simp
        _ ≤ (Real.exp q)⁻¹ * rq := mul_le_mul_of_nonneg_left hprod
          (le_of_lt (inv_pos.mpr (Real.exp_pos q)))
    have hlog : Real.log (t/rq) ≤ -q := by
      have h5 : Real.log (t/rq) ≤ Real.log ((Real.exp q)⁻¹) :=
        (Real.log_le_log_iff (div_pos ht hrq0) (inv_pos.mpr (Real.exp_pos q))).mpr hle
      rw [Real.log_inv (Real.exp q), Real.log_exp] at h5
      exact h5
    have h6 : rq * Real.log (t/rq) ≤ -(Real.log (1/ε)) := by
      have h7 : rq * Real.log (t/rq) ≤ rq * (-q) :=
        mul_le_mul_of_nonneg_left hlog (le_of_lt hrq0)
      have h8 : rq * (-q) = -(q * rq) := by ring
      have h9 : Real.log (1/ε) ≤ q * ((Real.exp q) * t + (Real.log (1/ε))/q) := by
        have h10 : q * ((Real.log (1/ε))/q) = Real.log (1/ε) := by field_simp
        have h11 : (0:ℝ) ≤ q * ((Real.exp q) * t) := by positivity
        nlinarith [h10, h11]
      linarith
    by_contra hrr
    have hlt : rq < r := lt_of_not_ge hrr
    have h10 := sim157_g_antimono ht hrq_t hlt
    linarith

end Qatlib.Concepts.QsvtCore.HamiltonianSim
