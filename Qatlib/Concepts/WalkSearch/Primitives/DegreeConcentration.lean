/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.DegreeTestContracts
import Qatlib.Concepts.WalkSearch.Primitives.DegreeRounds

/-!
# Concentration for corrected degree tests

Proves the corrected high- and low-degree misclassification bounds using single-round sampling
estimates and finite majority concentration. `fact2DegreeTest_concentration_allPositive` covers
every positive vertex count, and `fact2DegreeTest_concentration` supplies the version assuming
`n ≥ 64`; see [Ambainis2005] for the graph-search setting.

## Main statements

* `fact2DegreeTest_concentration_allPositive`: For every positive `n` and `0 < δ < 1`, the
  prescribed repeated degree test satisfies both high- and low-degree error-event bounds of at
  most `1 / n ^ 3` over uniformly counted tapes.
* `fact2DegreeTest_concentration`: Establishes the corrected degree-test concentration contract
  for `n ≥ 64`, with both error-event fractions bounded by `1 / n ^ 3`.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators

/-- For every positive `n` and `0 < δ < 1`, the prescribed repeated degree test satisfies both
high- and low-degree error-event bounds of at most `1 / n ^ 3` over uniformly counted tapes. -/
theorem fact2DegreeTest_concentration_allPositive : fact2DegreeTestAllPositive := by
  intro n δ hn hδ _hδ1 K c _hc G v
  have hn0 : 0<n := by omega
  letI : NeZero n := ⟨hn0.ne'⟩
  have hnR : (0:ℝ)<n := by exact_mod_cast hn0
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (by omega : 1≤n)
  have hK : 0<K := by dsimp [K];omega
  have hC : (n:ℝ)^δ≤(c:ℝ) := Nat.le_ceil _
  have hp : (n:ℝ)^δ*(n:ℝ)^(1-δ)=(n:ℝ) := by
    rw [← Real.rpow_add hnR,show δ+(1-δ)=1 by ring,Real.rpow_one]
  have hN : (0:ℝ)<Fintype.card (Fin K→Fin c→Fin n) := by
    exact_mod_cast (Fintype.card_pos : 0<Fintype.card (Fin K→Fin c→Fin n))
  have htail := logarithmic_round_tail n hn0
  constructor
  · by_cases hg : 10*Nat.ceil ((n:ℝ)^(1-δ))<degOf G.edges v
    · have hD : 10*(n:ℝ)^(1-δ)≤(degOf G.edges v:ℝ) := by
        have h1 := mul_le_mul_of_nonneg_left (Nat.le_ceil ((n:ℝ)^(1-δ))) (by norm_num : (0:ℝ)≤10)
        have h2 : 10*(Nat.ceil ((n:ℝ)^(1-δ)):ℝ)<degOf G.edges v := by exact_mod_cast hg
        exact h1.trans h2.le
      have hl : 10≤(degOf G.edges v:ℝ)*(c:ℝ)/(n:ℝ) := by
        apply (le_div_iff₀ hnR).mpr
        have hh := mul_le_mul hC hD (by positivity : (0:ℝ)≤10*(n:ℝ)^(1-δ)) (Nat.cast_nonneg c)
        nlinarith [hp,hh]
      have hm := finite_bad_round_majority K hK (fun s : Fin c→Fin n=>¬roundHit G v s)
        (high_degree_miss_fraction G v hn0 hl)
      have hs : (Finset.univ.filter (fun tape : Fin K→Fin c→Fin n=>
          10*Nat.ceil ((n:ℝ)^(1-δ))<degOf G.edges v ∧ degreeTestLowCorrected G v K c tape)) ⊆
          Finset.univ.filter (fun tape=>K≤2*(Finset.univ.filter (fun i=>¬roundHit G v (tape i))).card) := by
        intro tape ht
        have hh := (Finset.mem_filter.mp ht).2.2
        simp only [degreeTestLowCorrected,decide_eq_true_eq,hitRounds_eq_card_roundHit] at hh
        have hc1 :=
            Finset.card_filter_add_card_filter_not (s:=Finset.univ)
            (fun i : Fin K=>roundHit G v (tape i))
        simp only [Finset.card_univ,Fintype.card_fin] at hc1
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
      have hcard : ((Finset.univ.filter (fun tape : Fin K→Fin c→Fin n=>
          10*Nat.ceil ((n:ℝ)^(1-δ))<degOf G.edges v ∧ degreeTestLowCorrected G v K c tape)).card:ℝ)/
          (Fintype.card (Fin K→Fin c→Fin n):ℝ)≤1/(n:ℝ)^3 := by
        exact ((div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hs) hN.le).trans hm).trans htail
      have hh := (div_le_iff₀ hN).mp hcard
      have hb := mul_le_mul_of_nonneg_right hh (pow_nonneg hnR.le 3)
      have heq :
          (1/(n:ℝ)^3*(Fintype.card (Fin K→Fin c→Fin n):ℝ))*(n:ℝ)^3=Fintype.card
          (Fin K→Fin c→Fin n) := by field_simp
      rw [heq] at hb
      exact_mod_cast hb
    · simp [hg]
  · by_cases hg : degOf G.edges v<Nat.floor ((n:ℝ)^(1-δ)/10)
    · have hD : (degOf G.edges v:ℝ)≤(n:ℝ)^(1-δ)/10 := by
        exact (by exact_mod_cast hg.le : (degOf G.edges v:ℝ)≤Nat.floor ((n:ℝ)^(1-δ)/10)).trans
            (Nat.floor_le (by positivity))
      have hC2 : (c:ℝ)≤2*(n:ℝ)^δ := by
        have hc1 := Nat.ceil_lt_add_one (by positivity : (0:ℝ)≤(n:ℝ)^δ)
        have hc2 := Real.one_le_rpow hn1 hδ.le
        dsimp [c]
        linarith
      have hl : (c:ℝ)*(degOf G.edges v:ℝ)/(n:ℝ)≤1/5 := by
        apply (div_le_iff₀ hnR).mpr
        have hh :=
            mul_le_mul hC2 hD (Nat.cast_nonneg (degOf G.edges v)) (by positivity : (0:ℝ)≤2*(n:ℝ)^δ)
        nlinarith [hp,hh]
      have hm := finite_bad_round_majority K hK (fun s : Fin c→Fin n=>roundHit G v s)
        (low_degree_hit_fraction G v hn0 hl)
      have hs : (Finset.univ.filter (fun tape : Fin K→Fin c→Fin n=>
          degOf G.edges v<Nat.floor ((n:ℝ)^(1-δ)/10) ∧ ¬degreeTestLowCorrected G v K c tape)) ⊆
          Finset.univ.filter (fun tape=>K≤2*(Finset.univ.filter (fun i=>roundHit G v (tape i))).card) := by
        intro tape ht
        have hh := (Finset.mem_filter.mp ht).2.2
        simp only [degreeTestLowCorrected,decide_eq_true_eq,hitRounds_eq_card_roundHit] at hh
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
      have hcard : ((Finset.univ.filter (fun tape : Fin K→Fin c→Fin n=>
          degOf G.edges v<Nat.floor ((n:ℝ)^(1-δ)/10) ∧ ¬degreeTestLowCorrected G v K c tape)).card:ℝ)/
          (Fintype.card (Fin K→Fin c→Fin n):ℝ)≤1/(n:ℝ)^3 := by
        exact ((div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hs) hN.le).trans hm).trans htail
      have hh := (div_le_iff₀ hN).mp hcard
      have hb := mul_le_mul_of_nonneg_right hh (pow_nonneg hnR.le 3)
      have heq :
          (1/(n:ℝ)^3*(Fintype.card (Fin K→Fin c→Fin n):ℝ))*(n:ℝ)^3=Fintype.card
          (Fin K→Fin c→Fin n) := by field_simp
      rw [heq] at hb
      exact_mod_cast hb
    · simp [hg]

/-- Establishes the corrected degree-test concentration contract for `n ≥ 64`, with both
error-event fractions bounded by `1 / n ^ 3`. -/
theorem fact2DegreeTest_concentration : fact2DegreeTestCorrected := by
  intro n δ hn hδ hδ1
  exact fact2DegreeTest_concentration_allPositive n δ (by omega) hδ hδ1
end Qatlib.Concepts.WalkSearch.Primitives
