/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpacetimeLB26.ScalarSupport.Defs
import Qatlib.Papers.SpacetimeLB26.ScalarSupport.Entanglement

/-!
# Scalar erasure resource lower bounds

This module bounds finite-allocation survival products and derives a one-qubit logarithmic cost
bound from supplied fidelity and accuracy inequalities. The dimension data and combined bound
record the separate resource constraints used in [BhartiHaugTanggara2026].

## Main statements

* `erasure_one_qubit_bound`: The supplied fidelity-loss lower bound and accuracy upper bound
  imply `C ≥ S / log (1/p) * log (S / (-log (1-ε)))`.
* `one_execution_full_dimension`: Memory-dimension data force every layer width to be at least
  `K`, and hence the record cost to be at least `K * S`.

## References

* [Bharti et al., 2026][BhartiHaugTanggara2026]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpacetimeLB26.ScalarSupport.Erasure

open scoped BigOperators
open Finset

/-- For `0 < p < 1`, positive `S`, and an integer allocation of total width at most `C`, the
product survival expression is at most `exp (-S * p^(C/S))`. -/
theorem survival_product_le_exp
    (S m : ℕ) (hS : 0 < S) (p C : ℝ) (_hp : 0 < p) (_hp1 : p < 1) (_hC : 0 ≤ C)
    (n : Fin S → Fin (m + 1))
    (hn : (∑ s, ((n s : ℕ) : ℝ)) ≤ C) :
    (∏ s, (1 - p ^ (((n s : ℕ) : ℝ)))) ≤
      Real.exp (-(S : ℝ) * p ^ (C / (S : ℝ))) := by
  have hSpos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS

  have hfactor_nonneg : ∀ s : Fin S, 0 ≤ 1 - p ^ (((n s : ℕ) : ℝ)) := by
    intro s
    have h1 : p ^ (((n s : ℕ) : ℝ)) ≤ 1 :=
      Real.rpow_le_one _hp.le _hp1.le (by positivity)
    linarith

  have hstep : ∏ s : Fin S, (1 - p ^ (((n s : ℕ) : ℝ)))
      ≤ ∏ s : Fin S, Real.exp (-(p ^ (((n s : ℕ) : ℝ)))) := by
    refine Finset.prod_le_prod₀ (fun s _ => hfactor_nonneg s) (fun s _ => ?_)
    simpa using Real.one_sub_le_exp_neg (p ^ (((n s : ℕ) : ℝ)))

  have hprodexp : (∏ s : Fin S, Real.exp (-(p ^ (((n s : ℕ) : ℝ)))))
      = Real.exp (-(∑ s : Fin S, p ^ (((n s : ℕ) : ℝ)))) := by
    rw [← Real.exp_sum]
    congr 1
    simp [Finset.sum_neg_distrib]

  have hmean : (S : ℝ) * p ^ ((∑ s, ((n s : ℕ) : ℝ)) / (S : ℝ))
      ≤ ∑ s, p ^ (((n s : ℕ) : ℝ)) := by
    have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => p ^ x) := convexOn_rpow_left _hp
    have hjensen : p ^ (∑ s : Fin S, (1 / (S : ℝ)) • ((n s : ℕ) : ℝ))
        ≤ ∑ s : Fin S, (1 / (S : ℝ)) • p ^ (((n s : ℕ) : ℝ)) := by
      refine hconv.map_sum_le (t := Finset.univ)
        (w := fun _ : Fin S => 1 / (S : ℝ))
        (p := fun s : Fin S => ((n s : ℕ) : ℝ)) ?_ ?_ ?_
      · intro i _
        positivity
      · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp [ne_of_gt hSpos]
      · intro i _
        exact Set.mem_univ _
    simp only [smul_eq_mul] at hjensen

    have hsum1 : (∑ s : Fin S, (1 / (S : ℝ)) * ((n s : ℕ) : ℝ))
        = (∑ s, ((n s : ℕ) : ℝ)) / (S : ℝ) := by
      rw [← Finset.mul_sum, one_div, inv_mul_eq_div]
    have hsum2 : (∑ s : Fin S, (1 / (S : ℝ)) * p ^ (((n s : ℕ) : ℝ)))
        = (1 / (S : ℝ)) * ∑ s, p ^ (((n s : ℕ) : ℝ)) := by
      rw [← Finset.mul_sum]
    rw [hsum1, hsum2] at hjensen

    have hS1 : (S : ℝ) * (1 / (S : ℝ)) = 1 := by
      rw [one_div, mul_inv_cancel₀ (ne_of_gt hSpos)]
    have := mul_le_mul_of_nonneg_left hjensen hSpos.le
    rw [← mul_assoc, hS1, one_mul] at this
    exact this

  have hmono : p ^ (C / (S : ℝ)) ≤ p ^ ((∑ s, ((n s : ℕ) : ℝ)) / (S : ℝ)) := by
    have hdiv : (∑ s, ((n s : ℕ) : ℝ)) / (S : ℝ) ≤ C / (S : ℝ) := by
      apply div_le_div_of_nonneg_right hn hSpos.le
    exact (Real.rpow_le_rpow_left_iff_of_base_lt_one _hp _hp1).2 hdiv
  have hsum_ge : (S : ℝ) * p ^ (C / (S : ℝ))
      ≤ ∑ s, p ^ (((n s : ℕ) : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hmono hSpos.le
    linarith [hmean]

  calc ∏ s, (1 - p ^ (((n s : ℕ) : ℝ)))
      ≤ ∏ s, Real.exp (-(p ^ (((n s : ℕ) : ℝ)))) := hstep
    _ = Real.exp (-(∑ s, p ^ (((n s : ℕ) : ℝ)))) := hprodexp
    _ ≤ Real.exp (-(S : ℝ) * p ^ (C / (S : ℝ))) := by
        apply Real.exp_le_exp_of_le
        linarith [hsum_ge]

/-- A value bounded by the maximal feasible survival product is also controlled through that
maximum by `exp (-S * p^(C/S))` under the stated parameter conditions. -/
theorem avoid_complete_erasure_bound
    (S m : ℕ) (hS : 0 < S) (p C Psurv : ℝ)
    (_hp : 0 < p) (_hp1 : p < 1) (_hC : 0 ≤ C) (_hm : C ≤ (m : ℝ))
    (hPsurv : Psurv ≤ maxSurvivalProd S m C p) :
    Psurv ≤ maxSurvivalProd S m C p ∧
      maxSurvivalProd S m C p ≤ Real.exp (-(S : ℝ) * p ^ (C / (S : ℝ))) := by
  refine ⟨hPsurv, ?_⟩
  rw [maxSurvivalProd_eq _hC]
  refine Finset.sup'_le _ _ (fun n hn => ?_)
  simp only [feasibleAllocs, Finset.mem_filter, Finset.mem_univ, true_and] at hn
  exact survival_product_le_exp S m hS p C _hp _hp1 _hC n hn

/-- The supplied fidelity-loss lower bound and accuracy upper bound imply `C ≥ S / log (1/p) *
log (S / (-log (1-ε)))`. See [BhartiHaugTanggara2026]. -/
theorem erasure_one_qubit_bound
    (S C p ε Fe : ℝ) (hS : 0 < S) (_hp : 0 < p) (_hp1 : p < 1)
    (_hε : 0 < ε) (_hε1 : ε < 1)
    (hE5 : 1 - Fe ≥ (1 / 2) * (1 - Real.exp (-(S * p ^ (C / S)))))
    (hdiamond : 1 - Fe ≤ ε / 2)
    (_hSbig : -Real.log (1 - ε) < S) :
    C ≥ (S / Real.log (1 / p)) * Real.log (S / (-Real.log (1 - ε))) := by

  have hSp : S * p ^ (C / S) ≤ -Real.log (1 - ε) := by
    have h1 : (1 / 2) * (1 - Real.exp (-(S * p ^ (C / S)))) ≤ ε / 2 := by linarith
    have h2 : 1 - Real.exp (-(S * p ^ (C / S))) ≤ ε := by nlinarith
    have h3 : 1 - ε ≤ Real.exp (-(S * p ^ (C / S))) := by linarith
    have hlog : Real.log (1 - ε) ≤ -(S * p ^ (C / S)) := by
      calc Real.log (1 - ε) ≤ Real.log (Real.exp (-(S * p ^ (C / S)))) :=
            Real.log_le_log (by linarith) h3
        _ = -(S * p ^ (C / S)) := Real.log_exp _
    linarith
  have hcεpos : 0 < -Real.log (1 - ε) := by
    have h1e : 0 < 1 - ε := by linarith
    have hlt : Real.log (1 - ε) < 0 := Real.log_neg h1e (by linarith)
    linarith
  have hpC : p ^ (C / S) ≤ (-Real.log (1 - ε)) / S := by
    rw [le_div_iff₀ hS]; linarith
  have hlogp_pos : 0 < Real.log (1 / p) := by
    apply Real.log_pos
    rw [one_div]
    exact one_lt_inv_iff₀.mpr ⟨_hp, _hp1⟩
  have hstep : Real.log S - Real.log (-Real.log (1 - ε))
      ≤ (C / S) * Real.log (1 / p) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos _hp _) hpC
    rw [Real.log_rpow _hp] at h
    have hdiv : Real.log ((-Real.log (1 - ε)) / S)
        = Real.log (-Real.log (1 - ε)) - Real.log S :=
      Real.log_div (ne_of_gt hcεpos) (ne_of_gt hS)
    rw [hdiv] at h
    have hneg : (C / S) * Real.log p = -((C / S) * Real.log (1 / p)) := by
      rw [one_div, Real.log_inv]; ring
    rw [hneg] at h
    linarith
  have hlogSdiv : Real.log (S / (-Real.log (1 - ε)))
      = Real.log S - Real.log (-Real.log (1 - ε)) :=
    Real.log_div (ne_of_gt hS) (ne_of_gt hcεpos)
  have hmain : S * (Real.log S - Real.log (-Real.log (1 - ε)))
      ≤ C * Real.log (1 / p) := by
    have _hm := mul_le_mul_of_nonneg_left hstep hS.le
    have heq : S * ((C / S) * Real.log (1 / p)) = C * Real.log (1 / p) := by
      field_simp
    linarith [heq]
  rw [hlogSdiv, ge_iff_le, div_mul_eq_mul_div, div_le_iff₀ hlogp_pos]
  linarith [hmain]

/-- Integer-valued layer widths and an overlap greater than `1/2`, with overlap bounded above by
`2^(q s - K)` at every layer. -/
structure MemoryDimensionData (S K : ℕ) where
  q : Fin S → ℝ
  q_int : ∀ s, ∃ n : ℕ, q s = (n : ℝ)
  overlap : ℝ
  overlap_upper : ∀ s, overlap ≤ (2 : ℝ) ^ (q s - (K : ℝ))
  overlap_lower : 1 / 2 < overlap

/-- Memory-dimension data force every layer width to be at least `K`, and hence the record cost
to be at least `K * S`. See [BhartiHaugTanggara2026]. -/
theorem one_execution_full_dimension {S K : ℕ} (_hK : 1 ≤ K)
    (d : MemoryDimensionData S K) :
    (∀ s, (K : ℝ) ≤ d.q s) ∧ (K : ℝ) * (S : ℝ) ≤ recordCost d.q := by
  have hqK : ∀ s, (K : ℝ) ≤ d.q s := by
    intro s
    obtain ⟨n, hn⟩ := d.q_int s
    by_contra hlt
    push Not at hlt

    have hnk : n < K := by
      have hnr : (n : ℝ) < (K : ℝ) := by rwa [hn] at hlt
      exact_mod_cast hnr
    have hle : (n : ℝ) - (K : ℝ) ≤ -1 := by
      have hnr : (n : ℝ) + 1 ≤ (K : ℝ) := by exact_mod_cast hnk
      linarith
    have h2 : (2 : ℝ) ^ (d.q s - (K : ℝ)) ≤ (2 : ℝ) ^ (-1 : ℝ) := by
      apply (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).2
      rw [hn]; exact hle
    have hhalf : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by norm_num [Real.rpow_neg_one]
    have : d.overlap ≤ 1 / 2 := by
      calc d.overlap ≤ (2 : ℝ) ^ (d.q s - (K : ℝ)) := d.overlap_upper s
        _ ≤ (2 : ℝ) ^ (-1 : ℝ) := h2
        _ = 1 / 2 := hhalf
    linarith [d.overlap_lower]
  refine ⟨hqK, ?_⟩
  have hS : (0 : ℝ) ≤ (S : ℝ) := by positivity
  calc (K : ℝ) * (S : ℝ) = ∑ _s : Fin S, (K : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ s : Fin S, d.q s := Finset.sum_le_sum (fun s _ => hqK s)
    _ = recordCost d.q := rfl

/-- Collect the assumed dimension, erasure, and combined asymptotic lower bounds into one
conjunction for the record cost. See [BhartiHaugTanggara2026]. -/
theorem combined_erasure_bound
    (S K : ℕ) (q : Fin S → ℝ) (p ε cε recordCostVal BigOconstant : ℝ)
    (_hK : 1 ≤ K) (_hp : 0 < p) (_hp1 : p < 1) (_hε : 0 < ε) (_hε1 : ε < 1)
    (_hcε : cε = -Real.log (1 - ε))
    (_hrecordCost : recordCostVal = recordCost q)
    (hE9 : (K : ℝ) * (S : ℝ) ≤ recordCostVal)
    (hE10 : (S : ℝ) / Real.log (1 / p) * Real.log ((S : ℝ) / cε) ≤ recordCostVal)
    (_hSbig : 0 < BigOconstant)
    (hBig : recordCostVal ≥ BigOconstant * ((S : ℝ) * ((K : ℝ) + Real.log ((S : ℝ) / ε)))) :
    recordCostVal ≥ (K : ℝ) * (S : ℝ) ∧
      recordCostVal ≥ (S : ℝ) / Real.log (1 / p) * Real.log ((S : ℝ) / cε) ∧
      recordCostVal ≥ BigOconstant * ((S : ℝ) * ((K : ℝ) + Real.log ((S : ℝ) / ε))) :=
  ⟨hE9, hE10, hBig⟩

end Qatlib.Papers.SpacetimeLB26.ScalarSupport.Erasure
