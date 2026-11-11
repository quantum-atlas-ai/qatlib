/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Information-theoretic ordered-search lower bounds

Computes the entropy of a symmetric noise profile and derives lower bounds on its multiway
information. Under an explicit information-rate hypothesis, the module converts these bounds
into query lower bounds corresponding to the discussion in [BenOrHassidim2007].

## Main statements

* `source_theorem4_2_query_lower_bound`: gives the entropy-corrected query lower bound
  conditional on the information-rate bound.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
open scoped BigOperators

namespace Qatlib.Papers.OrderedList07.MainResults

/-- The noise profile on `k + 1` outcomes assigning mass `1 − δ` to zero and `δ / k` to each
other outcome. -/
noncomputable def sourceTheorem4_2Noise (k : ℕ) (δ : ℝ) : Fin (k + 1) → ℝ :=
  fun i => if i = 0 then 1 - δ else δ / k

/-- For positive `k`, expands the entropy sum of `sourceTheorem4_2Noise` into its distinguished
term and `k` equal remaining terms. -/
lemma source_theorem4_2_noise_entropy (k : ℕ) (hk : 0 < k) (δ : ℝ) :
    (∑ i : Fin (k + 1),
        -((sourceTheorem4_2Noise k δ i)
          * (Real.log (sourceTheorem4_2Noise k δ i) / Real.log 2)))
      = -((1 - δ) * (Real.log (1 - δ) / Real.log 2))
        + (k : ℝ) * (-(δ / (k : ℝ)) * (Real.log (δ / (k : ℝ)) / Real.log 2)) := by
  have h0 : (0 : Fin (k + 1)) ∈ (Finset.univ : Finset (Fin (k + 1))) := Finset.mem_univ _
  have hcard : (Finset.univ.erase (0 : Fin (k + 1))).card = k := by
    rw [Finset.card_erase_of_mem h0, Finset.card_univ, Fintype.card_fin]
    omega
  have hconst : ∀ i ∈ (Finset.univ.erase (0 : Fin (k + 1))),
      -((sourceTheorem4_2Noise k δ i)
          * (Real.log (sourceTheorem4_2Noise k δ i) / Real.log 2))
        = -((δ / (k : ℝ)) * (Real.log (δ / (k : ℝ)) / Real.log 2)) := by
    intro i hi
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
    simp only [sourceTheorem4_2Noise, if_neg hi0]
  have hErase : (∑ i ∈ (Finset.univ.erase (0 : Fin (k + 1))),
      -((sourceTheorem4_2Noise k δ i)
          * (Real.log (sourceTheorem4_2Noise k δ i) / Real.log 2)))
      = (k : ℝ) * (-((δ / (k : ℝ)) * (Real.log (δ / (k : ℝ)) / Real.log 2))) := by
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, hcard, nsmul_eq_mul]
  have hZero : -((sourceTheorem4_2Noise k δ 0)
        * (Real.log (sourceTheorem4_2Noise k δ 0) / Real.log 2))
      = -((1 - δ) * (Real.log (1 - δ) / Real.log 2)) := by
    simp [sourceTheorem4_2Noise]
  rw [← Finset.sum_erase_add _ _ h0, hErase, hZero]
  ring

/-- For `k ≥ 2` and `0 < δ < 1`, the multiway information is at least `(1 − δ) * log₂ k −
binEntropy δ` [BenOrHassidim2007]. -/
lemma source_theorem4_2_multiInfo_ge (k : ℕ) (hk : 2 ≤ k) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) * (Real.log k / Real.log 2) - binEntropy δ
      ≤ multiInfo (sourceTheorem4_2Noise k δ) := by
  have hkpos : 0 < k := by omega
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsum := source_theorem4_2_noise_entropy k hkpos δ
  have hkey : Real.log (δ / (k : ℝ)) / Real.log 2
      = Real.log δ / Real.log 2 - Real.log (k : ℝ) / Real.log 2 := by
    rw [Real.log_div hδ0.ne' hkR.ne', sub_div]
  have hlog : Real.log (k : ℝ) / Real.log 2 ≤ Real.log (1 + (k : ℝ)) / Real.log 2 := by
    apply div_le_div_of_nonneg_right _ h2.le
    apply Real.log_le_log hkR
    linarith
  rw [multiInfo, hsum, hkey, binEntropy]
  have hprod : (k : ℝ) * (-(δ / (k : ℝ))
        * ((Real.log δ / Real.log 2 - Real.log (k : ℝ) / Real.log 2)))
      = - (δ * (Real.log δ / Real.log 2 - Real.log (k : ℝ) / Real.log 2)) := by
    field_simp
  rw [hprod]
  ring_nf
  rw [mul_comm ((Real.log 2)⁻¹) (Real.log (1 + (k : ℝ)))]
  rw [div_eq_mul_inv, div_eq_mul_inv] at hlog
  linarith [hlog]

/-- An upper bound of `(π / log 2) * t` on the noise profile's multiway information implies the
corresponding lower bound on `t` [BenOrHassidim2007]. -/
theorem source_theorem4_3_query_lower_bound
    (k : ℕ) (δ t : ℝ)
    (hrate : multiInfo (sourceTheorem4_2Noise k δ) ≤ (Real.pi / Real.log 2) * t) :
    (Real.log 2 / Real.pi) * multiInfo (sourceTheorem4_2Noise k δ) ≤ t := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpos : 0 < Real.log 2 / Real.pi := div_pos h2 hpi
  have hmul := mul_le_mul_of_nonneg_left hrate hpos.le
  have heq : Real.log 2 / Real.pi * (Real.pi / Real.log 2 * t) = t := by
    field_simp
  linarith [hmul, heq]

/-- For `k ≥ 2` and `0 < δ < 1`, the information-rate hypothesis implies the entropy-corrected
query lower bound with coefficient `log 2 / π` [BenOrHassidim2007]. -/
theorem source_theorem4_2_query_lower_bound
    (k : ℕ) (hk : 2 ≤ k) (δ t : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hrate : multiInfo (sourceTheorem4_2Noise k δ) ≤ (Real.pi / Real.log 2) * t) :
    (Real.log 2 / Real.pi) * ((1 - δ) * (Real.log k / Real.log 2) - binEntropy δ) ≤ t := by
  have h1 := source_theorem4_2_multiInfo_ge k hk δ hδ0 hδ1
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcoef : 0 ≤ Real.log 2 / Real.pi := (div_pos h2 hpi).le
  have hstep : (Real.log 2 / Real.pi) * ((1 - δ) * (Real.log k / Real.log 2) - binEntropy δ)
      ≤ (Real.log 2 / Real.pi) * multiInfo (sourceTheorem4_2Noise k δ) :=
    mul_le_mul_of_nonneg_left h1 hcoef
  exact le_trans hstep (source_theorem4_3_query_lower_bound k δ t hrate)

end Qatlib.Papers.OrderedList07.MainResults
