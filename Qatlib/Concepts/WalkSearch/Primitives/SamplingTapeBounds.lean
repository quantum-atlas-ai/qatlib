/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.GraphVocabulary

/-!
# Avoidance bounds for sampling tapes

This module counts vertex-sampling tapes that avoid a fixed set and bounds that count under a
logarithmic sampling-size condition. `natLog_padding_ge_log` connects the discrete base-two
logarithm to the real natural logarithm for these estimates.

The sampling estimates serve the finite subset-search setting [ChildsEisenberg2003].

## Main statements

* `avoiding_tape_card`: exactly `(n - S.card) ^ k` avoiding tapes.
* `source_sampling_avoid_bound`: an inverse-fourth-power bound after normalization.

## References

* [Childs and Eisenberg, 2003][ChildsEisenberg2003]
-/

set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators

/-- There are exactly `(n - S.card) ^ k` length-`k` vertex tapes whose entries all avoid `S`. -/
theorem avoiding_tape_card (n k : ℕ) (S : Finset (Fin n)) :
    (Finset.univ.filter (fun s : Fin k→Fin n=>∀ i,s i∉S)).card=(n-S.card)^k := by
  rw [← Fintype.card_subtype]
  have he : {s : Fin k→Fin n // ∀ i,s i∉S} ≃ (Fin k→{v : Fin n //v∉S}) :=
      Equiv.subtypePiEquivPi (β := fun _ : Fin k=>Fin n) (p := fun _ v=>v∉S)
  rw [Fintype.card_congr he,Fintype.card_fun,Fintype.card_fin,Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_coe]

/-- For positive `n`, the natural logarithm of `n` is at most the real cast of `Nat.log 2 n +
1`. -/
theorem natLog_padding_ge_log (n : ℕ) (hn : 0<n) : Real.log (n:ℝ)≤(Nat.log 2 n+1:ℕ) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hp : (n:ℝ)<(2:ℝ)^(Nat.log 2 n+1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1<2) n
  have hl := Real.log_lt_log hnR hp
  rw [Real.log_pow] at hl
  have h2 : Real.log 2≤1 := by have hh:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2);linarith
  have hh := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (Nat.log 2 n+1))
  norm_num only [Nat.cast_add,Nat.cast_one] at hl hh ⊢
  nlinarith [hl]

/-- Under the target-size and sampling-length assumptions, `(n - d) ^ k ≤ n ^ k / n ^ 4` over
the reals. -/
theorem source_sampling_avoid_bound (n d k : ℕ) (ε : ℝ) (hn : 0<n) (_hε : 0<ε)
    (hd : d≤n) (hlarge : (n:ℝ)^(1-ε)≤(d:ℝ))
    (hk : 4*(n:ℝ)^ε*(Nat.log 2 n+1:ℕ)≤(k:ℝ)) :
    ((n-d:ℕ):ℝ)^k≤(n:ℝ)^k/(n:ℝ)^4 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hdR : (d:ℝ)≤n := by exact_mod_cast hd
  have hp : (n:ℝ)^ε*(n:ℝ)^(1-ε)=(n:ℝ) := by
    rw [← Real.rpow_add hnR,show ε+(1-ε)=1 by ring,Real.rpow_one]
  have hx : 0≤1-(d:ℝ)/(n:ℝ) := by rw [sub_nonneg,div_le_one hnR];exact hdR
  have he := Real.add_one_le_exp (-(d:ℝ)/(n:ℝ))
  have hbase : 1-(d:ℝ)/(n:ℝ)≤Real.exp (-(d:ℝ)/(n:ℝ)) := by
    simpa only [neg_div,sub_eq_add_neg,add_comm] using he
  have hpow : (1-(d:ℝ)/(n:ℝ))^k≤Real.exp (-(d:ℝ)/(n:ℝ)*(k:ℝ)) := by
    rw [mul_comm,Real.exp_nat_mul]
    exact pow_le_pow_left₀ hx hbase k
  have hlog := natLog_padding_ge_log n hn
  have hkd : 4*Real.log (n:ℝ)≤(d:ℝ)*(k:ℝ)/(n:ℝ) := by
    apply (le_div_iff₀ hnR).mpr
    have ht := mul_le_mul_of_nonneg_left hlarge (Real.rpow_nonneg hnR.le ε)
    rw [hp] at ht
    have hh := mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg d)
    have hhlog := mul_le_mul_of_nonneg_left hlog (by positivity : (0:ℝ)≤4*(n:ℝ))
    have htm := mul_le_mul_of_nonneg_right ht (by positivity : (0:ℝ)≤4*(Nat.log 2 n+1:ℕ))
    nlinarith [hh,hhlog,htm]
  have hExpArg : -(d:ℝ)/(n:ℝ)*(k:ℝ)≤-4*Real.log (n:ℝ) := by
    calc
      -(d:ℝ)/(n:ℝ)*(k:ℝ) = -((d:ℝ)*(k:ℝ)/(n:ℝ)) := by ring
      _ ≤ -4*Real.log (n:ℝ) := by linarith [hkd]
  have h4 : Real.exp (4*Real.log (n:ℝ))=(n:ℝ)^4 := by
    simpa only [Real.exp_log hnR] using! Real.exp_nat_mul (Real.log (n:ℝ)) 4
  have hexp : Real.exp (-(d:ℝ)/(n:ℝ)*(k:ℝ))≤1/(n:ℝ)^4 := by
    calc
      Real.exp (-(d:ℝ)/(n:ℝ)*(k:ℝ)) ≤ Real.exp (-4*Real.log (n:ℝ)) := Real.exp_le_exp.mpr hExpArg
      _ = 1/(n:ℝ)^4 := by
        rw [show -4*Real.log (n:ℝ)=-(4*Real.log (n:ℝ)) by ring,Real.exp_neg,h4]
        simp only [one_div]
  have hfrac : ((n-d:ℕ):ℝ)/(n:ℝ)=1-(d:ℝ)/(n:ℝ) := by rw [Nat.cast_sub hd];field_simp
  have hh := (hpow.trans hexp)
  rw [← hfrac,div_pow] at hh
  have hb := (div_le_iff₀ (pow_pos hnR k)).mp hh
  exact hb.trans_eq (by ring)
end Qatlib.Concepts.WalkSearch.Primitives
