/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.AnalysisLayer.ChooseEntropyBoundStat
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.MagicDistill24.AnalysisLayer
open scoped Classical BigOperators

/-- Establishes the binomial coefficient entropy bound specified by `ChooseEntropyBound`. -/
theorem chooseEntropyBound : ChooseEntropyBound := by
  intro n k hk
  by_cases hk0 : k=0
  · simp [hk0]
  by_cases hkn : k=n
  · subst k
    have hn0 : n ≠ 0 := hk0
    have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    simp [hnr]
  have hn : 0 < n := by omega
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  let r := (k : ℝ)/(n : ℝ)
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := (div_lt_one hnr).2 (by exact_mod_cast (show k < n by omega))
  have hs0 : 0 < 1-r := sub_pos.2 hr1
  have hbin : (Nat.choose n k : ℝ)*r^k*(1-r)^(n-k) ≤ 1 := by
    have hsum := add_pow r (1-r) n
    have hsingle := Finset.single_le_sum (s := Finset.range (n+1))
      (f := fun j => r^j*(1-r)^(n-j)*(Nat.choose n j : ℝ))
      (fun j _ => by positivity) (show k ∈ Finset.range (n+1) by simp; omega)
    rw [← hsum] at hsingle
    have hr : r+(1-r)=1 := by ring
    rw [hr,one_pow] at hsingle
    nlinarith only [hsingle]
  have hlog : (n : ℝ)*Real.binEntropy r+(k : ℝ)*Real.log r+((n-k : ℕ) : ℝ)*Real.log (1-r)=0 := by
    have he : (n : ℝ)*r=k := by dsimp [r]; field_simp
    simp only [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
      Real.negMulLog_def, Nat.cast_sub hk]
    calc
      _ = ((n : ℝ)*r-(k : ℝ))*(Real.log (1-r)-Real.log r) := by ring
      _ = 0 := by rw [he,sub_self,zero_mul]
  have hexp : Real.exp ((n : ℝ)*Real.binEntropy r)*r^k*(1-r)^(n-k)=1 := by
    have hpr : r^k=Real.exp ((k : ℝ)*Real.log r) := by rw [Real.exp_nat_mul,Real.exp_log hr0]
    have hps : (1-r)^(n-k)=Real.exp (((n-k : ℕ) : ℝ)*Real.log (1-r)) := by
      rw [Real.exp_nat_mul,Real.exp_log hs0]
    rw [hpr,hps,← Real.exp_add,← Real.exp_add,hlog,Real.exp_zero]
  have hpos : 0 < r^k*(1-r)^(n-k) := by positivity
  apply (mul_le_mul_iff_left₀ hpos).1
  have he : (r^k*(1-r)^(n-k))*(Nat.choose n k : ℝ) ≤
      (r^k*(1-r)^(n-k))*Real.exp ((n : ℝ)*Real.binEntropy r) := by
    nlinarith only [hbin,hexp]
  simpa only [mul_comm] using he

end Qatlib.Papers.MagicDistill24.AnalysisLayer
