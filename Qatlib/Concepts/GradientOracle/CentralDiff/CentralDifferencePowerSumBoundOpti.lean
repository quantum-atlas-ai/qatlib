/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferencePowerSumBoundStat
import Mathlib.Analysis.Complex.ExponentialBounds
import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceExactnessOpti
import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceBinomialBounds
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.GradientOracle.CentralDiff

theorem centralDifferencePowerSumBound_one (k : ℕ) :
    (∑ ℓ ∈ Finset.Ico (-1 : ℤ) 2,
      |centralDiffCoeff 1 ℓ * (ℓ : ℝ) ^ (k + 1)|) ≤
      6 * Real.exp (-(7 / 6 : ℝ)) := by
  have hs : Finset.Ico (-1 : ℤ) 2 = {-1, 0, 1} := by decide
  have hsum : (∑ ℓ ∈ Finset.Ico (-1 : ℤ) 2,
      |centralDiffCoeff 1 ℓ * (ℓ : ℝ) ^ (k + 1)|) = 1 := by
    norm_num [hs, centralDiffCoeff, abs_mul, abs_pow]
  rw [hsum]
  have he : Real.exp (7 / 6 : ℝ) ≤ 6 := by
    calc
      _ = Real.exp 1 * Real.exp (1 / 6 : ℝ) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ 3 * (1 / (1 - (1 / 6 : ℝ))) :=
        mul_le_mul Real.exp_one_lt_three.le
          (Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num))
          (Real.exp_pos _).le (by norm_num)
      _ ≤ 6 := by norm_num
  rw [Real.exp_neg]
  change 1 ≤ 6 / Real.exp (7 / 6 : ℝ)
  exact (le_div_iff₀ (Real.exp_pos _)).2 (by simpa using he)

theorem centralDiff_power_weight_abs (m l k : ℕ) (hl : 0<l) :
    |centralDiffCoeff m (l : ℤ)*(l : ℝ)^(k+1)|=
      ((Nat.choose m l : ℝ)/(Nat.choose (m+l) l : ℝ))*(l : ℝ)^k := by
  have hlz : (l : ℤ)≠0 := by exact_mod_cast hl.ne'
  have hlr : (l : ℝ)≠0 := by exact_mod_cast hl.ne'
  rw [centralDiffCoeff,if_neg hlz]
  simp only [Int.natAbs_natCast,Int.cast_natCast,abs_mul,abs_div,abs_pow,abs_neg,
    abs_one,one_pow,abs_of_nonneg (Nat.cast_nonneg l : (0 : ℝ)≤l),abs_of_nonneg (Nat.cast_nonneg (Nat.choose m l) : (0 : ℝ)≤Nat.choose m l),
    abs_of_nonneg (Nat.cast_nonneg (Nat.choose (m+l) l) : (0 : ℝ)≤Nat.choose (m+l) l)]
  rw [pow_succ]
  field_simp

theorem centralDifferencePowerSumBound : CentralDifferencePowerSumBound := by
  intro m k hm hk
  let S := Finset.Ico (-(m : ℤ)) ((m : ℤ)+1)
  let T := S.erase 0
  let A := fun l : ℤ => |centralDiffCoeff m l*(l : ℝ)^(k+1)|
  let D := 2*Real.sqrt m*(m : ℝ)^k*Real.exp (-(7/6 : ℝ)*(m : ℝ))
  have h0 : A 0=0 := by simp [A,centralDiffCoeff]
  have hs : (∑ l∈S,A l)=(∑ l∈T,A l) := by
    have hi : (∑ l∈T,A l)=(∑ l∈S,A l) := Finset.sum_subset (Finset.erase_subset _ _) (by
      intro l hl hn
      have hz : l=0 := by simpa only [T,Finset.mem_erase,hl,and_true,not_ne_iff] using hn
      simpa only [hz] using h0)
    exact hi.symm
  have hpoint (l : ℤ) (hl : l∈T) : A l≤D := by
    have hne : l≠0 := (Finset.mem_erase.mp hl).1
    have hmem : -(m : ℤ)≤l ∧ l<(m : ℤ)+1 := Finset.mem_Ico.mp (Finset.mem_erase.mp hl).2
    cases l with
    | ofNat l =>
      change (l : ℤ)≠0 at hne
      change -(m : ℤ)≤(l : ℤ) ∧ (l : ℤ)<(m : ℤ)+1 at hmem
      have hlp : 0<l := by omega
      have hlm : l≤m := by omega
      change |centralDiffCoeff m (l : ℤ)*(l : ℝ)^(k+1)|≤D
      rw [centralDiff_power_weight_abs m l k hlp]
      exact centralDiff_ratio_power_bound m l k hm hlp hlm hk
    | negSucc l =>
      have hlm : l+1≤m := by omega
      have hi : Int.negSucc l=-((l+1 : ℕ) : ℤ) := by omega
      change |centralDiffCoeff m (Int.negSucc l)*((Int.negSucc l : ℤ) : ℝ)^(k+1)|≤D
      rw [hi,centralDiffCoeff_neg,Int.cast_neg,Int.cast_natCast,abs_mul,abs_neg,abs_pow,abs_neg,
        abs_of_nonneg (by positivity : (0 : ℝ)≤(l+1 : ℕ))]
      have he := centralDiff_power_weight_abs m (l+1) k (by omega)
      rw [abs_mul,abs_pow,abs_of_nonneg (by positivity : (0 : ℝ)≤(l+1 : ℕ))] at he
      rw [he]
      exact centralDiff_ratio_power_bound m (l+1) k hm (by omega) hlm hk
  have hcard : T.card=2*m := by
    have hm0 : (0 : ℤ)∈S := Finset.mem_Ico.mpr ⟨by omega,by omega⟩
    rw [Finset.card_erase_of_mem hm0]
    simp only [S,Int.card_Ico]
    omega
  have hsum : (∑ l∈S,A l)≤(2*m : ℝ)*D := by
    rw [hs]
    calc
      _ ≤ ∑ _l∈T,D := Finset.sum_le_sum hpoint
      _ = _ := by simp only [Finset.sum_const,hcard,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
  have hmr : (0 : ℝ)<m := by exact_mod_cast hm
  have hp : (m : ℝ)^((k : ℝ)+3/2)=(m : ℝ)^k*(m : ℝ)*Real.sqrt m := by
    rw [Real.rpow_add hmr,Real.rpow_natCast,show (3/2 : ℝ)=1+1/2 by norm_num,
      Real.rpow_add hmr,Real.rpow_one,← Real.sqrt_eq_rpow]
    ring
  rw [hp]
  change (∑ l∈S,A l)≤_
  apply hsum.trans
  dsimp [D]
  have hn : 0≤Real.exp (-(7/6 : ℝ)*(m : ℝ))*(m : ℝ)^k*(m : ℝ)*Real.sqrt m := by positivity
  nlinarith

end Qatlib.Concepts.GradientOracle.CentralDiff
