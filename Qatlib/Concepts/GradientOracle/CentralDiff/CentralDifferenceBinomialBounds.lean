/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceEntropy
import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceAlgebra
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Exponential bounds for central-difference binomial ratios

Central binomial and entropy estimates bound the ratios appearing in high-order
central-difference weights. `centralDiff_ratio_power_bound` controls a ratio times `l ^ k` by `2
* sqrt m * m ^ k * exp (-(7 / 6) * m)` for `1 ≤ l ≤ m` and `2 * m ≤ k`. See
[GilyenArunachalamWiebe2019] for background.

## Main statements

* `centralDiff_central_choose_lower`: For positive `m`, the central binomial coefficient
  satisfies `4 ^ m ≤ 2 * sqrt m * choose (2 * m) m`.
* `centralDiff_ratio_power_bound`: For `0 < l ≤ m` and `2 * m ≤ k`, the binomial ratio times `l
  ^ k` is at most `2 * sqrt m * m ^ k * exp (-(7 / 6) * m)`.

## References

* [Gilyen, Arunachalam, and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Concepts.GradientOracle.CentralDiff
open scoped BigOperators

/-- For positive `m`, the central binomial coefficient satisfies `4 ^ m ≤ 2 * sqrt m * choose (2
* m) m`. -/
theorem centralDiff_central_choose_lower (m : ℕ) (hm : 0<m) :
    (4 : ℝ)^m≤2*Real.sqrt m*(Nat.choose (2*m) m : ℝ) := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm0 : m=0
    · subst m; norm_num
    · have hmp : 0<m := by omega
      have hmr : (0 : ℝ)<m := by exact_mod_cast hmp
      have hmn : (0 : ℝ)<(m : ℝ)+1 := by positivity
      have hi := ih hmp
      have hn := Nat.succ_mul_centralBinom_succ m
      simp only [Nat.centralBinom_eq_two_mul_choose] at hn
      have hc : ((m : ℝ)+1)*(Nat.choose (2*(m+1)) (m+1) : ℝ)=
          2*(2*(m : ℝ)+1)*(Nat.choose (2*m) m : ℝ) := by exact_mod_cast hn
      have hs : 2*((m : ℝ)+1)*Real.sqrt m≤(2*(m : ℝ)+1)*Real.sqrt ((m : ℝ)+1) := by
        apply (sq_le_sq₀ (by positivity) (by positivity)).mp
        simp only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg m),Real.sq_sqrt (by positivity : 0≤(m : ℝ)+1)]
        nlinarith
      have ha := mul_le_mul_of_nonneg_left hi (by positivity : 0≤4*((m : ℝ)+1))
      have hb := mul_le_mul_of_nonneg_left hs (by positivity : 0≤4*(Nat.choose (2*m) m : ℝ))
      have he : ((m : ℝ)+1)*(2*Real.sqrt ((m : ℝ)+1)*(Nat.choose (2*(m+1)) (m+1) : ℝ))=
          4*Real.sqrt ((m : ℝ)+1)*(2*(m : ℝ)+1)*(Nat.choose (2*m) m : ℝ) := by
        calc
          _ = 2*Real.sqrt ((m : ℝ)+1)*(((m : ℝ)+1)*(Nat.choose (2*(m+1)) (m+1) : ℝ)) := by ring
          _ = _ := by rw [hc]; ring
      rw [pow_succ]
      push_cast
      nlinarith

/-- The real exponential of seven sixths is at most four. -/
private theorem centralDiff_exp_seven_sixths : Real.exp (7/6 : ℝ)≤4 := by
  calc
    _ = Real.exp 1*Real.exp (1/6 : ℝ) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ 3*(1/(1-(1/6 : ℝ))) := mul_le_mul Real.exp_one_lt_three.le
      (Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)) (Real.exp_pos _).le (by norm_num)
    _ ≤ 4 := by norm_num

/-- For nonnegative `a` and `b`, any binomial term with `j ≤ n` is at most `(a + b) ^ n`. -/
theorem centralDiff_binomial_term_le (a b : ℝ) (ha : 0≤a) (hb : 0≤b) (n j : ℕ) (hj : j≤n) :
    (Nat.choose n j : ℝ)*a^j*b^(n-j)≤(a+b)^n := by
  have hmem : j∈Finset.range (n+1) := Finset.mem_range.mpr (by omega)
  have h := Finset.single_le_sum (s := Finset.range (n+1))
    (f := fun i => a^i*b^(n-i)*(Nat.choose n i : ℝ))
    (fun i _ => by positivity) hmem
  rw [← add_pow] at h
  simpa only [mul_assoc,mul_comm,mul_left_comm] using h

/-- For `0 < l < m`, the coefficient ratio multiplied by `(l / m) ^ (2 * m)` is at most `2 *
sqrt m * exp (-(7 / 6) * m)`. -/
theorem centralDiff_ratio_entropy (m l : ℕ) (hm : 0<m) (hl : 0<l) (hlm : l<m) :
    let y := (l : ℝ)/(m : ℝ)
    y^(2*m)*((Nat.choose m l : ℝ)/(Nat.choose (m+l) l : ℝ))≤
      2*Real.sqrt m*Real.exp (-(7/6 : ℝ)*(m : ℝ)) := by
  (try dsimp only)
  let y := (l : ℝ)/(m : ℝ)
  have hmr : (0 : ℝ)<m := by exact_mod_cast hm
  have hly : (0 : ℝ)<l := by exact_mod_cast hl
  have hle : (l : ℝ)<m := by exact_mod_cast hlm
  have hy : 0<y := div_pos hly hmr
  have hy1 : y<1 := (div_lt_one hmr).mpr hle
  have hp : 0<1+y := by linarith
  have hq : 0<1-y := by linarith
  let A := (1+y)^(m+l)*(1-y)^(m-l)
  have hA : 0<A := mul_pos (pow_pos hp _) (pow_pos hq _)
  have hC : (0 : ℝ)<Nat.choose (2*m) m := by exact_mod_cast Nat.choose_pos (by omega : m≤2*m)
  have ht := centralDiff_binomial_term_le (1+y) (1-y) hp.le hq.le (2*m) (m+l) (by omega)
  rw [show (1+y)+(1-y)=2 by ring,show 2*m-(m+l)=m-l by omega,pow_mul] at ht
  norm_num only [show (2 : ℝ)^2=4 by norm_num] at ht
  have hcentre := centralDiff_central_choose_lower m hm
  have hraw : (Nat.choose (2*m) (m+l) : ℝ)*A≤2*Real.sqrt m*(Nat.choose (2*m) m : ℝ) := by
    simpa only [A,mul_assoc] using ht.trans hcentre
  have hratio : (Nat.choose (2*m) (m+l) : ℝ)/(Nat.choose (2*m) m : ℝ)≤2*Real.sqrt m/A := by
    apply (div_le_div_iff₀ hC hA).mpr
    exact hraw
  rw [centralDiff_choose_ratio m l hlm.le]
  have hmul := mul_le_mul_of_nonneg_left hratio (pow_nonneg hy.le (2*m))
  have hcastplus : ((m+l : ℕ) : ℝ)=(m : ℝ)*(1+y) := by dsimp [y]; push_cast; field_simp
  have hcastminus : ((m-l : ℕ) : ℝ)=(m : ℝ)*(1-y) := by
    rw [Nat.cast_sub hlm.le]
    dsimp [y]
    field_simp
  have hlog : Real.log A=(m : ℝ)*centralDiffBinaryEntropy y := by
    dsimp only [A]
    rw [Real.log_mul (pow_ne_zero _ hp.ne') (pow_ne_zero _ hq.ne'),Real.log_pow,Real.log_pow,hcastplus,hcastminus]
    dsimp [centralDiffBinaryEntropy]
    ring
  have heq : y^(2*m)*(2*Real.sqrt m/A)=
      2*Real.sqrt m*Real.exp ((m : ℝ)*(2*Real.log y-centralDiffBinaryEntropy y)) := by
    rw [show A=Real.exp ((m : ℝ)*centralDiffBinaryEntropy y) from by rw [← hlog,Real.exp_log hA]]
    rw [mul_sub,Real.exp_sub]
    have hpow : y^(2*m)=Real.exp (((2*m : ℕ) : ℝ)*Real.log y) := by
      rw [Real.exp_nat_mul,Real.exp_log hy]
    have hpow' : y^(2*m)=Real.exp ((m : ℝ)*(2*Real.log y)) := by
      rw [hpow]
      congr 1
      push_cast
      ring
    rw [hpow']
    ring
  have hexp :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (centralDiff_entropy_exponent y hy hy1) hmr.le)
  calc
    _ ≤ _ := hmul
    _ = _ := heq
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [mul_comm] using hexp

/-- The exponentially decaying normalized coefficient-ratio bound holds also at the endpoint `l
= m`. -/
theorem centralDiff_ratio_entropy_closed (m l : ℕ) (hm : 0<m) (hl : 0<l) (hlm : l≤m) :
    ((l : ℝ)/(m : ℝ))^(2*m)*((Nat.choose m l : ℝ)/(Nat.choose (m+l) l : ℝ))≤
      2*Real.sqrt m*Real.exp (-(7/6 : ℝ)*(m : ℝ)) := by
  by_cases he : l=m
  · subst l
    have hmr : (0 : ℝ)<m := by exact_mod_cast hm
    have hC : (0 : ℝ)<Nat.choose (2*m) m := by exact_mod_cast Nat.choose_pos (by omega : m≤2*m)
    rw [div_self hmr.ne',one_pow,Nat.choose_self,Nat.cast_one,show m+m=2*m by omega]
    have hc := centralDiff_central_choose_lower m hm
    have hr : 1/(Nat.choose (2*m) m : ℝ)≤2*Real.sqrt m/(4 : ℝ)^m := by
      apply (div_le_div_iff₀ hC (by positivity)).mpr
      simpa only [one_mul] using hc
    have he : Real.exp ((m : ℝ)*(7/6 : ℝ))≤(4 : ℝ)^m := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos _).le centralDiff_exp_seven_sixths m
    have hexp : 1/(4 : ℝ)^m≤Real.exp (-(7/6 : ℝ)*(m : ℝ)) := by
      rw [show -(7/6 : ℝ)*(m : ℝ)=-((m : ℝ)*(7/6 : ℝ)) by ring,Real.exp_neg]
      rw [← one_div]
      apply (div_le_div_iff₀ (by positivity) (Real.exp_pos _)).mpr
      simpa only [one_mul] using he
    simpa only [one_mul] using
        hr.trans (by simpa only [div_eq_mul_inv,one_div,one_mul] using mul_le_mul_of_nonneg_left hexp (by positivity : 0≤2*Real.sqrt m))
  · exact centralDiff_ratio_entropy m l hm hl (by omega)

/-- For `0 < l ≤ m` and `2 * m ≤ k`, the binomial ratio times `l ^ k` is at most `2 * sqrt m * m
^ k * exp (-(7 / 6) * m)`. -/
theorem centralDiff_ratio_power_bound (m l k : ℕ) (hm : 0<m) (hl : 0<l) (hlm : l≤m) (hk : 2*m≤k) :
    ((Nat.choose m l : ℝ)/(Nat.choose (m+l) l : ℝ))*(l : ℝ)^k≤
      2*Real.sqrt m*(m : ℝ)^k*Real.exp (-(7/6 : ℝ)*(m : ℝ)) := by
  let y := (l : ℝ)/(m : ℝ)
  have hmr : (0 : ℝ)<m := by exact_mod_cast hm
  have hly : (0 : ℝ)<l := by exact_mod_cast hl
  have hy : 0≤y := (div_pos hly hmr).le
  have hy1 : y≤1 := (div_le_one hmr).mpr (by exact_mod_cast hlm)
  have hpow := pow_le_pow_of_le_one hy hy1 hk
  have hrat : 0≤((Nat.choose m l : ℝ)/(Nat.choose (m+l) l : ℝ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hpow hrat
  have he := centralDiff_ratio_entropy_closed m l hm hl hlm
  have hScaled := mul_le_mul_of_nonneg_left (hmul.trans he) (pow_nonneg hmr.le k)
  have hlm' : (l : ℝ)=(m : ℝ)*y := by dsimp [y]; field_simp
  rw [hlm',mul_pow]
  convert! hScaled using 1 <;> ring

end Qatlib.Concepts.GradientOracle.CentralDiff
