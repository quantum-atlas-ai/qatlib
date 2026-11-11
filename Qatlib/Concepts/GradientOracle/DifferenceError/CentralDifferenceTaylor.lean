/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferencePowerSumBoundOpti
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Taylor jets for central-difference remainders

`centralDiffTaylorJet` is the Taylor polynomial at zero written with iterated derivatives. The
module identifies it with the interval Taylor polynomial, proves exact central-difference action
on its degree-`2 * m` truncation, and bounds its remainder.

`centralDiff_remainder_prefactor` absorbs the coefficient power-sum factor and the Taylor
factorial into the exponential factor `exp (-(1 / 2) * m)`. See [GilyenArunachalamWiebe2019] for
background.

## Main statements

* `centralDiff_taylor_jet_action`: The order-`m` central-difference rule applied to the
  degree-`2 * m` Taylor jet equals `deriv f 0 * δ` for positive `m`.
* `centralDiff_taylor_remainder`: A bound `B` on the `(n + 1)`st derivative over the unoriented
  interval from zero to nonzero `x` bounds the Taylor-jet error by `B * |x| ^ (n + 1) / (n +
  1)!`.

## References

* [Gilyen, Arunachalam, and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

set_option warningAsError false
open Qatlib.Concepts.GradientOracle.CentralDiff

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Qatlib.Concepts.GradientOracle.DifferenceError
open scoped Classical BigOperators
open Set

/-- The Taylor polynomial at zero through degree `n`, evaluated at `x` using iterated
derivatives. -/
def centralDiffTaylorJet (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j∈Finset.range (n+1),iteratedDeriv j f 0/(Nat.factorial j : ℝ)*x^j

/-- The order-`m` central-difference rule applied to the degree-`2 * m` Taylor jet equals `deriv
f 0 * δ` for positive `m`. -/
theorem centralDiff_taylor_jet_action (m : ℕ) (hm : 0<m) (f : ℝ → ℝ) (δ : ℝ) :
    (∑ l∈Finset.Ico (-(m : ℤ)) ((m : ℤ)+1),centralDiffCoeff m l*centralDiffTaylorJet f (2*m) ((l : ℝ)*δ))=
      deriv f 0*δ := by
  simp only [centralDiffTaylorJet]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have he (j : ℕ) (hj : j∈Finset.range (2*m+1)) :
      (∑ l∈Finset.Ico (-(m : ℤ)) ((m : ℤ)+1),centralDiffCoeff m l*(iteratedDeriv j f 0/(Nat.factorial j : ℝ)*((l : ℝ)*δ)^j))=
        (iteratedDeriv j f 0/(Nat.factorial j : ℝ)*δ^j)*(if j=1 then 1 else 0) := by
    calc
      _ = (iteratedDeriv j f 0/(Nat.factorial j : ℝ)*δ^j)*
          (∑ l∈Finset.Ico (-(m : ℤ)) ((m : ℤ)+1),centralDiffCoeff m l*(l : ℝ)^j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        rw [mul_pow]
        ring
      _ = _ := by rw [centralDifferenceExactness m hm j (by have := Finset.mem_range.mp hj; omega)]
  rw [Finset.sum_congr rfl he]
  simp only [mul_ite,mul_one,mul_zero]
  rw [Finset.sum_ite_eq']
  have hmem : 1∈Finset.range (2*m+1) := Finset.mem_range.mpr (by omega)
  simp [hmem]

/-- For a sufficiently smooth function and a nonzero interval endpoint, the Taylor polynomial
within the unoriented interval equals the iterated-derivative Taylor jet. -/
theorem centralDiff_taylorWithin_eq (f : ℝ → ℝ) (n : ℕ) (hf : ContDiff ℝ (n+1) f)
    (x : ℝ) (hx : x≠0) (y : ℝ) :
    taylorWithinEval f n (uIcc 0 x) 0 y=centralDiffTaylorJet f n y := by
  have hu : UniqueDiffOn ℝ (uIcc 0 x) := uniqueDiffOn_Icc (by grind)
  rw [taylor_within_apply]
  unfold centralDiffTaylorJet
  apply Finset.sum_congr rfl
  intro j hj
  have hcont : ContDiffAt ℝ j f 0 := hf.contDiffAt.of_le (by
    exact_mod_cast (by have := Finset.mem_range.mp hj; omega : j≤n+1))
  rw [iteratedDerivWithin_eq_iteratedDeriv hu hcont (by simp),sub_zero,smul_eq_mul]
  ring

/-- A bound `B` on the `(n + 1)`st derivative over the unoriented interval from zero to nonzero
`x` bounds the Taylor-jet error by `B * |x| ^ (n + 1) / (n + 1)!`. -/
theorem centralDiff_taylor_remainder (f : ℝ → ℝ) (n : ℕ) (hf : ContDiff ℝ (n+1) f)
    (x B : ℝ) (hx : x≠0) (hB : ∀ u∈uIcc 0 x,|iteratedDeriv (n+1) f u|≤B) :
    |f x-centralDiffTaylorJet f n x|≤B*|x|^(n+1)/(Nat.factorial (n+1) : ℝ) := by
  obtain ⟨u,hu,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (x₀ := 0) (x := x)
    (by simpa only [ne_comm] using hx) hf.contDiffOn
  rw [centralDiff_taylorWithin_eq f n hf x hx x,sub_zero] at he
  rw [he,abs_div,abs_mul,abs_pow,abs_of_nonneg (Nat.cast_nonneg (Nat.factorial (n+1)) : (0 : ℝ)≤Nat.factorial (n+1))]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_right (hB u (Ioo_subset_Icc_self hu)) (by positivity)

/-- For positive `m`, dividing the central-difference power-sum prefactor by `(2 * m + 1)!`
bounds it by `exp (-(1 / 2) * m)`. -/
theorem centralDiff_remainder_prefactor (m : ℕ) (hm : 0<m) :
    6*Real.exp (-(7/6 : ℝ)*(m : ℝ))*(m : ℝ)^((2*m : ℕ)+3/2 : ℝ)/
      (Nat.factorial (2*m+1) : ℝ)≤Real.exp (-(1/2 : ℝ)*(m : ℝ)) := by
  have hmr : (0 : ℝ)<m := by exact_mod_cast hm
  have hS := Stirling.le_factorial_stirling (2*m)
  have hsqrt : Real.sqrt (2*Real.pi*((2*m : ℕ) : ℝ))=2*Real.sqrt Real.pi*Real.sqrt m := by
    push_cast
    rw [show 2*Real.pi*(2*(m : ℝ))=4*(Real.pi*(m : ℝ)) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ)≤4),Real.sqrt_mul Real.pi_pos.le]
    rw [show Real.sqrt (4 : ℝ)=2 by rw [show (4 : ℝ)=2^2 by norm_num,Real.sqrt_sq (by norm_num)]]
    ring
  rw [hsqrt] at hS
  let A := ((2*m+1 : ℕ) : ℝ)*(2*Real.sqrt Real.pi*Real.sqrt m)*(((2*m : ℕ) : ℝ)/Real.exp 1)^(2*m)
  have hA : 0<A := by dsimp [A]; positivity
  have hF : A≤(Nat.factorial (2*m+1) : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ)≤((2*m+1 : ℕ) : ℝ))
    simpa only [A,Nat.factorial_succ,Nat.cast_mul,mul_assoc] using h
  have hpi : (3/2 : ℝ)≤Real.sqrt Real.pi := by
    have h : (3/2 : ℝ)^2≤Real.pi := by linarith [Real.pi_gt_d2]
    have hs := Real.sqrt_le_sqrt h
    simpa only [Real.sqrt_sq (by norm_num : (0 : ℝ)≤3/2)] using hs
  have hP : 3*(m : ℝ)/(((2*m+1 : ℕ) : ℝ)*Real.sqrt Real.pi)≤1 := by
    apply (div_le_one (by positivity)).mpr
    push_cast
    nlinarith
  have hl4 : (4/3 : ℝ)≤Real.log 4 := by
    have he : Real.log 4=2*Real.log 2 := by rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
    rw [he]
    linarith [centralDiff_log_two_lower]
  have he : Real.exp ((5/6 : ℝ)*(m : ℝ))/(4 : ℝ)^m≤Real.exp (-(1/2 : ℝ)*(m : ℝ)) := by
    have hp := mul_le_mul_of_nonneg_right hl4 hmr.le
    have hlog : Real.log ((4 : ℝ)^m)=(m : ℝ)*Real.log 4 := Real.log_pow _ _
    rw [show (4 : ℝ)^m=Real.exp ((m : ℝ)*Real.log 4) by rw [← hlog,Real.exp_log (by positivity)],← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hpowl : (m : ℝ)^(((2*m : ℕ) : ℝ)+3/2)=(m : ℝ)^(2*m)*(m : ℝ)*Real.sqrt m := by
    rw [Real.rpow_add hmr,Real.rpow_natCast,show (3/2 : ℝ)=1+1/2 by norm_num,
      Real.rpow_add hmr,Real.rpow_one,← Real.sqrt_eq_rpow]
    ring
  have hEq : 6*Real.exp (-(7/6 : ℝ)*(m : ℝ))*(m : ℝ)^(((2*m : ℕ) : ℝ)+3/2)/A=
      (3*(m : ℝ)/(((2*m+1 : ℕ) : ℝ)*Real.sqrt Real.pi))*(Real.exp ((5/6 : ℝ)*(m : ℝ))/(4 : ℝ)^m) := by
    have hDen : (((2*m : ℕ) : ℝ)/Real.exp 1)^(2*m)=
        (4 : ℝ)^m*(m : ℝ)^(2*m)/Real.exp (2*(m : ℝ)) := by
      have h2 : (2 : ℝ)^(2*m)=(4 : ℝ)^m := by rw [pow_mul]; norm_num
      have he : Real.exp 1^(2*m)=Real.exp (2*(m : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [show ((2*m : ℕ) : ℝ)=2*(m : ℝ) by push_cast; rfl,div_pow,mul_pow,h2,he]
    have hE : Real.exp (-(7/6 : ℝ)*(m : ℝ))*Real.exp (2*(m : ℝ))=Real.exp ((5/6 : ℝ)*(m : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hpowl]
    dsimp only [A]
    rw [hDen]
    calc
      _ = (3*(m : ℝ)/(((2*m+1 : ℕ) : ℝ)*Real.sqrt Real.pi))*
          ((Real.exp (-(7/6 : ℝ)*(m : ℝ))*Real.exp (2*(m : ℝ)))/(4 : ℝ)^m) := by
        field_simp
        ring
      _ = _ := by rw [hE]
  have hN : 0≤6*Real.exp (-(7/6 : ℝ)*(m : ℝ))*(m : ℝ)^(((2*m : ℕ) : ℝ)+3/2) := by positivity
  calc
    _ ≤ 6*Real.exp (-(7/6 : ℝ)*(m : ℝ))*(m : ℝ)^(((2*m : ℕ) : ℝ)+3/2)/A :=
      div_le_div_of_nonneg_left hN hA hF
    _ = _ := hEq
    _ ≤ 1*Real.exp (-(1/2 : ℝ)*(m : ℝ)) := mul_le_mul hP he (by positivity) zero_le_one
    _ = _ := one_mul _
end Qatlib.Concepts.GradientOracle.DifferenceError
