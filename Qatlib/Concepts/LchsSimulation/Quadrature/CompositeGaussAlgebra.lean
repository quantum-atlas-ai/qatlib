/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.Quadrature.NearExponentialKernelQuadrature
import Mathlib.Data.Nat.Choose.Central
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace Qatlib.Concepts.LchsSimulation.Quadrature

private theorem two_pow_le_central_binom (n : ℕ) : 2^n≤Nat.centralBinom n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr := Nat.succ_mul_centralBinom_succ n
    have hm : (n+1)*(2*Nat.centralBinom n)≤(n+1)*Nat.centralBinom (n+1) := by nlinarith
    have hs : 2*Nat.centralBinom n≤Nat.centralBinom (n+1) :=
        (mul_le_mul_iff_left₀ (Nat.succ_pos n)).mp (by simpa only [Nat.mul_comm] using! hm)
    calc 2^(n+1)=2*2^n := by rw [pow_succ,Nat.mul_comm]
         _≤2*Nat.centralBinom n := Nat.mul_le_mul_left _ ih
         _≤_ := hs

theorem gauss_factorial_ratio_le (Q : ℕ) :
    (Q.factorial:ℝ)^4/((2*Q).factorial:ℝ)^2≤1/(2:ℝ)^(2*Q) := by
  have heNat : (2*Q).factorial=Nat.centralBinom Q*Q.factorial*Q.factorial := by
    simpa only [Nat.centralBinom,two_mul] using!
        (Nat.add_choose_mul_factorial_mul_factorial Q Q).symm
  have he : ((2*Q).factorial:ℝ)=(Nat.centralBinom Q:ℝ)*(Q.factorial:ℝ)^2 := by
    exact_mod_cast (by simpa only [pow_two,mul_assoc] using! heNat)
  have hcb : (2:ℝ)^Q≤(Nat.centralBinom Q:ℝ) := by exact_mod_cast two_pow_le_central_binom Q
  have hq0 : (Q.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero Q
  have hc0 : (Nat.centralBinom Q:ℝ)≠0 := by exact_mod_cast Nat.centralBinom_ne_zero Q
  have hr : (Q.factorial:ℝ)^4/((2*Q).factorial:ℝ)^2=1/(Nat.centralBinom Q:ℝ)^2 := by
    rw [he]
    field_simp
  rw [hr,show (2:ℝ)^(2*Q)=((2:ℝ)^Q)^2 by rw [← pow_mul];congr 1;omega]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith [hcb,pow_pos (by norm_num : (0:ℝ)<2) Q]

theorem gauss_cell_budget_le (Q : ℕ) (C h B : ℝ) (hC : 0≤C) (hh : 0≤h) (hB : 0≤B) :
    ((Q.factorial:ℝ)^4*h^(2*Q+1))/((2*Q+1:ℕ)*((2*Q).factorial:ℝ)^3)*
      (C*((2*Q).factorial:ℝ)*(2*Q+1:ℕ)*B^(2*Q))≤C*h^(2*Q+1)*(B/2)^(2*Q) := by
  have hf0 : ((2*Q).factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (2*Q)
  have hn0 : (2*Q+1:ℕ)≠(0:ℝ) := by positivity
  have hr : ((Q.factorial:ℝ)^4*h^(2*Q+1))/((2*Q+1:ℕ)*((2*Q).factorial:ℝ)^3)*
      (C*((2*Q).factorial:ℝ)*(2*Q+1:ℕ)*B^(2*Q))=
      C*h^(2*Q+1)*B^(2*Q)*((Q.factorial:ℝ)^4/((2*Q).factorial:ℝ)^2) := by
    field_simp
  rw [hr]
  calc _≤C*h^(2*Q+1)*B^(2*Q)*(1/(2:ℝ)^(2*Q)) :=
         mul_le_mul_of_nonneg_left (gauss_factorial_ratio_le Q) (by positivity)
       _=C*h^(2*Q+1)*(B/2)^(2*Q) := by rw [div_pow];ring
end Qatlib.Concepts.LchsSimulation.Quadrature
