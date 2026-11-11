/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.Quadrature.OrderedUnitaryParameterDerivatives
import Qatlib.Concepts.LchsSimulation.Kernel.NearExponentialLchsKernel
import Qatlib.Concepts.LchsSimulation.TimeLchs
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Derivative and precision budgets for LCHS quadrature

Parameter-derivative bounds for ordered unitary evolution combine with strip analyticity of the
principal-power kernel. The resulting derivative-growth estimate controls high-order LCHS
quadrature, and `composite_gauss_precision_budget` verifies explicit cell and node counts for a
positive target precision. See [AnChildsLin2026] for the mathematical setting.

## Main statements

* `ordered_unitary_k_derivative_bound`: For every natural `q`, the `q`-th parameter derivative
  of the ordered evolution has norm at most `(T * q * Λ)^q` under the stated continuity,
  Hermitian, and generator-bound hypotheses.
* `near_exponential_lchs_integrand_derivative_bound`: For `q ≥ 2` and `32 ≤ exp(1) * T * Λ`, the
  LCHS integrand has `q`-th derivative norm at most `(4 / (3 * highKernelC β)) * q.factorial *
  (q + 1) * (exp(1) * T * Λ)^q` under the stated kernel and generator hypotheses.
* `composite_gauss_precision_budget`: For the stated positive parameters and cutoff, the
  prescribed cell and node counts are positive, the cell width is at most `1 / (exp(1) * T *
  Λ)`, and the composite Gauss error budget is at most `ε`.

## References

* [An, Childs, and Lin, 2026][AnChildsLin2026]
-/


open Qatlib.Concepts.LchsSimulation.TimeLchs
open Qatlib.Concepts.LchsSimulation.Kernel
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

namespace Qatlib.Concepts.LchsSimulation.Quadrature

open Polynomial Set Metric
open scoped Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false

/-- For derivative orders `q ≤ 1`, the parameter-dependent ordered evolution has derivative norm
at most `(T * q * Λ)^q` under the stated continuity, Hermitian, and generator-bound
hypotheses. -/
theorem ordered_unitary_k_derivative_bound_le_one
    (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ → Matrix I I ℂ) (T Λ : ℝ)
    (hL : Continuous L) (hH : Continuous H)
    (hHermL : ∀ u, (L u).IsHermitian) (hHermH : ∀ u, (H u).IsHermitian)
    (hT : 0 ≤ T) (hΛ : 0 < Λ) (hbound : ∀ u ∈ Icc 0 T, ‖L u‖ ≤ Λ) :
    ∀ q : ℕ, q ≤ 1 → ∀ k : ℝ,
      ‖iteratedDeriv q (fun k : ℝ => orderedEvolution
        (fun u => Complex.I • (H u + k • L u)) 0 T) k‖ ≤ (T * (q : ℝ) * Λ) ^ q := by
  let U := fun k : ℝ => orderedEvolution (fun u => Complex.I • (H u + k • L u)) 0 T
  have hint : (∫ u in (0 : ℝ)..T, ‖L u‖) ≤ T * Λ := by
    calc
      _ ≤ ∫ u in (0 : ℝ)..T, Λ := intervalIntegral.integral_mono_on hT
        (hL.norm.intervalIntegrable 0 T) (continuous_const.intervalIntegrable 0 T) hbound
      _ = _ := by simp
  have hLip : LipschitzWith ⟨T * Λ, mul_nonneg hT hΛ.le⟩ U :=
    LipschitzWith.of_dist_le_mul (fun a b => by
      have h := time_dependent_lchs_same_unitary_stability I L H 0 T a b
        hL hH hHermL hHermH hT
      have hh := h.trans (mul_le_mul_of_nonneg_left hint (abs_nonneg _))
      rw [dist_eq_norm, dist_eq_norm]
      change ‖U a - U b‖ ≤ (T * Λ) * ‖a - b‖
      rw [Real.norm_eq_abs]
      exact hh.trans_eq (mul_comm _ _))
  intro q hq k
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with rfl | rfl
  · simpa only [iteratedDeriv_zero, pow_zero] using! l2_norm_unitary_le_one
      (ordered_evolution_hermitian_unitary I (fun u => H u + k • L u)
        (hH.add (hL.const_smul k))
        (fun u => (hHermH u).add ((hHermL u).smul (R := ℝ) (IsSelfAdjoint.all k))) 0 T)
  · simpa only [iteratedDeriv_one, Nat.cast_one, mul_one, pow_one, U, NNReal.coe_mk] using!
      (norm_deriv_le_of_lipschitz hLip (x₀ := k))

/-- For every natural `n`, `(n + 1).factorial ≤ (n + 1)^n`. -/
private theorem factorial_succ_le_pow (n : ℕ) : (n+1).factorial≤(n+1)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    calc (n+1+1).factorial=(n+1+1)*(n+1).factorial := Nat.factorial_succ _
         _≤(n+1+1)*(n+1)^n := Nat.mul_le_mul_left _ ih
         _≤(n+1+1)*(n+1+1)^n := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) n)
         _=(n+1+1)^(n+1) := by rw [pow_succ,Nat.mul_comm]

/-- For every natural `q`, the `q`-th parameter derivative of the ordered evolution has norm at
most `(T * q * Λ)^q` under the stated continuity, Hermitian, and generator-bound hypotheses. -/
theorem ordered_unitary_k_derivative_bound
    (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ→Matrix I I ℂ) (T Λ : ℝ)
    (hL : Continuous L) (hH : Continuous H) (hHermL : ∀ u,(L u).IsHermitian)
    (hHermH : ∀ u,(H u).IsHermitian) (hT : 0≤T) (hΛ : 0<Λ)
    (hbound : ∀ u∈Icc 0 T,‖L u‖≤Λ) (q : ℕ) (k : ℝ) :
    ‖iteratedDeriv q (fun x : ℝ=>orderedEvolution (fun u=>Complex.I • (H u+x • L u)) 0 T) k‖≤
      (T*(q:ℝ)*Λ)^q := by
  by_cases hq : q≤1
  · exact ordered_unitary_k_derivative_bound_le_one I L H T Λ hL hH hHermL hHermH hT hΛ hbound q hq k
  have hq2 : 2≤q := by omega
  by_cases hT0 : T=0
  · subst T
    simp [iteratedDeriv_const,show q≠0 by omega]
  have hx : 0<T*Λ := mul_pos (lt_of_le_of_ne hT (Ne.symm hT0)) hΛ
  rcases Nat.eq_or_lt_of_le hq2 with rfl | hq3
  · have hh := ordered_unitary_k_derivative_cauchy I L H T Λ hL hH hHermL hHermH hT hΛ hbound 2 k
      (2/(T*Λ)) (by positivity)
    have hR : (2/(T*Λ))*T*Λ=2 := by field_simp
    rw [hR] at hh
    have he : Real.exp 2≤8 := by
      rw [show (2:ℝ)=1+1 by ring,Real.exp_add]
      nlinarith [Real.exp_one_lt_d9,Real.exp_pos 1]
    have hm := mul_le_mul_of_nonneg_right he (sq_nonneg (T*Λ))
    have hid : (2:ℝ)*Real.exp 2/(2/(T*Λ))^2=(Real.exp 2/2)*(T*Λ)^2 := by field_simp
    have hr : (2:ℝ)*Real.exp 2/(2/(T*Λ))^2≤(T*2*Λ)^2 := by
      rw [hid]
      nlinarith [hm]
    apply le_trans _ hr
    simpa only [Nat.factorial_two,Nat.cast_ofNat] using! hh
  · have hh := ordered_unitary_k_derivative_cauchy I L H T Λ hL hH hHermL hHermH hT hΛ hbound q k
      (1/(T*Λ)) (by positivity)
    have hR : (1/(T*Λ))*T*Λ=1 := by field_simp
    rw [hR,one_div,inv_pow,div_inv_eq_mul] at hh
    have hfNat : q.factorial≤q^(q-1) := by
      cases q with
      | zero => omega
      | succ n => simpa only [Nat.add_sub_cancel] using! factorial_succ_le_pow n
    have hf : (q.factorial:ℝ)≤(q:ℝ)^(q-1) := by exact_mod_cast hfNat
    have he : Real.exp 1≤(q:ℝ) := by
      have hc : (3:ℝ)≤q := by exact_mod_cast (show 3≤q by omega)
      exact Real.exp_one_lt_three.le.trans hc
    have hfac : (q.factorial:ℝ)*Real.exp 1≤(q:ℝ)^q := by
      calc _≤(q:ℝ)^(q-1)*(q:ℝ) := mul_le_mul hf he (Real.exp_pos _).le (by positivity)
           _=(q:ℝ)^q := by rw [← pow_succ,Nat.sub_add_cancel (by omega : 1≤q)]
    calc _≤(q.factorial:ℝ)*Real.exp 1*(T*Λ)^q := hh
         _≤(q:ℝ)^q*(T*Λ)^q := mul_le_mul_of_nonneg_right hfac (by positivity)
         _=(T*(q:ℝ)*Λ)^q := by rw [← mul_pow];congr 1;ring

/-- The complex extension of the Cauchy-weighted principal-power kernel `highKernelF β z / (1 -
Complex.I * z)`. -/
private noncomputable def complexHighKernelG (β : ℝ) (z : ℂ) : ℂ :=
  highKernelF β z / (1 - Complex.I * z)

/-- The extension `complexHighKernelG β` is analytic at every point with `|z.im| ≤ 1 / 4`. -/
private theorem complexHighKernelG_analytic (β : ℝ) (z : ℂ)
    (hz : |z.im| ≤ 1 / 4) : AnalyticAt ℂ (complexHighKernelG β) z := by
  have hpos : 0 < (1 + Complex.I * z).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, zero_sub]
    linarith [(abs_le.mp hz).2]
  have hden : (1 : ℂ) - Complex.I * z ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, zero_sub, Complex.zero_re] at he
    linarith [(abs_le.mp hz).1]
  have ha : AnalyticAt ℂ (fun w : ℂ => 1 + Complex.I * w) z :=
    analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  exact ((((ha.cpow analyticAt_const (Or.inl hpos)).neg.cexp).div
    analyticAt_const (by exact_mod_cast highKernelC_ne_zero β)).div
      (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) hden)

/-- For `0 < β < 1` and `|z.im| ≤ 1 / 4`, the complex kernel norm is at most `4 / (3 *
highKernelC β)`. -/
private theorem complexHighKernelG_norm (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1)
    (z : ℂ) (hz : |z.im| ≤ 1 / 4) :
    ‖complexHighKernelG β z‖ ≤ 4 / (3 * highKernelC β) := by
  have hre : 0 ≤ (1 + Complex.I * z).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, zero_sub]
    linarith [(abs_le.mp hz).2]
  have hpow := highKernel_cpow_re_lower β hβ hβ1 (1 + Complex.I * z) hre
  have hcos := highKernel_cos_pos β hβ hβ1
  have hnonneg : 0 ≤ (Complex.cpow (1 + Complex.I * z) (β : ℂ)).re :=
    (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) β) hcos.le).trans hpow
  have hnum : ‖highKernelF β z‖ ≤ 1 / highKernelC β := by
    rw [highKernelF, norm_div, Complex.norm_exp, Complex.neg_re,
      Complex.norm_real, Real.norm_of_nonneg (highKernelC_pos β).le]
    exact div_le_div_of_nonneg_right (Real.exp_le_one_iff.mpr (by linarith)) (highKernelC_pos β).le
  have hden : (3 / 4 : ℝ) ≤ ‖(1 : ℂ) - Complex.I * z‖ := by
    have hr := Complex.re_le_norm ((1 : ℂ) - Complex.I * z)
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, zero_sub] at hr
    linarith [(abs_le.mp hz).1]
  calc
    _ = ‖highKernelF β z‖ / ‖(1 : ℂ) - Complex.I * z‖ := norm_div _ _
    _ ≤ (1 / highKernelC β) / (3 / 4 : ℝ) :=
      div_le_div₀ (by have hC := highKernelC_pos β; positivity) hnum (by norm_num) hden
    _ = _ := by ring

/-- Every iterated real derivative of `highKernelG β` equals the corresponding iterated complex
derivative of `complexHighKernelG β` at the real input. -/
private theorem kernel_iteratedDeriv_real_complex (β : ℝ) :
    ∀ q : ℕ, ∀ k : ℝ, iteratedDeriv q (highKernelG β) k =
      iteratedDeriv q (complexHighKernelG β) (k : ℂ) := by
  intro q
  induction q with
  | zero => intro k; rfl
  | succ q ih =>
    intro k
    have he : iteratedDeriv q (highKernelG β) =
        fun x : ℝ => iteratedDeriv q (complexHighKernelG β) (x : ℂ) := funext ih
    have ha := (complexHighKernelG_analytic β (k : ℂ) (by simp)).iterated_deriv q
    have hd := ha.differentiableAt.hasDerivAt.comp_ofReal
    simp only [iteratedDeriv_succ, he]
    simpa only [iteratedDeriv_eq_iterate] using! hd.deriv

/-- For `0 < β < 1` and positive `q`, the `q`-th derivative of `highKernelG β` has norm at most
`(4 / (3 * highKernelC β)) * 4^q * q.factorial`. -/
theorem highKernelG_deriv_le :
    ∀ β : ℝ, 0 < β → β < 1 →
      ∀ q : ℕ, 1 ≤ q → ∀ k : ℝ,
        ‖iteratedDeriv q (highKernelG β) k‖ ≤
          (4 / (3 * highKernelC β)) * (4 : ℝ) ^ q * (q.factorial : ℝ) := by
  intro β hβ hβ1 q _ k
  have him (z : ℂ) (hz : z ∈ closedBall (k : ℂ) (1 / 4)) : |z.im| ≤ 1 / 4 := by
    have h := (Complex.abs_im_le_norm (z - (k : ℂ))).trans (mem_closedBall_iff_norm.mp hz)
    simpa using! h
  have hd : DiffContOnCl ℂ (complexHighKernelG β) (ball (k : ℂ) (1 / 4)) :=
    DiffContOnCl.mk_ball
      (fun z hz => (complexHighKernelG_analytic β z (him z (ball_subset_closedBall hz))).differentiableAt.differentiableWithinAt)
      (fun z hz => (complexHighKernelG_analytic β z (him z hz)).continuousAt.continuousWithinAt)
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le q
    (by norm_num : (0 : ℝ) < 1 / 4) hd
    (fun z hz => complexHighKernelG_norm β hβ hβ1 z (him z (sphere_subset_closedBall hz)))
  rw [kernel_iteratedDeriv_real_complex]
  exact hc.trans_eq (by rw [div_pow, one_pow, div_div_eq_mul_div, div_one]; ring)

/-- For `q ≥ 2` and `32 ≤ exp(1) * T * Λ`, the LCHS integrand has `q`-th derivative norm at most
`(4 / (3 * highKernelC β)) * q.factorial * (q + 1) * (exp(1) * T * Λ)^q` under the stated
kernel and generator hypotheses. -/
theorem near_exponential_lchs_integrand_derivative_bound
    (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ→Matrix I I ℂ) (T β Λ : ℝ)
    (hL : Continuous L) (hH : Continuous H) (hHermL : ∀ u,(L u).IsHermitian)
    (hHermH : ∀ u,(H u).IsHermitian) (hT : 0≤T) (hΛ : 0<Λ)
    (hlarge : 32≤Real.exp 1*T*Λ) (hβ : 0<β) (hβ1 : β<1)
    (hbound : ∀ u∈Icc 0 T,‖L u‖≤Λ) (q : ℕ) (hq : 2≤q) (k : ℝ) :
    ‖iteratedDeriv q (fun x : ℝ=>highKernelG β x •
      orderedEvolution (fun u=>Complex.I • (H u+x • L u)) 0 T) k‖≤
      (4/(3*highKernelC β))*(q.factorial:ℝ)*(q+1:ℕ)*(Real.exp 1*T*Λ)^q := by
  let X := T*Λ
  have hX0 : 0≤X := mul_nonneg hT hΛ.le
  have hXe : 32≤Real.exp 1*X := by simpa only [X,mul_assoc] using! hlarge
  have hX4 : 4≤X := by
    have hh := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le hX0
    nlinarith
  have hX : 0<X := by linarith
  let R := 1/X
  have hR : 0<R := by dsimp [R];positivity
  have hR4 : R≤1/4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hX4
  let V := fun z : ℂ=>orderedEvolution (fun u=>Complex.I • (H u+z • L u)) 0 T
  let W := fun z : ℂ=>complexHighKernelG β z • V z
  have hV : Differentiable ℂ V := ordered_unitary_complex_parameter_entire I L H hL hH 0 T
  have ha (z : ℂ) (hz : |z.im|≤1/4) : AnalyticAt ℂ W z :=
    (complexHighKernelG_analytic β z hz).smul (hV.analyticAt z)
  have he : (fun x : ℝ=>highKernelG β x • orderedEvolution (fun u=>Complex.I • (H u+x • L u)) 0 T)=
      fun x : ℝ=>W (x:ℂ) := by
    funext x
    simp only [W,V,complexHighKernelG,highKernelG,Complex.coe_smul]
  have hder : ∀ n : ℕ,∀ x : ℝ,iteratedDeriv n (fun x : ℝ=>W (x:ℂ)) x=iteratedDeriv n W (x:ℂ) := by
    intro n
    induction n with
    | zero => intro x;rfl
    | succ n ih =>
      intro x
      have heq :
          iteratedDeriv n (fun y : ℝ=>W (y:ℂ))=fun y : ℝ=>iteratedDeriv n W (y:ℂ) := funext ih
      have han := (ha (x:ℂ) (by simp)).iterated_deriv n
      have hd :=
          (han.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt x Complex.ofRealCLM.hasDerivAt
      simp only [ContinuousLinearMap.coe_restrictScalars',Complex.ofRealCLM_apply,ContinuousLinearMap.toSpanSingleton_apply,Complex.ofReal_one,one_smul] at hd
      simp only [iteratedDeriv_succ,heq]
      simpa only [iteratedDeriv_eq_iterate,Function.comp_def] using! hd.deriv
  have him (z : ℂ) (hz : z∈closedBall (k:ℂ) R) : |z.im|≤R := by
    have hh := (Complex.abs_im_le_norm (z-(k:ℂ))).trans (mem_closedBall_iff_norm.mp hz)
    simpa using! hh
  have hdc : DiffContOnCl ℂ W (ball (k:ℂ) R) := DiffContOnCl.mk_ball
    (fun z hz=>(ha z ((him z (ball_subset_closedBall hz)).trans hR4)).differentiableAt.differentiableWithinAt)
    (fun z hz=>(ha z ((him z hz).trans hR4)).continuousAt.continuousWithinAt)
  have hb (z : ℂ) (hz : z∈sphere (k:ℂ) R) : ‖W z‖≤(4/(3*highKernelC β))*Real.exp 1 := by
    have hi := him z (sphere_subset_closedBall hz)
    have hU : ‖V z‖≤Real.exp 1 := by
      apply (ordered_unitary_complex_parameter_growth I L H T Λ hL hH hHermL hHermH hT hΛ hbound z).trans
      apply Real.exp_le_exp.mpr
      calc _≤R*T*Λ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi hT) hΛ.le
           _=1 := by
             dsimp only [R]
             rw [mul_assoc]
             change (1/X)*X=1
             exact one_div_mul_cancel hX.ne'
    dsimp only [W]
    rw [norm_smul]
    exact mul_le_mul (complexHighKernelG_norm β hβ hβ1 z (hi.trans hR4)) hU (norm_nonneg _)
        (by have hc:=highKernelC_pos β;positivity)
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le q hR hdc hb
  rw [he,hder]
  have hC : 0≤4/(3*highKernelC β) := by have hc:=highKernelC_pos β;positivity
  have heq : Real.exp 1≤(q+1:ℕ) := by
    have hn : (3:ℝ)≤(q+1:ℕ) := by exact_mod_cast (show 3≤q+1 by omega)
    exact Real.exp_one_lt_three.le.trans hn
  have hpow : X^q≤(Real.exp 1*X)^q := by
    gcongr
    exact le_mul_of_one_le_left hX0 (Real.one_le_exp (by norm_num))
  have hprod := mul_le_mul heq hpow (pow_nonneg hX0 _) (by positivity : (0:ℝ)≤(q+1:ℕ))
  calc _≤(q.factorial:ℝ)*((4/(3*highKernelC β))*Real.exp 1)*X^q := by
           simpa only [R,one_div,inv_pow,div_inv_eq_mul] using! hc
       _≤(4/(3*highKernelC β))*(q.factorial:ℝ)*(q+1:ℕ)*(Real.exp 1*X)^q := by
           have hh :=
               mul_le_mul_of_nonneg_left hprod (mul_nonneg hC (by positivity : (0:ℝ)≤q.factorial))
           nlinarith [hh]
       _=(4/(3*highKernelC β))*(q.factorial:ℝ)*(q+1:ℕ)*(Real.exp 1*T*Λ)^q := by simp only [X,mul_assoc]

/-- For the stated positive parameters and cutoff, the prescribed cell and node counts are
positive, the cell width is at most `1 / (exp(1) * T * Λ)`, and the composite Gauss error
budget is at most `ε`. -/
theorem composite_gauss_precision_budget :
    ∀ β T Λ ε : ℝ, 0 < β → β < 1 → 0 < T → 0 < Λ → 0 < ε →
      ∀ K : ℕ, 0 < K →
        let M := Nat.ceil (2 * K * Real.exp 1 * T * Λ)
        let Q := max 1 (Nat.ceil (Real.log ((8 / (3 * highKernelC β)) * K / ε) / Real.log 4))
        (0 : ℝ) < M ∧ 0 < Q ∧
          (2 * K : ℝ) / M ≤ 1 / (Real.exp 1 * T * Λ) ∧
          (8 / (3 * highKernelC β)) * K *
              ((2 * K : ℝ) / M) ^ ((2 : ℝ) * Q) *
              (Real.exp 1 * T * Λ / 2) ^ ((2 : ℝ) * Q) ≤ ε := by
  intro β T Λ ε _ _ hT hΛ hε K hK
  (try dsimp only)
  let M := Nat.ceil (2 * K * Real.exp 1 * T * Λ)
  let A := (8 / (3 * highKernelC β)) * K
  let Q := max 1 (Nat.ceil (Real.log (A / ε) / Real.log 4))
  let v := Real.exp 1 * T * Λ
  let h : ℝ := (2 * K : ℝ) / M
  have hv : 0 < v := by dsimp [v]; positivity
  have hA : 0 < A := by dsimp [A]; have hC := highKernelC_pos β; positivity
  have hMnat : 0 < M := Nat.ceil_pos.mpr (by positivity)
  have hM : (0 : ℝ) < M := by exact_mod_cast hMnat
  have hQ : 0 < Q := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hceil : (2 * K : ℝ) * v ≤ M := by
    simpa only [M, v, mul_assoc] using! Nat.le_ceil (2 * K * Real.exp 1 * T * Λ)
  have hh : h * v ≤ 1 := by
    dsimp [h]
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hM).mpr (by simpa using! hceil)
  have hstep : h ≤ 1 / v := (le_div_iff₀ hv).mpr (by simpa using! hh)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hQlog : Real.log (A / ε) / Real.log 4 ≤ Q :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 (Nat.ceil (Real.log (A / ε) / Real.log 4)))
  have hAeps : A / ε ≤ (4 : ℝ) ^ Q := by
    have he := Real.exp_le_exp.mpr ((div_le_iff₀ hlog4).mp hQlog)
    simpa only [Real.exp_log (div_pos hA hε), Real.rpow_natCast,
      ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), mul_comm] using! he
  have hp : A / (4 : ℝ) ^ Q ≤ ε :=
    (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 4) Q)).mpr
      (by nlinarith [(div_le_iff₀ hε).mp hAeps])
  refine ⟨hM, hQ, hstep, ?_⟩
  change A * h ^ ((2 : ℝ) * Q) * (v / 2) ^ ((2 : ℝ) * Q) ≤ ε
  have hexp : (2 : ℝ) * Q = ((2 * Q : ℕ) : ℝ) := by simp
  rw [hexp, Real.rpow_natCast, Real.rpow_natCast]
  calc
    A * h ^ (2 * Q) * (v / 2) ^ (2 * Q) = A * (h * v / 2) ^ (2 * Q) := by
      rw [show h * v / 2 = h * (v / 2) by ring, mul_pow]
      ring
    _ ≤ A * (1 / 2 : ℝ) ^ (2 * Q) := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by dsimp [h]; positivity) (by linarith) _) hA.le
    _ = A / (4 : ℝ) ^ Q := by
      rw [pow_mul]
      norm_num
      rw [div_pow, one_pow, div_eq_mul_inv]
      ring
    _ ≤ ε := hp

end Qatlib.Concepts.LchsSimulation.Quadrature
