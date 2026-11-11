/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.QaeLaw.FourierLaw
import Qatlib.Papers.MonteCarloInt20.QaeLaw.TrigonometricBias

/-!
# Bias and moment bounds for QAE payoffs

`estimate` is the sine-squared readout and `target` is its ideal amplitude. The module relates
the normalized Fourier-kernel bias to `innerQAEBias`, proves its exact trigonometric form and
`1/M` bound, and controls the second and absolute error moments.

`nonlinear_lipschitz_bound` propagates these estimates through a scaled Lipschitz payoff under
the raw two-branch readout law. See [KanekoEtAl2020].

## Main statements

* `physical_bias_closed` and `physical_bias_bound`: exact bias and its uniform bound.
* `second_moment_bound` and `mean_absolute_bound`: error moment estimates.
* `nonlinear_lipschitz_bound`: Lipschitz payoff error of order `1/√M`.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Qatlib.Papers.MonteCarloInt20.QaeLaw.Fourier
open Qatlib.Papers.MonteCarloInt20.QaeLaw.TrigonometricBias
namespace Qatlib.Papers.MonteCarloInt20.QaeLaw.Payoff

/-- The sine-squared amplitude estimate associated with Fourier outcome `k`. -/
def estimate (M : ℕ) (k : Fin M) : ℝ := Real.sin (k.val/(M:ℝ)*Real.pi)^2

/-- The ideal sine-squared amplitude at phase `θ`. -/
def target (θ : ℝ) : ℝ := Real.sin (θ*Real.pi)^2

/-- The estimate error factors as a product of a sum-angle sine and a phase-difference sine,
with the displayed minus sign. -/
theorem estimate_difference (M : ℕ) (θ : ℝ) (k : Fin M) :
    estimate M k-target θ =
      -Real.sin (k.val/(M:ℝ)*Real.pi+θ*Real.pi)*Real.sin ((θ-k.val/(M:ℝ))*Real.pi) := by
  rw [estimate,target,sin_sq_sub_sin_sq]
  have he : k.val/(M:ℝ)*Real.pi-θ*Real.pi = -((θ-k.val/(M:ℝ))*Real.pi) := by ring
  rw [he,Real.sin_neg]
  ring

/-- The physical phase mass equals the quotient kernel away from singularities and equals one at
singularities. -/
theorem physical_kernel_completion (M : ℕ) (θ : ℝ) (hM : 0 < M) (k : Fin M) :
    phaseMass M θ k = if Real.sin ((k.val/(M:ℝ)-θ)*Real.pi)=0 then 1 else
      qaeQuotient (k.val/(M:ℝ)) θ M := by
  have he : (k.val/(M:ℝ)-θ)*Real.pi = -((θ-k.val/(M:ℝ))*Real.pi) := by ring
  simp only [he,Real.sin_neg,neg_eq_zero]
  split_ifs with hs
  · exact mass_at_singularity M θ hM k hs
  · rw [mass_quotient M θ hM k hs,qaeQuotient_grid θ M hM k.val]
    have hy : Real.pi*((k.val:ℝ)-(M:ℝ)*θ)/(M:ℝ) = -((θ-k.val/(M:ℝ))*Real.pi) := by
      field_simp
      ring
    rw [hy,Real.sin_neg,neg_sq]

/-- Multiplying by the estimate error removes the discrepancy between the completed physical
kernel and the quotient kernel. -/
theorem physical_bias_term (M : ℕ) (θ : ℝ) (hM : 0 < M) (k : Fin M) :
    phaseMass M θ k*(estimate M k-target θ)=
      qaeQuotient (k.val/(M:ℝ)) θ M*(estimate M k-target θ) := by
  by_cases hs : Real.sin ((θ-k.val/(M:ℝ))*Real.pi)=0
  · have hd : estimate M k-target θ=0 := by rw [estimate_difference,hs]; ring
    rw [hd,mul_zero,mul_zero]
  · rw [mass_quotient M θ hM k hs,qaeQuotient_grid θ M hM k.val]
    have he : Real.pi*((k.val:ℝ)-(M:ℝ)*θ)/(M:ℝ) = -((θ-k.val/(M:ℝ))*Real.pi) := by
      field_simp
      ring
    rw [he,Real.sin_neg,neg_sq]

/-- The expected estimate error under the phase law equals `innerQAEBias`. -/
theorem physical_bias_eq_old (M : ℕ) (θ : ℝ) (hM : 0 < M) :
    (∑ k,phaseMass M θ k*(estimate M k-target θ))=innerQAEBias θ M := by
  simp_rw [physical_bias_term M θ hM]
  exact Fin.sum_univ_eq_sum_range (fun k =>
    qaeQuotient ((k:ℝ)/(M:ℝ)) θ M*
      (Real.sin ((k:ℝ)/(M:ℝ)*Real.pi)^2-Real.sin (θ*Real.pi)^2)) M

/-- The physical estimate bias equals `sin (M*θ*π)*sin ((M-2)*θ*π)/M` for positive `M`. See
[KanekoEtAl2020]. -/
theorem physical_bias_closed (M : ℕ) (θ : ℝ) (hM : 0 < M) :
    (∑ k,phaseMass M θ k*(estimate M k-target θ))=
      Real.sin ((M:ℝ)*θ*Real.pi)*Real.sin (((M:ℝ)-2)*θ*Real.pi)/(M:ℝ) := by
  rw [physical_bias_eq_old M θ hM,innerQAEBias_closed θ M hM]

/-- The absolute physical estimate bias is at most `1/M` for positive `M`. See [KanekoEtAl2020]. -/
theorem physical_bias_bound (M : ℕ) (θ : ℝ) (hM : 0 < M) :
    |∑ k,phaseMass M θ k*(estimate M k-target θ)| ≤ 1/(M:ℝ) := by
  rw [physical_bias_closed M θ hM,abs_div,abs_of_pos (by exact_mod_cast hM : (0:ℝ)<M),abs_mul]
  exact div_le_div_of_nonneg_right
    (by nlinarith [Real.abs_sin_le_one ((M:ℝ)*θ*Real.pi),
      Real.abs_sin_le_one (((M:ℝ)-2)*θ*Real.pi),
      abs_nonneg (Real.sin ((M:ℝ)*θ*Real.pi)),
      abs_nonneg (Real.sin (((M:ℝ)-2)*θ*Real.pi))]) (by positivity)

/-- Each phase-mass-weighted squared estimate error is at most `1/M^2`. -/
theorem second_moment_term (M : ℕ) (θ : ℝ) (hM : 0 < M) (k : Fin M) :
    phaseMass M θ k*(estimate M k-target θ)^2 ≤ 1/(M:ℝ)^2 := by
  have hp : 0 ≤ phaseMass M θ k := sq_nonneg _
  have hs := Real.sin_sq_le_one (k.val/(M:ℝ)*Real.pi+θ*Real.pi)
  have hd : (estimate M k-target θ)^2 ≤ Real.sin ((θ-k.val/(M:ℝ))*Real.pi)^2 := by
    rw [estimate_difference,mul_pow,neg_sq]
    exact mul_le_of_le_one_left (sq_nonneg _) hs
  calc
    _ ≤ phaseMass M θ k*Real.sin ((θ-k.val/(M:ℝ))*Real.pi)^2 := mul_le_mul_of_nonneg_left hd hp
    _ ≤ 1/(M:ℝ)^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos (by exact_mod_cast hM : (0:ℝ)<M))).mpr
      have hi := mass_sine_identity M θ hM k
      nlinarith [Real.sin_sq_le_one ((M:ℝ)*θ*Real.pi)]

/-- The expected squared estimate error under the phase law is at most `1/M`. See
[KanekoEtAl2020]. -/
theorem second_moment_bound (M : ℕ) (θ : ℝ) (hM : 0 < M) :
    (∑ k,phaseMass M θ k*(estimate M k-target θ)^2) ≤ 1/(M:ℝ) := by
  calc
    _ ≤ ∑ _k : Fin M,1/(M:ℝ)^2 := Finset.sum_le_sum (fun k _ => second_moment_term M θ hM k)
    _ = 1/(M:ℝ) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp

/-- The expected absolute estimate error under the phase law is at most `√(1/M)`. -/
theorem mean_absolute_bound (M : ℕ) (θ : ℝ) (hM : 0 < M) :
    (∑ k,phaseMass M θ k*|estimate M k-target θ|) ≤ Real.sqrt (1/(M:ℝ)) := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (Fin M))
    (r:=fun k => phaseMass M θ k*|estimate M k-target θ|)
    (f:=phaseMass M θ) (g:=fun k => phaseMass M θ k*(estimate M k-target θ)^2)
    (fun k _ => sq_nonneg _) (fun k _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun k _ => by rw [mul_pow,sq_abs]; exact le_of_eq (by ring))
  rw [phaseMass_sum_one M θ hM,one_mul] at hcs
  have hm := second_moment_bound M θ hM
  have hnn : 0 ≤ ∑ k,phaseMass M θ k*|estimate M k-target θ| :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (sq_nonneg _) (abs_nonneg _))
  have hs := Real.sq_sqrt (show 0 ≤ 1/(M:ℝ) by positivity)
  have hsn := Real.sqrt_nonneg (1/(M:ℝ))
  nlinarith

/-- An `L`-Lipschitz payoff of the scaled readout has raw-law expectation error at most
`L*|D|*√(1/M)`. -/
theorem nonlinear_lipschitz_bound (M : ℕ) (θ D : ℝ) (hM : 0 < M)
    (g : ℝ → ℝ) (L : NNReal) (hg : LipschitzWith L g) :
    |(∑ k,rawMass M θ k*g (D*estimate M k))-g (D*target θ)| ≤
      (L:ℝ)*|D| *Real.sqrt (1/(M:ℝ)) := by
  rw [show (∑ k,rawMass M θ k*g (D*estimate M k))=
    ∑ k,phaseMass M θ k*g (D*estimate M k) from nonlinear_payoff_expectation M θ D hM g]
  have he : (∑ k,phaseMass M θ k*g (D*estimate M k))-g (D*target θ)=
      ∑ k,phaseMass M θ k*(g (D*estimate M k)-g (D*target θ)) := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,phaseMass_sum_one M θ hM,one_mul]
  rw [he]
  calc
    _ ≤ ∑ k,|phaseMass M θ k*(g (D*estimate M k)-g (D*target θ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k,phaseMass M θ k*((L:ℝ)*|D| *|estimate M k-target θ|) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul,abs_of_nonneg (show 0 ≤ phaseMass M θ k from sq_nonneg _)]
      have hl := hg.dist_le_mul (D*estimate M k) (D*target θ)
      rw [Real.dist_eq,Real.dist_eq,← mul_sub,abs_mul] at hl
      exact mul_le_mul_of_nonneg_left (by nlinarith [hl]) (sq_nonneg _)
    _ = (L:ℝ)*|D| *(∑ k,phaseMass M θ k*|estimate M k-target θ|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mean_absolute_bound M θ hM) (mul_nonneg L.coe_nonneg (abs_nonneg D))

end Qatlib.Papers.MonteCarloInt20.QaeLaw.Payoff
