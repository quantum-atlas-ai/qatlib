/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.TorusMoments.PhasePush
import Qatlib.Papers.AmpInvReqTang26.BiasedFourier.Fourier

/-!
# Pushforward of the finite biased phase law

The expectation identity `actual_muEps_expect` expresses the mixture representation of the phase
law as explicit weights on `Fin q`. It applies to any complex-valued function of the phase and
connects the source law with the biased Fourier weights. This development supports the treatment
in [TangWright2025].

## Main statements

* `actual_omega_pow_card`: the chosen root raised to `q` is one.
* `actual_muEps_expect`: expectation transport to the finite root weights.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.AmpInvReqTang26.RootLaws
open Qatlib.Papers.AmpInvReqTang26.AccessModel
open Qatlib.Foundations.MatrixAlgebra.TorusMoments
set_option warningAsError false

/-- For positive `q`, the chosen root `omega q` has `q`th power one. -/
theorem actual_omega_pow_card (q : ℕ) (hq : 0<q) : omega q^q=1 := by
  have hom : omega q=Complex.exp (2*(Real.pi : ℂ)*Complex.I/(q : ℂ)) := by
    rw [omega]
    congr 1
    rw [Complex.ofReal_div,Complex.ofReal_mul]
    push_cast
    field_simp
  rw [hom]
  exact (Complex.isPrimitiveRoot_exp q hq.ne').pow_eq_one

/-- For `q > 1` and bias in `[0, 1]`, expectation of any function of the mixture phase equals
its sum against the explicit biased root weights [TangWright2025]. -/
theorem actual_muEps_expect (eps : ℝ) (q : ℕ) (hq : 1<q)
    (he0 : 0≤eps) (he1 : eps≤1) (f : ℂ→ℂ) :
    cExpect (muEps eps q (by omega) he0 he1) (fun x=>f (phaseEps q x)) =
      ∑g : Fin q,(BiasedFourier.muEpsWeight eps q g : ℂ)*f (phase q g) := by
  have hw0 : omega q≠0 := by
    intro hz
    have h := norm_omega q
    rw [hz,norm_zero] at h
    exact zero_ne_one h
  have hs := mixturePhase_sum hq (omega q) hw0 (actual_omega_pow_card q (by omega))
    (((1-eps)*(q : ℝ)⁻¹ : ℝ) : ℂ)
    ((eps*(halfCount q : ℝ)⁻¹ : ℝ) : ℂ) f
  unfold cExpect
  rw [Fintype.sum_sum_type]
  simpa only [muEps,phaseEps,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,phase,rightPhase,halfCount,
    BiasedFourier.muEpsWeight,BiasedFourier.isRightHalf,rightArc,Complex.ofReal_add,
    apply_ite Complex.ofReal,Complex.ofReal_zero] using! hs

end Qatlib.Papers.AmpInvReqTang26.RootLaws
