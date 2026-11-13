/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.KTrapezoid.TrapezoidQuadrature

/-!
# Derivative and mass bounds for trapezoidal sources

`inh_trap_source_derivatives` gives first and second derivatives of the source propagated to a
fixed final time and bounds the second derivative using generator and source data.
`inh_trap_source_mass_quadrature` bounds the trapezoidal sum of source norms by their time
integral plus a derivative-controlled correction.

The mathematical background is described in [AnLiuLin2023].

## Main statements

* `inh_trap_source_derivatives`: constructs the propagated-source derivatives and
  second-derivative bound.
* `inh_trap_source_mass_quadrature`: controls the weighted source mass.

## References

* [An et al., 2023][AnLiuLin2023]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LchsSimulation.InhomLeftGrid
open Qatlib.Concepts.LchsSimulation.KTrapezoid
open Qatlib.Concepts.LchsSimulation.TimeLchs
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.LchsSimulation.TimeTrapezoid
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The real continuous linear identification of finite complex state vectors with Euclidean
space. -/
private def inhEuclideanMap : QState I →L[ℝ] EuclideanSpace ℂ I :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℂ)).symm.toContinuousLinearMap

omit [DecidableEq I] in

/-- The derivative of a matrix-vector product is `M' *ᵥ v u + M u *ᵥ v'`. -/
private theorem inh_mulVec_deriv {M : ℝ → Matrix I I ℂ} {v : ℝ → QState I}
    {M' : Matrix I I ℂ} {v' : QState I} {u : ℝ}
    (hM : HasDerivAt M M' u) (hv : HasDerivAt v v' u) :
    HasDerivAt (fun z => M z *ᵥ v z) (M' *ᵥ v u+M u *ᵥ v') u := by
  apply hasDerivAt_pi.mpr
  intro i
  have hm (j : I) := hasDerivAt_pi.mp (hasDerivAt_pi.mp hM i) j
  have hvj (j : I) := hasDerivAt_pi.mp hv j
  simpa [Matrix.mulVec, dotProduct, Finset.sum_add_distrib] using!
    HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) => (hm j).mul (hvj j))

omit [DecidableEq I] in

/-- A source derivative bounded in Euclidean norm by `β` on a segment makes the Euclidean source
representation `β`-Lipschitz there. -/
private theorem inh_derivative_lipschitz (b b' : ℝ → QState I) (s t β : ℝ)
    (hd : ∀ u, s ≤ u → u ≤ t → HasDerivAt b (b' u) u)
    (hn : ∀ u, s ≤ u → u ≤ t → ‖toEuclidean_fromVec (b' u)‖ ≤ β) :
    ∀ a ∈ Set.Icc s t, ∀ z ∈ Set.Icc s t,
      ‖toEuclidean_fromVec (b a)-toEuclidean_fromVec (b z)‖ ≤ β*|a-z| := by
  have he (u : ℝ) (hu : u ∈ Set.Icc s t) :
      HasDerivAt (fun z => toEuclidean_fromVec (b z)) (toEuclidean_fromVec (b' u)) u :=
    (inhEuclideanMap (I := I)).hasFDerivAt.comp_hasDerivAt u (hd u hu.1 hu.2)
  intro a ha z hz
  have hl := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun u hu => (he u hu).differentiableAt)
    (fun u hu => by rw [(he u hu).deriv]; exact hn u hu.1 hu.2)
    (convex_Icc s t) hz ha
  simpa only [Real.norm_eq_abs] using! hl

/-- The propagated source has two derivatives on the segment, with second-derivative norm
bounded by `((lamL + lamH) ^ 2 + lamLd + lamHd) * bmax + 2 * (lamL + lamH) * β + β₂`. -/
theorem inh_trap_source_derivatives
    (L L' H H' : ℝ → Matrix I I ℂ) (b b' b'' : ℝ → QState I)
    (s t β β₂ lamL lamH lamLd lamHd bmax : ℝ)
    (hL : Continuous L) (hH : Continuous H)
    (hPSD : ∀ u, (L u).PosSemidef) (hHerm : ∀ u, (H u).IsHermitian)
    (hdL : ∀ u ∈ Set.Icc s t, HasDerivAt L (L' u) u)
    (hdH : ∀ u ∈ Set.Icc s t, HasDerivAt H (H' u) u)
    (hnLd : ∀ u ∈ Set.Icc s t, ‖L' u‖ ≤ lamLd)
    (hnHd : ∀ u ∈ Set.Icc s t, ‖H' u‖ ≤ lamHd)
    (hdb : ∀ u ∈ Set.Icc s t, HasDerivAt b (b' u) u)
    (hdb' : ∀ u ∈ Set.Icc s t, HasDerivAt b' (b'' u) u)
    (hβ : ∀ u ∈ Set.Icc s t, ‖toEuclidean_fromVec (b' u)‖ ≤ β)
    (hβ₂ : ∀ u ∈ Set.Icc s t, ‖toEuclidean_fromVec (b'' u)‖ ≤ β₂)
    (hbmax : ∀ u ∈ Set.Icc s t, ‖toEuclidean_fromVec (b u)‖ ≤ bmax)
    (hlL : ∀ u, ‖L u‖ ≤ lamL) (hlH : ∀ u, ‖H u‖ ≤ lamH) :
    ∃ F' F'' : ℝ → EuclideanSpace ℂ I,
      (∀ u ∈ Set.Icc s t, HasDerivAt
        (fun v => toEuclidean_fromVec (orderedEvolution (fun y => L y+Complex.I • H y) v t *ᵥ b v)) (F' u) u) ∧
      (∀ u ∈ Set.Icc s t, HasDerivAt F' (F'' u) u) ∧
      (∀ u ∈ Set.Icc s t, ‖F'' u‖ ≤
        ((lamL+lamH)^2+(lamLd+lamHd))*bmax+2*(lamL+lamH)*β+β₂) := by
  let A := fun u => L u+Complex.I • H u
  let Ad := fun u => L' u+Complex.I • H' u
  have hA : Continuous A := by dsimp [A]; fun_prop
  let V := fun u => orderedEvolution A u t
  let Vp := fun u => V u*A u
  let vp := fun u => Vp u *ᵥ b u+V u *ᵥ b' u
  let vpp := fun u => (Vp u*A u+V u*Ad u) *ᵥ b u+Vp u *ᵥ b' u+
    (Vp u *ᵥ b' u+V u *ᵥ b'' u)
  have hDV (u : ℝ) : HasDerivAt V (Vp u) u := orderedEvolution_hasDerivAt_start A hA t u
  have hDA (u : ℝ) (hu : u ∈ Set.Icc s t) : HasDerivAt A (Ad u) u := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    have hl := hasDerivAt_pi.mp (hasDerivAt_pi.mp (hdL u hu) i) j
    have hh := hasDerivAt_pi.mp (hasDerivAt_pi.mp (hdH u hu) i) j
    simpa [A, Ad, Matrix.smul_apply, smul_eq_mul] using! hl.add (hh.const_mul Complex.I)
  have hDVp (u : ℝ) (hu : u ∈ Set.Icc s t) :
      HasDerivAt Vp (Vp u*A u+V u*Ad u) u := (hDV u).mul (hDA u hu)
  have hdv (u : ℝ) (hu : u ∈ Set.Icc s t) :
      HasDerivAt (fun v => V v *ᵥ b v) (vp u) u := inh_mulVec_deriv (hDV u) (hdb u hu)
  have hdvp (u : ℝ) (hu : u ∈ Set.Icc s t) : HasDerivAt vp (vpp u) u :=
    (inh_mulVec_deriv (hDVp u hu) (hdb u hu)).add (inh_mulVec_deriv (hDV u) (hdb' u hu))
  refine ⟨fun u => toEuclidean_fromVec (vp u), fun u => toEuclidean_fromVec (vpp u), ?_, ?_, ?_⟩
  · intro u hu
    exact inhEuclideanMap.hasFDerivAt.comp_hasDerivAt u (hdv u hu)
  · intro u hu
    exact inhEuclideanMap.hasFDerivAt.comp_hasDerivAt u (hdvp u hu)
  · intro u hu
    have hVn : ‖V u‖ ≤ 1 := by
      simpa only [one_smul] using!
        (time_dependent_lchs_entire_parameter I L H u t hL hH hPSD hHerm hu.2).2 1 (by simp)
    have hAn : ‖A u‖ ≤ lamL+lamH := by
      calc
        _ ≤ ‖L u‖+‖Complex.I • H u‖ := norm_add_le _ _
        _ = ‖L u‖+‖H u‖ := by rw [norm_smul, Complex.norm_I, one_mul]
        _ ≤ _ := add_le_add (hlL u) (hlH u)
    have hAdn : ‖Ad u‖ ≤ lamLd+lamHd := by
      calc
        _ ≤ ‖L' u‖+‖Complex.I • H' u‖ := norm_add_le _ _
        _ = ‖L' u‖+‖H' u‖ := by rw [norm_smul, Complex.norm_I, one_mul]
        _ ≤ _ := add_le_add (hnLd u hu) (hnHd u hu)
    have hα : 0 ≤ lamL+lamH := (norm_nonneg _).trans hAn
    have hαd : 0 ≤ lamLd+lamHd := (norm_nonneg _).trans hAdn
    have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ u hu)
    have hb0 : 0 ≤ bmax := (norm_nonneg _).trans (hbmax u hu)
    have hVp : ‖Vp u‖ ≤ lamL+lamH :=
      (norm_mul_le _ _).trans ((mul_le_mul hVn hAn (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
    have hVpp : ‖Vp u*A u+V u*Ad u‖ ≤ (lamL+lamH)^2+(lamLd+lamHd) := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · exact (norm_mul_le _ _).trans
          ((mul_le_mul hVp hAn (norm_nonneg _) hα).trans_eq (pow_two _).symm)
      · exact (norm_mul_le _ _).trans
          ((mul_le_mul hVn hAdn (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
    have ht0 : 0 ≤ (lamL+lamH)^2+(lamLd+lamHd) := by positivity
    have hn0 := (l2_norm_mulVec_fromVec_le (Vp u*A u+V u*Ad u) (b u)).trans
      (mul_le_mul hVpp (hbmax u hu) (norm_nonneg _) ht0)
    have hn1 := (l2_norm_mulVec_fromVec_le (Vp u) (b' u)).trans
      (mul_le_mul hVp (hβ u hu) (norm_nonneg _) hα)
    have hn2 := (l2_norm_mulVec_fromVec_le (V u) (b'' u)).trans
      ((mul_le_mul hVn (hβ₂ u hu) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
    change ‖toEuclidean_fromVec (_+_)‖ ≤ _
    simp only [toEuclidean_fromVec, WithLp.toLp_add]
    have hbnd := (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add hn0 hn1))
      ((norm_add_le _ _).trans (add_le_add hn1 hn2)))
    exact hbnd.trans_eq (by ring)

omit [DecidableEq I] in

/-- The trapezoidal sum of source norms is at most their time integral plus `β * (t - s) ^ 2 /
Mt` when the source derivative norm is bounded by `β` and `Mt` is positive. -/
theorem inh_trap_source_mass_quadrature
    (b b' : ℝ → QState I) (s t β : ℝ) (Mt : ℕ)
    (hb : Continuous b) (hst : s ≤ t) (hMt : 0 < Mt)
    (hd : ∀ u, s ≤ u → u ≤ t → HasDerivAt b (b' u) u)
    (hβ : ∀ u, s ≤ u → u ≤ t → ‖toEuclidean_fromVec (b' u)‖ ≤ β) :
    (∑ l : Fin (Mt+1), inhTrapWeight Mt s t l*‖toEuclidean_fromVec (b (inhTrapNode Mt s t l))‖) ≤
      (∫ u in s..t, ‖toEuclidean_fromVec (b u)‖)+β*(t-s)^2/(Mt : ℝ) := by
  let F := fun u => ‖toEuclidean_fromVec (b u)‖
  have hcorr := inh_trap_sum_correction F Mt s t hMt
  simp only [smul_eq_mul] at hcorr
  have hleft := inh_source_mass_quadrature b b' s t β Mt hb hst hMt hd hβ
  have hlip := inh_derivative_lipschitz b b' s t β hd hβ t ⟨hst, le_rfl⟩ s ⟨le_rfl, hst⟩
  rw [abs_of_nonneg (sub_nonneg.2 hst)] at hlip
  have hdiff : F t-F s ≤ β*(t-s) :=
    (le_abs_self _).trans ((abs_norm_sub_norm_le _ _).trans hlip)
  have hstep := inh_step_nonneg Mt s t hst
  have hend := mul_le_mul_of_nonneg_left hdiff (div_nonneg hstep (by norm_num : (0 : ℝ) ≤ 2))
  rw [hcorr]
  apply (add_le_add hleft hend).trans_eq
  have hmR : (Mt : ℝ) ≠ 0 := by exact_mod_cast hMt.ne'
  dsimp [inhStep]
  field_simp
  ring

end Qatlib.Concepts.LchsSimulation.TimeTrapezoid
