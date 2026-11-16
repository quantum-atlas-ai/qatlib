/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullSourceGap

@[expose] public section


/-! # Complete finite gaps in the normalized source-form interface

These identities connect the full complex matrix minima to the exact source
forms and normalized Gibbs variance. The damped source already contains one
phase kernel, whereas the common matrix assembly uses `2 * phaseKernel`
against its built-in half. Neither parent is rescaled in this bridge.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds



namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

variable {D : ℕ} {ι : Type*} [Fintype ι]

/-- Full Parent Op damped hs Inner for the stated finite source data. -/
theorem fullParentOp_damped_hsInner (lam : Fin D → ℝ) (β : ℝ)
    (A : ι → Operator D) (X : Operator D) :
    hsInner X (fullParentOp lam β (fun ω => 2 * phaseKernel β ω) A X) =
      ∑ P, ckgSourceDampedForm β (gibbsDiag lam β) (fullNu lam)
        (fullTransition (A P)) X := by
  classical
  rw [fullParentOp_apply, hsInner_sum_right]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [parentGramFamOp_hsInner_complex]
  unfold wplainForm ckgSourceDampedForm wdampedForm
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hcoef : fullWeight lam β (fun ω => 2 * phaseKernel β ω) a b / 2 =
      ckgSourceWeight β (fullNu lam a) (fullNu lam b) *
        phaseKernel β (fullNu lam a - fullNu lam b) := by
    unfold fullWeight
    ring
  rw [hcoef]

/-- Full Gram Matrix damped rayleigh source for the stated finite source data. -/
theorem fullGramMatrix_damped_rayleigh_source (lam : Fin D → ℝ) (β : ℝ)
    (A : ι → Operator D) (z : FullCoord D → ℂ) :
    fullRayleigh (fullGramMatrix lam β (fun ω => 2 * phaseKernel β ω) A) z =
      ∑ P, (ckgSourceDampedForm β (gibbsDiag lam β) (fullNu lam)
        (fullTransition (A P)) (fun i j => z (i, j))).re := by
  let X : Operator D := fun i j => z (i, j)
  have hquad := fullGramMatrix_rayleigh_eq_hsInner lam β
    (fun ω => 2 * phaseKernel β ω) A z
  change star z ⬝ᵥ (fullGramMatrix lam β (fun ω => 2 * phaseKernel β ω) A *ᵥ z) =
    hsInner X (fullParentOp lam β (fun ω => 2 * phaseKernel β ω) A X) at hquad
  have hsource := fullParentOp_damped_hsInner lam β A X
  simpa only [fullRayleigh, Complex.re_sum, X] using!
    congrArg Complex.re (hquad.trans hsource)

/-- Full Source Plain Gap source Form for the stated finite source data. -/
theorem fullSourcePlainGap_sourceForm [Nonempty (Fin D)]
    (lam : Fin D → ℝ) {β : ℝ} (hβ : 0 < β) (A : ι → Operator D) :
    FormGapAtLeast
      (fun X => ∑ P, (ckgSourcePlainForm β (gibbsDiag lam β) (fullNu lam)
        (fullTransition (A P)) X).re)
      (CFC.sqrt (gibbsDiag lam β)) (fullSourcePlainGap lam β A) := by
  intro X
  have hb := fullRayleighGap_variance (fullGramMatrix_plain_posSemidef hβ lam A).isHermitian
    (fullGibbsVector lam β) (fullGibbsVector_ne_zero lam β)
    (fullGramMatrix_gibbsVector_eq_zero lam β (fun _ => 1) A) (fullVec X)
  rw [fullGibbsVariance_eq_hsVar, fullGramMatrix_plain_rayleigh_source] at hb
  exact hb

/-- Full Source Damped Gap source Form for the stated finite source data. -/
theorem fullSourceDampedGap_sourceForm [Nonempty (Fin D)]
    (lam : Fin D → ℝ) {β : ℝ} (hβ : 0 < β) (A : ι → Operator D) :
    FormGapAtLeast
      (fun X => ∑ P, (ckgSourceDampedForm β (gibbsDiag lam β) (fullNu lam)
        (fullTransition (A P)) X).re)
      (CFC.sqrt (gibbsDiag lam β)) (fullSourceDampedGap lam β A) := by
  intro X
  have hb := fullRayleighGap_variance (fullGramMatrix_damped_posSemidef hβ lam A).isHermitian
    (fullGibbsVector lam β) (fullGibbsVector_ne_zero lam β)
    (fullGramMatrix_gibbsVector_eq_zero lam β (fun ω => 2 * phaseKernel β ω) A) (fullVec X)
  rw [fullGibbsVariance_eq_hsVar, fullGramMatrix_damped_rayleigh_source] at hb
  exact hb

end Qatlib.Concepts.GibbsSource.SourceForms
