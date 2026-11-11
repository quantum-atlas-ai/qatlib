/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeChebyshevUniformMass
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeChebyshevWordCheck
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-! A backend's uniform accuracy and complete exact residual identity suffice
for the actual posterior check, with a linear residual-length precision loss.
This is a completeness implication, not a numerical producer success theorem.
The original checker and its soundness consumer are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords

open Polynomial
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

/-- The finite construction in `NativeChebyshevUniformAcceptance` satisfies `nativeRationalCoefficientCheck_complete` under the displayed hypotheses. -/
theorem nativeRationalCoefficientCheck_complete (xs ys : List ℚ)
    (h : realTarget xs=realTarget ys) : nativeRationalCoefficientCheck xs ys=true := by
  simp only [nativeRationalCoefficientCheck,decide_eq_true_eq]
  intro i
  have hc := congrArg (fun p : Polynomial ℝ => p.coeff i.val) h
  rw [realTarget_coeff,realTarget_coeff] at hc
  exact_mod_cast hc

/-- The finite construction in `NativeChebyshevUniformAcceptance` satisfies `nativeChebyshevResidualCheck_complete` under the displayed hypotheses. -/
theorem nativeChebyshevResidualCheck_complete (target residual : List ℚ) (data : PhaseData)
    (h : realTarget (nativeResponseRealCoefficients data)-
      nativeChebyshevPolynomialFrom 0 target=nativeChebyshevPolynomialFrom 0 residual) :
    nativeChebyshevResidualCheck target residual data=true := by
  apply nativeRationalCoefficientCheck_complete
  simpa only [realTarget_sub,nativeChebyshevPowerSumFrom_semantics] using h

/-- The finite construction in `NativeChebyshevUniformAcceptance` satisfies `gaussian_unit_coordinates_of_norm` under the displayed hypotheses. -/
private theorem gaussian_unit_coordinates_of_norm (z : GaussianRat)
    (hz : ‖gaussianRatComplex z‖=1) : z.1*z.1+z.2*z.2=1 := by
  have hs : ‖gaussianRatComplex z‖^2=1 := by rw [hz]; norm_num
  rw [Complex.sq_norm,Complex.normSq_apply] at hs
  have hr : (z.1 : ℝ)*(z.1 : ℝ)+(z.2 : ℝ)*(z.2 : ℝ)=1 := by
    simpa [gaussianRatComplex,pow_two] using hs
  exact_mod_cast hr

/-- The finite construction in `NativeChebyshevUniformAcceptance` satisfies `nativeStandardUnitsCheck_complete` under the displayed hypotheses. -/
theorem nativeStandardUnitsCheck_complete (data : PhaseData)
    (hb : ‖gaussianRatComplex data.base‖=1)
    (hz : ∀ z∈data.phases,‖gaussianRatComplex z‖=1) :
    nativeStandardUnitsCheck data=true := by
  simp only [nativeStandardUnitsCheck,Bool.and_eq_true,List.all_eq_true,
    nativeGaussianUnitCheck,decide_eq_true_eq]
  exact ⟨gaussian_unit_coordinates_of_norm _ hb,
    fun z h => gaussian_unit_coordinates_of_norm z (hz z h)⟩

/-- The true whole residual identity plus a backend uniform bound pays only
2*length(residual). No acceptance Boolean or final matrix bound is input. -/
theorem nativeChebyshevPacketCheck_of_uniform (target residual : List ℚ)
    (data : PhaseData) (E : ℚ) (u : ℝ)
    (hb : ‖gaussianRatComplex data.base‖=1)
    (hz : ∀ z∈data.phases,‖gaussianRatComplex z‖=1)
    (hidentity : realTarget (nativeResponseRealCoefficients (nativePacketFromStandard data))-
      nativeChebyshevPolynomialFrom 0 target=nativeChebyshevPolynomialFrom 0 residual)
    (haccuracy : ∀ x∈Set.Icc (-1 : ℝ) 1,
      |((standardResponseP (gaussianRatComplex data.base)
        (data.phases.map gaussianRatComplex)).eval (x : ℂ)).im-
          (nativeChebyshevPolynomialFrom 0 target).eval x|≤u)
    (hbudget : 2*(residual.length : ℝ)*u≤(E : ℝ)) :
    nativeChebyshevPacketCheck target residual data E=true := by
  have hu : ∀ x∈Set.Icc (-1 : ℝ) 1,
      |(nativeChebyshevPolynomialFrom 0 residual).eval x|≤u := by
    intro x hx
    have hi := congrArg (fun p : Polynomial ℝ => p.eval x) hidentity
    rw [Polynomial.eval_sub,nativeResponseRealCoefficients_eval,
      nativePacketFromStandard_real_imag] at hi
    rw [←hi]
    exact haccuracy x hx
  have hm := (nativeChebyshevMass_of_uniform residual u hu).trans hbudget
  have hmQ : nativeChebyshevMass residual≤E := by exact_mod_cast hm
  simp only [nativeChebyshevPacketCheck,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨nativeStandardUnitsCheck_complete data hb hz,
    nativeChebyshevResidualCheck_complete _ _ _ hidentity⟩,hmQ⟩

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
