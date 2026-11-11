/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeChebyshevCertificate
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

open Qatlib.Foundations.QueryWordCore.Circuit

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.PureStateMath.Reflection

/-!
# Native Chebyshev Word Check

Unit checks, exact full residual identity, and computed mass acceptance. An arbitrary backend proposal is allowed, but no final uniform guarantee is input.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords

open Qatlib
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Matrix Polynomial
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Construction for native Gaussian Unit Check in the native chebyshev word check model. -/
def nativeGaussianUnitCheck (z : GaussianRat) : Bool := decide (z.1*z.1+z.2*z.2=1)

/-- Construction for native Standard Units Check in the native chebyshev word check model. -/
def nativeStandardUnitsCheck (data : PhaseData) : Bool :=
  nativeGaussianUnitCheck data.base && data.phases.all nativeGaussianUnitCheck

/-- The finite construction in `NativeChebyshevWordCheck` satisfies `gaussian_norm_of_unit_coordinates` under the displayed hypotheses. -/
private theorem gaussian_norm_of_unit_coordinates (z : GaussianRat)
    (hz : z.1*z.1+z.2*z.2=1) : ‖gaussianRatComplex z‖=1 := by
  have hzR : (z.1 : ℝ)*(z.1 : ℝ)+(z.2 : ℝ)*(z.2 : ℝ)=1 := by exact_mod_cast hz
  have h : ‖gaussianRatComplex z‖^2=1 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp [gaussianRatComplex,Complex.mul_re,Complex.mul_im]
    nlinarith
  nlinarith [norm_nonneg (gaussianRatComplex z)]

/-- The finite construction in `NativeChebyshevWordCheck` satisfies `nativeStandardUnitsCheck_sound` under the displayed hypotheses. -/
theorem nativeStandardUnitsCheck_sound (data : PhaseData)
    (h : nativeStandardUnitsCheck data=true) :
    ‖gaussianRatComplex data.base‖=1 ∧ ∀ z∈data.phases,‖gaussianRatComplex z‖=1 := by
  simp only [nativeStandardUnitsCheck,Bool.and_eq_true,List.all_eq_true,
    nativeGaussianUnitCheck,decide_eq_true_eq] at h
  exact ⟨gaussian_norm_of_unit_coordinates _ h.1,
    fun z hz => gaussian_norm_of_unit_coordinates z (h.2 z hz)⟩

/-- Unit checks, exact full residual identity, and computed mass acceptance.
An arbitrary backend proposal is allowed, but no final uniform guarantee is input. -/
def nativeChebyshevPacketCheck (target residual : List ℚ) (data : PhaseData) (E : ℚ) : Bool :=
  nativeStandardUnitsCheck data &&
    nativeChebyshevResidualCheck target residual (nativePacketFromStandard data) &&
    decide (nativeChebyshevMass residual≤E)

/-- The finite construction in `NativeChebyshevWordCheck` satisfies `nativeChebyshevPacketCheck_uniform` under the displayed hypotheses. -/
theorem nativeChebyshevPacketCheck_uniform (target residual : List ℚ) (data : PhaseData) (E : ℚ)
    (hcheck : nativeChebyshevPacketCheck target residual data E=true) :
    0≤(E : ℝ) ∧ ‖gaussianRatComplex data.base‖=1 ∧
    (∀ z∈data.phases,‖gaussianRatComplex z‖=1) ∧
    ∀ x∈Set.Icc (-1 : ℝ) 1,
      |((standardResponseP (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)).eval
        (x : ℂ)).im-(nativeChebyshevPolynomialFrom 0 target).eval x|≤(E : ℝ) := by
  simp only [nativeChebyshevPacketCheck,Bool.and_eq_true,decide_eq_true_eq] at hcheck
  have hu := nativeStandardUnitsCheck_sound data hcheck.1.1
  have hE : 0≤E := (nativeChebyshevMass_nonneg residual).trans hcheck.2
  refine ⟨by exact_mod_cast hE,hu.1,hu.2,?_⟩
  intro x hx
  rw [←nativePacketFromStandard_real_imag]
  have h := nativeChebyshevResidualCheck_uniform target residual (nativePacketFromStandard data)
    hcheck.1.2 x hx
  exact h.trans ((Rat.cast_le (K := ℝ)).mpr hcheck.2)

/-- The finite construction in `NativeChebyshevWordCheck` satisfies `native_chebyshev_checked_word_transform` under the displayed hypotheses. -/
theorem native_chebyshev_checked_word_transform
    {H I O : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
    (target residual : List ℚ) (data : PhaseData) (E : ℚ)
    (henc : ProjectedUnitaryEncoding A U L R)
    (hcheck : nativeChebyshevPacketCheck target residual data E=true) :
    let cs := nativeStandardPhaseWord (rangeProjector R) (rangeProjector L) data
    WellFormedAdjointCircuit (nativeStandardPhaseWord (rangeProjector L) (rangeProjector R) data) ∧
    WellFormedAdjointCircuit cs ∧
      adjointQueryCount cs=data.phases.length ∧ adjointGateCount cs=data.phases.length+1 ∧
      (data.phases.length%2=1 →
        BlockEncoding (oddSingularTransform A (fun x => (((nativeChebyshevPolynomialFrom 0 target).eval x : ℝ) : ℂ)))
          (evaluate (parallelOracle U) cs) (averageFrame L) (averageFrame R) 1 (E : ℝ)) ∧
      (data.phases.length%2=0 →
        BlockEncoding (rightSingularTransform A (fun x => (((nativeChebyshevPolynomialFrom 0 target).eval x : ℝ) : ℂ)))
          (evaluate (parallelOracle Uᴴ)
            (nativeStandardPhaseWord (rangeProjector L) (rangeProjector R) data))
          (averageFrame R) (averageFrame R) 1 (E : ℝ)) := by
  have hu := nativeChebyshevPacketCheck_uniform target residual data E hcheck
  have h := native_standard_phase_word_transform A U L R data
    (fun x => (nativeChebyshevPolynomialFrom 0 target).eval x) (E : ℝ) henc hu.2.1 hu.2.2.1
    hu.1 hu.2.2.2
  refine ⟨native_standard_phase_word_wellFormed (rangeProjector L) (rangeProjector R) _
    (rangeProjector_isOrthogonalProjector henc.left_isometry)
    (rangeProjector_isOrthogonalProjector henc.right_isometry) hu.2.1 hu.2.2.1,?_⟩
  exact h

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
