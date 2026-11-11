/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourcePacketAccuracy
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-! Original-input, accepted-certificate nonconstant source packet: NativePacket.
Value and physical-word guarantees here do not certify a root proposer, Python interpreter or total costs. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section FinalResponse

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open scoped Matrix.Norms.L2Operator

/-- Construction for source Native Packet in the native source native packet model. -/
def sourceNativePacket {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ) (f : Fin m → RootIntegerFactorData) : PhaseData :=
  nativePacketFromStandard (sourceBoundaryPacket cs N E f)

/-- The finite construction in `NativeSourceNativePacket` satisfies `source_native_packet_spec` under the displayed hypotheses. -/
theorem source_native_packet_spec {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) (f : Fin m → RootIntegerFactorData) :
    (sourceNativePacket cs N E f).phases.length=N ∧
      ‖gaussianRatComplex (sourceNativePacket cs N E f).base‖=1 ∧
      ∀ z∈(sourceNativePacket cs N E f).phases,‖gaussianRatComplex z‖=1 := by
  have hs := source_boundary_packet_spec cs N E hparity hd f
  have hu := nativePacketFromStandard_unit (sourceBoundaryPacket cs N E f) hs.2.1 hs.2.2
  exact ⟨(nativePacketFromStandard_length _).trans hs.1,hu⟩

/-- The finite construction in `NativeSourceNativePacket` satisfies `source_native_to_regularized` under the displayed hypotheses. -/
theorem source_native_to_regularized (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (m : ℕ) (content : ℤ) (f : Fin m → RootIntegerFactorData)
    (hcontent : content≠0)
    (hguard : rootIntegerFactorProduct content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent)))=
        rootCanonicalCoefficients (sourceIntegerComplement cs N E))
    (haccepted : ∀ j,RootIntegerFactorGuards (f j) (sourceInputEta cs N E))
    (x : ℝ) (hx : x∈Set.Icc (-1 : ℝ) 1) :
    let data := sourceNativePacket cs N E f
    |((responseP (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)).eval (x : ℂ)).re-
      (nativeChebyshevPolynomialFrom 0 (sourceOutputList cs N E)).eval x|≤(sourceInputU cs N E : ℝ)/4 := by
  let theta := Real.arccos x
  let G := sourceIdealMatrixArray cs N E
  let data := sourceBoundaryPacket cs N E f
  let W := standardMatrixWord (gaussianRatComplex data.base) x (Real.sin theta) (data.phases.map gaussianRatComplex)
  have hcos : Real.cos theta=x := Real.cos_arccos hx.1 hx.2
  have hsc : Real.sin theta*Real.sin theta=1-x*x := by
    have hs := Real.sin_sq_add_cos_sq theta
    rw [hcos] at hs
    nlinarith
  have hm := source_boundary_packet_error cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted theta
  change ‖standardMatrixWord (gaussianRatComplex data.base) (Real.cos theta) (Real.sin theta)
    (data.phases.map gaussianRatComplex)-sourceCompletionCircleValue G (theta : AddCircle (2*Real.pi))‖≤_ at hm
  rw [hcos] at hm
  have he := (sourceCompletionMatrix_entry_norm (W-sourceCompletionCircleValue G (theta : AddCircle (2*Real.pi))) false false).trans hm
  change ‖W false false-sourceCompletionCircleValue G (theta : AddCircle (2*Real.pi)) false false‖≤(sourceInputU cs N E : ℝ)/4 at he
  have him := (Complex.abs_im_le_norm (W false false-sourceCompletionCircleValue G (theta : AddCircle (2*Real.pi)) false false)).trans he
  have hcircle : sourceCompletionCircleValue G (theta : AddCircle (2*Real.pi))=sourceCompletionLaurentMatrix G theta := sourceCompletionCircleValue_real G theta
  have hvalue := sourceIdealArray_value cs N E hE htail hparity hd hnorm theta
  have himg : (sourceCompletionCircleValue G (theta : AddCircle (2*Real.pi)) false false).im=
      (nativeChebyshevPolynomialFrom 0 (sourceOutputList cs N E)).eval x := by
    rw [hcircle,hvalue]
    simp [sourceCompletionPointMatrix,standardPhaseMatrix,standardSignalMatrix,sourceCompletionResponseA,hcos]
  simp only [Complex.sub_im,himg] at him
  change |((responseP (gaussianRatComplex (nativePacketFromStandard data).base)
    ((nativePacketFromStandard data).phases.map gaussianRatComplex)).eval (x : ℂ)).re-_|≤_
  rw [nativePacketFromStandard_matrix_real_imag data x (Real.sin theta) hsc]
  exact him

/-- The estimate `source_regularized_error` retains the actual parameter, input-error and normalization budgets. -/
theorem source_regularized_error (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x|≤1)
    (x : ℝ) (hx : x∈Set.Icc (-1 : ℝ) 1) :
    |(nativeChebyshevPolynomialFrom 0 (sourceOutputList cs N E)).eval x-
      (nativeChebyshevPolynomialFrom 0 cs).eval x|≤5*(sourceInputU cs N E : ℝ)/32 := by
  let u := sourceInputU cs N E
  let v := (nativeChebyshevPolynomialFrom 0 cs).eval x
  let out := (nativeChebyshevPolynomialFrom 0 (sourceOutputList cs N E)).eval x
  have hu : (0 : ℝ)<(u : ℝ) := by exact_mod_cast sourceInputU_pos cs N E hE
  have hm : (sourceRoundingMass cs N E : ℝ)≤(u : ℝ)/32 := by
    exact_mod_cast sourceRoundingMass_small cs N E hE
  have he : |out-(1-(u : ℝ)/8)*v|≤(u : ℝ)/32 := by
    simpa only [Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat] using
      (sourceOutput_error cs N E htail x hx).trans hm
  have hscale : |(1-(u : ℝ)/8)*v-v|≤(u : ℝ)/8 := by
    calc
      _ = (u : ℝ)/8*|v| := by
        rw [show (1-(u : ℝ)/8)*v-v= -((u : ℝ)/8)*v by ring,abs_mul,abs_neg,
          abs_of_nonneg (by positivity : 0≤(u : ℝ)/8)]
      _ ≤ (u : ℝ)/8*1 := mul_le_mul_of_nonneg_left (hnorm x hx) (by positivity)
      _ = _ := mul_one _
  exact (abs_sub_le out ((1-(u : ℝ)/8)*v) v).trans (by linarith)

/-- The finite construction in `NativeSourceNativePacket` satisfies `source_native_uniform` under the displayed hypotheses. -/
theorem source_native_uniform (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (m : ℕ) (content : ℤ) (f : Fin m → RootIntegerFactorData)
    (hcontent : content≠0)
    (hguard : rootIntegerFactorProduct content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent)))=
        rootCanonicalCoefficients (sourceIntegerComplement cs N E))
    (haccepted : ∀ j,RootIntegerFactorGuards (f j) (sourceInputEta cs N E))
 :
    let data := sourceNativePacket cs N E f
    ∀ x∈Set.Icc (-1 : ℝ) 1,
      |((responseP (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)).eval (x : ℂ)).re-
        (nativeChebyshevPolynomialFrom 0 cs).eval x|≤13*(sourceInputU cs N E : ℝ)/32 := by
  dsimp only
  intro x hx
  have he := source_native_to_regularized cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted x hx
  have hr := source_regularized_error cs N E hE htail hnorm x hx
  have ht := abs_sub_le
    (((responseP (gaussianRatComplex (sourceNativePacket cs N E f).base)
      ((sourceNativePacket cs N E f).phases.map gaussianRatComplex)).eval (x : ℂ)).re)
    ((nativeChebyshevPolynomialFrom 0 (sourceOutputList cs N E)).eval x)
    ((nativeChebyshevPolynomialFrom 0 cs).eval x)
  exact ht.trans (by linarith)

end FinalResponse

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
