/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceDegeneratePacket
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-! Actual source zero/constant/N=0 dispatch and the original-input all-branch packet.
Accepted raw roots are required only on the nonconstant path; proposer execution and total fees remain outside this value theorem. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section ZeroDegree

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Polynomial

/-- The finite construction in `NativeSourceZeroDegreePacket` satisfies `cheb_zero` under the displayed hypotheses. -/
private theorem cheb_zero (cs : List ℚ) : ∀ j,
    (∀ k,cs.getD k 0=0) → nativeChebyshevPolynomialFrom j cs=0 := by
  induction cs with
  | nil => intro j _; rfl
  | cons c cs ih =>
    intro j h
    have hc : c=0 := by simpa using h 0
    have ht : ∀ k,cs.getD k 0=0 := by intro k; simpa using h (k+1)
    simp only [nativeChebyshevPolynomialFrom,hc,Rat.cast_zero,Polynomial.C_0,zero_mul,zero_add]
    exact ih (j+1) ht

/-- The finite construction in `NativeSourceZeroDegreePacket` satisfies `sourceOriginalConstant_polynomial` under the displayed hypotheses. -/
theorem sourceOriginalConstant_polynomial (cs : List ℚ) (htail : ∀ k,1≤ k → cs.getD k 0=0) :
    nativeChebyshevPolynomialFrom 0 cs=C (cs.getD 0 0 : ℝ) := by
  cases cs with
  | nil => simp [nativeChebyshevPolynomialFrom]
  | cons c cs =>
    have ht : ∀ k,cs.getD k 0=0 := by intro k; simpa using htail (k+1) (by omega)
    simp [nativeChebyshevPolynomialFrom,cheb_zero cs 1 ht]

/-- Construction for source Zero Degree Precision in the native source zero degree packet model. -/
def sourceZeroDegreePrecision (cs : List ℚ) (E : ℚ) : ℕ := sourcePacketPrecision cs 0 E+8

/-- Construction for source Zero Degree Base in the native source zero degree packet model. -/
def sourceZeroDegreeBase (cs : List ℚ) (E : ℚ) : GaussianRat :=
  let p := sourceZeroDegreePrecision cs E
  sourceConstantRoundedBase (cs.getD 0 0) (p+8) p

/-- Construction for source Zero Degree Boundary Packet in the native source zero degree packet model. -/
def sourceZeroDegreeBoundaryPacket (cs : List ℚ) (E : ℚ) : PhaseData :=
  ⟨sourceZeroDegreeBase cs E,[]⟩

/-- The estimate `sourceZeroDegreePrecision_literal` retains the actual parameter, input-error and normalization budgets. -/
theorem sourceZeroDegreePrecision_literal (cs : List ℚ) (E : ℚ) :
    sourceZeroDegreePrecision cs E=sourceCeilLog2 (1/sourceInputU cs 0 E)+8 := by
  simp [sourceZeroDegreePrecision,sourcePacketPrecision]

/-- The finite construction in `NativeSourceZeroDegreePacket` satisfies `source_zero_degree_base_spec` under the displayed hypotheses. -/
theorem source_zero_degree_base_spec (cs : List ℚ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,1≤ k → cs.getD k 0=0)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x|≤ 1) :
    ‖gaussianRatComplex (sourceZeroDegreeBase cs E)‖=1 ∧
      ‖gaussianRatComplex (sourceZeroDegreeBase cs E)-sourceConstantIdealBase (cs.getD 0 0)‖≤
        9*(sourceInputU cs 0 E : ℝ)/32768 := by
  have ha : |cs.getD 0 0|≤ 1 := by
    have h := hnorm 0 (by constructor <;> norm_num)
    rw [sourceOriginalConstant_polynomial cs htail,Polynomial.eval_C] at h
    exact_mod_cast h
  let p := sourceZeroDegreePrecision cs E
  have hs := sourceConstantRoundedBase_spec (cs.getD 0 0) ha (p+8) p
  have heq : (2 : ℝ)/(2 : ℝ)^(p+8)+1/(16*(2 : ℝ)^p)=
      (9/2048 : ℝ)*(1/(16*(2 : ℝ)^sourcePacketPrecision cs 0 E)) := by
    dsimp [p,sourceZeroDegreePrecision]
    simp only [pow_add]
    norm_num
    ring
  rw [heq] at hs
  have hr : 1/(16*(2 : ℝ)^sourcePacketPrecision cs 0 E)≤ (sourceInputU cs 0 E : ℝ)/16 := by
    simpa using source_output_rounding_budget cs 0 E hE
  exact ⟨hs.1,hs.2.trans (by nlinarith)⟩

/-- The finite construction in `NativeSourceZeroDegreePacket` satisfies `source_zero_degree_uniform` under the displayed hypotheses. -/
theorem source_zero_degree_uniform (cs : List ℚ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,1≤ k → cs.getD k 0=0)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x|≤ 1) :
    let data := nativePacketFromStandard (sourceZeroDegreeBoundaryPacket cs E)
    ∀ x∈Set.Icc (-1 : ℝ) 1,
      |((responseP (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)).eval (x : ℂ)).re-
        (nativeChebyshevPolynomialFrom 0 cs).eval x|≤ 9*(sourceInputU cs 0 E : ℝ)/32768 := by
  dsimp only
  intro x _
  rw [nativePacketFromStandard_real_imag]
  have he := (Complex.abs_im_le_norm (gaussianRatComplex (sourceZeroDegreeBase cs E)-sourceConstantIdealBase (cs.getD 0 0))).trans
    (source_zero_degree_base_spec cs E hE htail hnorm).2
  rw [sourceOriginalConstant_polynomial cs htail,Polynomial.eval_C]
  simpa only [sourceZeroDegreeBoundaryPacket,List.map_nil,standardResponseP_nil,Polynomial.eval_C,Complex.sub_im,
    sourceConstantIdealBase] using he

/-- The finite construction in `NativeSourceZeroDegreePacket` satisfies `source_zero_degree_packet_spec` under the displayed hypotheses. -/
theorem source_zero_degree_packet_spec (cs : List ℚ) (E : ℚ) :
    (sourceZeroDegreeBoundaryPacket cs E).phases.length=0 ∧
      ‖gaussianRatComplex (sourceZeroDegreeBoundaryPacket cs E).base‖=1 ∧
      ∀ z∈(sourceZeroDegreeBoundaryPacket cs E).phases,‖gaussianRatComplex z‖=1 := by
  refine ⟨rfl,?_,by simp [sourceZeroDegreeBoundaryPacket]⟩
  exact nativePhasePair_norm _ _ _

/-- The finite construction in `NativeSourceZeroDegreePacket` satisfies `source_zero_degree_posterior_accepts` under the displayed hypotheses. -/
theorem source_zero_degree_posterior_accepts (cs : List ℚ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,1≤ k → cs.getD k 0=0)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x|≤ 1) :
    let data := sourceZeroDegreeBoundaryPacket cs E
    nativeChebyshevPacketCheck cs (sourceResidual cs data) data E=true := by
  have hs := source_zero_degree_packet_spec cs E
  apply sourcePacket_accepts_of_original_uniform cs 0 E hE (sourceZeroDegreeBoundaryPacket cs E) hs.1 hs.2.1 hs.2.2
  intro x hx
  have he := source_zero_degree_uniform cs E hE htail hnorm x hx
  have hu : (0 : ℝ)<(sourceInputU cs 0 E : ℝ) := by exact_mod_cast sourceInputU_pos cs 0 E hE
  exact he.trans (by linarith)

end ZeroDegree

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
