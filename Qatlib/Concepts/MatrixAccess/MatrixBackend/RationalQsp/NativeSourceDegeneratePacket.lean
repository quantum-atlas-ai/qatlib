/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourcePosterior
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


section ZeroPacket

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Polynomial

/-- The finite construction in `NativeSourceDegeneratePacket` satisfies `sourceOnesResponse_real` under the displayed hypotheses. -/
theorem sourceOnesResponse_real (n : ℕ) (x : ℝ) :
    ((standardResponseP 1 (List.replicate n 1)).eval (x : ℂ)).im=0 ∧
      ((standardResponseQ 1 (List.replicate n 1)).eval (x : ℂ)).re=0 := by
  induction n with
  | zero => simp [standardResponseP,standardResponseQ,standardResponse]
  | succ n ih =>
    simp only [List.replicate_succ,standardResponseP_cons,standardResponseQ_cons,
      Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_pow,
      Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,star_one,one_mul]
    constructor <;> simp [Complex.mul_re,Complex.mul_im,pow_two,ih.1,ih.2]

/-- The estimate `sourceOnesBoundary` retains the actual parameter, input-error and normalization budgets. -/
theorem sourceOnesBoundary (N : ℕ) :
    nativeEquatorialBoundaryPacket (1,0) (List.replicate N (1,0))=
      (⟨(1,0),List.replicate N (1,0)⟩ : PhaseData) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hc : gconj (1,0)=(1,0) := by decide +kernel
    have hm : gmul (1,0) (1,0)=(1,0) := by decide +kernel
    simp only [List.replicate_succ,nativeEquatorialBoundaryPacket,hc,ih,hm]

/-- Construction for source Zero Boundary Packet in the native source degenerate packet model. -/
def sourceZeroBoundaryPacket (N : ℕ) : PhaseData :=
  nativeEquatorialBoundaryPacket (1,0) (List.replicate N (1,0))

/-- The finite construction in `NativeSourceDegeneratePacket` satisfies `sourceZeroNative_response` under the displayed hypotheses. -/
theorem sourceZeroNative_response (N : ℕ) (x : ℝ) :
    let data := nativePacketFromStandard (sourceZeroBoundaryPacket N)
    ((responseP (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)).eval (x : ℂ)).re=0 := by
  change ((responseP (gaussianRatComplex (nativePacketFromStandard (sourceZeroBoundaryPacket N)).base)
    ((nativePacketFromStandard (sourceZeroBoundaryPacket N)).phases.map gaussianRatComplex)).eval (x : ℂ)).re=0
  rw [nativePacketFromStandard_real_imag]
  have hb := sourceOnesBoundary N
  change sourceZeroBoundaryPacket N=⟨(1,0),List.replicate N (1,0)⟩ at hb
  rw [hb]
  simpa only [List.map_replicate,show gaussianRatComplex (1,0)=1 by norm_num [gaussianRatComplex]]
    using (sourceOnesResponse_real N x).1

/-- The finite construction in `NativeSourceDegeneratePacket` satisfies `sourceZeroPacket_spec` under the displayed hypotheses. -/
theorem sourceZeroPacket_spec (N : ℕ) :
    (sourceZeroBoundaryPacket N).phases.length=N ∧
      ‖gaussianRatComplex (sourceZeroBoundaryPacket N).base‖=1 ∧
      ∀ z∈(sourceZeroBoundaryPacket N).phases,‖gaussianRatComplex z‖=1 := by
  have h := sourceOnesBoundary N
  change sourceZeroBoundaryPacket N=⟨(1,0),List.replicate N (1,0)⟩ at h
  rw [h]
  simp [gaussianRatComplex]

/-- The finite construction in `NativeSourceDegeneratePacket` satisfies `cheb_replicate_zero` under the displayed hypotheses. -/
private theorem cheb_replicate_zero (n j : ℕ) :
    nativeChebyshevPolynomialFrom j (List.replicate n 0)=0 := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,nativeChebyshevPolynomialFrom,ih]

/-- The finite construction in `NativeSourceDegeneratePacket` satisfies `sourceZeroRegularized_polynomial` under the displayed hypotheses. -/
theorem sourceZeroRegularized_polynomial (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hzero : ∀ j : Fin (N+1),sourceCoefficient cs N E j=0) :
    nativeChebyshevPolynomialFrom 0 (sourceOutputList cs N E)=0 := by
  have hf : sourceOutputCoefficient cs N E=(fun _ : Fin (N+1) => 0) := by
    funext j
    simp only [sourceOutputCoefficient,hzero,mul_zero]
  have hl : sourceOutputList cs N E=List.replicate (N+1) 0 := by
    simp only [sourceOutputList,hf,List.ofFn_const]
  rw [hl,cheb_replicate_zero]

/-- The finite construction in `NativeSourceDegeneratePacket` satisfies `source_zero_native_uniform` under the displayed hypotheses. -/
theorem source_zero_native_uniform (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1≤k → cs.getD k 0=0)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x|≤1)
    (hzero : ∀ j : Fin (N+1),sourceCoefficient cs N E j=0) :
    let data := nativePacketFromStandard (sourceZeroBoundaryPacket N)
    ∀ x∈Set.Icc (-1 : ℝ) 1,
      |((responseP (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)).eval (x : ℂ)).re-
        (nativeChebyshevPolynomialFrom 0 cs).eval x|≤5*(sourceInputU cs N E : ℝ)/32 := by
  dsimp only
  intro x hx
  rw [sourceZeroNative_response]
  have he := source_regularized_error cs N E hE htail hnorm x hx
  rw [sourceZeroRegularized_polynomial cs N E hzero,Polynomial.eval_zero] at he
  exact he

/-- The finite construction in `NativeSourceDegeneratePacket` satisfies `sourcePacket_accepts_of_original_uniform` under the displayed hypotheses. -/
theorem sourcePacket_accepts_of_original_uniform (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (data : PhaseData) (hlen : data.phases.length=N)
    (hb : ‖gaussianRatComplex data.base‖=1)
    (hp : ∀ z∈data.phases,‖gaussianRatComplex z‖=1)
    (huniform : ∀ x∈Set.Icc (-1 : ℝ) 1,
      |((responseP (gaussianRatComplex (nativePacketFromStandard data).base)
        ((nativePacketFromStandard data).phases.map gaussianRatComplex)).eval (x : ℂ)).re-
        (nativeChebyshevPolynomialFrom 0 cs).eval x|≤13*(sourceInputU cs N E : ℝ)/32) :
    nativeChebyshevPacketCheck cs (sourceResidual cs data) data E=true := by
  let delta : ℝ := 13*(sourceInputU cs N E : ℝ)/32
  have hu : (0 : ℝ)<(sourceInputU cs N E : ℝ) := by exact_mod_cast sourceInputU_pos cs N E hE
  apply nativeChebyshevPacketCheck_of_uniform cs (sourceResidual cs data) data E delta hb hp
    (sourceResidual_identity cs data)
  · intro x hx
    simpa only [nativePacketFromStandard_real_imag] using huniform x hx
  · have hl := sourceResidual_length_le cs data
    rw [hlen] at hl
    have hR : ((sourceResidual cs data).length : ℝ)≤(max (N+1) cs.length : ℝ) := by exact_mod_cast hl
    calc
      _ ≤ 2*(max (N+1) cs.length : ℝ)*delta :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR (by norm_num)) (by positivity)
      _ ≤ 13*(E : ℝ)/32 := source_posterior_budget cs N E
      _ ≤ (E : ℝ) := by
        have hER : (0 : ℝ)<(E : ℝ) := by exact_mod_cast hE
        linarith

/-- The finite construction in `NativeSourceDegeneratePacket` satisfies `source_zero_posterior_accepts` under the displayed hypotheses. -/
theorem source_zero_posterior_accepts (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1≤k → cs.getD k 0=0)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x|≤1)
    (hzero : ∀ j : Fin (N+1),sourceCoefficient cs N E j=0) :
    nativeChebyshevPacketCheck cs (sourceResidual cs (sourceZeroBoundaryPacket N)) (sourceZeroBoundaryPacket N) E=true := by
  have hs := sourceZeroPacket_spec N
  apply sourcePacket_accepts_of_original_uniform cs N E hE (sourceZeroBoundaryPacket N) hs.1 hs.2.1 hs.2.2
  intro x hx
  have he := source_zero_native_uniform cs N E hE htail hnorm hzero x hx
  have hu : (0 : ℝ)<(sourceInputU cs N E : ℝ) := by exact_mod_cast sourceInputU_pos cs N E hE
  exact he.trans (by linarith)

end ZeroPacket

section ConstantCore

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Matrix Polynomial
open scoped Matrix.Norms.L2Operator

/-- Construction for source Constant Ideal Base in the native source degenerate packet model. -/
def sourceConstantIdealBase (a : ℚ) : ℂ := ⟨-Real.sqrt (1-(a : ℝ)^2),(a : ℝ)⟩
/-- Construction for source Constant Raw Base in the native source degenerate packet model. -/
def sourceConstantRawBase (a : ℚ) (q : ℕ) : GaussianRat := (-sourceSqrtLower (1-a^2) q,a)
/-- Construction for source Constant Rounded Base in the native source degenerate packet model. -/
def sourceConstantRoundedBase (a : ℚ) (q p : ℕ) : GaussianRat :=
  nativePhasePair (sourceConstantRawBase a q).1 (sourceConstantRawBase a q).2 p

/-- The finite construction in `NativeSourceDegeneratePacket` satisfies `sourceConstantIdealBase_norm` under the displayed hypotheses. -/
theorem sourceConstantIdealBase_norm (a : ℚ) (ha : |a|≤1) : ‖sourceConstantIdealBase a‖=1 := by
  have haR : |(a : ℝ)|≤1 := by exact_mod_cast ha
  have hrad : 0≤1-(a : ℝ)^2 := by nlinarith [(abs_le.mp haR).1,(abs_le.mp haR).2]
  have hs := Real.sq_sqrt hrad
  have hn : ‖sourceConstantIdealBase a‖^2=1 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    dsimp [sourceConstantIdealBase]
    nlinarith
  nlinarith [norm_nonneg (sourceConstantIdealBase a)]

/-- The estimate `sourceConstantRawBase_error` retains the actual parameter, input-error and normalization budgets. -/
theorem sourceConstantRawBase_error (a : ℚ) (ha : |a|≤1) (q : ℕ) :
    ‖gaussianRatComplex (sourceConstantRawBase a q)-sourceConstantIdealBase a‖≤1/(2 : ℝ)^q := by
  have hrad : (0 : ℚ)≤1-a^2 := by nlinarith [(abs_le.mp ha).1,(abs_le.mp ha).2]
  have hs := sourceSqrtLower_error (1-a^2) hrad q
  simp only [Rat.cast_sub,Rat.cast_one,Rat.cast_pow] at hs
  have hid : gaussianRatComplex (sourceConstantRawBase a q)-sourceConstantIdealBase a=
      ((Real.sqrt (1-(a : ℝ)^2)-(sourceSqrtLower (1-a^2) q : ℝ) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [gaussianRatComplex,sourceConstantRawBase,sourceConstantIdealBase]
    ring
  rw [hid,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hs.1)]
  exact hs.2.le

/-- The finite construction in `NativeSourceDegeneratePacket` satisfies `sourceConstantRoundedBase_spec` under the displayed hypotheses. -/
theorem sourceConstantRoundedBase_spec (a : ℚ) (ha : |a|≤1) (q p : ℕ) :
    ‖gaussianRatComplex (sourceConstantRoundedBase a q p)‖=1 ∧
      ‖gaussianRatComplex (sourceConstantRoundedBase a q p)-sourceConstantIdealBase a‖≤
        2/(2 : ℝ)^q+1/(16*(2 : ℝ)^p) := by
  have hs := nativePhasePair_error_of_unit_total (sourceConstantRawBase a q).1 (sourceConstantRawBase a q).2
    p (sourceConstantIdealBase a) (1/(2 : ℝ)^q) (sourceConstantIdealBase_norm a ha) (sourceConstantRawBase_error a ha q)
  have heq : (2 : ℝ)*(1/(2 : ℝ)^q)=2/(2 : ℝ)^q := by ring
  simpa only [sourceConstantRoundedBase,heq] using hs

/-- Construction for source Constant Padded Packet in the native source degenerate packet model. -/
def sourceConstantPaddedPacket (b : GaussianRat) (N : ℕ) : PhaseData :=
  nativeEquatorialBoundaryPacket b (sourcePaddingHalves (N/2))

/-- The finite construction in `NativeSourceDegeneratePacket` satisfies `sourceConstantPaddedPacket_spec` under the displayed hypotheses. -/
theorem sourceConstantPaddedPacket_spec (b : GaussianRat) (N : ℕ) (hN : N%2=0)
    (hb : ‖gaussianRatComplex b‖=1) :
    (sourceConstantPaddedPacket b N).phases.length=N ∧
      ‖gaussianRatComplex (sourceConstantPaddedPacket b N).base‖=1 ∧
      ∀ z∈(sourceConstantPaddedPacket b N).phases,‖gaussianRatComplex z‖=1 := by
  have hs := nativeEquatorialBoundaryPacket_spec b (sourcePaddingHalves (N/2)) hb (sourcePaddingHalves_norm _)
  have hl : (sourcePaddingHalves (N/2)).length=N := by rw [sourcePaddingHalves_length]; omega
  exact ⟨hs.1.trans hl,hs.2⟩

/-- The finite construction in `NativeSourceDegeneratePacket` satisfies `sourceConstantPaddedPacket_response` under the displayed hypotheses. -/
theorem sourceConstantPaddedPacket_response (b : GaussianRat) (N : ℕ) (x : ℝ)
    (hx : x∈Set.Icc (-1 : ℝ) 1) :
    let data := nativePacketFromStandard (sourceConstantPaddedPacket b N)
    ((responseP (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)).eval (x : ℂ)).re=
      (gaussianRatComplex b).im := by
  let s := Real.sqrt (1-x*x)
  have hr : 0≤1-x*x := by nlinarith [hx.1,hx.2]
  have hs : s*s=1-x*x := by simpa only [pow_two] using Real.sq_sqrt hr
  have he := nativePacketFromStandard_matrix_real_imag (sourceConstantPaddedPacket b N) x s hs
  change _=(standardMatrixWord
      (gaussianRatComplex (nativeEquatorialBoundaryPacket b (sourcePaddingHalves (N/2))).base) x s
      ((nativeEquatorialBoundaryPacket b (sourcePaddingHalves (N/2))).phases.map gaussianRatComplex)
      false false).im at he
  rw [nativeEquatorialBoundaryPacket_matrix b _ x s (sourcePaddingHalves_norm _),
    sourcePaddingHalves_product _ x s hs,mul_one] at he
  exact he

end ConstantCore

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
