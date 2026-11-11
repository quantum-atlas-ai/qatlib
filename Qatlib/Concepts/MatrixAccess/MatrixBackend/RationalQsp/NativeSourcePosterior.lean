/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceNativePacket
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeGeneratedChebyshevResidual
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Original-input, accepted-certificate nonconstant source packet: Posterior.
Value and physical-word guarantees here do not certify a root proposer, Python interpreter or total costs. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section Posterior

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

/-- The finite construction in `NativeSourcePosterior` satisfies `cheb_neg` under the displayed hypotheses. -/
private theorem cheb_neg (xs : List ℚ) (j : ℕ) :
    nativeChebyshevPolynomialFrom j (xs.map Neg.neg)= -nativeChebyshevPolynomialFrom j xs := by
  induction xs generalizing j with
  | nil => simp [nativeChebyshevPolynomialFrom]
  | cons c cs ih => simp only [List.map_cons,nativeChebyshevPolynomialFrom,ih,Rat.cast_neg,Polynomial.C_neg]; ring

/-- The finite construction in `NativeSourcePosterior` satisfies `cheb_sub` under the displayed hypotheses. -/
private theorem cheb_sub (xs ys : List ℚ) (j : ℕ) :
    nativeChebyshevPolynomialFrom j (ratSubList xs ys)=
      nativeChebyshevPolynomialFrom j xs-nativeChebyshevPolynomialFrom j ys := by
  induction xs generalizing ys j with
  | nil => simp [ratSubList,nativeChebyshevPolynomialFrom,cheb_neg]
  | cons c cs ih =>
    cases ys with
    | nil => simp [ratSubList,nativeChebyshevPolynomialFrom]
    | cons d ds => simp only [ratSubList,nativeChebyshevPolynomialFrom,ih,Rat.cast_sub,Polynomial.C_sub]; ring

/-- The same emitted instruction list satisfies `sub_length` with the displayed gate and query accounting. -/
private theorem sub_length (xs ys : List ℚ) : (ratSubList xs ys).length=max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [ratSubList]
  | cons c cs ih => cases ys <;> simp [ratSubList,ih]

/-- Construction for source Residual in the native source posterior model. -/
def sourceResidual (target : List ℚ) (data : PhaseData) : List ℚ :=
  ratSubList (nativeChebyshevFromPower (nativeResponseRealCoefficients (nativePacketFromStandard data))) target

/-- The finite construction in `NativeSourcePosterior` satisfies `sourceResidual_identity` under the displayed hypotheses. -/
theorem sourceResidual_identity (target : List ℚ) (data : PhaseData) :
    realTarget (nativeResponseRealCoefficients (nativePacketFromStandard data))-
      nativeChebyshevPolynomialFrom 0 target=nativeChebyshevPolynomialFrom 0 (sourceResidual target data) := by
  rw [sourceResidual,cheb_sub,nativeChebyshevFromPower_semantics]

/-- The same emitted instruction list satisfies `sourceResidual_length_le` with the displayed gate and query accounting. -/
theorem sourceResidual_length_le (target : List ℚ) (data : PhaseData) :
    (sourceResidual target data).length≤ max (data.phases.length+1) target.length := by
  have hl : (nativeChebyshevFromPower (nativeResponseRealCoefficients (nativePacketFromStandard data))).length≤
      data.phases.length+1 := calc
    _ ≤ (nativeResponseRealCoefficients (nativePacketFromStandard data)).length := nativeChebyshevFromPower_length_le _
    _ = _ := by rw [nativeResponseRealCoefficients_length,nativePacketFromStandard_length]
  rw [sourceResidual,sub_length]
  exact max_le_max hl (le_refl _)

/-- The finite construction in `NativeSourcePosterior` satisfies `source_posterior_budget` under the displayed hypotheses. -/
theorem source_posterior_budget (cs : List ℚ) (N : ℕ) (E : ℚ) :
    2*(max (N+1) cs.length : ℝ)*(13*(sourceInputU cs N E : ℝ)/32)≤13*(E : ℝ)/32 := by
  let M := max (N+1) cs.length
  have hM : (0 : ℚ)<(M : ℚ) := by exact_mod_cast lt_of_lt_of_le (Nat.succ_pos N) (le_max_left (N+1) cs.length)
  have hu : sourceInputU cs N E≤E/(2*(M : ℚ)) := min_le_right _ _
  have hc : 2*(M : ℚ)*sourceInputU cs N E≤E := by
    have h := (le_div_iff₀ (show (0 : ℚ)<2*(M : ℚ) by positivity)).mp hu
    simpa only [mul_comm] using h
  have hr : 2*(M : ℝ)*(sourceInputU cs N E : ℝ)≤(E : ℝ) := by exact_mod_cast hc
  dsimp only [M] at hr
  push_cast at hr
  nlinarith

/-- The finite construction in `NativeSourcePosterior` satisfies `source_posterior_accepts` under the displayed hypotheses. -/
theorem source_posterior_accepts (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
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
    let data := sourceBoundaryPacket cs N E f
    nativeChebyshevPacketCheck cs (sourceResidual cs data) data E=true := by
  let data := sourceBoundaryPacket cs N E f
  let delta : ℝ := 13*(sourceInputU cs N E : ℝ)/32
  have hu : (0 : ℝ)<(sourceInputU cs N E : ℝ) := by exact_mod_cast sourceInputU_pos cs N E hE
  have hs := source_boundary_packet_spec cs N E hparity hd f
  apply nativeChebyshevPacketCheck_of_uniform cs (sourceResidual cs data) data E delta hs.2.1 hs.2.2
    (sourceResidual_identity cs data)
  · intro x hx
    simpa only [sourceNativePacket,nativePacketFromStandard_real_imag] using
      source_native_uniform cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted x hx
  · have hl := sourceResidual_length_le cs data
    rw [hs.1] at hl
    have hR : ((sourceResidual cs data).length : ℝ)≤(max (N+1) cs.length : ℝ) := by exact_mod_cast hl
    calc
      _ ≤ 2*(max (N+1) cs.length : ℝ)*delta :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR (by norm_num)) (by positivity)
      _ ≤ 13*(E : ℝ)/32 := source_posterior_budget cs N E
      _ ≤ (E : ℝ) := by
        have hER : (0 : ℝ)<(E : ℝ) := by exact_mod_cast hE
        linarith

/-- The estimate `source_residual_mass_bound` retains the actual parameter, input-error and normalization budgets. -/
theorem source_residual_mass_bound (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
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
    let data := sourceBoundaryPacket cs N E f
    (nativeChebyshevMass (sourceResidual cs data) : ℝ)≤13*(E : ℝ)/32 := by
  let data := sourceBoundaryPacket cs N E f
  let delta : ℝ := 13*(sourceInputU cs N E : ℝ)/32
  have hu : (0 : ℝ)<(sourceInputU cs N E : ℝ) := by exact_mod_cast sourceInputU_pos cs N E hE
  have hs := source_boundary_packet_spec cs N E hparity hd f
  have hres : ∀ x∈Set.Icc (-1 : ℝ) 1,
      |(nativeChebyshevPolynomialFrom 0 (sourceResidual cs data)).eval x|≤delta := by
    intro x hx
    have hi := congrArg (fun q : Polynomial ℝ => q.eval x) (sourceResidual_identity cs data)
    simp only [Polynomial.eval_sub,nativeResponseRealCoefficients_eval] at hi
    rw [←hi]
    exact source_native_uniform cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted x hx
  have hm := nativeChebyshevMass_of_uniform (sourceResidual cs data) delta hres
  have hl := sourceResidual_length_le cs data
  rw [hs.1] at hl
  have hR : ((sourceResidual cs data).length : ℝ)≤(max (N+1) cs.length : ℝ) := by exact_mod_cast hl
  exact hm.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hR (by norm_num)) (by positivity)).trans (source_posterior_budget cs N E))

end Posterior

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
