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


section ConstantInput

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Polynomial

/-- The finite construction in `NativeSourceConstantPacket` satisfies `cheb_zero_replicate` under the displayed hypotheses. -/
private theorem cheb_zero_replicate (n j : ℕ) :
    nativeChebyshevPolynomialFrom j (List.replicate n 0)=0 := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,nativeChebyshevPolynomialFrom,ih]

/-- The finite construction in `NativeSourceConstantPacket` satisfies `source_constant_tail` under the displayed hypotheses. -/
theorem source_constant_tail (cs : List ℚ) (N : ℕ) (E : ℚ) (hd : sourceDegree cs N E=0)
    (j : Fin (N+1)) (hj : 0<j.val) : sourceCoefficient cs N E j=0 := by
  apply sourceArrayDegree_tail_zero _ j
  change sourceDegree cs N E<j.val
  rwa [hd]

/-- The finite construction in `NativeSourceConstantPacket` satisfies `source_constant_polynomial` under the displayed hypotheses. -/
theorem source_constant_polynomial (cs : List ℚ) (N : ℕ) (E : ℚ) (hd : sourceDegree cs N E=0) :
    nativeChebyshevPolynomialFrom 0 (sourceOutputList cs N E)=C (sourceCoefficient cs N E 0 : ℝ) := by
  have ht : (fun j : Fin N => sourceOutputCoefficient cs N E j.succ)=(fun _ : Fin N => 0) := by
    funext j
    simp only [sourceOutputCoefficient,source_constant_tail cs N E hd j.succ (by simp),mul_zero]
  unfold sourceOutputList
  rw [List.ofFn_succ,ht,List.ofFn_const]
  simp [nativeChebyshevPolynomialFrom,cheb_zero_replicate,sourceOutputCoefficient,sourceWeight]

/-- The finite construction in `NativeSourceConstantPacket` satisfies `source_constant_nonzero` under the displayed hypotheses. -/
theorem source_constant_nonzero (cs : List ℚ) (N : ℕ) (E : ℚ) (hd : sourceDegree cs N E=0)
    (hnotzero : ¬∀ j : Fin (N+1),sourceCoefficient cs N E j=0) : sourceCoefficient cs N E 0≠0 := by
  intro h0
  apply hnotzero
  intro j
  by_cases hj : j.val=0
  · have he : j=0 := Fin.ext hj
    simpa only [he] using h0
  · exact source_constant_tail cs N E hd j (Nat.pos_of_ne_zero hj)

/-- The finite construction in `NativeSourceConstantPacket` satisfies `source_constant_even` under the displayed hypotheses. -/
theorem source_constant_even (cs : List ℚ) (N : ℕ) (E : ℚ) (hd : sourceDegree cs N E=0)
    (hnotzero : ¬∀ j : Fin (N+1),sourceCoefficient cs N E j=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0) : N%2=0 := by
  have hn := source_constant_nonzero cs N E hd hnotzero
  by_contra hN
  have hcs := hparity 0 (by simpa only [Fin.val_zero,Nat.zero_mod] using Ne.symm hN)
  exact hn (sourceCoefficient_zero cs N E 0 hcs)

/-- The finite construction in `NativeSourceConstantPacket` satisfies `source_constant_abs` under the displayed hypotheses. -/
theorem source_constant_abs (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1≤ k → cs.getD k 0=0)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x|≤ 1)
    (hd : sourceDegree cs N E=0) : |sourceCoefficient cs N E 0|≤ 1 := by
  have hg := sourceOutput_uniform_gap cs N E hE htail hnorm 0 (by constructor <;> norm_num)
  rw [source_constant_polynomial cs N E hd,Polynomial.eval_C] at hg
  have hu : (0 : ℝ)<(sourceInputU cs N E : ℝ) := by exact_mod_cast sourceInputU_pos cs N E hE
  exact_mod_cast hg.trans (show 1-3*(sourceInputU cs N E : ℝ)/32≤ 1 by linarith)

/-- The finite construction in `NativeSourceConstantPacket` satisfies `source_eta_output_budget` under the displayed hypotheses. -/
theorem source_eta_output_budget (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E) :
    sourceInputEta cs N E≤ sourceInputU cs N E/(32*(N+1 : ℚ)) := by
  let u := sourceInputU cs N E
  let h := sourceGrid N u
  let K := sourceK N u
  let eta := sourceInputEta cs N E
  have hu : 0<u := sourceInputU_pos cs N E hE
  have hu1 : u≤ 1/2 := sourceInputU_le_half cs N E
  have he : 0<eta := by dsimp [eta,sourceInputEta]; positivity
  have hN : (1 : ℚ)≤ N+1 := by
    have hn : (0 : ℚ)≤ N := by positivity
    linarith
  have hpow : (1 : ℚ)≤ (N+1 : ℚ)^6 := one_le_pow₀ hN
  have hK : (1 : ℚ)≤ K := by
    dsimp only [K,sourceK]
    apply (le_div_iff₀ (sq_pos_of_pos hu)).mpr
    norm_num only [one_mul,show (2 : ℚ)^20=1048576 by norm_num]
    nlinarith
  have hh : 0<h := sourceGrid_pos N u
  have hh1 : h≤ 1 := by
    dsimp [h,sourceGrid]
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hL : (1 : ℚ)≤ 128/h := (le_div_iff₀ hh).mpr (by linarith)
  have hLp : (1 : ℚ)≤ (128/h)^(N+1) := one_le_pow₀ hL
  have hbound := (source_input_budget cs N E hE).2
  change K*eta*(128/h)^(N+1)≤ u/(32*(N+1 : ℚ)) at hbound
  have hke : eta≤ K*eta := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hK he.le
  exact hke.trans ((le_mul_of_one_le_right (mul_nonneg (by linarith) he.le) hLp).trans hbound)

/-- Construction for source Constant Base in the native source constant packet model. -/
def sourceConstantBase (cs : List ℚ) (N : ℕ) (E : ℚ) : GaussianRat :=
  sourceConstantRoundedBase (sourceCoefficient cs N E 0) (sourceInputR cs N E+4) (sourcePacketPrecision cs N E)

/-- Construction for source Constant Boundary Packet in the native source constant packet model. -/
def sourceConstantBoundaryPacket (cs : List ℚ) (N : ℕ) (E : ℚ) : PhaseData :=
  sourceConstantPaddedPacket (sourceConstantBase cs N E) N

/-- The estimate `source_constant_base_error` retains the actual parameter, input-error and normalization budgets. -/
theorem source_constant_base_error (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1≤ k → cs.getD k 0=0)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x|≤ 1)
    (hd : sourceDegree cs N E=0) :
    ‖gaussianRatComplex (sourceConstantBase cs N E)‖=1 ∧
      ‖gaussianRatComplex (sourceConstantBase cs N E)-sourceConstantIdealBase (sourceCoefficient cs N E 0)‖≤
        17*(sourceInputU cs N E : ℝ)/256 := by
  have hs := sourceConstantRoundedBase_spec (sourceCoefficient cs N E 0)
    (source_constant_abs cs N E hE htail hnorm hd) (sourceInputR cs N E+4) (sourcePacketPrecision cs N E)
  have heq : (2 : ℝ)/(2 : ℝ)^(sourceInputR cs N E+4)=(sourceInputEta cs N E : ℝ)/8 := by
    simp only [sourceInputEta,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat,pow_add]
    norm_num
    ring
  rw [heq] at hs
  have hu : (0 : ℝ)<(sourceInputU cs N E : ℝ) := by exact_mod_cast sourceInputU_pos cs N E hE
  have hN : (1 : ℝ)≤ N+1 := by
    have hn : (0 : ℝ)≤ N := by positivity
    linarith
  have he : (sourceInputEta cs N E : ℝ)≤ (sourceInputU cs N E : ℝ)/(32*(N+1 : ℝ)) := by
    exact_mod_cast source_eta_output_budget cs N E hE
  have he' : (sourceInputEta cs N E : ℝ)≤ (sourceInputU cs N E : ℝ)/32 :=
    he.trans (div_le_div_of_nonneg_left hu.le (by norm_num) (by nlinarith))
  have hr := (source_output_rounding_budget cs N E hE).trans
    (div_le_div_of_nonneg_left hu.le (by norm_num : (0 : ℝ)<16) (by nlinarith : (16 : ℝ)≤ 16*(N+1 : ℝ)))
  exact ⟨hs.1,hs.2.trans (by linarith)⟩

/-- The finite construction in `NativeSourceConstantPacket` satisfies `source_constant_packet_spec` under the displayed hypotheses. -/
theorem source_constant_packet_spec (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hd : sourceDegree cs N E=0)
    (hnotzero : ¬∀ j : Fin (N+1),sourceCoefficient cs N E j=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0) :
    (sourceConstantBoundaryPacket cs N E).phases.length=N ∧
      ‖gaussianRatComplex (sourceConstantBoundaryPacket cs N E).base‖=1 ∧
      ∀ z∈(sourceConstantBoundaryPacket cs N E).phases,‖gaussianRatComplex z‖=1 := by
  apply sourceConstantPaddedPacket_spec _ N (source_constant_even cs N E hd hnotzero hparity)
  exact nativePhasePair_norm _ _ _

/-- The finite construction in `NativeSourceConstantPacket` satisfies `source_constant_native_uniform` under the displayed hypotheses. -/
theorem source_constant_native_uniform (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1≤ k → cs.getD k 0=0)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x|≤ 1)
    (hd : sourceDegree cs N E=0) :
    let data := nativePacketFromStandard (sourceConstantBoundaryPacket cs N E)
    ∀ x∈Set.Icc (-1 : ℝ) 1,
      |((responseP (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)).eval (x : ℂ)).re-
        (nativeChebyshevPolynomialFrom 0 cs).eval x|≤ 57*(sourceInputU cs N E : ℝ)/256 := by
  dsimp only
  intro x hx
  have hnative := sourceConstantPaddedPacket_response (sourceConstantBase cs N E) N x hx
  change ((responseP (gaussianRatComplex (nativePacketFromStandard (sourceConstantBoundaryPacket cs N E)).base)
    ((nativePacketFromStandard (sourceConstantBoundaryPacket cs N E)).phases.map gaussianRatComplex)).eval (x : ℂ)).re=
    (gaussianRatComplex (sourceConstantBase cs N E)).im at hnative
  rw [hnative]
  have hb := (Complex.abs_im_le_norm
    (gaussianRatComplex (sourceConstantBase cs N E)-sourceConstantIdealBase (sourceCoefficient cs N E 0))).trans
      (source_constant_base_error cs N E hE htail hnorm hd).2
  change |(gaussianRatComplex (sourceConstantBase cs N E)).im-(sourceCoefficient cs N E 0 : ℝ)|≤
    17*(sourceInputU cs N E : ℝ)/256 at hb
  have hr := source_regularized_error cs N E hE htail hnorm x hx
  rw [source_constant_polynomial cs N E hd,Polynomial.eval_C] at hr
  exact (abs_sub_le (gaussianRatComplex (sourceConstantBase cs N E)).im
    (sourceCoefficient cs N E 0 : ℝ) ((nativeChebyshevPolynomialFrom 0 cs).eval x)).trans (by linarith)

/-- The finite construction in `NativeSourceConstantPacket` satisfies `source_constant_posterior_accepts` under the displayed hypotheses. -/
theorem source_constant_posterior_accepts (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1≤ k → cs.getD k 0=0)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x|≤ 1)
    (hd : sourceDegree cs N E=0)
    (hnotzero : ¬∀ j : Fin (N+1),sourceCoefficient cs N E j=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0) :
    let data := sourceConstantBoundaryPacket cs N E
    nativeChebyshevPacketCheck cs (sourceResidual cs data) data E=true := by
  have hs := source_constant_packet_spec cs N E hd hnotzero hparity
  apply sourcePacket_accepts_of_original_uniform cs N E hE (sourceConstantBoundaryPacket cs N E) hs.1 hs.2.1 hs.2.2
  intro x hx
  have he := source_constant_native_uniform cs N E hE htail hnorm hd x hx
  have hu : (0 : ℝ)<(sourceInputU cs N E : ℝ) := by exact_mod_cast sourceInputU_pos cs N E hE
  exact he.trans (by linarith)

end ConstantInput

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
