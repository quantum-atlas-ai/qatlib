/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InstrumentCore.PatternCompile.UniversalRawFrameReadoutStat
import Qatlib.Concepts.InstrumentCore.PatternCompile.UniversalRawGraphAux
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Concepts.ClusterPatterns.PauliNetwork
open Qatlib.Concepts.ClusterPatterns.Preentangled
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.InstrumentCore.PatternCompile
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators ComplexOrder Kronecker

theorem mbqcRawBranch_formula {n L : ℕ} (G : GraphWord n L)
    (hlegal : networkLegal (List.ofFn G)) (h : GraphHistory G) (ρ : Operator (2^n)) :
    mbqcRawBranch G h ρ=(1/2 : ℂ)^(graphWireCount G) •
      (pauliFrameGate n (graphFinalFrame G h)*networkLogicalMatrix (List.ofFn G)*ρ*
        (pauliFrameGate n (graphFinalFrame G h)*networkLogicalMatrix (List.ofFn G))ᴴ) := by
  ext i j
  simp only [mbqcRawBranch,mbqcRawReference_formula G hlegal,
    tensorGate_conjTranspose,Matrix.conjTranspose_one,tensorGate_mul,Matrix.one_mul,
    Matrix.smul_apply]
  simp only [TensorGate,Matrix.kronecker_apply,Matrix.one_apply_eq,mul_one]

theorem mbqcFrameDecode_involutive {n : ℕ} (F : PauliFrame n) :
    Function.Involutive (mbqcFrameDecode F) := by
  intro r
  simp [mbqcFrameDecode]

private theorem frame_entry (n : ℕ) (F : PauliFrame n) (r c : Fin (2^n)) :
    pauliFrameGate n F r c =
      if (bitVecEquiv n).symm r=frameShift F ((bitVecEquiv n).symm c)
      then frameSign F ((bitVecEquiv n).symm c) else 0 := by
  have he := congrFun (congrFun (graphPauliFrameB_eq n F) ((bitVecEquiv n).symm r))
    ((bitVecEquiv n).symm c)
  simpa [relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,pauliFrameGateB_entry] using!
      he.symm

theorem mbqcFrameDecode_support {n : ℕ} (F : PauliFrame n) (r c : Fin (2^n))
    (h : pauliFrameGate n F r c ≠ 0) : mbqcFrameDecode F r=c := by
  rw [frame_entry] at h
  have hs : (bitVecEquiv n).symm r=frameShift F ((bitVecEquiv n).symm c) := by
    by_contra hn
    exact h (if_neg hn)
  apply (bitVecEquiv n).symm.injective
  funext i
  simp only [mbqcFrameDecode,Equiv.symm_apply_apply] at ⊢
  rw [congrFun hs i]
  simp [frameShift]

theorem mbqcFrame_projector {n : ℕ} (F : PauliFrame n) (E : Finset (Fin (2^n))) :
    Projector (mbqcDecodedEvent F E)*pauliFrameGate n F=pauliFrameGate n F*Projector E := by
  ext r c
  simp only [Projector,Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases hrc : pauliFrameGate n F r c=0
  · simp [hrc]
  · have he := mbqcFrameDecode_support F r c hrc
    simp [mbqcDecodedEvent,he,mul_comm]

theorem mbqcFrame_densityEvent {n : ℕ} (F : PauliFrame n)
    (A : Operator (2^n)) (E : Finset (Fin (2^n))) :
    mbqcDensityEvent (pauliFrameGate n F*A*(pauliFrameGate n F)ᴴ)
      (mbqcDecodedEvent F E)=mbqcDensityEvent A E := by
  have hu : (pauliFrameGate n F)ᴴ*pauliFrameGate n F=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using!
      (Matrix.mem_unitaryGroup_iff').mp (pauliFrameGate_unitary n F)
  unfold mbqcDensityEvent
  congr 1
  calc
    Matrix.trace (Projector (mbqcDecodedEvent F E)*(pauliFrameGate n F*A*(pauliFrameGate n F)ᴴ))
      = Matrix.trace ((pauliFrameGate n F)ᴴ*Projector (mbqcDecodedEvent F E)*(pauliFrameGate n F*A)) := by
        simpa only [Matrix.mul_assoc] using!
          Matrix.trace_mul_cycle (Projector (mbqcDecodedEvent F E))
            (pauliFrameGate n F*A) (pauliFrameGate n F)ᴴ
    _ = Matrix.trace (Projector E*A) := by
      rw [Matrix.mul_assoc,← Matrix.mul_assoc (Projector (mbqcDecodedEvent F E)),
        mbqcFrame_projector,← Matrix.mul_assoc,← Matrix.mul_assoc,hu,Matrix.one_mul]

theorem mbqcDensityEvent_smul {D : ℕ} (a : ℝ) (ρ : Operator D) (E : Finset (Fin D)) :
    mbqcDensityEvent ((a : ℂ) • ρ) E=a*mbqcDensityEvent ρ E := by
  simp [mbqcDensityEvent,Matrix.trace_smul]

theorem mbqcRaw_instrument {n L : ℕ} (G : GraphWord n L)
    (hlegal : networkLegal (List.ofFn G)) :
    ∃ I : Instrument (GraphHistory G) (2^n) (2^n),
      (∀ h ρ, I.branch h ρ=mbqcRawBranch G h ρ) ∧
      ∀ (ρ : Operator (2^n)), IsDensityOperator ρ → ∀ h,
        instrumentProb I ρ h=(1/2 : ℝ)^(graphWireCount G) := by
  let U := networkLogicalMatrix (List.ofFn G)
  let w := graphWireCount G
  let V : GraphHistory G → Operator (2^n) := fun h => pauliFrameGate n (graphFinalFrame G h)*U
  let K : GraphHistory G → Operator (2^n) := fun h => ((Real.sqrt 2 : ℂ)⁻¹)^w • V h
  have hv (h : GraphHistory G) : V h ∈ Matrix.unitaryGroup (Fin (2^n)) ℂ :=
    Submonoid.mul_mem _ (pauliFrameGate_unitary n _) (networkLogicalMatrix_unitary _ hlegal)
  have hunit (h : GraphHistory G) : (V h)ᴴ*V h=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff').mp (hv h)
  have hK : ∑ h : GraphHistory G, (K h)ᴴ*K h=1 := by
    simp only [K,Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
      graphAmplitude_square_rev,hunit,Finset.sum_const,Finset.card_univ,graphHistory_card]
    ext i j
    simp only [Matrix.smul_apply,smul_eq_mul]
    rw [nsmul_eq_mul]
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    rw [← mul_assoc,graphProbability_sum_scalar,one_mul]
  let I := Instrument.ofKraus K hK
  have hb (h : GraphHistory G) (ρ : Operator (2^n)) :
      I.branch h ρ=(1/2 : ℂ)^w • (V h*ρ*(V h)ᴴ) := by
    simp only [I,Instrument.ofKraus_branch,K,Matrix.conjTranspose_smul,Matrix.smul_mul,
      Matrix.mul_smul,smul_smul,graphAmplitude_square]
  refine ⟨I,?_,?_⟩
  · intro h ρ
    rw [hb,mbqcRawBranch_formula G hlegal h ρ]
  · intro ρ hρ h
    unfold instrumentProb
    rw [hb,Matrix.trace_smul]
    change (((1/2 : ℂ)^w)*Matrix.trace (conjBranch (V h) ρ)).re=(1/2 : ℝ)^w
    rw [trace_conjBranch_unitary (V h) (hv h),hρ.2,mul_one]
    have hh : (1/2 : ℂ)=((1/2 : ℝ) : ℂ) := by norm_num
    rw [hh,← Complex.ofReal_pow,Complex.ofReal_re]

theorem universalRawFrameReadout_answer : UniversalRawFrameReadout := by
  intro n L G hlegal
  refine ⟨mbqcRawProgram_leafCount G,mbqcRawLeaf_resources G,
    mbqcRawReference_formula G hlegal,mbqcRaw_instrument G hlegal,?_⟩
  intro ρ _ E
  have he (h : GraphHistory G) : mbqcDensityEvent (mbqcRawBranch G h ρ)
      (mbqcDecodedEvent (graphFinalFrame G h) E)=(1/2 : ℝ)^(graphWireCount G)*
      mbqcDensityEvent (networkLogicalMatrix (List.ofFn G)*ρ*(networkLogicalMatrix (List.ofFn G))ᴴ) E := by
    rw [mbqcRawBranch_formula G hlegal]
    have hh : (1/2 : ℂ)^(graphWireCount G)=Complex.ofReal ((1/2 : ℝ)^(graphWireCount G)) := by
      push_cast
      norm_num
    rw [hh,mbqcDensityEvent_smul]
    congr 1
    simpa only [Matrix.conjTranspose_mul,Matrix.mul_assoc] using!
      mbqcFrame_densityEvent (graphFinalFrame G h)
        (networkLogicalMatrix (List.ofFn G)*ρ*(networkLogicalMatrix (List.ofFn G))ᴴ) E
  refine ⟨he,?_⟩
  simp_rw [he]
  rw [Finset.sum_const,Finset.card_univ,graphHistory_card,nsmul_eq_mul]
  have hh : (2 : ℝ)^(graphWireCount G)*(1/2 : ℝ)^(graphWireCount G)=1 := by
    rw [← mul_pow]
    norm_num
  rw [Nat.cast_pow,Nat.cast_ofNat,← mul_assoc,hh,one_mul]

end Qatlib.Concepts.InstrumentCore.PatternCompile
