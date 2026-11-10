/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstructionDefs
import Qatlib.Concepts.HspRecovery.Distinguisher.BoundedErrorNearPeriodSimo
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Papers.QPowerSimon97.Recovery.SimonQueryTree

open Qatlib.Concepts.AbelianDecoders.SimonDecoding
open Qatlib.Concepts.AbelianDecoders.SimonDecoding
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation Qatlib.Concepts.CircuitImpl.ReflectionCompile
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.HspRecovery.Distinguisher

set_option autoImplicit false

open Qatlib.Concepts.AbelianDecoders.SimonDecoding Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.QtmSimulation.Phi3Compilation
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Concepts.CircuitImpl.Phi3Universal
open Matrix
open scoped Classical BigOperators ENNReal

namespace Qatlib.Papers.QPowerSimon97.Recovery
noncomputable section

private theorem experiment_run_sum {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (O : Matrix I I ℂ) (C : Circuit I) (z : J → ℂ) (v : J → QState I) :
    Run O C (∑ j, z j • v j) = ∑ j, z j • Run O C (v j) := by
  induction C generalizing v with
  | nil => rfl
  | cons g C ih =>
    cases g <;> simp only [run_gate, run_query, ApplyGate, Matrix.mulVec_sum,
      Matrix.mulVec_smul, ih]
end
noncomputable section

private theorem experiment_encode_ket {n m : ℕ} (x : BooleanVec n) (y : BooleanVec m) :
    simonEncodeState (Qatlib.Foundations.PureStateMath.Ket (x,y)) = Qatlib.Foundations.PureStateMath.Ket (simonEncodePair x y) := by
  simp [simonEncodeState, Qatlib.Foundations.PureStateMath.Ket]
end
noncomputable section

private theorem experiment_encode_sum {n m : ℕ} {J : Type} [Fintype J]
    (z : J → ℂ) (v : J → QState (BooleanVec n × BooleanVec m)) :
    simonEncodeState (∑ j, z j • v j) = ∑ j, z j • simonEncodeState (v j) := by
  simp only [simonEncodeState, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm
end
noncomputable section
private def experimentHadamards (n : ℕ) : List (ReflectionGate n) :=
  (List.finRange n).map (fun w => Sum.inl (w, Hadamard))
end
noncomputable section

private theorem experimentHadamards_legal (n : ℕ) :
    reflectionLegal (experimentHadamards n) := by
  rintro g hg
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hg
  exact hadamard_unitary
end
noncomputable section

private theorem experimentHadamards_run (n : ℕ) (ψ : QState (Reg n)) :
    Run 1 (reflectionCompile (experimentHadamards n)) ψ = ApplyGate (HadamardN n) ψ := by
  have hc : reflectionCompile (experimentHadamards n) = localProgramCircuit (localHadamard n) := by
    simp only [experimentHadamards, reflectionCompile, localHadamard, localProgramCircuit,
      List.map_map]
    apply List.map_congr_left
    intro w _
    change Step.gate (wireGate n w Hadamard) = Step.gate (localGateMatrix (.h w))
    apply congrArg (fun M : Matrix (Reg n) (Reg n) ℂ => Step.gate M)
    ext a b
    exact wireGate_apply n w Hadamard a b
  rw [hc]
  exact (localDyadicProgram_run_adjoint_cost n (localHadamard n) ψ).1.trans
    (congrArg (fun M => ApplyGate M ψ) (localProgramMatrix_localHadamard n))
end
noncomputable section
private def experimentFirstWires (n m : ℕ) : Fin n ↪ Fin (simonWireLayout n m) :=
  ⟨fun i => ⟨i.val, by have := i.isLt; unfold simonWireLayout; omega⟩,
    fun _ _ h => Fin.ext (congrArg (fun k : Fin (simonWireLayout n m) => k.val) h)⟩
end
noncomputable section

private theorem experiment_extend_encoding {n m : ℕ} (x : BooleanVec n) (y : BooleanVec m) :
    qtmWireContextExtend (experimentFirstWires n m) (simonEncodePair 0 y)
      ((regBooleanEquiv n).symm x) = simonEncodePair x y := by
  funext i
  by_cases hi : i.val < n
  · let j : Fin n := ⟨i.val,hi⟩
    have hij : experimentFirstWires n m j = i := Fin.ext rfl
    rw [← hij, qtmWireContextExtend_at]
    simp only [regBooleanEquiv_symm_apply, simonEncodePair, simonEncodeContext,
      experimentFirstWires, Function.Embedding.coeFn_mk, dif_pos j.isLt]
    change boolZModEquiv.symm (x j) = decide (x j = 1)
    have hx := (boolZModEquiv.apply_symm_apply (x j))
    cases h : boolZModEquiv.symm (x j)
    · have hx0 : x j = 0 := by simpa [h] using! hx.symm
      simp [hx0]
    · have hx1 : x j = 1 := by simpa [h] using! hx.symm
      simp [hx1]
  · have hout : ¬ ∃ j, experimentFirstWires n m j = i := by
      rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      exact hi (hv ▸ j.isLt)
    rw [qtmWireContextExtend, Function.extend_apply' _ _ i hout]
    simp [simonEncodePair, simonEncodeContext, hi]
end
noncomputable section

private theorem experiment_booleanHadamard_eq_fourier (n : ℕ) :
    relabelGate (regBooleanEquiv n) (HadamardN n) =
      fourierGate (booleanCharacterEquiv n).toEquiv := by
  ext a b
  have h := congrArg (fun M => M ((regBooleanEquiv n).symm a)
    ((regBooleanEquiv n).symm b)) (hadamardN_eq_booleanFourierGate_submatrix n)
  simpa [relabelGate] using! h
end
noncomputable section

private theorem experiment_apply_ket {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (a : I) : ApplyGate U (Qatlib.Foundations.PureStateMath.Ket a) = fun b => U b a := by
  funext b
  simp [ApplyGate, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]
end
noncomputable section

private theorem experiment_hadamard_encode {n m : ℕ} (x : BooleanVec n) (y : BooleanVec m) :
    qtmWireContextEmbed (experimentFirstWires n m) (simonEncodePair 0 y)
      (ApplyGate (HadamardN n) (Qatlib.Foundations.PureStateMath.Ket ((regBooleanEquiv n).symm x))) =
    simonEncodeState (ApplyGate
      (TensorGate (relabelGate (regBooleanEquiv n) (HadamardN n))
        (1 : Matrix (BooleanVec m) (BooleanVec m) ℂ)) (Qatlib.Foundations.PureStateMath.Ket (x,y))) := by
  rw [experiment_apply_ket, experiment_apply_ket]
  simp only [qtmWireContextEmbed, simonEncodeState, Fintype.sum_prod_type,
    TensorGate, Matrix.kroneckerMap_apply, Matrix.one_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Equiv.sum_comp (regBooleanEquiv n)]
  apply Finset.sum_congr rfl
  intro a _
  rw [← experiment_extend_encoding (regBooleanEquiv n a) y]
  simp [relabelGate]
end
noncomputable section

private theorem experiment_hadamard_word_exists (n m : ℕ) :
    ∃ H : List (Phi3Gate (simonWireLayout n m)), H.length = n ∧
      ∀ (x : BooleanVec n) (y : BooleanVec m),
        Run 1 (phi3Compile H) (Qatlib.Foundations.PureStateMath.Ket (simonEncodePair x y)) =
        simonEncodeState (ApplyGate
          (TensorGate (relabelGate (regBooleanEquiv n) (HadamardN n))
            (1 : Matrix (BooleanVec m) (BooleanVec m) ℂ)) (Qatlib.Foundations.PureStateMath.Ket (x,y))) := by
  let D := 2*(n+m)+1
  let e : Fin n ↪ Fin D :=
    ⟨fun i => ⟨i.val, by have := i.isLt; dsimp [D]; omega⟩,
      fun _ _ h => Fin.ext (congrArg (fun k : Fin D => k.val) h)⟩
  let gs := (experimentHadamards n).map (knownWireGateMap e)
  obtain ⟨H,hHlen,hH⟩ := qtmPhi3_translate_table gs
    (knownWireMapList_legal e _ (experimentHadamards_legal n))
  have hmap : gs.map (knownWireGateMap (knownPrefixWires D 3)) =
      (experimentHadamards n).map (knownWireGateMap (experimentFirstWires n m)) := by
    simp only [gs, List.map_map]
    apply List.map_congr_left
    intro g _
    rcases g with ⟨w,U⟩ | ⟨c,t⟩ <;> rfl
  have hHfinal : @phi3Compile (simonWireLayout n m) H =
      reflectionCompile ((experimentHadamards n).map
        (knownWireGateMap (experimentFirstWires n m))) :=
    hH.trans (congrArg reflectionCompile hmap)
  refine ⟨H, ?_, ?_⟩
  · simpa [gs, experimentHadamards] using! hHlen
  · intro x y
    rw [hHfinal, ← experiment_extend_encoding x y,
      ← qtmWireContextEmbed_ket, qtmWireProgram_context _ _ _ (experimentHadamards_legal n),
      experimentHadamards_run, experiment_hadamard_encode]
end
noncomputable section

private theorem experiment_word_encode {n m : ℕ}
    (G : List (Phi3Gate (simonWireLayout n m)))
    (U : Matrix (BooleanVec n × BooleanVec m) (BooleanVec n × BooleanVec m) ℂ)
    (hG : ∀ x y, Run 1 (phi3Compile G) (Qatlib.Foundations.PureStateMath.Ket (simonEncodePair x y)) =
      simonEncodeState (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket (x,y))))
    (ψ : QState (BooleanVec n × BooleanVec m)) :
    Run 1 (phi3Compile G) (simonEncodeState ψ) = simonEncodeState (ApplyGate U ψ) := by
  have hu : ApplyGate U ψ = ∑ p, ψ p • ApplyGate U (Qatlib.Foundations.PureStateMath.Ket p) := by
    conv_lhs => arg 2; rw [state_ket_expansion ψ]
    simp only [ApplyGate, Matrix.mulVec_sum, Matrix.mulVec_smul]
  calc
    _ = ∑ p, ψ p • Run 1 (phi3Compile G) (Qatlib.Foundations.PureStateMath.Ket (simonEncodePair p.1 p.2)) :=
      experiment_run_sum 1 (phi3Compile G) _ _
    _ = ∑ p, ψ p • simonEncodeState (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket p)) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [hG p.1 p.2]
    _ = simonEncodeState (∑ p, ψ p • ApplyGate U (Qatlib.Foundations.PureStateMath.Ket p)) :=
      (experiment_encode_sum _ _).symm
    _ = simonEncodeState (ApplyGate U ψ) := congrArg simonEncodeState hu.symm
end
noncomputable section

theorem simonExperimentWord_exists {n m : ℕ} (f : BooleanVec n → BooleanVec m)
    (Gq : List (Phi3Gate (simonWireLayout n m))) (hq : SimonQueryWordRealizes f Gq) :
    ∃ B, SimonExperimentWordRealizes f B ∧ B.length = Gq.length + 2*n := by
  obtain ⟨H,hHlen,hH⟩ := experiment_hadamard_word_exists n m
  let U : Matrix (BooleanVec n × BooleanVec m) (BooleanVec n × BooleanVec m) ℂ :=
    TensorGate (relabelGate (regBooleanEquiv n) (HadamardN n)) 1
  have hquery : ∀ x y, Run 1 (phi3Compile Gq) (Qatlib.Foundations.PureStateMath.Ket (simonEncodePair x y)) =
      simonEncodeState (ApplyGate (AddOracle f) (Qatlib.Foundations.PureStateMath.Ket (x,y))) := by
    intro x y
    rw [applyGate_addOracle_ket, experiment_encode_ket]
    exact hq x y (fun _ => false)
  refine ⟨H ++ Gq ++ H, ?_, by simp only [List.length_append, hHlen]; omega⟩
  intro x y
  simp only [phi3Compile, List.map_append, run_append]
  change Run 1 (phi3Compile H)
    (Run 1 (phi3Compile Gq) (Run 1 (phi3Compile H) (Qatlib.Foundations.PureStateMath.Ket (simonEncodePair x y)))) = _
  rw [hH, experiment_word_encode Gq (AddOracle f) hquery,
    experiment_word_encode H U hH]
  apply congrArg simonEncodeState
  simp only [simonPreparedCircuit, hiddenSubgroupSamplingCircuit, run_gate, run_query,
    run_nil, U, experiment_booleanHadamard_eq_fourier]
end
noncomputable section
abbrev simonDataWidth (n m : ℕ) : ℕ := 2*(n+m)+1
end
noncomputable section

def simonPack {n m : ℕ} (x : Reg n) (y : Reg m) (c : Reg n) (a : Reg m)
    (b : Bool) : Reg (simonDataWidth n m) := fun i =>
  if h : i.val< n then x ⟨i.val,h⟩
  else if h : i.val< n+m then y ⟨i.val-n,by omega⟩
  else if h : i.val<2*n+m then c ⟨i.val-(n+m),by omega⟩
  else if h : i.val<2*(n+m) then a ⟨i.val-(2*n+m),by omega⟩
  else b
end
noncomputable section
abbrev simonXWire (n m : ℕ) (i : Fin n) : Fin (simonDataWidth n m) :=
    ⟨i.val,by dsimp [simonDataWidth]; omega⟩
end
noncomputable section
abbrev simonYWire (n m : ℕ) (i : Fin m) : Fin (simonDataWidth n m) :=
    ⟨n+i.val,by dsimp [simonDataWidth]; omega⟩
end
noncomputable section
abbrev simonCWire (n m : ℕ) (i : Fin n) : Fin (simonDataWidth n m) :=
    ⟨n+m+i.val,by dsimp [simonDataWidth]; omega⟩
end
noncomputable section
abbrev simonAWire (n m : ℕ) (i : Fin m) : Fin (simonDataWidth n m) :=
    ⟨2*n+m+i.val,by dsimp [simonDataWidth]; omega⟩
end
noncomputable section
abbrev simonDWire (n m : ℕ) : Fin (simonDataWidth n m) := ⟨2*(n+m),by dsimp [simonDataWidth]; omega⟩
end
noncomputable section

@[simp] theorem simonPack_x {n m : ℕ} (x : Reg n) (y : Reg m) (c : Reg n)
    (a : Reg m) (b : Bool) (i : Fin n) : simonPack x y c a b (simonXWire n m i)=x i := by
  simp [simonPack]
end
noncomputable section

@[simp] theorem simonPack_y {n m : ℕ} (x : Reg n) (y : Reg m) (c : Reg n)
    (a : Reg m) (b : Bool) (i : Fin m) : simonPack x y c a b (simonYWire n m i)=y i := by
  simp [simonPack,show ¬n+i.val< n by omega,show n+i.val< n+m by omega]
end
noncomputable section

@[simp] theorem simonPack_c {n m : ℕ} (x : Reg n) (y : Reg m) (c : Reg n)
    (a : Reg m) (b : Bool) (i : Fin n) : simonPack x y c a b (simonCWire n m i)=c i := by
  simp [simonPack,show ¬n+m+i.val< n by omega,
    show ¬n+m+i.val< n+m by omega,show n+m+i.val<2*n+m by omega]
end
noncomputable section

@[simp] theorem simonPack_a {n m : ℕ} (x : Reg n) (y : Reg m) (c : Reg n)
    (a : Reg m) (b : Bool) (i : Fin m) : simonPack x y c a b (simonAWire n m i)=a i := by
  simp [simonPack,show ¬2*n+m+i.val< n by omega,
    show ¬2*n+m+i.val< n+m by omega,show ¬2*n+m+i.val<2*n+m by omega,
    show 2*n+m+i.val<2*(n+m) by omega]
end
noncomputable section

@[simp] theorem simonPack_d {n m : ℕ} (x : Reg n) (y : Reg m) (c : Reg n)
    (a : Reg m) (b : Bool) : simonPack x y c a b (simonDWire n m)=b := by
  simp [simonPack,show ¬2*(n+m)< n by omega,
    show ¬2*(n+m)< n+m by omega,show ¬2*(n+m)<2*n+m by omega]
end
noncomputable section

theorem simonReg_ext {n m : ℕ} {r t : Reg (simonDataWidth n m)}
    (hx : ∀ i, r (simonXWire n m i)=t (simonXWire n m i))
    (hy : ∀ i, r (simonYWire n m i)=t (simonYWire n m i))
    (hc : ∀ i, r (simonCWire n m i)=t (simonCWire n m i))
    (ha : ∀ i, r (simonAWire n m i)=t (simonAWire n m i))
    (hd : r (simonDWire n m)=t (simonDWire n m)) : r=t := by
  funext j
  by_cases h : j.val< n
  · exact hx ⟨j.val,h⟩
  by_cases h' : j.val< n+m
  · have e : j=simonYWire n m ⟨j.val-n,by omega⟩ := Fin.ext (by dsimp; omega)
    rw [e]; exact hy _
  by_cases h'' : j.val<2*n+m
  · have e : j=simonCWire n m ⟨j.val-(n+m),by omega⟩ := Fin.ext (by dsimp; omega)
    rw [e]; exact hc _
  by_cases h''' : j.val<2*(n+m)
  · have e : j=simonAWire n m ⟨j.val-(2*n+m),by omega⟩ := Fin.ext (by dsimp; omega)
    rw [e]; exact ha _
  · have e : j=simonDWire n m := Fin.ext (by dsimp [simonDataWidth] at *; omega)
    rw [e]; exact hd
end
noncomputable section

def simonCopyGate (n m : ℕ) (rev : Bool) (i : Fin n) : ReflectionGate (simonDataWidth n m) :=
  if rev then .inr (simonCWire n m i,simonXWire n m i)
  else .inr (simonXWire n m i,simonCWire n m i)
end
noncomputable section
def simonCopySteps (n m : ℕ) (rev : Bool) : List (ReflectionGate (simonDataWidth n m)) :=
  (List.finRange n).map (simonCopyGate n m rev)
end
noncomputable section

theorem simonCopySteps_legal (n m : ℕ) (rev : Bool) : reflectionLegal (simonCopySteps n m rev) := by
  rintro g hg
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hg
  cases rev <;> simp only [simonCopyGate,Bool.false_eq_true,if_false,if_true,reflectionGateLegal]
  all_goals intro h; have e:=congrArg Fin.val h; dsimp at e; omega
end
noncomputable section

def simonCopyBasis {n m : ℕ} (x : Reg n) (y : Reg m) (c : Reg n) (a : Reg m)
    (b rev : Bool) (is : List (Fin n)) : Reg (simonDataWidth n m) :=
  simonPack (fun j => if rev && decide (j∈is) then x j ^^ c j else x j) y
    (fun j => if !rev && decide (j∈is) then c j ^^ x j else c j) a b
end
noncomputable section

theorem simonCopyGate_action {n m : ℕ} (x : Reg n) (y : Reg m) (c : Reg n)
    (a : Reg m) (b rev : Bool) (is : List (Fin n)) (i : Fin n) (hi : i∉is) :
    ApplyGate (reflectionGateMatrix (simonCopyGate n m rev i))
      (Qatlib.Foundations.PureStateMath.Ket (simonCopyBasis x y c a b rev is)) =
    Qatlib.Foundations.PureStateMath.Ket (simonCopyBasis x y c a b rev (i::is)) := by
  cases rev <;> simp only [simonCopyGate,Bool.false_eq_true,if_false,if_true,reflectionGateMatrix]
  all_goals
    rw [applyGate_cnotGate_ket _ _ _ (by intro h; have e:=congrArg Fin.val h; dsimp at e; omega)]
    congr 1
    apply simonReg_ext
  all_goals
    intros
    simp only [simonCopyBasis,simonPack_x,simonPack_y,simonPack_c,simonPack_a,simonPack_d,
      Bool.false_and,Bool.true_and,Bool.not_false,Bool.not_true,ite_false,Bool.false_eq_true]
    simp (disch := omega) [Function.update_apply,simonPack_x,simonPack_y,simonPack_c,
      simonPack_a,simonPack_d,simonXWire,simonYWire,simonCWire,simonAWire,simonDWire,
      Fin.mk.injEq,hi,Bool.xor_comm,Fin.val_inj]
  all_goals first | omega | (split_ifs <;> simp_all )
end
noncomputable section

theorem simonCopyWord_action {n m : ℕ} (x : Reg n) (y : Reg m) (c : Reg n)
    (a : Reg m) (b rev : Bool) (is : List (Fin n)) (hi : is.Nodup) :
    Run 1 (reflectionCompile (is.map (simonCopyGate n m rev))) (Qatlib.Foundations.PureStateMath.Ket (simonPack x y c a b)) =
      Qatlib.Foundations.PureStateMath.Ket (simonCopyBasis x y c a b rev is) := by
  induction is using List.reverseRecOn with
  | nil => simp [simonCopyBasis,reflectionCompile]
  | append_singleton is i ih =>
    have hd := List.nodup_append.mp hi
    have hin : i∉is := by
      intro h
      exact hd.2.2 i h i (by simp) rfl
    rw [List.map_append,reflectionCompile_append,run_append,ih hd.1]
    simp only [List.map_cons,List.map_nil,reflectionCompile,List.map_cons,List.map_nil,
      run_gate,run_nil]
    rw [simonCopyGate_action x y c a b rev is i hin]
    congr 1
    simp [simonCopyBasis,or_comm]
end
noncomputable section

theorem simonCopySteps_action {n m : ℕ} (x : Reg n) (y : Reg m) (c : Reg n)
    (a : Reg m) (b rev : Bool) :
    Run 1 (reflectionCompile (simonCopySteps n m rev)) (Qatlib.Foundations.PureStateMath.Ket (simonPack x y c a b)) =
      Qatlib.Foundations.PureStateMath.Ket (simonPack (if rev then fun i => x i ^^ c i else x) y
        (if rev then c else fun i => c i ^^ x i) a b) := by
  rw [simonCopySteps,simonCopyWord_action x y c a b rev _ (List.nodup_finRange n)]
  cases rev <;> simp [simonCopyBasis]
end
noncomputable section

def simonFullPack {n m : ℕ} (x : Reg n) (y : Reg m) (c : Reg n) (a : Reg m) (b : Bool) :
    Reg (simonWireLayout n m) :=
  knownWireExtend (knownPrefixWires (simonDataWidth n m) 3) (simonPack x y c a b)
end
noncomputable section

theorem simonTranslate_exists {n m : ℕ} (gs : List (ReflectionGate (simonDataWidth n m)))
    (hg : reflectionLegal gs) :
    ∃ ws : List (Phi3Gate (simonWireLayout n m)), ws.length=gs.length ∧
      ∀ ψ : QState (Reg (simonDataWidth n m)),
        Run 1 (phi3Compile ws) (knownWireEmbed (knownPrefixWires (simonDataWidth n m) 3) ψ) =
          knownWireEmbed (knownPrefixWires (simonDataWidth n m) 3)
            (Run 1 (reflectionCompile gs) ψ) := by
  obtain ⟨ws,hlen,hcompile⟩ := qtmPhi3_translate_table gs hg
  refine ⟨ws,hlen,fun ψ => ?_⟩
  change Run 1 (phi3Compile ws) (knownWireEmbed (knownPrefixWires (simonDataWidth n m) 3) ψ) = _
  simpa only [hcompile] using!
      knownWireProgram_embed (knownPrefixWires (simonDataWidth n m) 3) gs hg ψ
end
noncomputable section

theorem simonCopyPhi3_exists (n m : ℕ) (rev : Bool) :
    ∃ ws : List (Phi3Gate (simonWireLayout n m)), ws.length=n ∧
      ∀ (x : Reg n) (y : Reg m) (c : Reg n) (a : Reg m) (b : Bool),
        Run 1 (phi3Compile ws) (Qatlib.Foundations.PureStateMath.Ket (simonFullPack x y c a b)) =
          Qatlib.Foundations.PureStateMath.Ket (simonFullPack (if rev then fun i => x i ^^ c i else x) y
            (if rev then c else fun i => c i ^^ x i) a b) := by
  obtain ⟨ws,hlen,hr⟩ := simonTranslate_exists (simonCopySteps n m rev)
    (simonCopySteps_legal n m rev)
  refine ⟨ws,by simpa [simonCopySteps] using! hlen,?_⟩
  intro x y c a b
  unfold simonFullPack
  rw [← knownWireEmbed_ket,hr,simonCopySteps_action,knownWireEmbed_ket]
end
noncomputable section

noncomputable def simonEqualityFlips (m : ℕ) : List (ReflectionGate (m+1+(m-1))) :=
  knownFlipSteps ((List.finRange m).map (multiKnownControlWire m))
end
noncomputable section

theorem simonEqualityFlips_action (m : ℕ) (y : Reg m) (b : Bool) (a : Reg (m-1)) :
    Run 1 (reflectionCompile (simonEqualityFlips m))
      (Qatlib.Foundations.PureStateMath.Ket ((multiKnownSplit m).symm ((y,b),a))) =
    Qatlib.Foundations.PureStateMath.Ket ((multiKnownSplit m).symm ((fun i => !(y i),b),a)) := by
  have hinj : Function.Injective (multiKnownControlWire m) := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun q : Fin (m+1+(m-1)) => q.val) h
  rw [simonEqualityFlips,knownFlipSteps_action _ ((List.nodup_finRange m).map hinj)]
  congr 1
  apply (multiKnownSplit m).injective
  rw [Equiv.apply_symm_apply]
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext i
    change (if multiKnownControlWire m i ∈ _ then _ else _) = _
    have hm : multiKnownControlWire m i ∈ (List.finRange m).map (multiKnownControlWire m) :=
      List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩
    rw [if_pos hm]
    change Bool.not ((multiKnownSplit m).symm ((y,b),a) (multiKnownControlWire m i)) = Bool.not
        (y i)
    rw [multiKnownJoin_control]
  · change (if multiKnownTargetWire m ∈ _ then _ else _) = _
    have h : multiKnownTargetWire m ∉ (List.finRange m).map (multiKnownControlWire m) := by
      rintro h
      obtain ⟨i,_,hi⟩ := List.mem_map.mp h
      have hv:=congrArg Fin.val hi
      dsimp at hv
      omega
    rw [if_neg h]
    change (multiKnownSplit m).symm ((y,b),a) (multiKnownTargetWire m) = b
    exact multiKnownJoin_target m y b a
  · funext i
    change (if multiKnownWorkWire m i ∈ _ then _ else _) = _
    have h : multiKnownWorkWire m i ∉ (List.finRange m).map (multiKnownControlWire m) := by
      rintro h
      obtain ⟨j,_,hj⟩ := List.mem_map.mp h
      have hv:=congrArg Fin.val hj
      dsimp at hv
      omega
    rw [if_neg h]
    change (multiKnownSplit m).symm ((y,b),a) (multiKnownWorkWire m i) = a i
    exact multiKnownJoin_work m y b a i
end
noncomputable section

theorem simonEqualityLocal_exists (m : ℕ) :
    ∃ gs : List (ReflectionGate (m+1+(m-1))), reflectionLegal gs ∧
      gs.length=2*m+multiKnownCost m ∧
      ∀ (y : Reg m) (b : Bool),
        Run 1 (reflectionCompile gs)
          (Qatlib.Foundations.PureStateMath.Ket ((multiKnownSplit m).symm ((y,b),fun _ => false))) =
        Qatlib.Foundations.PureStateMath.Ket ((multiKnownSplit m).symm ((y,b ^^ decide (y=fun _ => false)),fun _ => false)) := by
  let p := knownQubitAnglesOfUnitary PauliX
  have hp : knownQubitUnitary p=PauliX :=
    (knownQubitEuler_explicit_angles_cover_unitaries PauliX pauliX_unitary).1
  let fs := simonEqualityFlips m
  let gs := fs ++ multiKnownSteps m p ++ fs
  have hf : reflectionLegal fs := knownFlipSteps_legal _
  refine ⟨gs,(reflectionLegal_append _ _).mpr
    ⟨(reflectionLegal_append _ _).mpr ⟨hf,multiKnownSteps_legal m p⟩,hf⟩,?_,?_⟩
  · simp [gs,fs,simonEqualityFlips,knownFlipSteps,multiKnownSteps_length]; omega
  · intro y b
    simp only [gs,fs,reflectionCompile_append,run_append]
    rw [simonEqualityFlips_action,multiKnown_basis_action,hp]
    have ha : allControlTrue m (fun i => !(y i)) = decide (y=fun _ => false) := by
      rw [allControlTrue_eq_decide]
      congr 1
      simp [funext_iff]
    rw [ha]
    by_cases hy : y=fun _ => false <;> cases b <;>
      simp [hy,PauliX,permMatrix,Matrix.one_apply,
        simonEqualityFlips_action]
end
noncomputable section

def simonEqualityWires (n m : ℕ) : Fin (m+1+(m-1)) ↪ Fin (simonDataWidth n m) where
  toFun i := if h : i.val< m then simonYWire n m ⟨i.val,h⟩
    else if h : i.val=m then simonDWire n m
    else simonAWire n m ⟨i.val-(m+1),by omega⟩
  inj' i j h := by
    dsimp at h
    split_ifs at h <;> have hv:=congrArg Fin.val h <;> apply Fin.ext <;> dsimp at hv <;> omega
end
noncomputable section

@[simp] theorem simonEqualityWires_control (n m : ℕ) (i : Fin m) :
    simonEqualityWires n m (multiKnownControlWire m i)=simonYWire n m i := by
  simp [simonEqualityWires]
end
noncomputable section

@[simp] theorem simonEqualityWires_target (n m : ℕ) :
    simonEqualityWires n m (multiKnownTargetWire m)=simonDWire n m := by
  simp [simonEqualityWires]
end
noncomputable section

@[simp] theorem simonEqualityWires_work (n m : ℕ) (i : Fin (m-1)) :
    simonEqualityWires n m (multiKnownWorkWire m i)=simonAWire n m ⟨i.val,by omega⟩ := by
  simp [simonEqualityWires,show ¬ m+1+i.val< m by omega,show ¬ m+1+i.val=m by omega]
end
noncomputable section

theorem simonEqualityWires_not_x (n m : ℕ) (i : Fin (m+1+(m-1))) (j : Fin n) :
    simonEqualityWires n m i ≠ simonXWire n m j := by
  intro h
  dsimp [simonEqualityWires] at h
  split_ifs at h <;> have hv:=congrArg Fin.val h <;> dsimp at hv <;> omega
end
noncomputable section

theorem simonEqualityWires_not_c (n m : ℕ) (i : Fin (m+1+(m-1))) (j : Fin n) :
    simonEqualityWires n m i ≠ simonCWire n m j := by
  intro h
  dsimp [simonEqualityWires] at h
  split_ifs at h <;> have hv:=congrArg Fin.val h <;> dsimp at hv <;> omega
end
noncomputable section

theorem simonEqualityWires_not_unused (n m : ℕ) (i : Fin (m+1+(m-1)))
    (j : Fin m) (hj : ¬j.val< m-1) : simonEqualityWires n m i≠simonAWire n m j := by
  intro h
  dsimp [simonEqualityWires] at h
  split_ifs at h <;> have hv:=congrArg Fin.val h <;> dsimp at hv <;> omega
end
noncomputable section

theorem simonEqualityContext {n m : ℕ} (x : Reg n) (y y' : Reg m) (c : Reg n)
    (b b' : Bool) :
    qtmWireContextExtend (simonEqualityWires n m) (simonPack x y c (fun _=>false) b)
      ((multiKnownSplit m).symm ((y',b'),fun _=>false)) =
      simonPack x y' c (fun _=>false) b' := by
  apply simonReg_ext
  · intro i
    rw [qtmWireContextExtend,Function.extend_apply' _ _ _
      (by rintro ⟨j,h⟩; exact simonEqualityWires_not_x n m j i h)]
    simp
  · intro i
    rw [← simonEqualityWires_control n m i,qtmWireContextExtend_at,multiKnownJoin_control]
    simp
  · intro i
    rw [qtmWireContextExtend,Function.extend_apply' _ _ _
      (by rintro ⟨j,h⟩; exact simonEqualityWires_not_c n m j i h)]
    simp
  · intro i
    by_cases hi : i.val< m-1
    · let j : Fin (m-1) := ⟨i.val,hi⟩
      have he : simonEqualityWires n m (multiKnownWorkWire m j)=simonAWire n m i := by
        rw [simonEqualityWires_work]
      rw [← he,qtmWireContextExtend_at,multiKnownJoin_work]
      simp
    · rw [qtmWireContextExtend,Function.extend_apply' _ _ _
        (by rintro ⟨j,h⟩; exact simonEqualityWires_not_unused n m j i hi h)]
      simp
  · rw [← simonEqualityWires_target n m,qtmWireContextExtend_at,multiKnownJoin_target]
    simp
end
noncomputable section

theorem simonEqualityData_exists (n m : ℕ) :
    ∃ gs : List (ReflectionGate (simonDataWidth n m)), reflectionLegal gs ∧
      gs.length=2*m+multiKnownCost m ∧
      ∀ (x : Reg n) (y : Reg m) (c : Reg n) (b : Bool),
        Run 1 (reflectionCompile gs) (Qatlib.Foundations.PureStateMath.Ket (simonPack x y c (fun _=>false) b)) =
          Qatlib.Foundations.PureStateMath.Ket (simonPack x y c (fun _=>false) (b ^^ decide (y=fun _=>false))) := by
  obtain ⟨ls,hl,hlen,hr⟩ := simonEqualityLocal_exists m
  let e := simonEqualityWires n m
  refine ⟨ls.map (knownWireGateMap e),knownWireMapList_legal e ls hl,by simpa using! hlen,?_⟩
  intro x y c b
  let ctx := simonPack x y c (fun _=>false) b
  have he := simonEqualityContext x y y c b b
  rw [← he,← qtmWireContextEmbed_ket,qtmWireProgram_context e ctx ls hl,hr,
    qtmWireContextEmbed_ket,simonEqualityContext]
end
noncomputable section

theorem simonEqualityPhi3_exists (n m : ℕ) :
    ∃ ws : List (Phi3Gate (simonWireLayout n m)), ws.length=2*m+multiKnownCost m ∧
      ∀ (x : Reg n) (y : Reg m) (c : Reg n) (b : Bool),
        Run 1 (phi3Compile ws) (Qatlib.Foundations.PureStateMath.Ket (simonFullPack x y c (fun _=>false) b)) =
          Qatlib.Foundations.PureStateMath.Ket (simonFullPack x y c (fun _=>false) (b ^^ decide (y=fun _=>false))) := by
  obtain ⟨gs,hg,hlen,hr⟩ := simonEqualityData_exists n m
  obtain ⟨ws,hwlen,hwr⟩ := simonTranslate_exists gs hg
  refine ⟨ws,hwlen.trans hlen,?_⟩
  intro x y c b
  unfold simonFullPack
  rw [← knownWireEmbed_ket,hwr,hr,knownWireEmbed_ket]
end
noncomputable section

@[simp] theorem simonBoolDecode (a : ZMod 2) : boolZModEquiv.symm a = decide (a=1) := by
  obtain ⟨b,rfl⟩ := boolZModEquiv.surjective a
  rw [Equiv.symm_apply_apply]
  cases b <;> simp
end
noncomputable section

@[simp] theorem simonBoolEncode (b : Bool) : decide (boolZModEquiv b=1)=b := by
  cases b <;> simp
end
noncomputable section

@[simp] theorem simonBoolDecodeAdd (a b : ZMod 2) :
    boolZModEquiv.symm (a+b) = (boolZModEquiv.symm a ^^ boolZModEquiv.symm b) := by
  obtain ⟨a,rfl⟩ := boolZModEquiv.surjective a
  obtain ⟨b,rfl⟩ := boolZModEquiv.surjective b
  cases a <;> cases b <;> decide
end
noncomputable section

@[simp] theorem simonFullPack_apply {n m : ℕ} (x : Reg n) (y : Reg m) (c : Reg n)
    (a : Reg m) (b : Bool) (i : Fin (simonWireLayout n m)) :
    simonFullPack x y c a b i = if h : i.val<simonDataWidth n m then
      simonPack x y c a b ⟨i.val,h⟩ else false := by
  dsimp [simonWireLayout] at i ⊢
  by_cases hi : i.val<simonDataWidth n m
  · let j : Fin (simonDataWidth n m) := ⟨i.val,hi⟩
    have he : i=knownPrefixWires (simonDataWidth n m) 3 j := Fin.ext rfl
    rw [he]
    change knownWireExtend (knownPrefixWires (simonDataWidth n m) 3) (simonPack x y c a b)
      (knownPrefixWires (simonDataWidth n m) 3 j) = _
    rw [knownWireExtend_at]
    simp [hi,j,knownPrefixWires]
  · have he : ¬∃ j, knownPrefixWires (simonDataWidth n m) 3 j=i := by
      rintro ⟨j,h⟩
      have hv:=congrArg Fin.val h
      dsimp [knownPrefixWires] at hv
      omega
    change Function.extend (knownPrefixWires (simonDataWidth n m) 3) (simonPack x y c a b)
        (fun _=>false) i = _
    rw [Function.extend_apply' _ _ _ he,dif_neg hi]
end
noncomputable section

theorem simonEncodeContext_pack {n m : ℕ} (x x' : Reg n) (y y' : Reg m)
    (c : Reg n) (a : Reg m) (b : Bool) :
    simonEncodeContext (regBooleanEquiv n x') (regBooleanEquiv m y') (simonFullPack x y c a b) =
      simonFullPack x' y' c a b := by
  funext i
  simp only [simonEncodeContext,simonFullPack_apply,regBooleanEquiv_apply]
  dsimp [simonDataWidth] at *
  split_ifs
  all_goals first | omega | simp (disch := omega) only [simonPack,dif_pos,dif_neg]
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp only [decide_eq_true_eq]
  all_goals rw [← boolZModEquiv_true]
  all_goals exact boolZModEquiv.injective.eq_iff
end
noncomputable section

def simonFBits {n m : ℕ} (f : BooleanVec n → BooleanVec m) (x : Reg n) : Reg m :=
  (regBooleanEquiv m).symm (f (regBooleanEquiv n x))
end
noncomputable section

theorem simonQuery_pack {n m : ℕ} (f : BooleanVec n → BooleanVec m)
    (Gq : List (Phi3Gate (simonWireLayout n m))) (hq : SimonQueryWordRealizes f Gq)
    (x : Reg n) (y : Reg m) (c : Reg n) (a : Reg m) (b : Bool) :
    Run 1 (phi3Compile Gq) (Qatlib.Foundations.PureStateMath.Ket (simonFullPack x y c a b)) =
      Qatlib.Foundations.PureStateMath.Ket (simonFullPack x (fun i => y i ^^ simonFBits f x i) c a b) := by
  have h:=hq (regBooleanEquiv n x) (regBooleanEquiv m y) (simonFullPack x y c a b)
  rw [simonEncodeContext_pack] at h
  have he : regBooleanEquiv m (fun i => y i ^^ simonFBits f x i) =
      regBooleanEquiv m y+f (regBooleanEquiv n x) := by
    apply (regBooleanEquiv m).symm.injective
    rw [Equiv.symm_apply_apply]
    funext i
    change (y i ^^ boolZModEquiv.symm (f (regBooleanEquiv n x) i)) =
      boolZModEquiv.symm (boolZModEquiv (y i)+f (regBooleanEquiv n x) i)
    rw [simonBoolDecodeAdd,Equiv.symm_apply_apply]
  rw [← he,simonEncodeContext_pack] at h
  exact h
end
noncomputable section

@[simp] theorem simonPhi3Compile_append {L : ℕ} (xs ys : List (Phi3Gate L)) :
    phi3Compile (xs++ys)=phi3Compile xs++phi3Compile ys := List.map_append
end
noncomputable section

@[simp] theorem simonXor_cancel_left (a b : Bool) : (a ^^ (a ^^ b))=b := by
  cases a <;> cases b <;> rfl
end
noncomputable section

theorem simonXor_eq_false {m : ℕ} (y z : Reg m) :
    (fun i => y i ^^ z i) = (fun _=>false) ↔ y=z := by
  constructor
  · intro h
    funext i
    have hi:=congrFun h i
    cases hy:y i <;> cases hz:z i <;> simp_all
  · rintro rfl
    simp
end
noncomputable section

theorem simonVerifyWord_exists {n m : ℕ} (f : BooleanVec n → BooleanVec m)
    (Gq : List (Phi3Gate (simonWireLayout n m))) (hq : SimonQueryWordRealizes f Gq) :
    ∃ ws : List (Phi3Gate (simonWireLayout n m)),
      ws.length=4*Gq.length+6*n+(2*m+multiKnownCost m) ∧
      ∀ x : Reg n,
        Run 1 (phi3Compile ws) (Qatlib.Foundations.PureStateMath.Ket (simonFullPack x (fun _=>false) (fun _=>false) (fun _=>false) false)) =
          Qatlib.Foundations.PureStateMath.Ket (simonFullPack x (fun _=>false) (fun _=>false) (fun _=>false)
            (decide (f (regBooleanEquiv n x)=f 0))) := by
  obtain ⟨F,hFlen,hF⟩ := simonCopyPhi3_exists n m false
  obtain ⟨R,hRlen,hR⟩ := simonCopyPhi3_exists n m true
  obtain ⟨E,hElen,hE⟩ := simonEqualityPhi3_exists n m
  simp only [Bool.false_eq_true,ite_false,ite_true] at hF hR
  let ws := Gq++F++R++Gq++R++E++Gq++R++Gq++R++F
  refine ⟨ws,by simp only [ws,List.length_append,hFlen,hRlen,hElen]; omega,?_⟩
  intro x
  simp only [ws,simonPhi3Compile_append,run_append]
  rw [simonQuery_pack f Gq hq,hF,hR]
  simp only [Bool.false_xor,Bool.xor_self]
  rw [simonQuery_pack f Gq hq,hR]
  simp only [Bool.false_xor]
  rw [hE,simonQuery_pack f Gq hq,hR]
  simp only [Bool.false_xor,Bool.xor_self,Bool.xor_comm]
  rw [simonQuery_pack f Gq hq,hR,hF]
  simp only [Bool.false_xor,Bool.xor_self]
  simp only [simonXor_cancel_left,Bool.xor_self]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,simonXor_eq_false]
  have hz : regBooleanEquiv n (fun _=>false)=(0 : BooleanVec n) := by ext; simp
  simp only [simonFBits,hz,Equiv.apply_eq_iff_eq_symm_apply]
  simp only [Equiv.symm_symm,Equiv.apply_symm_apply]
end
noncomputable section

@[simp] theorem simonFullPack_zero (n m : ℕ) :
    simonFullPack (fun _ : Fin n=>false) (fun _ : Fin m=>false)
      (fun _=>false) (fun _=>false) false = (fun _=>false) := by
  funext i
  simp [simonFullPack_apply,simonPack]
end
noncomputable section

theorem simonFullPack_canonical {n m : ℕ} (x : Reg n) (y : Reg m) :
    simonFullPack x y (fun _=>false) (fun _=>false) false =
      simonEncodePair (regBooleanEquiv n x) (regBooleanEquiv m y) := by
  unfold simonEncodePair
  rw [← simonFullPack_zero n m,simonEncodeContext_pack]
end
noncomputable section

theorem simonFullPack_decision {n m : ℕ} (x : Reg n) (b : Bool) :
    simonFullPack x (fun _ : Fin m=>false) (fun _=>false) (fun _=>false) b =
      fun i => if i.val=2*(n+m) then b
        else simonEncodePair (regBooleanEquiv n x) 0 i := by
  have hz : regBooleanEquiv m (fun _=>false)=(0 : BooleanVec m) := by ext; simp
  rw [← hz,← simonFullPack_canonical]
  funext i
  simp only [simonFullPack_apply]
  dsimp [simonDataWidth] at *
  by_cases hd : i.val=2*(n+m)
  · simp [hd,simonPack,show ¬2*(n+m)<n by omega,show ¬2*(n+m)<n+m by omega,
      show ¬2*(n+m)<2*n+m by omega]
  · simp only [hd,if_false]
    split_ifs with hi
    · simp only [simonPack]
      split_ifs <;> first | rfl | omega
    · rfl
end
noncomputable section

theorem simonVerifyWord_realizes {n m : ℕ} (f : BooleanVec n → BooleanVec m)
    (Gq : List (Phi3Gate (simonWireLayout n m))) (Tf : ℕ)
    (hq : SimonQueryWordRealizes f Gq) (hlen : Gq.length≤Tf) :
    ∃ ws : List (Phi3Gate (simonWireLayout n m)), SimonVerifyWordRealizes f ws ∧
      ws.length≤4*Tf+simonVerifyPadGates n m := by
  obtain ⟨ws,hwlen,hwr⟩ := simonVerifyWord_exists f Gq hq
  refine ⟨ws,?_,?_⟩
  · intro cand
    have h:=hwr ((regBooleanEquiv n).symm cand)
    have hz : regBooleanEquiv m (fun _=>false)=(0 : BooleanVec m) := by ext; simp
    rw [simonFullPack_canonical,hz,Equiv.apply_symm_apply,simonFullPack_decision,
      Equiv.apply_symm_apply] at h
    exact h
  · rw [hwlen]
    unfold simonVerifyPadGates multiKnownCost
    split_ifs <;> omega
end
noncomputable section

theorem simonStandard_expected_gate_bound {n m : ℕ} (f : BooleanVec n → BooleanVec m)
    (s : Reg n) (hp : BooleanSimonPromise f (regBooleanEquiv n s))
    (B Wv : List (Phi3Gate (simonWireLayout n m))) (Tf : ℕ)
    (hB : B.length≤Tf+simonExperimentPadGates n)
    (hW : Wv.length≤4*Tf+simonVerifyPadGates n m) :
    (generalUnboundedTime (simonVerifiedRetryKernel f) (Sum.inr ()) : ℝ≥0∞) *
      ((n+1)*B.length+Wv.length+simonDecodePadGates n : ℕ) ≤
    (2 : ℝ≥0∞)*((n+1)*(Tf+simonExperimentPadGates n)+
      (4*Tf+simonVerifyPadGates n m)+simonDecodePadGates n : ℕ) := by
  have ht := (simon_verified_unbounded_expected_queries_and_cutoff n (BooleanVec m) f s hp).2.1
  apply mul_le_mul' ht
  exact_mod_cast Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left (n+1) hB) hW)
    (simonDecodePadGates n)
end
noncomputable section

theorem clause4_complete : Clause4StandardModelBridge := by
  intro n m f s hp Gq Tf hq hlen
  obtain ⟨B,hB,hBlen⟩ := simonExperimentWord_exists f Gq hq
  obtain ⟨Wv,hW,hWlen⟩ := simonVerifyWord_realizes f Gq Tf hq hlen
  have hBL : B.length≤Tf+simonExperimentPadGates n := by
    rw [hBlen]
    exact Nat.add_le_add_right hlen _
  exact ⟨B,Wv,hB,hW,hBL,hWlen,simonStandard_expected_gate_bound f s hp B Wv Tf hBL hWlen⟩
end
noncomputable section

theorem clause4_complete_outputPriced
    (n m : ℕ) (f : BooleanVec n → BooleanVec m) (s : Reg n)
    (hp : BooleanSimonPromise f (regBooleanEquiv n s))
    (Gq : List (Phi3Gate (simonWireLayout n m))) (Tf : ℕ)
    (hq : SimonQueryWordRealizes f Gq) (hlen : Gq.length ≤ Tf) (hout : m ≤ Tf) :
    ∃ (B Wv : List (Phi3Gate (simonWireLayout n m))),
      SimonExperimentWordRealizes f B ∧ SimonVerifyWordRealizes f Wv ∧
      B.length ≤ Tf + simonExperimentPadGates n ∧
      Wv.length ≤ 4*Tf + simonVerifyPadGates n m ∧
      (generalUnboundedTime (simonVerifiedRetryKernel f) (Sum.inr ()) : ℝ≥0∞) *
        ((n+1)*B.length + Wv.length + simonDecodePadGates n : ℕ) ≤
      (2 : ℝ≥0∞)*((n+37)*Tf + 2*n*(n+1) + 6*n + 6 + simonDecodePadGates n : ℕ) := by
  obtain ⟨B,Wv,hB,hW,hBL,hWL,hcost⟩ :=
    clause4_complete n m f s hp Gq Tf hq hlen
  refine ⟨B,Wv,hB,hW,hBL,hWL,hcost.trans ?_⟩
  have hnat : (n+1)*(Tf+simonExperimentPadGates n) +
      (4*Tf+simonVerifyPadGates n m) + simonDecodePadGates n ≤
      (n+37)*Tf + 2*n*(n+1) + 6*n + 6 + simonDecodePadGates n := by
    unfold simonExperimentPadGates simonVerifyPadGates
    nlinarith only [hout]
  exact mul_le_mul_right (by exact_mod_cast hnat) (2 : ℝ≥0∞)
end
end Qatlib.Papers.QPowerSimon97.Recovery
