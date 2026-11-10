/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.SequentialProgram
import Qatlib.Papers.MonteCarloInt20.MainResults.ExecutedAccuracy
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedWord
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedAccuracy
open Qatlib.Papers.MonteCarloInt20.MainResults.FlagRotation
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerCircuit
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerOracle
open Qatlib.Papers.MonteCarloInt20.MainResults.ActualNested
open Qatlib.Papers.MonteCarloInt20.MainResults.SequentialStore
open Qatlib.Papers.MonteCarloInt20.MainResults.SequentialLoop
open Qatlib.Papers.MonteCarloInt20.MainResults.Sequential

namespace Qatlib.Papers.MonteCarloInt20.MainResults.SequentialReadout

noncomputable local instance workDecision (n s d p : ℕ) : DecidableEq (Work n s d p) :=
    instDecidableEqProd
noncomputable local instance sampleDecision (n s d p : ℕ) : DecidableEq (Reg s × Work n s d p) :=
    instDecidableEqProd
noncomputable local instance fullDecision (n s d p : ℕ) :
    DecidableEq ((Reg s × Work n s d p) × Bool) := instDecidableEqProd
noncomputable local instance outerDecision (n s d p N : ℕ) :
    DecidableEq (Inner N ((Reg s × Work n s d p) × Bool)) := instDecidableEqProd

theorem previous_matrix_unitary {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (g : ℝ → ℝ)
    (hg : ∀ v : Codes d p,g (∑ i : Reg d,Qatlib.Papers.MonteCarloInt20.MainResults.TermCode.decodeCode p (v i)) ∈ Set.Icc (0:ℝ) 1) :
    runMatrix (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode) (previousCircuit (s:=s) (d:=d) (p:=p) a c seed g) ∈
      unitaryGroup ((Reg s × Work n s d p) × Bool) ℂ := by
  rw [previousCircuit_eval]
  apply cleanFlagPreparation_unitary
  · intro j
    exact runMatrix_unitary (oracle termCode j) _ (oracle_unitary termCode j)
        (loopCircuit_unitary (p:=p) a c seed j (allTerms d))
  · exact fun v => hg v.2.2

theorem previous_ae_accuracy {n s d p : ℕ} (hd : 0 < d) (N : ℕ) (hN : 2 ≤ N)
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (g : ℝ → ℝ)
    (hg : ∀ v : Codes d p,g (∑ i : Reg d,Qatlib.Papers.MonteCarloInt20.MainResults.TermCode.decodeCode p (v i)) ∈ Set.Icc (0:ℝ) 1) :
    8/Real.pi^2 ≤ ∑ z ∈ Finset.univ.filter (fun z : Fin N =>
      |aeEstimate N z-finiteTarget a c seed termCode ((2:ℝ)^d) g| ≤
        outerWindow N (finiteTarget a c seed termCode ((2:ℝ)^d) g)),
      (aeLaw (I:=(Reg s × Work n s d p) × Bool) N (runMatrix (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode) (previousCircuit (s:=s) (d:=d) (p:=p) a c seed g))
        (previousSeed n s d p seed) (Finset.univ.filter (fun v => v.2=true))
        (previous_matrix_unitary a c seed termCode g hg) hN).prob z := by
  have h := (prepared_ae_bhmt_error_and_endpoints (I:=(Reg s × Work n s d p) × Bool) N hN
    (runMatrix (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode) (previousCircuit (s:=s) (d:=d) (p:=p) a c seed g))
    (previousSeed n s d p seed) (Finset.univ.filter (fun v => v.2=true))
    (previous_matrix_unitary a c seed termCode g hg)).1
  rw [preparedAAState,previous_flag_born hd a c seed termCode g hg] at h
  exact h

def retained {I : Type} [Fintype I] [DecidableEq I] (O : Matrix I I ℂ) (C : Circuit I) : GateWord (Matrix I I ℂ) :=
  C.map (fun s => match s with | .query => (.inputForward,O) | .gate U => (.fixed,U))

theorem retained_eval {I : Type} [Fintype I] [DecidableEq I] (O : Matrix I I ℂ) (C : Circuit I) :
    wordEval (retained O C)=runMatrix O C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> change wordEval (retained O C)*_=runMatrix O C*_ <;> rw [ih]

theorem retained_counts {I : Type} [Fintype I] [DecidableEq I] (O : Matrix I I ℂ) (C : Circuit I) :
    accessCount .inputForward (retained O C)=QueryCount C ∧ accessCount .inputBackward (retained O C)=0 := by
  induction C with
  | nil => exact ⟨rfl,rfl⟩
  | cons s C ih =>
    cases s <;> simp only [retained,List.map_cons,accessCount,List.sum_cons,List.map_cons,reduceCtorEq,
      ↓reduceIte,zero_add,queryCount_gate,queryCount_query] at * <;> constructor <;> omega

def previousOuterWord {n s d p : ℕ} (N : ℕ) (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (g : ℝ → ℝ) :
    GateWord (Matrix (Inner N ((Reg s × Work n s d p) × Bool)) (Inner N ((Reg s × Work n s d p) × Bool)) ℂ) :=
  (aeAccessWord (I:=(Reg s × Work n s d p) × Bool) N).flatMap
    (expandOuterStep (I:=(Reg s × Work n s d p) × Bool) N (previousSeed n s d p seed) (Finset.univ.filter (fun v => v.2=true))
      (retained (previousOracle termCode) (previousCircuit (s:=s) (d:=d) (p:=p) a c seed g)))

theorem previousOuterWord_eval {n s d p : ℕ} (N : ℕ) (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (g : ℝ → ℝ) :
    wordEval (G:=Matrix (Inner N ((Reg s × Work n s d p) × Bool)) (Inner N ((Reg s × Work n s d p) × Bool)) ℂ) (previousOuterWord N a c seed termCode g)=
      runMatrix (I:=Inner N ((Reg s × Work n s d p) × Bool)) (aeControlledGate (I:=(Reg s × Work n s d p) × Bool) N (preparedMark (Finset.univ.filter (fun v => v.2=true))))
        (countedAECircuit (I:=(Reg s × Work n s d p) × Bool) N (runMatrix (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode) (previousCircuit (s:=s) (d:=d) (p:=p) a c seed g))
          (previousSeed n s d p seed)) := by
  have h := expandedOuterWord_eval (I:=(Reg s × Work n s d p) × Bool) N (previousSeed n s d p seed)
    (Finset.univ.filter (fun v => v.2=true))
    (retained (previousOracle termCode) (previousCircuit (s:=s) (d:=d) (p:=p) a c seed g))
    (aeAccessWord (I:=(Reg s × Work n s d p) × Bool) N)
  rw [retained_eval (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode) (previousCircuit (s:=s) (d:=d) (p:=p) a c seed g)] at h
  exact h

theorem previousOuterWord_counts {n s d p : ℕ} (N : ℕ) (hN : 0 < N)
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (g : ℝ → ℝ) :
    accessCount .inputForward (previousOuterWord N a c seed termCode g)+
      accessCount .inputBackward (previousOuterWord N a c seed termCode g)=(4*2^d)*(2*N-1) := by
  have hc := expandedOuterWord_counts (I:=(Reg s × Work n s d p) × Bool) N (previousSeed n s d p seed) (Finset.univ.filter (fun v => v.2=true))
    (retained (previousOracle termCode) (previousCircuit (s:=s) (d:=d) (p:=p) a c seed g))
    (aeAccessWord (I:=(Reg s × Work n s d p) × Bool) N)
  have hr :=
      retained_counts (previousOracle termCode) (previousCircuit (s:=s) (d:=d) (p:=p) a c seed g)
  rw [hr.1,hr.2,(previousCircuit_counts (p:=p) a c seed g).1,
    (prepared_ae_separate_access_counts (I:=(Reg s × Work n s d p) × Bool) N hN).1,
    (prepared_ae_separate_access_counts (I:=(Reg s × Work n s d p) × Bool) N hN).2.1] at hc
  unfold previousOuterWord
  rw [hc.1,hc.2]
  have hn : 2*N-1=N+(N-1) := by omega
  rw [hn]
  ring

theorem previousOuterWord_event {n s d p : ℕ} (N : ℕ) (hN : 2 ≤ N)
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (g : ℝ → ℝ)
    (hg : ∀ v : Codes d p,g (∑ i : Reg d,Qatlib.Papers.MonteCarloInt20.MainResults.TermCode.decodeCode p (v i)) ∈ Set.Icc (0:ℝ) 1)
    (P : Fin N → Prop) :
    MeasureProb (I:=Inner N ((Reg s × Work n s d p) × Bool)) (ApplyGate (I:=Inner N ((Reg s × Work n s d p) × Bool)) (wordEval (G:=Matrix (Inner N ((Reg s × Work n s d p) × Bool)) (Inner N ((Reg s × Work n s d p) × Bool)) ℂ) (previousOuterWord N a c seed termCode g))
      (Ket (I:=Inner N ((Reg s × Work n s d p) × Bool)) (innerSeed N (by omega) (previousSeed n s d p seed))))
      (Finset.univ.filter (fun v => P v.1))=
      ∑ z ∈ Finset.univ.filter P,(aeLaw (I:=(Reg s × Work n s d p) × Bool) N
        (runMatrix (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode) (previousCircuit (s:=s) (d:=d) (p:=p) a c seed g))
        (previousSeed n s d p seed) (Finset.univ.filter (fun v => v.2=true))
        (previous_matrix_unitary a c seed termCode g hg) hN).prob z := by
  rw [previousOuterWord_eval N a c seed termCode g,runMatrix_apply (I:=Inner N ((Reg s × Work n s d p) × Bool)),
    innerSeed_ket (I:=(Reg s × Work n s d p) × Bool) N (show 0<N by omega) (previousSeed n s d p seed)]
  exact (aeLaw_event (I:=(Reg s × Work n s d p) × Bool) N hN
    (runMatrix (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode) (previousCircuit (s:=s) (d:=d) (p:=p) a c seed g))
    (previousSeed n s d p seed) (Finset.univ.filter (fun v => v.2=true))
    (previous_matrix_unitary a c seed termCode g hg) P).symm

theorem previous_executed_accuracy {n s d p : ℕ} (hd : 0 < d) (N : ℕ) (hN : 2 ≤ N)
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (g : ℝ → ℝ)
    (hg : ∀ v : Codes d p,g (∑ i : Reg d,Qatlib.Papers.MonteCarloInt20.MainResults.TermCode.decodeCode p (v i)) ∈ Set.Icc (0:ℝ) 1) :
    8/Real.pi^2 ≤ MeasureProb (I:=Inner N ((Reg s × Work n s d p) × Bool)) (ApplyGate (I:=Inner N ((Reg s × Work n s d p) × Bool)) (wordEval (G:=Matrix (Inner N ((Reg s × Work n s d p) × Bool)) (Inner N ((Reg s × Work n s d p) × Bool)) ℂ) (previousOuterWord N a c seed termCode g))
      (Ket (I:=Inner N ((Reg s × Work n s d p) × Bool)) (innerSeed N (by omega) (previousSeed n s d p seed))))
      (Finset.univ.filter (fun v => |aeEstimate N v.1-finiteTarget a c seed termCode ((2:ℝ)^d) g| ≤
        outerWindow N (finiteTarget a c seed termCode ((2:ℝ)^d) g))) := by
  exact (previous_ae_accuracy hd N hN a c seed termCode g hg).trans_eq
    (previousOuterWord_event N hN a c seed termCode g hg
      (fun z => |aeEstimate N z-finiteTarget a c seed termCode ((2:ℝ)^d) g| ≤
        outerWindow N (finiteTarget a c seed termCode ((2:ℝ)^d) g))).symm

theorem actual_two_program_counts {n s d p : ℕ} (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (g : ℝ → ℝ) :
    (accessCount .inputForward (nestedWord s M N hM (innerBody a c seed termCode)
      (bodySeed n s d p seed) (fun _ => bodyGood n s d p) ((2:ℝ)^d) g)+
     accessCount .inputBackward (nestedWord s M N hM (innerBody a c seed termCode)
      (bodySeed n s d p seed) (fun _ => bodyGood n s d p) ((2:ℝ)^d) g))*
      QueryCount (bodyCircuit (d:=d) (p:=p) a c seed (ZeroStr s))=2*((2*N-1)*(2*M-1)) ∧
    accessCount .inputForward (previousOuterWord N a c seed termCode g)+
      accessCount .inputBackward (previousOuterWord N a c seed termCode g)=(4*2^d)*(2*N-1) := by
  exact ⟨Qatlib.Papers.MonteCarloInt20.MainResults.ExecutedAccuracy.actual_term_call_hierarchy M N hM hN a c seed termCode ((2:ℝ)^d) g,
    previousOuterWord_counts N hN a c seed termCode g⟩

end Qatlib.Papers.MonteCarloInt20.MainResults.SequentialReadout
