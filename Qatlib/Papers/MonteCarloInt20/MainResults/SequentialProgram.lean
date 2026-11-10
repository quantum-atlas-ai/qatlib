/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.SequentialLoop
import Qatlib.Papers.MonteCarloInt20.MainResults.CoherentBody
import Qatlib.Papers.MonteCarloInt20.MainResults.ActualNested
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.CircuitReversal.ReversalAlgebra
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedWord
open Qatlib.Papers.MonteCarloInt20.MainResults.FlagRotation
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerOracle
open Qatlib.Papers.MonteCarloInt20.MainResults.SequentialStore
open Qatlib.Papers.MonteCarloInt20.MainResults.SequentialLoop
open Qatlib.Papers.MonteCarloInt20.MainResults.TermCode
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerCircuit
open Qatlib.Papers.MonteCarloInt20.MainResults.CoherentBody
open Qatlib.Papers.MonteCarloInt20.MainResults.ActualNested

namespace Qatlib.Papers.MonteCarloInt20.MainResults.Sequential

noncomputable local instance workDecision (n s d p : ℕ) : DecidableEq (Work n s d p) :=
    instDecidableEqProd
noncomputable local instance sampleDecision (n s d p : ℕ) : DecidableEq (Reg s × Work n s d p) :=
    instDecidableEqProd
noncomputable local instance fullDecision (n s d p : ℕ) :
    DecidableEq ((Reg s × Work n s d p) × Bool) := instDecidableEqProd

def sampleOracle {n s d p : ℕ} (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) :
    Matrix (Reg s × Work n s d p) (Reg s × Work n s d p) ℂ := select (oracle termCode)

def sampleStep {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (i : Reg d) : Circuit (Reg s × Work n s d p) :=
  [.gate (select (fun j : Reg s => TensorGate (prepareAddress (p:=p) a c seed j i) (1:Matrix (Codes d p) (Codes d p) ℂ))),
    .query,.gate (TensorGate 1 (copyGate n s d p)),.query,
    .gate (select (fun j : Reg s => TensorGate (prepareAddress (p:=p) a c seed j i).conjTranspose (1:Matrix (Codes d p) (Codes d p) ℂ)))]

def sampleLoop {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (is : List (Reg d)) : Circuit (Reg s × Work n s d p) :=
  is.flatMap (sampleStep (s:=s) (p:=p) a c seed)

theorem sampleStep_eval {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (i : Reg d) :
    runMatrix (sampleOracle termCode) (sampleStep (s:=s) (p:=p) a c seed i)=
      select (fun j : Reg s => runMatrix (oracle termCode j) (storeCircuit (p:=p) a c seed j i)) := by
  simp only [sampleStep,runMatrix,Matrix.one_mul,sampleOracle]
  rw [tensor_one_select,parallel_select_mul,parallel_select_mul,parallel_select_mul,parallel_select_mul]
  apply congrArg select
  funext j
  simp only [storeCircuit,runMatrix,Matrix.one_mul]

theorem sampleLoop_eval {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (is : List (Reg d)) :
    runMatrix (sampleOracle termCode) (sampleLoop (s:=s) (p:=p) a c seed is)=
      select (fun j : Reg s => runMatrix (oracle termCode j) (loopCircuit (p:=p) a c seed j is)) := by
  induction is with
  | nil => simp only [sampleLoop,loopCircuit,List.flatMap_nil,runMatrix]; exact selectHom.map_one.symm
  | cons i is ih =>
    change runMatrix (sampleOracle termCode)
        (sampleStep (s:=s) (p:=p) a c seed i++sampleLoop (s:=s) (p:=p) a c seed is)=_
    rw [runMatrix_append (sampleOracle termCode) (sampleStep (s:=s) (p:=p) a c seed i) (sampleLoop (s:=s) (p:=p) a c seed is)]
    rw [sampleStep_eval a c seed termCode i,ih,parallel_select_mul]
    apply congrArg select
    funext j
    exact (runMatrix_append (oracle termCode j) (storeCircuit (p:=p) a c seed j i) (loopCircuit (p:=p) a c seed j is)).symm

theorem sampleLoop_counts {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (is : List (Reg d)) :
    QueryCount (sampleLoop (s:=s) (p:=p) a c seed is)=2*is.length ∧ GateCount (sampleLoop (s:=s) (p:=p) a c seed is)=3*is.length := by
  induction is with
  | nil => exact ⟨rfl,rfl⟩
  | cons i is ih =>
    simp only [sampleLoop,List.flatMap_cons,queryCount_append,gateCount_append]
    change 2+QueryCount (sampleLoop (s:=s) (p:=p) a c seed is)=2*(i::is).length ∧
      3+GateCount (sampleLoop (s:=s) (p:=p) a c seed is)=3*(i::is).length
    rw [ih.1,ih.2,List.length_cons]
    constructor <;> omega

def payoff {n s d p : ℕ} (g : ℝ → ℝ) (v : Reg s × Work n s d p) : ℝ :=
  g (∑ i : Reg d,decodeCode p (v.2.2 i))

def previousCircuit {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (g : ℝ → ℝ) :
    Circuit ((Reg s × Work n s d p) × Bool) :=
  [.gate (TensorGate (TensorGate (HadamardN s) (1:Matrix (Work n s d p) (Work n s d p) ℂ)) 1)]++
    oracleLift (I:=Reg s × Work n s d p) (J:=(Reg s × Work n s d p) × Bool) rightSpectatorHom (sampleLoop (s:=s) (p:=p) a c seed (allTerms d))++
    [.gate (payoffRotation (payoff (n:=n) (s:=s) (d:=d) (p:=p) g))]++
    ReverseCircuit (oracleLift (I:=Reg s × Work n s d p) (J:=(Reg s × Work n s d p) × Bool) rightSpectatorHom (sampleLoop (s:=s) (p:=p) a c seed (allTerms d)))

def previousOracle {n s d p : ℕ} (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) :
    Matrix ((Reg s × Work n s d p) × Bool) ((Reg s × Work n s d p) × Bool) ℂ :=
  TensorGate (sampleOracle termCode) 1

theorem previousCircuit_eval {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (g : ℝ → ℝ) :
    runMatrix (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode) (previousCircuit (s:=s) (d:=d) (p:=p) a c seed g)=
      cleanFlagPreparation s (fun j : Reg s => runMatrix (oracle termCode j) (loopCircuit (p:=p) a c seed j (allTerms d)))
        (payoff (n:=n) (s:=s) (d:=d) (p:=p) g) := by
  have hO : (previousOracle termCode).conjTranspose=previousOracle termCode := by
    rw [previousOracle,tensorGate_conjTranspose,Matrix.conjTranspose_one,sampleOracle,parallel_select_adjoint]
    congr 1
    apply congrArg select
    funext j
    exact oracle_selfadjoint termCode j
  have hLift := oracleLift_eval (I:=Reg s × Work n s d p) (J:=(Reg s × Work n s d p) × Bool)
    rightSpectatorHom (sampleOracle termCode) (sampleLoop (s:=s) (p:=p) a c seed (allTerms d))
  let C : Circuit ((Reg s × Work n s d p) × Bool) := oracleLift (I:=Reg s × Work n s d p)
    (J:=(Reg s × Work n s d p) × Bool) rightSpectatorHom (sampleLoop (s:=s) (p:=p) a c seed (allTerms d))
  let H : Matrix ((Reg s × Work n s d p) × Bool) ((Reg s × Work n s d p) × Bool) ℂ :=
    TensorGate (TensorGate (HadamardN s) (1:Matrix (Work n s d p) (Work n s d p) ℂ)) 1
  let R := payoffRotation (payoff (n:=n) (s:=s) (d:=d) (p:=p) g)
  change runMatrix (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode)
      ((([.gate H]++C)++[.gate R])++ReverseCircuit C)=_
  have e0 : runMatrix (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode)
      ((([Step.gate H]++C)++[Step.gate R])++ReverseCircuit C)=
      runMatrix (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode) (ReverseCircuit C)*
      runMatrix (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode) (([Step.gate H]++C)++[Step.gate R]) :=
    runMatrix_append (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode) _ _
  have e1 : runMatrix (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode) (([Step.gate H]++C)++[Step.gate R])=
      runMatrix (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode) [Step.gate R]*
      runMatrix (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode) ([Step.gate H]++C) :=
    runMatrix_append (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode) _ _
  have e2 : runMatrix (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode) ([Step.gate H]++C)=
      runMatrix (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode) C*
      runMatrix (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode) [Step.gate H] :=
    runMatrix_append (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode) _ _
  rw [e0,e1,e2,runMatrix_reverse (I:=(Reg s × Work n s d p) × Bool) _ hO C]
  have hc : runMatrix (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode) C=TensorGate
      (select (fun j : Reg s => runMatrix (oracle termCode j) (loopCircuit (p:=p) a c seed j (allTerms d)))) 1 := by
    exact hLift.trans (congrArg rightSpectatorHom (sampleLoop_eval a c seed termCode (allTerms d)))
  rw [hc]
  simp only [runMatrix,Matrix.one_mul,tensorGate_conjTranspose,Matrix.conjTranspose_one]
  unfold cleanFlagPreparation payoffPreparation computePreparation
  simp only [H,R,tensorGate_mul,Matrix.one_mul]

theorem previousCircuit_counts {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (g : ℝ → ℝ) :
    QueryCount (previousCircuit (s:=s) (d:=d) (p:=p) a c seed g)=4*2^d ∧
    GateCount (previousCircuit (s:=s) (d:=d) (p:=p) a c seed g)=6*2^d+2 := by
  have hL := oracleLift_counts (I:=Reg s × Work n s d p) (J:=(Reg s × Work n s d p) × Bool)
    rightSpectatorHom (sampleLoop (s:=s) (p:=p) a c seed (allTerms d))
  have hC := sampleLoop_counts (s:=s) (p:=p) a c seed (allTerms d)
  have hlen : (allTerms d).length=2^d := by simp [allTerms,Reg]
  simp only [previousCircuit,queryCount_append,gateCount_append,queryCount_reverseCircuit,gateCount_reverseCircuit,
    queryCount_gate,gateCount_gate,queryCount_nil,gateCount_nil,hL.1,hL.2,hC.1,hC.2,hlen]
  constructor <;> omega

def previousSeed (n s d p : ℕ) (seed : ZMod (2^n)) : ((Reg s × Work n s d p) × Bool) :=
  ((ZeroStr s,((ZeroStr d,dataSeed n s d p seed),fun _ => ZeroStr (p+1))),false)

theorem previous_flag_born {n s d p : ℕ} (hd : 0 < d) (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (g : ℝ → ℝ)
    (hg : ∀ v : Codes d p,g (∑ i : Reg d,decodeCode p (v i)) ∈ Set.Icc (0:ℝ) 1) :
    MeasureProb (ApplyGate (runMatrix (I:=(Reg s × Work n s d p) × Bool) (previousOracle termCode) (previousCircuit (s:=s) (d:=d) (p:=p) a c seed g))
      (Ket (previousSeed n s d p seed))) (Finset.univ.filter (fun v => v.2=true))=
      finiteTarget a c seed termCode ((2:ℝ)^d) g := by
  rw [previousCircuit_eval a c seed termCode g]
  have hU (j : Reg s) := runMatrix_unitary (oracle termCode j) (loopCircuit (p:=p) a c seed j (allTerms d))
    (oracle_unitary termCode j) (loopCircuit_unitary (p:=p) a c seed j (allTerms d))
  have hb := cleanFlagPreparation_born (W:=Work n s d p) s
    (fun j : Reg s => runMatrix (oracle termCode j) (loopCircuit (p:=p) a c seed j (allTerms d))) hU
    ((ZeroStr d,dataSeed n s d p seed),fun _ => ZeroStr (p+1))
    (fun j : Reg s => ((ZeroStr d,dataSeed n s d p seed),fun i => codeBits (termCode j i (residue a c seed j i))))
    (allTerms_basis hd a c seed termCode) (payoff (n:=n) (s:=s) (d:=d) (p:=p) g) (fun v => hg v.2.2)
  change _=_ at hb
  change MeasureProb (ApplyGate (cleanFlagPreparation s (fun j : Reg s => runMatrix (oracle termCode j) (loopCircuit (p:=p) a c seed j (allTerms d))) (payoff (n:=n) (s:=s) (d:=d) (p:=p) g))
    (Ket ((ZeroStr s,((ZeroStr d,dataSeed n s d p seed),fun _ => ZeroStr (p+1))),false))) (Finset.univ.filter (fun v => v.2=true))=_
  rw [hb,source_sum_target]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  unfold payoff
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact decodeCode_codeBits _

end Qatlib.Papers.MonteCarloInt20.MainResults.Sequential
