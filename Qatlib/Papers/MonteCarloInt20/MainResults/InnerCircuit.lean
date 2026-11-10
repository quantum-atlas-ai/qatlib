/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.InnerOracle
import Qatlib.Papers.MonteCarloInt20.MainResults.NestedWord
import Qatlib.Foundations.CircuitReversal.ReversalAlgebra.CircuitReversal
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.CircuitReversal.ReversalAlgebra
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedWord
open Qatlib.Papers.MonteCarloInt20.PrnJump.Stride
open Qatlib.Papers.MonteCarloInt20.PrnJump.Compiled
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerOracle
open Qatlib.Papers.MonteCarloInt20.MainResults.TermCode

namespace Qatlib.Papers.MonteCarloInt20.MainResults.InnerCircuit

noncomputable local instance bodyDecision (n s d p : ℕ) : DecidableEq (BodyReg n s d p) :=
    instDecidableEqProd

theorem runMatrix_append {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (C D : Circuit I) : runMatrix O (C++D)=runMatrix O D*runMatrix O C := by
  induction C with
  | nil => simp [runMatrix]
  | cons s C ih => cases s <;> simp only [List.cons_append,runMatrix,ih,Matrix.mul_assoc]

theorem runMatrix_reverse {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (hO : O.conjTranspose=O) (C : Circuit I) :
    runMatrix O (ReverseCircuit C)=(runMatrix O C).conjTranspose := by
  induction C with
  | nil => simp [ReverseCircuit,runMatrix]
  | cons s C ih =>
    rw [reverseCircuit_cons,runMatrix_append,ih]
    cases s <;> simp [reverseStep,runMatrix,Matrix.conjTranspose_mul,hO]

def knownLift {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (f : Matrix I I ℂ →* Matrix J J ℂ) (O : Matrix I I ℂ) (C : Circuit I) : Circuit J :=
  C.map (fun s => .gate (f (stepMatrix O s)))

theorem knownLift_eval {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (f : Matrix I I ℂ →* Matrix J J ℂ) (O : Matrix I I ℂ) (Q : Matrix J J ℂ) (C : Circuit I) :
    runMatrix Q (knownLift f O C)=f (runMatrix O C) := by
  induction C with
  | nil => exact f.map_one.symm
  | cons s C ih =>
    change runMatrix Q (knownLift f O C)*f (stepMatrix O s)=_
    rw [ih]
    cases s <;> exact (f.map_mul _ _).symm

theorem knownLift_counts {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (f : Matrix I I ℂ →* Matrix J J ℂ) (O : Matrix I I ℂ) (C : Circuit I) :
    QueryCount (knownLift f O C)=0 ∧ GateCount (knownLift f O C)=C.length := by
  induction C with
  | nil => exact ⟨rfl,rfl⟩
  | cons s C ih =>
    change QueryCount (knownLift f O C)=0 ∧ GateCount (knownLift f O C)+1=C.length+1
    exact ⟨ih.1,congrArg (fun x : ℕ => x+1) ih.2⟩

def nativeLiftHom (n s d p : ℕ) :
    Matrix (Reg (width n (s+d+1))) (Reg (width n (s+d+1))) ℂ →*
      Matrix (BodyReg n s d p) (BodyReg n s d p) ℂ :=
  rightSpectatorHom.comp (leftSpectatorHom.comp rightSpectatorHom)

def nativeStage {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) : Circuit (BodyReg n s d p) :=
  knownLift (nativeLiftHom n s d p) 1
    (reflectionCompile (nativeWord a c (List.ofFn (fun q : Fin (s+d+1) => q))))

def bodyOracle {n s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    Matrix (BodyReg n s d p) (BodyReg n s d p) ℂ :=
  TensorGate (queryOracle (k:=s+d+1) termCode j) 1

theorem bodyOracle_selfadjoint {n s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    (bodyOracle termCode j).conjTranspose=bodyOracle termCode j := by
  rw [bodyOracle,tensorGate_conjTranspose,queryOracle_selfadjoint,Matrix.conjTranspose_one]

def loaderGate {n s d p : ℕ} (seed : ZMod (2^n)) (j : Reg s) :
    Matrix (BodyReg n s d p) (BodyReg n s d p) ℂ :=
  TensorGate (select (fun i : Reg d => TensorGate (xorMatrix (loaderMask seed j i)) 1)) 1

def termHadamard (n s d p : ℕ) : Matrix (BodyReg n s d p) (BodyReg n s d p) ℂ :=
  TensorGate (TensorGate (HadamardN d) 1) 1

def codeRotation (n s d p : ℕ) : Matrix (BodyReg n s d p) (BodyReg n s d p) ℂ :=
  payoffRotation (fun v : Reg d × Data n (s+d+1) p => decodeCode p v.2.2)

def computeCircuit {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) : Circuit (BodyReg n s d p) :=
  [.gate (loaderGate (d:=d) (p:=p) seed j)]++nativeStage (s:=s) (d:=d) (p:=p) a c++[.query]

def bodyCircuit {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) : Circuit (BodyReg n s d p) :=
  [.gate (termHadamard n s d p)]++computeCircuit (d:=d) (p:=p) a c seed j++
    [.gate (codeRotation n s d p)]++ReverseCircuit (computeCircuit (d:=d) (p:=p) a c seed j)

theorem tensor_one_select {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (U : Matrix I I ℂ) : TensorGate (1 : Matrix J J ℂ) U=select (fun _ : J => U) := by
  simpa only [parallelOracle,TensorGate] using! (parallelOracle_eq_kronecker (J:=J) U).symm

theorem computeCircuit_eval {n s d p : ℕ}
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    runMatrix (bodyOracle termCode j) (computeCircuit (d:=d) (p:=p) a c seed j)=
      TensorGate (select (dataCompute a c seed termCode j)) 1 := by
  let O := bodyOracle termCode j
  let C := reflectionCompile (nativeWord a c (List.ofFn (fun q : Fin (s+d+1) => q)))
  have he := knownLift_eval (I:=Reg (width n (s+d+1))) (J:=BodyReg n s d p)
    (nativeLiftHom n s d p) 1 O C
  change runMatrix O
      ([.gate (loaderGate (d:=d) (p:=p) seed j)]++knownLift (nativeLiftHom n s d p) 1 C++[.query])=_
  rw [runMatrix_append O,runMatrix_append O,he]
  simp only [runMatrix,Matrix.one_mul]
  change TensorGate (queryOracle (k:=s+d+1) termCode j) 1 *
    (TensorGate (TensorGate 1 (TensorGate (nativeJumpMatrix (k:=s+d+1) a c) 1)) 1*
      TensorGate (select (fun i : Reg d => TensorGate (xorMatrix (loaderMask seed j i)) 1)) 1)=_
  rw [tensorGate_mul,Matrix.one_mul,tensorGate_mul,Matrix.one_mul,queryOracle_eq_select,tensor_one_select,
    parallel_select_mul,parallel_select_mul]
  apply congrArg (fun V : Matrix (Reg d × Data n (s+d+1) p) (Reg d × Data n (s+d+1) p) ℂ =>
    TensorGate V (1 : Matrix Bool Bool ℂ))
  apply congrArg select
  funext i
  rw [dataCompute,strideCompute,tensorGate_mul,Matrix.one_mul]

theorem bodyCircuit_eval {n s d p : ℕ}
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    runMatrix (bodyOracle termCode j) (bodyCircuit (d:=d) (p:=p) a c seed j)=innerBody a c seed termCode j := by
  rw [bodyCircuit,runMatrix_append,runMatrix_append,runMatrix_append,
    runMatrix_reverse _ (bodyOracle_selfadjoint termCode j),computeCircuit_eval]
  simp only [runMatrix,Matrix.one_mul]
  rw [tensorGate_conjTranspose,Matrix.conjTranspose_one]
  change (TensorGate (select (dataCompute a c seed termCode j)).conjTranspose 1*
      (codeRotation n s d p*(TensorGate (select (dataCompute a c seed termCode j)) 1*
        termHadamard n s d p)))=_
  simp only [codeRotation,termHadamard]
  rw [innerBody,Qatlib.Papers.MonteCarloInt20.MainResults.FlagRotation.cleanFlagPreparation,payoffPreparation,
    Qatlib.Papers.MonteCarloInt20.MainResults.FlagRotation.computePreparation,tensorGate_mul,Matrix.one_mul]

theorem bodyCircuit_counts {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) :
    QueryCount (bodyCircuit (d:=d) (p:=p) a c seed j)=2 ∧
    GateCount (bodyCircuit (d:=d) (p:=p) a c seed j)=
      2*(nativeWord a c (List.ofFn (fun q : Fin (s+d+1) => q))).length+4 := by
  have hc := knownLift_counts (nativeLiftHom n s d p) 1
    (reflectionCompile (nativeWord a c (List.ofFn (fun q : Fin (s+d+1) => q))))
  have hlen : (reflectionCompile (nativeWord a c (List.ofFn (fun q : Fin (s+d+1) => q)))).length=
      (nativeWord a c (List.ofFn (fun q : Fin (s+d+1) => q))).length := by
    simp [reflectionCompile]
  simp only [bodyCircuit,queryCount_append,gateCount_append,queryCount_reverseCircuit,gateCount_reverseCircuit,
    computeCircuit,queryCount_gate,gateCount_gate,queryCount_query,gateCount_query,queryCount_nil,gateCount_nil,
    nativeStage,hc.1,hc.2,hlen]
  constructor
  · trivial
  · omega

theorem bodyCircuit_flag_born {n s d p : ℕ} (hd : 0 < d)
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    MeasureProb (Run (bodyOracle termCode j) (bodyCircuit (d:=d) (p:=p) a c seed j) (Ket (bodySeed n s d p seed)))
      (Finset.univ.filter (fun v => v.2=true))=termMean a c seed termCode j := by
  rw [← runMatrix_apply,bodyCircuit_eval]
  exact innerBody_flag_born hd a c seed termCode j

end Qatlib.Papers.MonteCarloInt20.MainResults.InnerCircuit
