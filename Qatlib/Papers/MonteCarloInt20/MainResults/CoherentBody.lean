/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.InnerCircuit

/-!
# Coherent sample-controlled term circuits

`oracleLift` transports circuit gates along a matrix monoid homomorphism while retaining query
tokens. The coherent circuits then select the PRN-based inner computation by a sample register,
as required by the nested Monte Carlo construction of [KanekoEtAl2020].

`coherentCircuit_eval` identifies the resulting matrix with the selected family of inner
preparations, and `coherentCircuit_counts` gives its exact query and gate counts.

## Main statements

* `oracleLift_eval`: relates lifted circuit evaluation to the matrix homomorphism.
* `coherentCircuit_eval`: identifies the coherent circuit with `select (innerBody ...)`.
* `coherentCircuit_counts`: counts two queries and the explicit native gates.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

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
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedWord
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerOracle
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerCircuit
open Qatlib.Papers.MonteCarloInt20.PrnJump.Compiled

namespace Qatlib.Papers.MonteCarloInt20.MainResults.CoherentBody

noncomputable local instance bodyDecision (n s d p : ℕ) : DecidableEq (BodyReg n s d p) :=
    instDecidableEqProd
noncomputable local instance coherentDecision (n s d p : ℕ) :
    DecidableEq (Reg s × BodyReg n s d p) := instDecidableEqProd

/-- Lift each known gate of a circuit through a matrix monoid homomorphism, retaining each query
token. -/
def oracleLift {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (f : Matrix I I ℂ →* Matrix J J ℂ) (C : Circuit I) : Circuit J :=
  C.map (fun s => match s with | .gate U => .gate (f U) | .query => .query)

/-- Evaluating a lifted circuit against the lifted oracle equals applying the monoid
homomorphism to the original circuit evaluation. -/
theorem oracleLift_eval {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (f : Matrix I I ℂ →* Matrix J J ℂ) (O : Matrix I I ℂ) (C : Circuit I) :
    runMatrix (f O) (oracleLift f C)=f (runMatrix O C) := by
  induction C with
  | nil => exact f.map_one.symm
  | cons s C ih => cases s <;> change runMatrix (f O) (oracleLift f C)*_=f (runMatrix O C*_) <;>
      rw [ih,map_mul]

/-- Lifting a circuit through a matrix monoid homomorphism preserves both query count and gate
count. -/
theorem oracleLift_counts {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (f : Matrix I I ℂ →* Matrix J J ℂ) (C : Circuit I) :
    QueryCount (oracleLift f C)=QueryCount C ∧ GateCount (oracleLift f C)=GateCount C := by
  induction C with
  | nil => exact ⟨rfl,rfl⟩
  | cons s C ih =>
    cases s with
    | gate U =>
      change QueryCount (oracleLift f C)=QueryCount C ∧ GateCount (oracleLift f C)+1=GateCount C+1
      exact ⟨ih.1,congrArg (fun x : ℕ => x+1) ih.2⟩
    | query =>
      change QueryCount (oracleLift f C)+1=QueryCount C+1 ∧ GateCount (oracleLift f C)=GateCount C
      exact ⟨congrArg (fun x : ℕ => x+1) ih.1,ih.2⟩

/-- The term oracle selected coherently by the sample register. -/
def coherentOracle {n s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) :
    Matrix (Reg s × BodyReg n s d p) (Reg s × BodyReg n s d p) ℂ :=
  select (bodyOracle termCode)

/-- The native PRN stage lifted to a register space with a spectator sample register. -/
def coherentNativeStage {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) :
    Circuit (Reg s × BodyReg n s d p) :=
  knownLift leftSpectatorHom 1 (nativeStage (s:=s) (d:=d) (p:=p) a c)

/-- The coherent term computation consisting of sample-selected loading, the native PRN stage,
and one term query. -/
def coherentCompute {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) :
    Circuit (Reg s × BodyReg n s d p) :=
  [.gate (select (fun j : Reg s => loaderGate (d:=d) (p:=p) seed j))]++
    coherentNativeStage (s:=s) (d:=d) (p:=p) a c++[.query]

/-- The coherent inner preparation consisting of coordinate Hadamards, term computation, code
rotation, and reversed term computation. -/
def coherentCircuit {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) :
    Circuit (Reg s × BodyReg n s d p) :=
  [.gate (TensorGate 1 (termHadamard n s d p))]++coherentCompute (s:=s) (d:=d) (p:=p) a c seed++
    [.gate (TensorGate 1 (codeRotation n s d p))]++ReverseCircuit (coherentCompute (s:=s) (d:=d) (p:=p) a c seed)

/-- The coherently selected term oracle equals its conjugate transpose. -/
theorem coherentOracle_selfadjoint {n s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) :
    (coherentOracle termCode).conjTranspose=coherentOracle termCode := by
  rw [coherentOracle,parallel_select_adjoint]
  apply congrArg select
  funext j
  exact bodyOracle_selfadjoint termCode j

/-- The coherent computation evaluates to the sample-selected family of individual
term-computation matrices. -/
theorem coherentCompute_eval {n s d p : ℕ}
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) :
    runMatrix (coherentOracle termCode) (coherentCompute (s:=s) (d:=d) (p:=p) a c seed)=
      select (fun j : Reg s => runMatrix (bodyOracle termCode j) (computeCircuit (d:=d) (p:=p) a c seed j)) := by
  rw [coherentCompute,runMatrix_append,runMatrix_append]
  simp only [runMatrix,Matrix.one_mul,coherentNativeStage,knownLift_eval]
  change select (bodyOracle termCode)*
    (TensorGate 1 (runMatrix 1 (nativeStage (s:=s) (d:=d) (p:=p) a c))*
      select (fun j : Reg s => loaderGate (d:=d) (p:=p) seed j))=_
  rw [tensor_one_select,parallel_select_mul,parallel_select_mul]
  apply congrArg select
  funext j
  rw [computeCircuit,runMatrix_append,runMatrix_append]
  simp only [runMatrix,Matrix.one_mul]
  have h := knownLift_eval (nativeLiftHom n s d p) 1 (bodyOracle termCode j)
    (reflectionCompile (nativeWord a c (List.ofFn (fun q : Fin (s+d+1) => q))))
  have h₀ := knownLift_eval (nativeLiftHom n s d p) 1 (1 : Matrix (BodyReg n s d p) (BodyReg n s d p) ℂ)
    (reflectionCompile (nativeWord a c (List.ofFn (fun q : Fin (s+d+1) => q))))
  change bodyOracle termCode j*(runMatrix 1 (nativeStage (s:=s) (d:=d) (p:=p) a c)*loaderGate (d:=d) (p:=p) seed j)=_
  rw [show runMatrix 1 (nativeStage (s:=s) (d:=d) (p:=p) a c)=
      runMatrix (bodyOracle termCode j) (nativeStage (s:=s) (d:=d) (p:=p) a c) from h₀.trans h.symm]

/-- The coherent circuit evaluates to the sample-selected family of `innerBody` preparations
[KanekoEtAl2020]. -/
theorem coherentCircuit_eval {n s d p : ℕ}
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) :
    runMatrix (coherentOracle termCode) (coherentCircuit (s:=s) (d:=d) (p:=p) a c seed)=
      select (innerBody a c seed termCode) := by
  rw [coherentCircuit,runMatrix_append,runMatrix_append,runMatrix_append,
    runMatrix_reverse _ (coherentOracle_selfadjoint termCode),coherentCompute_eval]
  simp only [runMatrix,Matrix.one_mul]
  rw [parallel_select_adjoint,tensor_one_select,tensor_one_select,
    parallel_select_mul,parallel_select_mul,parallel_select_mul]
  apply congrArg select
  funext j
  rw [← bodyCircuit_eval a c seed termCode j,bodyCircuit,runMatrix_append,runMatrix_append,runMatrix_append,
    runMatrix_reverse _ (bodyOracle_selfadjoint termCode j)]
  simp only [runMatrix,Matrix.one_mul]

/-- The coherent inner circuit uses two term queries and `2 * (nativeWord a c (List.ofFn (fun q
: Fin (s+d+1) => q))).length + 4` known gates. -/
theorem coherentCircuit_counts {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) :
    QueryCount (coherentCircuit (s:=s) (d:=d) (p:=p) a c seed)=2 ∧
    GateCount (coherentCircuit (s:=s) (d:=d) (p:=p) a c seed)=
      2*(nativeWord a c (List.ofFn (fun q : Fin (s+d+1) => q))).length+4 := by
  have hc := knownLift_counts (leftSpectatorHom : Matrix (BodyReg n s d p) (BodyReg n s d p) ℂ →*
    Matrix (Reg s × BodyReg n s d p) (Reg s × BodyReg n s d p) ℂ) 1
    (nativeStage (s:=s) (d:=d) (p:=p) a c)
  have hl : (nativeStage (s:=s) (d:=d) (p:=p) a c).length=
    (nativeWord a c (List.ofFn (fun q : Fin (s+d+1) => q))).length := by
    simp [nativeStage,knownLift,reflectionCompile]
  simp only [coherentCircuit,coherentCompute,queryCount_append,gateCount_append,
    queryCount_reverseCircuit,gateCount_reverseCircuit,queryCount_gate,gateCount_gate,
    queryCount_query,gateCount_query,queryCount_nil,gateCount_nil,coherentNativeStage,hc.1,hc.2,hl]
  constructor
  · trivial
  · omega

end Qatlib.Papers.MonteCarloInt20.MainResults.CoherentBody
