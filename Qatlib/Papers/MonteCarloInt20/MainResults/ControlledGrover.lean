/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.InnerCircuit
import Qatlib.Papers.MonteCarloInt20.MainResults.InnerValidity
import Qatlib.Papers.MonteCarloInt20.MainResults.ActualNested
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerOracle
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerCircuit
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerValidity
open Qatlib.Papers.MonteCarloInt20.MainResults.ActualNested
open Qatlib.Papers.MonteCarloInt20.PrnJump.Compiled

namespace Qatlib.Papers.MonteCarloInt20.MainResults.ControlledGrover

noncomputable local instance bodyDecision (n s d p : ℕ) : DecidableEq (BodyReg n s d p) :=
    instDecidableEqProd
noncomputable local instance controlDecision (n s d p : ℕ) :
    DecidableEq (Bool × BodyReg n s d p) := instDecidableEqProd
noncomputable local instance phaseDecision (n s d p M : ℕ) :
    DecidableEq (Inner M (BodyReg n s d p)) := instDecidableEqProd

def operatorWord {I : Type} (C : Circuit I) : List (AdjointStep I) :=
  C.reverse.map (fun s => match s with | .gate U => .gate U | .query => .forward)

theorem operatorWord_eval {I : Type} [Fintype I] [DecidableEq I] (O : Matrix I I ℂ) (C : Circuit I) :
    evaluate O (operatorWord C)=runMatrix O C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    simp only [operatorWord,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,evaluate_append]
    cases s with
    | gate U =>
      change evaluate O (operatorWord C)*(U*1)=runMatrix O C*U
      rw [ih,Matrix.mul_one]
    | query =>
      change evaluate O (operatorWord C)*(O*1)=runMatrix O C*O
      rw [ih,Matrix.mul_one]

theorem operatorWord_counts {I : Type} (C : Circuit I) :
    adjointQueryCount (operatorWord C)=QueryCount C ∧ adjointGateCount (operatorWord C)=GateCount C := by
  induction C with
  | nil => exact ⟨rfl,rfl⟩
  | cons s C ih =>
    simp only [operatorWord,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,adjointQueryCount_append,adjointGateCount_append]
    cases s with
    | gate U =>
      change adjointQueryCount (operatorWord C)+0=QueryCount C ∧
          adjointGateCount (operatorWord C)+(0+1)=GateCount C+1
      rw [ih.1,ih.2]
      constructor <;> omega
    | query =>
      change adjointQueryCount (operatorWord C)+(0+1)=QueryCount C+1 ∧
          adjointGateCount (operatorWord C)+0=GateCount C
      rw [ih.1,ih.2]
      constructor <;> omega

theorem operatorWord_wellFormed {I : Type} [Fintype I] [DecidableEq I] (C : Circuit I) (hC : IsUnitaryCircuit C) :
    WellFormedAdjointCircuit (operatorWord C) := by
  intro V hV
  obtain ⟨s,hs,he⟩ := List.mem_map.mp hV
  have hs' : s∈C := List.mem_reverse.mp hs
  cases s with
  | query => contradiction
  | gate U =>
    have he' : U=V := by injection he
    subst V
    exact hC U hs'

def bodyWord {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) : List (AdjointStep (BodyReg n s d p)) :=
  operatorWord (bodyCircuit (d:=d) (p:=p) a c seed j)

theorem bodyWord_eval {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    evaluate (H:=BodyReg n s d p) (bodyOracle termCode j) (bodyWord (d:=d) (p:=p) a c seed j)=innerBody a c seed termCode j := by
  rw [bodyWord,operatorWord_eval,bodyCircuit_eval]

theorem bodyWord_wellFormed {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) :
    WellFormedAdjointCircuit (bodyWord (d:=d) (p:=p) a c seed j) :=
  operatorWord_wellFormed _ (bodyCircuit_unitary (d:=d) (p:=p) a c seed j)

theorem bodyWord_counts {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) :
    adjointQueryCount (bodyWord (d:=d) (p:=p) a c seed j)=2 ∧
    adjointGateCount (bodyWord (d:=d) (p:=p) a c seed j)=2*(nativeWord a c (List.ofFn (fun q : Fin (s+d+1) => q))).length+4 := by
  have h := operatorWord_counts (bodyCircuit (d:=d) (p:=p) a c seed j)
  rw [(bodyCircuit_counts (d:=d) (p:=p) a c seed j).1,(bodyCircuit_counts (d:=d) (p:=p) a c seed j).2] at h
  exact h

theorem optimized_body_grover {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    evaluate (H:=Bool × BodyReg n s d p) (parallelOracle (J:=Bool) (bodyOracle termCode j))
      (TokenPreservingGrover.instructions (H:=BodyReg n s d p) (bodyWord (d:=d) (p:=p) a c seed j) (bodySeed n s d p seed) (bodyGood n s d p))=
      controlOracle (preparedAAIterate (innerBody a c seed termCode j) (bodySeed n s d p seed) (bodyGood n s d p)) := by
  have h := TokenPreservingGrover.evaluate_instructions (H:=BodyReg n s d p) (bodyOracle termCode j)
    (bodyWord (d:=d) (p:=p) a c seed j) (bodySeed n s d p seed) (bodyGood n s d p)
    (bodyOracle_unitary termCode j) (bodyWord_wellFormed (d:=d) (p:=p) a c seed j)
  rw [bodyWord_eval a c seed termCode j] at h
  exact h

theorem optimized_body_branches {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) (x y : BodyReg n s d p) :
    evaluate (H:=Bool × BodyReg n s d p) (parallelOracle (J:=Bool) (bodyOracle termCode j))
      (TokenPreservingGrover.instructions (H:=BodyReg n s d p) (bodyWord (d:=d) (p:=p) a c seed j) (bodySeed n s d p seed) (bodyGood n s d p)) (false,x) (false,y)=
      (1:Matrix (BodyReg n s d p) (BodyReg n s d p) ℂ) x y ∧
    evaluate (H:=Bool × BodyReg n s d p) (parallelOracle (J:=Bool) (bodyOracle termCode j))
      (TokenPreservingGrover.instructions (H:=BodyReg n s d p) (bodyWord (d:=d) (p:=p) a c seed j) (bodySeed n s d p seed) (bodyGood n s d p)) (true,x) (true,y)=
      preparedAAIterate (innerBody a c seed termCode j) (bodySeed n s d p seed) (bodyGood n s d p) x y := by
  rw [optimized_body_grover a c seed termCode j]
  constructor <;> simp [controlOracle,select]

theorem controlled_minus_not_global {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    controlOracle (-preparedAAIterate (innerBody a c seed termCode j) (bodySeed n s d p seed) (bodyGood n s d p))≠
      -controlOracle (preparedAAIterate (innerBody a c seed termCode j) (bodySeed n s d p seed) (bodyGood n s d p)) := by
  intro h
  have he := congrArg (fun V : Matrix (Bool × BodyReg n s d p) (Bool × BodyReg n s d p) ℂ =>
    V (false,bodySeed n s d p seed) (false,bodySeed n s d p seed)) h
  norm_num [controlOracle,select] at he

theorem optimized_grover_counts {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) :
    adjointQueryCount (TokenPreservingGrover.instructions (H:=BodyReg n s d p) (bodyWord (d:=d) (p:=p) a c seed j) (bodySeed n s d p seed) (bodyGood n s d p))=4 ∧
    adjointGateCount (TokenPreservingGrover.instructions (H:=BodyReg n s d p) (bodyWord (d:=d) (p:=p) a c seed j) (bodySeed n s d p seed) (bodyGood n s d p))=
      4*(nativeWord a c (List.ofFn (fun q : Fin (s+d+1) => q))).length+10 := by
  have h :=
      TokenPreservingGrover.counts (H:=BodyReg n s d p) (bodyWord (d:=d) (p:=p) a c seed j)
      (bodySeed n s d p seed) (bodyGood n s d p)
  rw [(bodyWord_counts (d:=d) (p:=p) a c seed j).1,(bodyWord_counts (d:=d) (p:=p) a c seed j).2] at h
  constructor <;> omega

theorem optimized_inner_ae_counts {n s d p : ℕ} (M : ℕ) (hM : 0<M)
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) :
    adjointQueryCount (TokenPreservingAmplitudeEstimation.instructions (H:=BodyReg n s d p) M (bodyWord (d:=d) (p:=p) a c seed j) (bodySeed n s d p seed) (bodyGood n s d p))=2*(2*M-1) := by
  have h := TokenPreservingAmplitudeEstimation.resources (H:=BodyReg n s d p) M hM (bodyWord (d:=d) (p:=p) a c seed j)
    (bodySeed n s d p seed) (bodyGood n s d p) (bodyWord_wellFormed (d:=d) (p:=p) a c seed j)
  rw [(bodyWord_counts (d:=d) (p:=p) a c seed j).1] at h
  exact h.2.1.trans (Nat.mul_comm _ _)

end Qatlib.Papers.MonteCarloInt20.MainResults.ControlledGrover
