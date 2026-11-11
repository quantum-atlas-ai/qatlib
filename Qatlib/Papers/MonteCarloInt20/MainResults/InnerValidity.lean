/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.InnerCircuit

/-!
# Unitarity of the inner preparation circuits

This module proves the circuit-level validity of the native PRN stage, term computation, and
complete inner preparation used for [KanekoEtAl2020]. The lifting lemmas transport unitarity to
larger register spaces, and `bodyCircuit_unitary` verifies the full compute-rotate-uncompute
circuit.

## Main statements

* `knownLift_unitary`: transports circuit validity through a map preserving unitary matrices.
* `computeCircuit_unitary`: verifies the term-computation circuit.
* `bodyCircuit_unitary`: verifies the complete inner body circuit.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.CircuitReversal.ReversalAlgebra
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedWord
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn
open Qatlib.Papers.MonteCarloInt20.PrnJump.Stride
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerOracle
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerCircuit
open Qatlib.Papers.MonteCarloInt20.PrnJump.Compiled
open Qatlib.Papers.MonteCarloInt20.MainResults.TermCode

namespace Qatlib.Papers.MonteCarloInt20.MainResults.InnerValidity

noncomputable local instance bodyDecision (n s d p : ℕ) : DecidableEq (BodyReg n s d p) :=
    instDecidableEqProd

/-- A known-gate lift is a unitary circuit when the original circuit and oracle are unitary and
the matrix homomorphism preserves unitarity. -/
theorem knownLift_unitary {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (f : Matrix I I ℂ →* Matrix J J ℂ)
    (hf : ∀ U,U ∈ unitaryGroup I ℂ → f U ∈ unitaryGroup J ℂ)
    (O : Matrix I I ℂ) (hO : O ∈ unitaryGroup I ℂ) (C : Circuit I) (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (knownLift f O C) := by
  intro U hU
  obtain ⟨s,hs,he⟩ := List.mem_map.mp hU
  have he' : f (stepMatrix O s)=U := by injection he
  rw [← he']
  apply hf
  cases s with
  | query => exact hO
  | gate V => exact hC V hs

/-- Extending a native PRN matrix by spectator identities preserves unitarity. -/
theorem nativeLiftHom_unitary (n s d p : ℕ)
    (U : Matrix (Reg (width n (s+d+1))) (Reg (width n (s+d+1))) ℂ)
    (hU : U ∈ unitaryGroup (Reg (width n (s+d+1))) ℂ) :
    nativeLiftHom n s d p U ∈ unitaryGroup (BodyReg n s d p) ℂ :=
  tensorGate_unitary (tensorGate_unitary (unitaryGroup (Reg d) ℂ).one_mem
    (tensorGate_unitary hU (unitaryGroup (Reg (p+1)) ℂ).one_mem))
    (unitaryGroup Bool ℂ).one_mem

/-- The lifted compiled native PRN stage is a unitary circuit. -/
theorem nativeStage_unitary {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) :
    IsUnitaryCircuit (nativeStage (s:=s) (d:=d) (p:=p) a c) :=
  knownLift_unitary (nativeLiftHom n s d p) (nativeLiftHom_unitary n s d p) 1 (unitaryGroup (Reg (width n (s+d+1))) ℂ).one_mem
    (reflectionCompile (nativeWord a c (List.ofFn (fun q : Fin (s+d+1) => q)))) (native_unitary a c _)

/-- The term-query oracle extended by the flag identity is unitary. -/
theorem bodyOracle_unitary {n s d p : ℕ}
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) :
    bodyOracle termCode j ∈ unitaryGroup (BodyReg n s d p) ℂ :=
  tensorGate_unitary (queryOracle_unitary (k:=s+d+1) termCode j) (unitaryGroup Bool ℂ).one_mem

/-- The selected XOR loader on the inner body registers is unitary. -/
theorem loaderGate_unitary {n s d p : ℕ} (seed : ZMod (2^n)) (j : Reg s) :
    loaderGate (d:=d) (p:=p) seed j ∈ unitaryGroup (BodyReg n s d p) ℂ :=
  tensorGate_unitary (select_unitary _ (fun _ => tensorGate_unitary (xorMatrix_unitary _)
    (unitaryGroup (Reg (p+1)) ℂ).one_mem)) (unitaryGroup Bool ℂ).one_mem

/-- The PRN-loading and term-query computation is a unitary circuit. -/
theorem computeCircuit_unitary {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) :
    IsUnitaryCircuit (computeCircuit (d:=d) (p:=p) a c seed j) := by
  simp only [computeCircuit,isUnitaryCircuit_append,isUnitaryCircuit_gate,isUnitaryCircuit_query,
    isUnitaryCircuit_nil,and_true]
  exact ⟨loaderGate_unitary (d:=d) (p:=p) seed j,nativeStage_unitary (s:=s) (d:=d) (p:=p) a c⟩

/-- The complete inner compute-rotate-uncompute preparation is a unitary circuit
[KanekoEtAl2020]. -/
theorem bodyCircuit_unitary {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) :
    IsUnitaryCircuit (bodyCircuit (d:=d) (p:=p) a c seed j) := by
  have hC := computeCircuit_unitary (d:=d) (p:=p) a c seed j
  have hH : termHadamard n s d p ∈ unitaryGroup (BodyReg n s d p) ℂ :=
    tensorGate_unitary (tensorGate_unitary (hadamardN_unitary d)
      (unitaryGroup (Data n (s+d+1) p) ℂ).one_mem) (unitaryGroup Bool ℂ).one_mem
  have hR : codeRotation n s d p ∈ unitaryGroup (BodyReg n s d p) ℂ :=
    payoffRotation_mem_unitaryGroup _ (fun v => decodeCode_bounds p v.2.2)
  simp only [bodyCircuit,isUnitaryCircuit_append,isUnitaryCircuit_gate,isUnitaryCircuit_nil,and_true]
  exact ⟨⟨⟨hH,hC⟩,hR⟩,isUnitaryCircuit_reverseCircuit hC⟩

end Qatlib.Papers.MonteCarloInt20.MainResults.InnerValidity
