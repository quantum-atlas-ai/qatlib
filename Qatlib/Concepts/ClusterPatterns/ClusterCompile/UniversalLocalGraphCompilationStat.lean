/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InstrumentCore.PatternCompile.UniversalGraphDefs

/-!
# Specification of universal local graph compilation

This module defines `UniversalLocalGraphCompilation` for legal lists of single-qubit and CNOT
gates, expressing the one-way compilation objective of [RaussendorfBriegel2000]. The
specification combines network legality and counts, logical semantics up to a unit-norm scalar,
uniformly weighted instrument branches, finite-reference output, and exact leaf execution costs.

## Main statements

* `UniversalLocalGraphCompilation`: For local counts `a` and `b`, requires `4*a + 2*b`
  measurements and at most `16*a + 10*b + 2*n` gates per accepted leaf.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.InstrumentCore.PatternCompile
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Concepts.ClusterPatterns.PauliNetwork
open Qatlib.Concepts.ClusterPatterns.Preentangled

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
set_option autoImplicit false
namespace Qatlib.Concepts.ClusterPatterns.ClusterCompile
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators ComplexOrder Kronecker

/-- The specification of graph compilation for legal local gate lists, including exact network
counts, logical semantics up to phase, uniform instrument branches, finite-reference output,
and leaf resource bounds. -/
def UniversalLocalGraphCompilation : Prop :=
  ∀ (n : ℕ) (gs : List (ReflectionGate n)), reflectionLegal gs →
    let G := mbqcGraphWord gs
    let a := (mbqcLocalCounts gs).1
    let b := (mbqcLocalCounts gs).2
    (mbqcCompiledWord gs).length=4*a+3*b ∧
    List.ofFn G=mbqcCompiledWord gs ∧ networkLegal (List.ofFn G) ∧
    networkCounts (List.ofFn G)=(4*a+2*b,b) ∧
    ‖mbqcLocalScalar gs‖=1 ∧
    networkLogicalMatrix (List.ofFn G)=mbqcLocalScalar gs • mbqcLogicalMatrix gs ∧
    (∀ (R : ℕ) (h : GraphHistory G)
      (X : Matrix (Fin (2^n) × Fin R) (Fin (2^n) × Fin R) ℂ),
      graphActualReference true G h R X=(1/2 : ℂ)^(4*a+2*b) •
        (TensorGate (mbqcLogicalMatrix gs) (1 : Operator R)*X*
          (TensorGate (mbqcLogicalMatrix gs) (1 : Operator R))ᴴ)) ∧
    (∃ I : Instrument (GraphHistory G) (2^n) (2^n),
      (∀ h ρ, I.branch h ρ=graphActualBranch true G h ρ) ∧
      (∀ (ρ : Operator (2^n)), IsDensityOperator ρ → ∀ h,
        instrumentProb I ρ h=(1/2 : ℝ)^(4*a+2*b)) ∧
      ∀ (R : ℕ) (X : Matrix (Fin (2^n) × Fin R) (Fin (2^n) × Fin R) ℂ),
        (∑ h : GraphHistory G, graphActualReference true G h R X)=
          TensorGate (mbqcLogicalMatrix gs) (1 : Operator R)*X*
            (TensorGate (mbqcLogicalMatrix gs) (1 : Operator R))ᴴ) ∧
    ∀ h : GraphHistory G,
      (graphProgramLeaf true G h).accepted=true ∧ (graphProgramLeaf true G h).queries=0 ∧
      (graphProgramLeaf true G h).gates=16*a+10*b+frameCorrectionCost (graphFinalFrame G h) ∧
      (graphProgramLeaf true G h).gates ≤ 16*a+10*b+2*n ∧
      (graphProgramLeaf true G h).measurements=4*a+2*b ∧
      (graphMessage G h).length=4*a+2*b

end Qatlib.Concepts.ClusterPatterns.ClusterCompile
