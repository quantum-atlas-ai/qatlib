/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InstrumentCore.PatternCompile.UniversalGraphDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Concepts.ClusterPatterns.PauliNetwork
open Qatlib.Concepts.ClusterPatterns.Preentangled
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
set_option autoImplicit false
namespace Qatlib.Concepts.InstrumentCore.PatternCompile
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators ComplexOrder Kronecker

def UniversalKnownUnitaryGraph : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (U : Matrix (Reg n) (Reg n) ℂ),
    U ∈ Matrix.unitaryGroup (Reg n) ℂ →
    ∃ gs : List (ReflectionGate n), reflectionLegal gs ∧
      gs.length ≤ 768*(n+1)^3*4^n ∧ mbqcLogicalMatrix gs=relabelGate (bitVecEquiv n) U ∧
      (mbqcCompiledWord gs).length ≤ 4*(768*(n+1)^3*4^n) ∧
      graphWireCount (mbqcGraphWord gs) ≤ 4*(768*(n+1)^3*4^n) ∧
      networkLegal (List.ofFn (mbqcGraphWord gs)) ∧
      (∀ (h : GraphHistory (mbqcGraphWord gs)) (R : ℕ)
        (X : Matrix (Fin (2^n) × Fin R) (Fin (2^n) × Fin R) ℂ),
        graphActualReference true (mbqcGraphWord gs) h R X=
          (1/2 : ℂ)^(graphWireCount (mbqcGraphWord gs)) •
            (TensorGate (relabelGate (bitVecEquiv n) U) (1 : Operator R)*X*
              (TensorGate (relabelGate (bitVecEquiv n) U) (1 : Operator R))ᴴ) ∧
        mbqcRawReference (mbqcGraphWord gs) h R X=
          (1/2 : ℂ)^(graphWireCount (mbqcGraphWord gs)) •
            (TensorGate (pauliFrameGate n (graphFinalFrame (mbqcGraphWord gs) h)*
              relabelGate (bitVecEquiv n) U) (1 : Operator R)*X*
              (TensorGate (pauliFrameGate n (graphFinalFrame (mbqcGraphWord gs) h)*
                relabelGate (bitVecEquiv n) U) (1 : Operator R))ᴴ)) ∧
      (∀ h : GraphHistory (mbqcGraphWord gs),
        (mbqcRawLeaf (mbqcGraphWord gs) h).accepted=true ∧
        (mbqcRawLeaf (mbqcGraphWord gs) h).queries=0 ∧
        (mbqcRawLeaf (mbqcGraphWord gs) h).gates ≤ 16*(768*(n+1)^3*4^n) ∧
        (mbqcRawLeaf (mbqcGraphWord gs) h).measurements ≤ 4*(768*(n+1)^3*4^n) ∧
        (graphMessage (mbqcGraphWord gs) h).length ≤ 4*(768*(n+1)^3*4^n)) ∧
      (∀ (E : Finset (Fin (2^n))) (h : GraphHistory (mbqcGraphWord gs)) (y : Fin (2^n)),
        (mbqcReadoutLeaf (mbqcGraphWord gs) E h y).queries=0 ∧
        (mbqcReadoutLeaf (mbqcGraphWord gs) E h y).gates ≤ 16*(768*(n+1)^3*4^n) ∧
        (mbqcReadoutLeaf (mbqcGraphWord gs) E h y).measurements ≤ 4*(768*(n+1)^3*4^n)+1) ∧
      ∀ (ρ : Operator (2^n)), IsDensityOperator ρ → ∀ E : Finset (Fin (2^n)),
        mbqcReadoutAcceptance (mbqcGraphWord gs) E ρ=
          mbqcDensityEvent (relabelGate (bitVecEquiv n) U*ρ*(relabelGate (bitVecEquiv n) U)ᴴ) E

end Qatlib.Concepts.InstrumentCore.PatternCompile
