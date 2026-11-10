/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InstrumentCore.PatternCompile.UniversalGraphDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Concepts.ClusterPatterns.PauliNetwork
open Qatlib.Concepts.ClusterPatterns.Preentangled
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
set_option autoImplicit false
namespace Qatlib.Concepts.InstrumentCore.PatternCompile
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators ComplexOrder Kronecker

def UniversalRawFrameReadout : Prop :=
  ∀ (n L : ℕ) (G : GraphWord n L), networkLegal (List.ofFn G) →
    observedLeafCount (mbqcRawProgram G)=2^(graphWireCount G) ∧
    (∀ h : GraphHistory G,
      (mbqcRawLeaf G h).accepted=true ∧ (mbqcRawLeaf G h).queries=0 ∧
      (mbqcRawLeaf G h).gates=2*L+2*graphWireCount G ∧
      (mbqcRawLeaf G h).measurements=graphWireCount G ∧
      (graphMessage G h).length=graphWireCount G) ∧
    (∀ (h : GraphHistory G) (R : ℕ)
      (X : Matrix (Fin (2^n) × Fin R) (Fin (2^n) × Fin R) ℂ),
      mbqcRawReference G h R X=(1/2 : ℂ)^(graphWireCount G) •
        (TensorGate (pauliFrameGate n (graphFinalFrame G h)*networkLogicalMatrix (List.ofFn G))
          (1 : Operator R)*X*
          (TensorGate (pauliFrameGate n (graphFinalFrame G h)*networkLogicalMatrix (List.ofFn G))
            (1 : Operator R))ᴴ)) ∧
    (∃ I : Instrument (GraphHistory G) (2^n) (2^n),
      (∀ h ρ, I.branch h ρ=mbqcRawBranch G h ρ) ∧
      ∀ (ρ : Operator (2^n)), IsDensityOperator ρ → ∀ h,
        instrumentProb I ρ h=(1/2 : ℝ)^(graphWireCount G)) ∧
    ∀ (ρ : Operator (2^n)), IsDensityOperator ρ → ∀ E : Finset (Fin (2^n)),
      (∀ h : GraphHistory G, mbqcDensityEvent (mbqcRawBranch G h ρ)
        (mbqcDecodedEvent (graphFinalFrame G h) E)=
          (1/2 : ℝ)^(graphWireCount G)*mbqcDensityEvent
            (networkLogicalMatrix (List.ofFn G)*ρ*(networkLogicalMatrix (List.ofFn G))ᴴ) E) ∧
      (∑ h : GraphHistory G, mbqcDensityEvent (mbqcRawBranch G h ρ)
        (mbqcDecodedEvent (graphFinalFrame G h) E))=
          mbqcDensityEvent (networkLogicalMatrix (List.ofFn G)*ρ*
            (networkLogicalMatrix (List.ofFn G))ᴴ) E

end Qatlib.Concepts.InstrumentCore.PatternCompile
