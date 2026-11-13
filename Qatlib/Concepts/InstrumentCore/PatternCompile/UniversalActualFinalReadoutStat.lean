/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InstrumentCore.PatternCompile.UniversalGraphDefs

/-!
# Specification of actual final readout

The proposition `UniversalActualFinalReadout` specifies physical final measurement for every
legal graph word. It records well-formedness, the leaf count `2^(graphWireCount G)*2^n`, leaf
operators and outcomes, Pauli-frame decoding, and exact resource fields.

For density inputs it requires the physical input to remain a density operator and the
acceptance value to equal the density-event value of the logical circuit. This formalizes
final-readout requirements for the measurement-based scheme of [RaussendorfBriegel2000].

## Main statements

* `UniversalActualFinalReadout`: the complete physical final-readout property for legal graph
  words.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.ShadowModels.ShadowChannel
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

/-- The specification that every legal graph word has a well-formed final-readout program with
exact leaf count, leaf operators, decoded acceptance, and resource fields. It also requires
a density physical input and equality between physical acceptance and the logical circuit's
output event value for every density input. -/
def UniversalActualFinalReadout : Prop :=
  ∀ (n L : ℕ) (G : GraphWord n L), networkLegal (List.ofFn G) →
    ∀ E : Finset (Fin (2^n)),
      observedWellFormed (mbqcReadoutProgram G E) ∧
      observedLeafCount (mbqcReadoutProgram G E)=2^(graphWireCount G)*2^n ∧
      (∀ (h : GraphHistory G) (y : Fin (2^n)),
        graphHistoryIndex G h * 2^n + y.val < observedLeafCount (mbqcReadoutProgram G E) ∧
        (mbqcReadoutLeaf G E h y).operator =
          Projector (Finset.univ.filter (fun r => mbqcOutputLabel G r=y)) *
            (mbqcRawLeaf G h).operator ∧
        (mbqcReadoutLeaf G E h y).accepted=decide (mbqcFrameDecode (graphFinalFrame G h) y ∈ E) ∧
        (mbqcReadoutLeaf G E h y).queries=0 ∧
        (mbqcReadoutLeaf G E h y).gates=2*L+2*graphWireCount G ∧
        (mbqcReadoutLeaf G E h y).measurements=graphWireCount G+1 ∧
        (mbqcReadoutLeaf G E h y).outcomes=(mbqcRawLeaf G h).outcomes ++ [(2^n,y.val)]) ∧
      ∀ (ρ : Operator (2^n)), IsDensityOperator ρ →
        IsDensityOperator (mbqcPhysicalInput G ρ) ∧
        mbqcReadoutAcceptance G E ρ=
          mbqcDensityEvent (networkLogicalMatrix (List.ofFn G)*ρ*
            (networkLogicalMatrix (List.ofFn G))ᴴ) E

end Qatlib.Concepts.InstrumentCore.PatternCompile
