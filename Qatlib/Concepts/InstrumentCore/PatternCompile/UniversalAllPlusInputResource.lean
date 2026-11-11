/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InstrumentCore.PatternCompile.UniversalGraphDefs

/-!
# Specification of all-plus input resources

The proposition `UniversalAllPlusInputResource` specifies an all-plus resource for legal
reflection programs on a nonzero number of qubits. The resource is independent of the classical
input, while the compiled input graph must have the stated length, wire count, legality, and
density properties.

The specification also requires explicit Pauli-frame branch states, exact raw and readout
resource counts, and agreement of decoded and physical readout probabilities with the reflection
program on each classical input. These are resource and readout requirements for the measurement
scheme of [RaussendorfBriegel2000].

## Main statements

* `UniversalAllPlusInputResource`: input-independent resources, branch semantics, and readout
  probability requirements.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
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

/-- The specification that legal reflection programs possess an all-plus graph resource
independent of the classical input, with explicit compiled lengths, wire counts, branch
states, and measurement resources. It requires the summed decoded events and physical
readout acceptance to equal the reflection program's output probabilities on every classical
input. -/
def UniversalAllPlusInputResource : Prop :=
  ∀ (n : ℕ) [NeZero n] (gs : List (ReflectionGate n)), reflectionLegal gs →
    let L := 8*n+(mbqcCompiledWord gs).length
    let w := 8*n+4*(mbqcLocalCounts gs).1+2*(mbqcLocalCounts gs).2
    (∀ x y : Reg n, mbqcAllPlusResource (mbqcInputGraph gs x)=
      mbqcAllPlusResource (mbqcInputGraph gs y)) ∧
    ∀ x : Reg n,
      List.ofFn (mbqcInputGraph gs x)=mbqcCompiledWord (mbqcClassicalInputWord gs x) ∧
      (mbqcCompiledWord (mbqcClassicalInputWord gs x)).length=L ∧
      networkLegal (List.ofFn (mbqcInputGraph gs x)) ∧
      graphWireCount (mbqcInputGraph gs x)=w ∧
      mbqcPreparedResource (mbqcInputGraph gs x)=mbqcAllPlusResource (mbqcInputGraph gs x) ∧
      IsDensityOperator (mbqcAllPlusResource (mbqcInputGraph gs x)) ∧
      (∀ h : GraphHistory (mbqcInputGraph gs x),
        mbqcRawBranch (mbqcInputGraph gs x) h (outerProduct (Uniform (Fin (2^n))))=
          (1/2 : ℂ)^w •
            (pauliFrameGate n (graphFinalFrame (mbqcInputGraph gs x) h)*
              outerProduct (fun i : Fin (2^n) =>
                (reflectionProgramMatrix gs *ᵥ Qatlib.Foundations.PureStateMath.Ket x) ((bitVecEquiv n).symm i))*
              (pauliFrameGate n (graphFinalFrame (mbqcInputGraph gs x) h))ᴴ) ∧
        (mbqcRawLeaf (mbqcInputGraph gs x) h).accepted=true ∧
        (mbqcRawLeaf (mbqcInputGraph gs x) h).queries=0 ∧
        (mbqcRawLeaf (mbqcInputGraph gs x) h).gates=2*L+2*w ∧
        (mbqcRawLeaf (mbqcInputGraph gs x) h).measurements=w ∧
        (graphMessage (mbqcInputGraph gs x) h).length=w ∧
        ∀ (E : Finset (Fin (2^n))) (y : Fin (2^n)),
          (mbqcReadoutLeaf (mbqcInputGraph gs x) E h y).queries=0 ∧
          (mbqcReadoutLeaf (mbqcInputGraph gs x) E h y).gates=2*L+2*w ∧
          (mbqcReadoutLeaf (mbqcInputGraph gs x) E h y).measurements=w+1) ∧
      ∀ E : Finset (Fin (2^n)),
        (∑ h : GraphHistory (mbqcInputGraph gs x),
          mbqcDensityEvent (mbqcRawBranch (mbqcInputGraph gs x) h
            (outerProduct (Uniform (Fin (2^n)))))
            (mbqcDecodedEvent (graphFinalFrame (mbqcInputGraph gs x) h) E))=
          MeasureProb (fun i : Fin (2^n) =>
            (reflectionProgramMatrix gs *ᵥ Qatlib.Foundations.PureStateMath.Ket x) ((bitVecEquiv n).symm i)) E ∧
        mbqcReadoutAcceptance (mbqcInputGraph gs x) E (outerProduct (Uniform (Fin (2^n))))=
          MeasureProb (fun i : Fin (2^n) =>
            (reflectionProgramMatrix gs *ᵥ Qatlib.Foundations.PureStateMath.Ket x) ((bitVecEquiv n).symm i)) E

end Qatlib.Concepts.InstrumentCore.PatternCompile
