/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.InnerCircuit

/-!
# Tagged inner-body circuits and fee ledgers

`BodyTag` classifies term accesses, native arithmetic, index computation, term Hadamards, and
code rotations in an inner-body circuit. Erasing the tags from `computeTagged` and `bodyTagged`
recovers their corresponding circuit words, and tagged reversal agrees with circuit reversal.

Exact category counts give the weighted expression `pricedBody_eq`, connecting the explicit body
construction to cost accounting for [KanekoEtAl2020].

## Main statements

* `bodyTagged_compile`: Erasing body tags gives the underlying body circuit.
* `bodyTagged_counts`: Compute the six category counts of the tagged body.
* `pricedBody_eq`: Evaluate the weighted fee from those counts.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped Classical
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.CircuitReversal.ReversalAlgebra
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Papers.MonteCarloInt20.PrnJump.Compiled
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerOracle
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerCircuit

namespace Qatlib.Papers.MonteCarloInt20.CostModels.BodyReceipts

/-- The six operation categories for inner-body accounting: forward and backward term accesses,
native arithmetic, index computation, term Hadamards, and code rotations. -/
inductive BodyTag where
  | termForward | termBackward | nativeArithmetic | indexCompute | termHadamard | codeRotation
  deriving DecidableEq

/-- Exchange forward and backward term tags while leaving the other body tags unchanged. -/
def invertTag : BodyTag → BodyTag
  | .termForward => .termBackward
  | .termBackward => .termForward
  | t => t

/-- A list of circuit steps paired with body-accounting tags. -/
abbrev TaggedCircuit (I : Type) := List (BodyTag × Step I)

/-- Reverse a tagged circuit word, reverse each step, and exchange forward and backward term
tags. -/
def reverseTagged {I : Type} [Fintype I] [DecidableEq I] (w : TaggedCircuit I) : TaggedCircuit I :=
  w.reverse.map (fun a => (invertTag a.1,reverseStep a.2))

/-- Erasing tags after tagged reversal gives the reversal of the circuit obtained by erasing
tags first. -/
theorem reverseTagged_compile {I : Type} [Fintype I] [DecidableEq I] (w : TaggedCircuit I) :
    (reverseTagged w).map Prod.snd=ReverseCircuit (w.map Prod.snd) := by
  simp [reverseTagged,ReverseCircuit,List.map_map,List.map_reverse,Function.comp_def]

/-- The tagged computation word consisting of index loading, native arithmetic, and a forward
term query. -/
def computeTagged {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) :
    TaggedCircuit (BodyReg n s d p) :=
  [(.indexCompute,.gate (loaderGate (d:=d) (p:=p) seed j))]++
  (nativeStage (s:=s) (d:=d) (p:=p) a c).map (fun step => (.nativeArithmetic,step))++[(.termForward,.query)]

/-- The tagged body word consisting of a term Hadamard, computation, code rotation, and reversed
computation. -/
def bodyTagged {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) :
    TaggedCircuit (BodyReg n s d p) :=
  [(.termHadamard,.gate (termHadamard n s d p))]++computeTagged (d:=d) (p:=p) a c seed j++
    [(.codeRotation,.gate (codeRotation n s d p))]++reverseTagged (computeTagged (d:=d) (p:=p) a c seed j)

/-- Erasing the tags from `computeTagged` yields `computeCircuit`. -/
theorem computeTagged_compile {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) :
    (computeTagged (d:=d) (p:=p) a c seed j).map Prod.snd=computeCircuit (d:=d) (p:=p) a c seed j := by
  simp [computeTagged,computeCircuit,List.map_append,List.map_map,Function.comp_def]

/-- Erasing the tags from `bodyTagged` yields `bodyCircuit`. -/
theorem bodyTagged_compile {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) :
    (bodyTagged (d:=d) (p:=p) a c seed j).map Prod.snd=bodyCircuit (d:=d) (p:=p) a c seed j := by
  simp only [bodyTagged,List.map_append,reverseTagged_compile,computeTagged_compile,List.map_cons,List.map_nil]
  rfl

/-- The number of steps of a tagged circuit word carrying the specified body tag. -/
def bodyCount {I : Type} (t : BodyTag) (w : TaggedCircuit I) : ℕ :=
  (w.map (fun a => if a.1=t then 1 else 0)).sum

/-- The tagged body has one forward term query, one backward query, twice the native-word length
in arithmetic steps, two index computations, one term Hadamard, and one code rotation; see
[KanekoEtAl2020]. -/
theorem bodyTagged_counts {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) :
    bodyCount .termForward (bodyTagged (d:=d) (p:=p) a c seed j)=1 ∧
    bodyCount .termBackward (bodyTagged (d:=d) (p:=p) a c seed j)=1 ∧
    bodyCount .nativeArithmetic (bodyTagged (d:=d) (p:=p) a c seed j)=
      2*(nativeWord a c (List.ofFn (fun q : Fin (s+d+1) => q))).length ∧
    bodyCount .indexCompute (bodyTagged (d:=d) (p:=p) a c seed j)=2 ∧
    bodyCount .termHadamard (bodyTagged (d:=d) (p:=p) a c seed j)=1 ∧
    bodyCount .codeRotation (bodyTagged (d:=d) (p:=p) a c seed j)=1 := by
  simp [bodyCount,bodyTagged,computeTagged,reverseTagged,invertTag,nativeStage,knownLift,
    reflectionCompile,List.map_append,List.map_reverse,List.map_map,Function.comp_def,List.sum_append]
  omega

/-- The weighted sum of body-tag counts, charging the same term fee for forward and backward
queries and separate fees for the other categories. -/
def pricedBody {I : Type} (qTerm cNative cIndex cHad cRot : ℕ) (w : TaggedCircuit I) : ℕ :=
  qTerm*(bodyCount .termForward w+bodyCount .termBackward w)+
  cNative*bodyCount .nativeArithmetic w+cIndex*bodyCount .indexCompute w+
  cHad*bodyCount .termHadamard w+cRot*bodyCount .codeRotation w

/-- The tagged body fee is `2 * qTerm` plus twice the native-word length times `cNative`, plus
`2 * cIndex + cHad + cRot`; see [KanekoEtAl2020]. -/
theorem pricedBody_eq {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s)
    (qTerm cNative cIndex cHad cRot : ℕ) :
    pricedBody qTerm cNative cIndex cHad cRot (bodyTagged (d:=d) (p:=p) a c seed j)=
      2*qTerm+2*(nativeWord a c (List.ofFn (fun q : Fin (s+d+1) => q))).length*cNative+
        2*cIndex+cHad+cRot := by
  have h := bodyTagged_counts (p:=p) (d:=d) a c seed j
  rw [pricedBody,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2]
  ring

end Qatlib.Papers.MonteCarloInt20.CostModels.BodyReceipts
