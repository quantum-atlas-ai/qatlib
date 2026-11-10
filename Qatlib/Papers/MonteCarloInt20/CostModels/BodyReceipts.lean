/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.InnerCircuit
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

inductive BodyTag where
  | termForward | termBackward | nativeArithmetic | indexCompute | termHadamard | codeRotation
  deriving DecidableEq

def invertTag : BodyTag → BodyTag
  | .termForward => .termBackward
  | .termBackward => .termForward
  | t => t

abbrev TaggedCircuit (I : Type) := List (BodyTag × Step I)

def reverseTagged {I : Type} [Fintype I] [DecidableEq I] (w : TaggedCircuit I) : TaggedCircuit I :=
  w.reverse.map (fun a => (invertTag a.1,reverseStep a.2))

theorem reverseTagged_compile {I : Type} [Fintype I] [DecidableEq I] (w : TaggedCircuit I) :
    (reverseTagged w).map Prod.snd=ReverseCircuit (w.map Prod.snd) := by
  simp [reverseTagged,ReverseCircuit,List.map_map,List.map_reverse,Function.comp_def]

def computeTagged {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) :
    TaggedCircuit (BodyReg n s d p) :=
  [(.indexCompute,.gate (loaderGate (d:=d) (p:=p) seed j))]++
  (nativeStage (s:=s) (d:=d) (p:=p) a c).map (fun step => (.nativeArithmetic,step))++[(.termForward,.query)]

def bodyTagged {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) :
    TaggedCircuit (BodyReg n s d p) :=
  [(.termHadamard,.gate (termHadamard n s d p))]++computeTagged (d:=d) (p:=p) a c seed j++
    [(.codeRotation,.gate (codeRotation n s d p))]++reverseTagged (computeTagged (d:=d) (p:=p) a c seed j)

theorem computeTagged_compile {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) :
    (computeTagged (d:=d) (p:=p) a c seed j).map Prod.snd=computeCircuit (d:=d) (p:=p) a c seed j := by
  simp [computeTagged,computeCircuit,List.map_append,List.map_map,Function.comp_def]

theorem bodyTagged_compile {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s) :
    (bodyTagged (d:=d) (p:=p) a c seed j).map Prod.snd=bodyCircuit (d:=d) (p:=p) a c seed j := by
  simp only [bodyTagged,List.map_append,reverseTagged_compile,computeTagged_compile,List.map_cons,List.map_nil]
  rfl

def bodyCount {I : Type} (t : BodyTag) (w : TaggedCircuit I) : ℕ :=
  (w.map (fun a => if a.1=t then 1 else 0)).sum

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

def pricedBody {I : Type} (qTerm cNative cIndex cHad cRot : ℕ) (w : TaggedCircuit I) : ℕ :=
  qTerm*(bodyCount .termForward w+bodyCount .termBackward w)+
  cNative*bodyCount .nativeArithmetic w+cIndex*bodyCount .indexCompute w+
  cHad*bodyCount .termHadamard w+cRot*bodyCount .codeRotation w

theorem pricedBody_eq {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n)) (j : Reg s)
    (qTerm cNative cIndex cHad cRot : ℕ) :
    pricedBody qTerm cNative cIndex cHad cRot (bodyTagged (d:=d) (p:=p) a c seed j)=
      2*qTerm+2*(nativeWord a c (List.ofFn (fun q : Fin (s+d+1) => q))).length*cNative+
        2*cIndex+cHad+cRot := by
  have h := bodyTagged_counts (p:=p) (d:=d) a c seed j
  rw [pricedBody,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2]
  ring

end Qatlib.Papers.MonteCarloInt20.CostModels.BodyReceipts
