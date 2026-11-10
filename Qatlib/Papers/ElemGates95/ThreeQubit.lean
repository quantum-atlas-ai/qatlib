/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemGates95.QubitControl.Section5
import Qatlib.Concepts.CircuitImpl.MultiControl.Corollary62Elem
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
import Qatlib.Concepts.CircuitImpl.MultiControl.CountToffoliGadget
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Papers.ElemGates95.QubitControl.Section4

namespace Qatlib.Papers.ElemGates95.ThreeQubit

def twoControlledGate (U : Matrix Bool Bool ℂ) :
    Matrix (Bool × (Bool × Bool)) (Bool × (Bool × Bool)) ℂ :=
  BlockDiag (fun b => if b then ControlledGate U else 1)

theorem lemma6_1 (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    ∃ V : Matrix Bool Bool ℂ, V ∈ Matrix.unitaryGroup Bool ℂ ∧ V * V = U ∧
      ∀ a b : Bool,
        (if a then V else 1) * (if a ^^ b then star V else 1) *
          (if b then V else 1) = if a && b then U else 1 := by
  obtain ⟨V, hV, hVV⟩ := noWork_unitary_square_root U hU
  have hL : star V * V = 1 := (Matrix.mem_unitaryGroup_iff').mp hV
  have hR : V * star V = 1 := (Matrix.mem_unitaryGroup_iff).mp hV
  refine ⟨V, hV, hVV, ?_⟩
  intro a b
  cases a <;> cases b <;> simp [hL, hR, hVV]

theorem corollary6_2_paper (N : ℕ) (c : ℕ → Fin N) (t : Fin N)
    (hc : Set.InjOn c (Set.Iio 2)) (ht : ∀ i < 2, c i ≠ t)
    (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    ∃ gs : List (ReflectionGate N),
      reflectionLegal gs ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      (gs.filter Sum.isLeft).length ≤ 8 ∧
      (gs.filter Sum.isRight).length ≤ 8 ∧
      ∀ (x : Reg N) (φ : QState Bool),
        Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile gs)
            (multiWireState t x φ) =
          multiWireState t x
            (ApplyGate (if noWorkPrefixAnd (fun i => x (c i)) 2 then U else 1) φ) :=
  corollary6_2 N c t hc ht U hU

theorem section6_2_relative_toffoli (N : ℕ) (a b t : Fin N)
    (_hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    reflectionLegal (sourceRelativeToffoliSteps a b t) ∧
      (sourceRelativeToffoliSteps a b t).length = 7 ∧
      ((sourceRelativeToffoliSteps a b t).filter Sum.isLeft).length = 4 ∧
      ((sourceRelativeToffoliSteps a b t).filter Sum.isRight).length = 3 ∧
      QueryCount (reflectionCompile (sourceRelativeToffoliSteps a b t)) = 0 ∧
      GateCount (reflectionCompile (sourceRelativeToffoliSteps a b t)) = 7 ∧
      ∀ x : Reg N, Run (1 : Matrix (Reg N) (Reg N) ℂ)
        (reflectionCompile (sourceRelativeToffoliSteps a b t)) (Ket x) =
        (if x a && !x b && x t then (-1 : ℂ) else 1) •
          Ket (Function.update x t (x t ^^ (x a && x b))) := by
  obtain ⟨hlen, hsingle⟩ := sourceRelativeToffoliSteps_counts a b t
  refine ⟨sourceRelativeToffoliSteps_legal a b t hat hbt, hlen, hsingle,
    rfl, queryCount_reflectionCompile _, ?_, sourceRelativeToffoliSteps_ket a b t hat hbt⟩
  rw [gateCount_reflectionCompile, hlen]

end Qatlib.Papers.ElemGates95.ThreeQubit
