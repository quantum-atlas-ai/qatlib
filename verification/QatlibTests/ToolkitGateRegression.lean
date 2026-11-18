/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GateKit.MultiControl
public import Qatlib.Concepts.CircuitImpl.MultiControl.BarencoSharpDefs
public import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
public import Qatlib.Foundations.QueryWordCore.Circuit
public import Qatlib.Foundations.PureStateMath.Qubit

/-! The seven-wire instance of Corollary 7.4 keeps its three counting units apart (Toffoli blocks, elementary
gates, oracle queries) and excludes both the identity and the unconditional-flip
misreading of the compiled multi-controlled toggle. Counts refer to the compiled
reflection word, not to a different gate basis. -/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateKit

namespace QatlibTests.ToolkitGate

/-- Computational basis kets are equal only when their labels are equal. -/
private theorem ketInj {I : Type} [DecidableEq I] {x y : I}
    (h : Ket x = Ket y) : x = y := by
  by_cases hxy : x = y
  · exact hxy
  · have h1 := congrFun h x
    rw [ket_self, ket_ne hxy] at h1
    exact absurd h1 one_ne_zero

/-- At `n = 7` the compiled Corollary 7.4 word has sixteen Toffoli blocks, one hundred
thirty-one elementary gates, and zero oracle queries: three different counting units
that must not be conflated with each other. -/
theorem countsDisjoint :
    toffCount (cor74Blocks 5 cor7Ctl cor7Spc cor7Tgt) = 16 ∧
      GateCount (reflectionCompile cor7Word) = 131 ∧
      QueryCount (reflectionCompile cor7Word) = 0 ∧
      toffCount (cor74Blocks 5 cor7Ctl cor7Spc cor7Tgt) ≠
        GateCount (reflectionCompile cor7Word) := by
  obtain ⟨_, _, _, _, hq, hg, _⟩ := cor7Ledger
  have hc := cor74Blocks_census 5 cor7Ctl cor7Spc cor7Tgt (by omega)
  have hl : cor7Word.length = 48 * 5 - 109 :=
    cor74Word_length 5 cor7Ctl cor7Spc cor7Tgt (by omega)
  refine ⟨hc.2.2, ?_, hq, ?_⟩
  · rw [hg, hl]
  · rw [hg]
    have ht : toffCount (cor74Blocks 5 cor7Ctl cor7Spc cor7Tgt) = 8 * 5 - 24 := hc.2.2
    omega

/-- The positive instance rules out the identity reading: the compiled matrix moves
the ket whose five controls are all on. -/
theorem matrixNotId :
    ApplyGate (reflectionProgramMatrix cor7Word) (Ket (fun k : Fin 7 => decide (k.val ≠ 5))) ≠
      Ket (fun k : Fin 7 => decide (k.val ≠ 5)) := by
  rw [cor7Hit]
  intro heq
  have hket : (fun _ : Fin 7 => true) = (fun k : Fin 7 => decide (k.val ≠ 5)) := ketInj heq
  have h5 : (true : Bool) = (false : Bool) := congrFun hket cor7Tgt
  exact Bool.noConfusion h5

/-- The negative instance rules out the unconditional-flip reading: the compiled
matrix does not toggle the target on every input register. -/
theorem notUncondFlip :
    ¬ ∀ x : Reg 7, ApplyGate (reflectionProgramMatrix cor7Word) (Ket x) =
      Ket (Function.update x cor7Tgt (!(x cor7Tgt))) := by
  intro h
  have h0 := h (fun k : Fin 7 => decide (k.val ≠ 0))
  rw [cor7Miss] at h0
  have hket : (fun k : Fin 7 => decide (k.val ≠ 0)) =
      Function.update (fun k : Fin 7 => decide (k.val ≠ 0)) cor7Tgt
        (!(fun k : Fin 7 => decide (k.val ≠ 0)) cor7Tgt) := ketInj h0
  have h5 : (true : Bool) = (false : Bool) := congrFun hket cor7Tgt
  exact Bool.noConfusion h5

end QatlibTests.ToolkitGate
