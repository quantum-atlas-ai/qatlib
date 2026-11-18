/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CircuitImpl.MultiControl.BarencoSharpDefs
public import Qatlib.Concepts.CircuitImpl.MultiControl.BarencoSharp
public import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
public import Qatlib.Foundations.QueryWordCore.Circuit
public import Qatlib.Foundations.PureStateMath.Qubit

/-!
# GateKit multi-control scaffold for Corollary 7.4

Demand: `Corollary 7.4` (Barenco et al., quant-ph/9503016v1, Corollary 7.4): on an
`n`-bit network with `n ≥ 7`, the `(n - 2)`-controlled NOT is simulated by `8 * (n - 5)`
three-bit Toffoli blocks and by at most `48 * n - 204` basic operations. The Corollary 7.4
construction uses `cor74Blocks`/`cor74Word` (`Qatlib.Concepts.CircuitImpl.MultiControl.BarencoSharpDefs`) with the ledger
`cor74Word_semantics`/`corollary7_4_two_layer_ledger` (`Qatlib.Concepts.CircuitImpl.MultiControl.BarencoSharp`), wrapped by
`Qatlib.Papers.ElemGates95.MultiControl.Section7.corollary7_4_paper`.

## Public no-work synthesis inventory of `NoWorkTwoLevelSynthesis`

The imported module `Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis`
exports 14 definitions and 45 public theorems (21 further lemmas are private). The
definitions are `noWorkOneBitEquiv`, `noWorkControlSplit`, `singleAncillaSplit`,
`singleAncillaEmbed`, `noWorkDirtyTripleSteps`, `noWorkPrefixAnd`,
`noWorkDirtyPrefixStage`, `noWorkDirtyPrefixBits`, `noWorkDirtyPrefixSteps`,
`noWorkToffoliUpdate`, `noWorkDirtyPrefixTransform`, `noWorkDirtyPrefixLayout`,
`noWorkBorrowedAndSteps`, and `noWorkControlWires`. Its actual consumer
`Qatlib/Papers/ElemGates95/MultiControl/Section7/MultibitNetworks.lean` (import on
line 15) uses eight declarations: `noWorkPrefixAnd` (in `corollary7_4_paper`,
`lemma7_8_approx`, `lemma7_8_with_tolerance`, `lemma7_9`, `corollary7_10_paper`, and
`lemma7_11`), `noWorkControlSplit` and `no_work_multi_known_control_local_table_and_cost`
(in `corollary7_6`), `noWork_multi_control_wire_table` (in `lemma7_9`),
`noWork_single_dirty_and_table` and `noWork_and_table_wireState` (in `lemma7_11`), and
`singleAncillaEmbed` and `single_ancilla_known_control_local_table_and_cost` (in
`corollary7_12_paper`). Their precise types are provided by the imported public modules.

This module covers the Corollary 7.4 construction. It reuses the public construction unchanged at its smallest legal size `n = 7` and adds
satisfiable positive and negative basis-state instances of its matrix semantics.
Placed-wire circuit interfaces are treated separately in the circuit-language modules.

## Main statements

* `cor7Ledger`: the Corollary 7.4 ledger is satisfiable at `n = 7` (16 Toffoli blocks, four
  exact blocks, at most 132 elementary gates, legality, zero queries).
* `cor7Matrix`/`cor7Sem`: the compiled program matrix acts on every basis ket as the
  five-controlled target toggle.
* `cor7Hit`/`cor7Miss`: concrete positive and negative ket instances.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.GateKit

/-- The five control wires `0, 1, 2, 3, 4` of the seven-wire Corollary 7.4 instance,
extended to a total wire assignment by clamping. -/
def cor7Ctl : ℕ → Fin 7 := fun i => if h : i < 7 then ⟨i, h⟩ else ⟨0, by omega⟩

/-- The target wire `5` of the seven-wire Corollary 7.4 instance. -/
def cor7Tgt : Fin 7 := ⟨5, by omega⟩

/-- The borrowed spectator wire `6` of the seven-wire Corollary 7.4 instance. -/
def cor7Spc : Fin 7 := ⟨6, by omega⟩

/-- The Corollary 7.4 elementary gate word at `n = 7`, with five controls. -/
noncomputable def cor7Word : List (ReflectionGate 7) := cor74Word 5 cor7Ctl cor7Spc cor7Tgt

/-- Below seven the control-wire function is the canonical embedding. -/
private theorem cor7Ctl_lt (i : ℕ) (hi : i < 7) : cor7Ctl i = ⟨i, hi⟩ := by
  simp only [cor7Ctl, dite_eq_left hi]

/-- The five chosen control wires are pairwise distinct below five. -/
private theorem cor7CtlInj : Set.InjOn cor7Ctl (Set.Iio 5) := by
  intro i hi j hj he
  simp only [Set.mem_Iio] at hi hj
  rw [cor7Ctl_lt i (by omega), cor7Ctl_lt j (by omega)] at he
  exact congrArg Fin.val he

/-- Every chosen control wire differs from the borrowed spectator wire. -/
private theorem cor7CtlNeSpc : ∀ i < 5, cor7Ctl i ≠ cor7Spc := by
  intro i hi he
  rw [cor7Ctl_lt i (by omega : i < 7)] at he
  have hv := congrArg Fin.val he
  dsimp only [cor7Spc] at hv
  omega

/-- Every chosen control wire differs from the target wire. -/
private theorem cor7CtlNeTgt : ∀ i < 5, cor7Ctl i ≠ cor7Tgt := by
  intro i hi he
  rw [cor7Ctl_lt i (by omega : i < 7)] at he
  have hv := congrArg Fin.val he
  dsimp only [cor7Tgt] at hv
  omega

/-- The borrowed spectator wire and the target wire are distinct. -/
private theorem cor7SpcNeTgt : cor7Spc ≠ cor7Tgt := by
  intro he
  have hv := congrArg Fin.val (he : cor7Spc = cor7Tgt)
  dsimp only [cor7Spc, cor7Tgt] at hv
  omega

/-- Corollary 7.4 of [BarencoEtAl1995] is satisfiable at its smallest legal size `n = 7`:
the concrete seven-wire layout realizes `8 * (7 - 5)` Toffoli blocks with four exact
blocks, at most `48 * 7 - 204` elementary gates, legality, zero oracle queries, gate
count equal to the word length, and exact conjunction-toggle ket semantics. -/
theorem cor7Ledger :
    toffCount (cor74Blocks 5 cor7Ctl cor7Spc cor7Tgt) = 8 * (7 - 5) ∧
      exactCount (cor74Blocks 5 cor7Ctl cor7Spc cor7Tgt) = 4 ∧
      cor7Word.length ≤ 48 * 7 - 204 ∧
      reflectionLegal cor7Word ∧
      QueryCount (reflectionCompile cor7Word) = 0 ∧
      GateCount (reflectionCompile cor7Word) = cor7Word.length ∧
      ∀ x : Reg 7,
        Run (1 : Matrix (Reg 7) (Reg 7) ℂ) (reflectionCompile cor7Word) (Ket x) =
          Ket (Function.update x cor7Tgt
            (x cor7Tgt ^^ noWorkPrefixAnd (fun i => x (cor7Ctl i)) 5)) :=
  corollary7_4_two_layer_ledger (n := 7) cor7Ctl cor7Spc cor7Tgt (by omega)
    cor7CtlInj cor7CtlNeSpc cor7CtlNeTgt cor7SpcNeTgt

/-- The seven-wire Corollary 7.4 word toggles the target ket by the five-control
conjunction and preserves every other wire. -/
theorem cor7Sem (x : Reg 7) :
    Run (1 : Matrix (Reg 7) (Reg 7) ℂ) (reflectionCompile cor7Word) (Ket x) =
      Ket (Function.update x cor7Tgt
        (x cor7Tgt ^^ noWorkPrefixAnd (fun i => x (cor7Ctl i)) 5)) :=
  cor7Ledger.2.2.2.2.2.2 x

/-- Matrix-level correctness of the seven-wire Corollary 7.4 compilation: the program
matrix `reflectionProgramMatrix cor7Word` acts on every computational basis ket exactly
as the five-controlled target toggle. -/
theorem cor7Matrix (x : Reg 7) :
    ApplyGate (reflectionProgramMatrix cor7Word) (Ket x) =
      Ket (Function.update x cor7Tgt
        (x cor7Tgt ^^ noWorkPrefixAnd (fun i => x (cor7Ctl i)) 5)) := by
  rw [← run_reflectionCompile]
  exact cor7Sem x

/-- The seven-wire Corollary 7.4 program matrix is unitary; legality of the word
carries unitarity with no further hypothesis. -/
theorem cor7Unitary : reflectionProgramMatrix cor7Word ∈ Matrix.unitaryGroup (Reg 7) ℂ :=
  reflectionProgramMatrix_unitary cor7Word cor7Ledger.2.2.2.1

/-- Positive satisfiable instance of the Corollary 7.4 matrix semantics: with all five controls
true and the target false, the compiled matrix sends the ket to the all-true ket, so
the target flips exactly once. -/
theorem cor7Hit :
    ApplyGate (reflectionProgramMatrix cor7Word) (Ket (fun k : Fin 7 => decide (k.val ≠ 5))) =
      Ket (fun _ : Fin 7 => true) := by
  rw [cor7Matrix]
  have hp : noWorkPrefixAnd (fun i => (fun k : Fin 7 => decide (k.val ≠ 5)) (cor7Ctl i)) 5
        = true := by decide
  rw [hp]
  have hu : Function.update (fun k : Fin 7 => decide (k.val ≠ 5)) cor7Tgt
        ((fun k : Fin 7 => decide (k.val ≠ 5)) cor7Tgt ^^ true) = (fun _ : Fin 7 => true) := by
    funext k
    by_cases hk : k = cor7Tgt
    · subst hk
      simp only [Function.update_self]
      decide
    · simp only [Function.update_of_ne hk]
      exact decide_eq_true_iff.mpr fun h => hk (Fin.ext h)
  rw [hu]

/-- Negative satisfiable instance of the Corollary 7.4 matrix semantics: with control zero
false, the remaining controls true, and the target true, the compiled matrix leaves
the ket unchanged. This excludes the unconditional-flip reading and any reading
controlled by fewer than all five wires. -/
theorem cor7Miss :
    ApplyGate (reflectionProgramMatrix cor7Word) (Ket (fun k : Fin 7 => decide (k.val ≠ 0))) =
      Ket (fun k : Fin 7 => decide (k.val ≠ 0)) := by
  rw [cor7Matrix]
  have hp : noWorkPrefixAnd (fun i => (fun k : Fin 7 => decide (k.val ≠ 0)) (cor7Ctl i)) 5
        = false := by decide
  rw [hp]
  have hu : Function.update (fun k : Fin 7 => decide (k.val ≠ 0)) cor7Tgt
        ((fun k : Fin 7 => decide (k.val ≠ 0)) cor7Tgt ^^ false) =
      (fun k : Fin 7 => decide (k.val ≠ 0)) := by
    funext k
    by_cases hk : k = cor7Tgt
    · subst hk
      simp only [Function.update_self]
      decide
    · simp only [Function.update_of_ne hk]
  rw [hu]

end Qatlib.Concepts.GateKit
