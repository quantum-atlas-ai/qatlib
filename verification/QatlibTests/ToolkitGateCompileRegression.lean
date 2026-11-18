/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CircuitLang.QueryWords
public import Qatlib.Concepts.GateKit.Cor74Net
public import Qatlib.Concepts.GateKit.Cor74Counts
public import Qatlib.Concepts.GateKit.MultiControl
public import Qatlib.Concepts.CircuitImpl.MultiControl.BarencoSharpDefs
public import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
public import Qatlib.Foundations.QueryWordCore.Circuit
public import Qatlib.Foundations.PureStateMath.Qubit
public import Qatlib.Concepts.CostModels.Profile
public import Qatlib.Concepts.CostModels.Budget

@[expose] public section

/-! The compiled Corollary 7.4 product keeps its gate-counting conventions separate.
These examples check the measured counts, budget comparisons, and matrix semantics.

* Measured profile of the seven-wire instance: zero queries, sixteen Toffoli macro
  blocks, seventy-one one-qubit and sixty two-qubit elementary gates summing to the
  elementary count 131, twenty-five literal T/T† gates, and unmodeled depth and
  width (`none`, never a fake zero).
* Positive budget: the measured profile meets `cor74Budget 7` through `cor7Cert`.
* Counterexample for the fieldwise budget: a profile with an inflated one-qubit count of one
  thousand still passes the per-field budget while its elementary total exceeds the
  paper's `48 * n - 204` bound — the seven-field `BudgetLe` cannot express sum
  bounds (`notFreeBasic`).
* Negative zero-cost check: `none` never stands in for a measured zero, even against
  a zero budget (`notZeroCost`), and the fully opaque profile fails outright
  (`opaqueFails`).
* Matrix recheck: the compiled denotation equals the reflection program matrix
  (`denoteReflCor7`), and the ideal multi-controlled NOT matrix reproduces the
  positive and negative ket instances (`cor7netHit`, `cor7netMiss`). -/

set_option autoImplicit false
set_option warningAsError true

open Matrix
open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CircuitLang.QueryWords
open Qatlib.Concepts.GateKit
open Qatlib.Concepts.CostModels.Profile
open Qatlib.Concepts.CostModels.Budget

namespace QatlibTests.ToolkitGateCompile

/-- The measured query count of the seven-wire instance is a genuine zero. -/
private theorem cor7queries : (cor74Profile cor7Net).queries = some 0 := by
  simp only [cor74Profile]

/-- The measured one-qubit count of the seven-wire instance is seventy-one. -/
private theorem cor7oneQ : (cor74Profile cor7Net).oneQ = some 71 := by
  simp only [cor74Profile, Cor74Net.word]
  show some (oneQOf (cor74Word 5 cor7Ctl cor7Spc cor7Tgt)) = some 71
  rw [cor74OneQ 5 cor7Ctl cor7Spc cor7Tgt (by omega)]

/-- The measured two-qubit count of the seven-wire instance is sixty. -/
private theorem cor7twoQ : (cor74Profile cor7Net).twoQ = some 60 := by
  simp only [cor74Profile, Cor74Net.word]
  show some (twoQOf (cor74Word 5 cor7Ctl cor7Spc cor7Tgt)) = some 60
  rw [cor74TwoQ 5 cor7Ctl cor7Spc cor7Tgt (by omega)]

/-- The measured literal T-count of the seven-wire instance is twenty-five. -/
private theorem cor7tGate : (cor74Profile cor7Net).tCount = some 25 := by
  simp only [cor74Profile, Cor74Net.word]
  show some (tGateOf (cor74Word 5 cor7Ctl cor7Spc cor7Tgt)) = some 25
  rw [cor74TGate 5 cor7Ctl cor7Spc cor7Tgt (by omega)]

/-- Depth is unmodeled for the compiled product. -/
private theorem cor7depth : (cor74Profile cor7Net).depth = none := by
  simp only [cor74Profile]

/-- Width is unmodeled for the compiled product. -/
private theorem cor7width : (cor74Profile cor7Net).width = none := by
  simp only [cor74Profile]

/-- Field-wise measured profile of the seven-wire instance, together with the
elementary total: the two counts sum to 131, which is exactly the compiled
gate count of the same word. -/
theorem cor7CountsVal :
    (cor74Profile cor7Net).queries = some 0 ∧
    (cor74Profile cor7Net).macroGates = some 16 ∧
    (cor74Profile cor7Net).oneQ = some 71 ∧
    (cor74Profile cor7Net).twoQ = some 60 ∧
    (cor74Profile cor7Net).tCount = some 25 ∧
    (cor74Profile cor7Net).depth = none ∧
    (cor74Profile cor7Net).width = none ∧
    oneQOf cor7Word + twoQOf cor7Word = 131 ∧
    GateCount (reflectionCompile cor7Word) = 131 :=
  ⟨cor7queries, cor7Macro, cor7oneQ, cor7twoQ, cor7tGate, cor7depth, cor7width,
    by
      rw [oneTwoSum]
      have hl : cor7Word.length = 48 * 5 - 109 :=
        cor74Word_length 5 cor7Ctl cor7Spc cor7Tgt (by omega)
      omega,
    by
      rw [gateCount_reflectionCompile]
      have hl : cor7Word.length = 48 * 5 - 109 :=
        cor74Word_length 5 cor7Ctl cor7Spc cor7Tgt (by omega)
      omega⟩

/-- Positive budget instance: the measured profile of the compiled product fits the
seven-wire source budget, via the compilation cost certificate. -/
theorem cor7CertFits : BudgetLe (cor74Profile cor7Net) (cor74Budget 7) :=
  cor7Cert.fits

/-- The profile of the seven-wire instance with the one-qubit slot inflated to one
thousand gates. -/
noncomputable def overOneQ : CostProfile := { cor74Profile cor7Net with oneQ := some 1000 }

/-- Seam negative for the cost slot: the inflated profile still conforms to the
per-field budget — the budget constrains only queries and macro blocks — while its
elementary total of one thousand sixty gates already exceeds the paper's `48 * 7 -
204 = 132` basic-operation bound. The seven-field `BudgetLe` cannot express this
sum bound; the exact sum bound on the real product is `cor74BasicBound`. -/
theorem notFreeBasic :
    BudgetLe overOneQ (cor74Budget 7) ∧ ¬ (1000 + 60 ≤ 48 * 7 - 204) :=
  ⟨budgetLeIntro
    ⟨0, rfl, Nat.le_refl 0⟩
    ⟨16, cor7Macro, by norm_num⟩
    trivial trivial trivial trivial trivial,
    by omega⟩

/-- Zero-cost negative: an unmodeled measurement never satisfies a constrained slot,
not even a zero budget — `none` is never a stand-in for a measured zero, while the
real product's query count is the measured zero `some 0`. -/
theorem notZeroCost : ¬ optLe none (some 0) ∧ (cor74Profile cor7Net).queries = some 0 :=
  ⟨optLeNoneNeg, cor7queries⟩

/-- Opaque negative: the fully unmodeled profile fails the seven-wire budget
outright because the budget constrains queries. -/
theorem opaqueFails : ¬ BudgetLe opaqueProfile (cor74Budget 7) :=
  budgetNoOpaque rfl

/-- The circuit semantics and the matrix denotation agree on the compiled word:
`denoteRefl` instantiates on `cor7Word`. -/
theorem denoteReflCor7 :
    Denote (1 : Matrix (Reg 7) (Reg 7) ℂ) (reflectionCompile cor7Word) =
      reflectionProgramMatrix cor7Word :=
  denoteRefl cor7Word

/-- Matrix recheck on the positive ket: the ideal multi-controlled NOT matrix of
the compiled network reproduces the `cor7Hit` outcome. -/
theorem cor7netHit :
    ApplyGate (mcnotMatrix cor7Net.m cor7Net.ctl cor7Net.tgt)
        (Ket (fun k : Fin 7 => decide (k.val ≠ 5))) = Ket (fun _ : Fin 7 => true) := by
  rw [← cor74NetMatrix cor7Net, cor74DenoteEq cor7Net _]
  exact (cor7Matrix _).symm.trans cor7Hit

/-- Matrix recheck on the negative ket: the ideal multi-controlled NOT matrix of
the compiled network reproduces the `cor7Miss` outcome. -/
theorem cor7netMiss :
    ApplyGate (mcnotMatrix cor7Net.m cor7Net.ctl cor7Net.tgt)
        (Ket (fun k : Fin 7 => decide (k.val ≠ 0))) =
      Ket (fun k : Fin 7 => decide (k.val ≠ 0)) := by
  rw [← cor74NetMatrix cor7Net, cor74DenoteEq cor7Net _]
  exact (cor7Matrix _).symm.trans cor7Miss

end QatlibTests.ToolkitGateCompile
