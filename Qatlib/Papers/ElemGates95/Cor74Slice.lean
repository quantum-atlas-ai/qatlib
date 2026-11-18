/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GateKit.Cor74Counts
public import Qatlib.Concepts.GateKit.GateContract

@[expose] public section

/-!
# Corollary 7.4 first slice: word semantics and the 8(n−5) count coincide at n = 7

The first auditable slice of the ElemGates95 line (Corollary 7.4). It
joins the two halves the claim needs: the seven-wire Cor74 network is a query word
whose denotation is the program matrix, and its macro-gate
count is exactly 8(n − 5) at n = 7, i.e. sixteen macro blocks. What is not claimed:
the literal-T count of the compiled artifact, the ε-approximate regime, and general
`n` beyond the frozen seven-wire instance.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CircuitLang.QueryWords
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateKit
open Qatlib.Concepts.GateKit.GateContract

namespace Qatlib.Papers.ElemGates95.Cor74Slice

/-- The seven-wire Cor74 network's word denotation is its program matrix. -/
theorem cor7WordDenote :
    Denote (1 : Matrix (Reg 7) (Reg 7) ℂ) (reflectionCompile cor7Word)
      = reflectionProgramMatrix cor7Word :=
  denoteRefl cor7Word

/-- The seven-wire instance meets the corollary's count exactly: sixteen
controlled-NOT macro blocks equal 8 · (7 − 5). -/
theorem cor7_count : (cor74Profile cor7Net).macroGates = some (8 * (7 - 5)) :=
  cor7Macro

/-- The count and the word semantics are properties of the same network object:
one `Cor74Net 7` carries both. -/
theorem cor7_same_net :
    (cor74Profile cor7Net).macroGates = some (8 * (7 - 5)) ∧
      Denote (1 : Matrix (Reg 7) (Reg 7) ℂ) (reflectionCompile cor7Word)
        = reflectionProgramMatrix cor7Word :=
  ⟨cor7_count, cor7WordDenote⟩

end Qatlib.Papers.ElemGates95.Cor74Slice
