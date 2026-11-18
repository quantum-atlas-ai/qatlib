/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CircuitLang.SelFill
public import Qatlib.Concepts.CircuitLang.WordOps

/-! Constructive wire filling and the conjugation and noncommutativity
operations of the unified word semantics. Positive examples cover the non-canonical
three-wire completion, the adjoint of query words, and unitarity of conjugated words;
the negative example shows the two opposite controlled NOTs do not commute. -/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace QatlibTests.WirePlacement

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CircuitLang.WireReg
open Qatlib.Concepts.CircuitLang.LocGates
open Qatlib.Concepts.CircuitLang.SelSplit
open Qatlib.Concepts.CircuitLang.SelFill
open Qatlib.Concepts.CircuitLang.CtrlGates
open Qatlib.Concepts.CircuitLang.QueryWords
open Qatlib.Concepts.CircuitLang.WordOps
open scoped BigOperators Classical Matrix

/-- The non-adjacent selection really selects wires two and zero. -/
theorem exSel_hits : exSel.sel ⟨0, by omega⟩ = ⟨2, by omega⟩ := exSel_vals.1

/-- The filled complement of the non-adjacent selection is the untouched wire one. -/
theorem exCompl_one :
    ((mkSplit (m := 1) (k := 2) exSel).compl ⟨0, by omega⟩ : Wire 3).val = 1 :=
  exCompl_val

/-- The filled completion placed on a unitary block stays unitary: unitarity of
arbitrary-wire placement follows from the construction. -/
theorem fillPlace_uni :
    PlacedSel (mkSplit (lastSel 1 1)) cnotU ∈ Matrix.unitaryGroup (Reg (1 + 1)) ℂ :=
  placedSel_uni cnotU_uni

/-- The adjoint of a gate-then-query word denotes the daggered product. -/
theorem adj_gq (o U : Matrix Bool Bool ℂ) :
    Denote o (wordAdj o.conjTranspose [Step.query, Step.gate U])
      = o.conjTranspose * U.conjTranspose := by
  rw [denoteAdj, denote_query, denote_gate, denote_nil, Matrix.one_mul,
    Matrix.conjTranspose_mul]

/-- The adjoint of the empty word is the empty word and denotes the identity. -/
theorem adj_nil :
    Denote (1 : Matrix Bool Bool ℂ) (wordAdj (1 : Matrix Bool Bool ℂ) []) = 1 := by
  simp [wordAdj, denote_nil]

/-- A one-query word under a unitary oracle conjugates to a unitary matrix. -/
theorem adjQuery_uni {o : Matrix Bool Bool ℂ} (ho : o ∈ Matrix.unitaryGroup Bool ℂ) :
    Denote o (wordAdj o.conjTranspose [Step.query]) ∈ Matrix.unitaryGroup Bool ℂ := by
  exact wordAdjUni o ho (by simp)

/-- Regression: the two opposite controlled NOTs do not commute. -/
theorem cn_noncomm : cn * cnR ≠ cnR * cn := cn_cnR_noncomm

/-- The forward controlled NOT on |11⟩ produces |10⟩. -/
theorem cn_TT : cn *ᵥ Ket (fun _ => true) = Ket (fun w => decide (w = ⟨0, by omega⟩)) :=
  cn_ketTT

end QatlibTests.WirePlacement
