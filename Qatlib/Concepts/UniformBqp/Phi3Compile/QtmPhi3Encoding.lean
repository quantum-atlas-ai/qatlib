/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.FiniteBasisPadding
import Qatlib.Foundations.StandardModel.WindowSim.QtmSimulationDefs
import Qatlib.Concepts.CircuitImpl.Phi3Universal.Phi3Defs

/-!
# Binary encodings of QTM window states

This module defines `qtmWindowBasisCode`, which concatenates fixed-width cell encodings across a
finite QTM window. `qtmPhi3State` and `qtmPhi3Basis` extend the resulting binary register by
three known wires, while `phi3PaddingBudget` records the gate budget used in compilation.

For background, see [Yao1993].

## Main statements

* `qtmWindowBasisCode`: binary encoding of a window basis register.
* `qtmPhi3State`: embedding into the Phi3 simulation register.
* `phi3PaddingBudget`: explicit padding budget.

## References

* [Yao, 1993][Yao1993]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.WalkFind.SearchAlgorithm

namespace Qatlib.Concepts.UniformBqp.Phi3Compile
open Matrix
open scoped Classical

/-- The padding gate budget `768 * (b + 1)^3 * 4^b` for a binary register of width `b`. -/
def phi3PaddingBudget (b : ℕ) : ℕ := 768*(b+1)^3*4^b

/-- Encodes each cell of a window register in `b` bits and concatenates the encodings into `(2 *
t + 1) * b` bits. -/
def qtmWindowBasisCode {Q A : Type} (t b : ℕ) (e : CellState Q A → Reg b)
    (r : WReg t Q A) : Reg ((2*t+1)*b) :=
  fun w => let i := (finProdFinEquiv (m := 2*t+1) (n := b)).symm w
           e (r i.1) i.2

/-- Embeds a window state through its binary basis encoding and extends the register with three
known wires. -/
def qtmPhi3State {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    (t b : ℕ) (e : CellState Q A → Reg b) (ψ : QState (WReg t Q A)) :
    QState (Reg ((2*t+1)*b+3)) :=
  knownWireEmbed (knownPrefixWires ((2*t+1)*b) 3)
    (finiteBasisPadState (qtmWindowBasisCode t b e) ψ)

/-- Extends a binary-encoded window basis register with the three known wires used by Phi3
compilation. -/
def qtmPhi3Basis {Q A : Type} (t b : ℕ) (e : CellState Q A → Reg b)
    (r : WReg t Q A) : Reg ((2*t+1)*b+3) :=
  knownWireExtend (knownPrefixWires ((2*t+1)*b) 3) (qtmWindowBasisCode t b e r)

end Qatlib.Concepts.UniformBqp.Phi3Compile
