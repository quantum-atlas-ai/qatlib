/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.FiniteBasisPadding
import Qatlib.Foundations.StandardModel.WindowSim.QtmSimulationDefs
import Qatlib.Concepts.CircuitImpl.Phi3Universal.Phi3Defs
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

def phi3PaddingBudget (b : ℕ) : ℕ := 768*(b+1)^3*4^b

def qtmWindowBasisCode {Q A : Type} (t b : ℕ) (e : CellState Q A → Reg b)
    (r : WReg t Q A) : Reg ((2*t+1)*b) :=
  fun w => let i := (finProdFinEquiv (m := 2*t+1) (n := b)).symm w
           e (r i.1) i.2

def qtmPhi3State {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    (t b : ℕ) (e : CellState Q A → Reg b) (ψ : QState (WReg t Q A)) :
    QState (Reg ((2*t+1)*b+3)) :=
  knownWireEmbed (knownPrefixWires ((2*t+1)*b) 3)
    (finiteBasisPadState (qtmWindowBasisCode t b e) ψ)

def qtmPhi3Basis {Q A : Type} (t b : ℕ) (e : CellState Q A → Reg b)
    (r : WReg t Q A) : Reg ((2*t+1)*b+3) :=
  knownWireExtend (knownPrefixWires ((2*t+1)*b) 3) (qtmWindowBasisCode t b e r)

end Qatlib.Concepts.UniformBqp.Phi3Compile
