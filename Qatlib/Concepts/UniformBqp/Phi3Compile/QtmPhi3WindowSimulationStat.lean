/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QtmSimulation.Phi3Compilation.QtmCellPhi3CompilationStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CircuitImpl.Phi3Universal

open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.WalkFind.SearchAlgorithm

namespace Qatlib.Concepts.UniformBqp.Phi3Compile
open Matrix

def QtmPhi3WindowSimulation : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (A : Type) [Fintype A] [DecidableEq A]
    (M : LocalQTM Q A) (b n t : ℕ) (hb : Fintype.card (CellState Q A) ≤ 2^b),
    0 < n → 0 < t → n ≤ t →
    let e := finiteBasisCode (CellState Q A) b hb
    ∃ gs : List (Phi3Gate ((2*t+1)*b+3)),
      IsUnitaryCircuit (phi3Compile gs) ∧ QueryCount (phi3Compile gs) = 0 ∧
      GateCount (phi3Compile gs) = gs.length ∧
      gs.length ≤ t*((2*t-1)*phi3PaddingBudget (3*b)+(2*t+1)*phi3PaddingBudget b) ∧
      ∀ (x : Fin n → A) (c : WindowCfg t Q A),
        Normalized (qtmPhi3State t b e (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M n x)))) ∧
        Normalized (Run (1 : Matrix (Reg ((2*t+1)*b+3)) (Reg ((2*t+1)*b+3)) ℂ) (phi3Compile gs)
          (qtmPhi3State t b e (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M n x))))) ∧
        Run (1 : Matrix (Reg ((2*t+1)*b+3)) (Reg ((2*t+1)*b+3)) ℂ) (phi3Compile gs)
          (qtmPhi3State t b e (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M n x)))) =
          qtmPhi3State t b e (windowEmbed ((windowStep M)^t*ᵥKet (initWindowCfg M n x))) ∧
        BornProb (Run (1 : Matrix (Reg ((2*t+1)*b+3)) (Reg ((2*t+1)*b+3)) ℂ) (phi3Compile gs)
          (qtmPhi3State t b e (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M n x)))))
            (qtmPhi3Basis t b e (windowEncode c)) =
          BornProb ((windowStep M)^t*ᵥKet (initWindowCfg M n x)) c

end Qatlib.Concepts.UniformBqp.Phi3Compile
