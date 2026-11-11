/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.VariableTimeDefs

/-!
# Variable-time program syntax and compilation

`VtStep` describes forward, backward, and controlled stage access together with fixed gates on
an extended workspace and control register. This module defines access-time accounting, matrix
interpretation, compilation, legality, and the embedding of data states.

This development concerns variable-time amplitude amplification in [Ambainis2012].

## Main statements

* `compileWord`: interpretation of program words as circuits.
* `WordLegal`: bounds on stage indices and unitarity of fixed gates.
* `embedState`: embedding with a fixed workspace value and false control bit.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LocalMachine.LocalTransport

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Matrix

variable {C : Type} [Fintype C] [DecidableEq C]

namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel

/-- The register consisting of a workspace value, a Boolean control bit, and a three-flag
payload register. -/
abbrev VtReg (W C : Type) [Fintype C] : Type := W × (Bool × (Fin 3 × C))

/-- Instructions for forward, backward, and controlled stage calls, together with arbitrary
fixed gates on the extended register. -/
inductive VtStep (W C : Type) [Fintype C] : Type where
  | stageF : ℕ → VtStep W C
  | stageB : ℕ → VtStep W C
  | cstageF : ℕ → VtStep W C
  | cstageB : ℕ → VtStep W C
  | fixGate : Matrix (VtReg W C) (VtReg W C) ℂ → VtStep W C

/-- Charges each stage call at index `j` the time `2^j` and fixed gates zero stage-access time. -/
def stepTime {W C : Type} [Fintype C] : VtStep W C → ℕ
  | .stageF j => 2 ^ j
  | .stageB j => 2 ^ j
  | .cstageF j => 2 ^ j
  | .cstageB j => 2 ^ j
  | .fixGate _ => 0

/-- The sum of stage-access times of the instructions in a program word. -/
def wordStageTime {W C : Type} [Fintype C] (w : List (VtStep W C)) : ℕ :=
  (w.map stepTime).sum

/-- The matrix semantics of a variable-time instruction on the extended workspace, control, and
data register. -/
noncomputable def stepMatrix {W C : Type} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]
    (stages : List (Matrix (Fin 3 × C) (Fin 3 × C) ℂ)) :
    VtStep W C → Matrix (VtReg W C) (VtReg W C) ℂ
  | .stageF j =>
      TensorGate (1 : Matrix W W ℂ)
        (TensorGate (1 : Matrix Bool Bool ℂ) (stages.getD j 0))
  | .stageB j =>
      TensorGate (1 : Matrix W W ℂ)
        (TensorGate (1 : Matrix Bool Bool ℂ) (stages.getD j 0)ᴴ)
  | .cstageF j =>
      TensorGate (1 : Matrix W W ℂ)
        (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (stages.getD j 0))
  | .cstageB j =>
      TensorGate (1 : Matrix W W ℂ)
        (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (stages.getD j 0)ᴴ)
  | .fixGate U => U

/-- Compiles a program word into a circuit by replacing each instruction with its matrix gate. -/
noncomputable def compileWord {W C : Type} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]
    (stages : List (Matrix (Fin 3 × C) (Fin 3 × C) ℂ))
    (w : List (VtStep W C)) : Circuit (VtReg W C) :=
  w.map (fun s => Step.gate (stepMatrix stages s))

/-- The condition that all stage calls use valid indices and all fixed gates appearing in a word
are unitary. -/
def WordLegal {W C : Type} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]
    (stages : List (Matrix (Fin 3 × C) (Fin 3 × C) ℂ))
    (w : List (VtStep W C)) : Prop :=
  (∀ j : ℕ, (∃ s ∈ w, ∃ _ : Bool, s = .stageF j ∨ s = .stageB j
      ∨ s = .cstageF j ∨ s = .cstageB j) → j < stages.length) ∧
    ∀ U : Matrix (VtReg W C) (VtReg W C) ℂ, .fixGate U ∈ w →
      U ∈ Matrix.unitaryGroup (VtReg W C) ℂ

/-- Embeds a data state with workspace fixed to `w₀` and the control bit fixed to `false`. -/
noncomputable def embedState {W C : Type} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]
    (w₀ : W) (χ : QState (Fin 3 × C)) : QState (VtReg W C) :=
  fun p => if p.1 = w₀ ∧ p.2.1 = false then χ p.2.2 else 0
end Qatlib.Papers.VarTimeAmpAmp10.StopModel
