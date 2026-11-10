/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.VariableTimeDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LocalMachine.LocalTransport

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Matrix

variable {C : Type} [Fintype C] [DecidableEq C]

namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel

abbrev VtReg (W C : Type) [Fintype C] : Type := W × (Bool × (Fin 3 × C))

inductive VtStep (W C : Type) [Fintype C] : Type where
  | stageF : ℕ → VtStep W C
  | stageB : ℕ → VtStep W C
  | cstageF : ℕ → VtStep W C
  | cstageB : ℕ → VtStep W C
  | fixGate : Matrix (VtReg W C) (VtReg W C) ℂ → VtStep W C

def stepTime {W C : Type} [Fintype C] : VtStep W C → ℕ
  | .stageF j => 2 ^ j
  | .stageB j => 2 ^ j
  | .cstageF j => 2 ^ j
  | .cstageB j => 2 ^ j
  | .fixGate _ => 0

def wordStageTime {W C : Type} [Fintype C] (w : List (VtStep W C)) : ℕ :=
  (w.map stepTime).sum

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

noncomputable def compileWord {W C : Type} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]
    (stages : List (Matrix (Fin 3 × C) (Fin 3 × C) ℂ))
    (w : List (VtStep W C)) : Circuit (VtReg W C) :=
  w.map (fun s => Step.gate (stepMatrix stages s))

def WordLegal {W C : Type} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]
    (stages : List (Matrix (Fin 3 × C) (Fin 3 × C) ℂ))
    (w : List (VtStep W C)) : Prop :=
  (∀ j : ℕ, (∃ s ∈ w, ∃ _ : Bool, s = .stageF j ∨ s = .stageB j
      ∨ s = .cstageF j ∨ s = .cstageB j) → j < stages.length) ∧
    ∀ U : Matrix (VtReg W C) (VtReg W C) ℂ, .fixGate U ∈ w →
      U ∈ Matrix.unitaryGroup (VtReg W C) ℂ

noncomputable def embedState {W C : Type} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]
    (w₀ : W) (χ : QState (Fin 3 × C)) : QState (VtReg W C) :=
  fun p => if p.1 = w₀ ∧ p.2.1 = false then χ p.2.2 else 0
end Qatlib.Papers.VarTimeAmpAmp10.StopModel
