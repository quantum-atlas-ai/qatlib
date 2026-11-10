/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Data.Fintype.Basic

namespace Qatlib.Concepts.ClassicalTape.TapeCompilation

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

def BitMachineAfter (machine : Turing.TM0.Machine Γ Λ) (input : List Γ) :
    ℕ → Option (Turing.TM0.Cfg Γ Λ)
  | 0 => some (Turing.TM0.init input)
  | t + 1 => (BitMachineAfter machine input t).bind (Turing.TM0.step machine)

def BitMachineHaltsAt (machine : Turing.TM0.Machine Γ Λ)
    (input : List Γ) (t : ℕ) : Prop :=
  ∃ final, BitMachineAfter machine input t = some final ∧
    Turing.TM0.step machine final = none

def BitMachinePolynomialTime [Fintype Γ] [Fintype Λ]
    (machine : Turing.TM0.Machine Γ Λ) : Prop :=
  ∃ c k : ℕ, ∀ input : List Γ, ∃ t : ℕ,
    t ≤ c * input.length ^ k + c ∧ BitMachineHaltsAt machine input t

theorem bitMachineAfter_succ_of_halts {machine : Turing.TM0.Machine Γ Λ}
    {input : List Γ} {t : ℕ} (h : BitMachineHaltsAt machine input t) :
    BitMachineAfter machine input (t + 1) = none := by
  rcases h with ⟨final, hrun, hstop⟩
  simp [BitMachineAfter, hrun, hstop]

end Qatlib.Concepts.ClassicalTape.TapeCompilation
