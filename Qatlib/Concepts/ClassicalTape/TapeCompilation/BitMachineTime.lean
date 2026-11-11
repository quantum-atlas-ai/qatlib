/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Data.Fintype.Basic

/-!
# Exact-step execution and polynomial tape-machine time

This module defines exact-step TM0 execution by `BitMachineAfter`, halting at a specified step
by `BitMachineHaltsAt`, and a uniform integer polynomial bound by `BitMachinePolynomialTime`.
These definitions make explicit the tape-machine running-time convention used in
complexity-theoretic comparisons [BernsteinVazirani1997].

## Main statements

* `bitMachineAfter_succ_of_halts`: execution returns `none` one step after a halting
  configuration is reached.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

namespace Qatlib.Concepts.ClassicalTape.TapeCompilation

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- The optional configuration after exactly `t` TM0 steps from the initialized input,
propagating `none` after a halting step. -/
def BitMachineAfter (machine : Turing.TM0.Machine Γ Λ) (input : List Γ) :
    ℕ → Option (Turing.TM0.Cfg Γ Λ)
  | 0 => some (Turing.TM0.init input)
  | t + 1 => (BitMachineAfter machine input t).bind (Turing.TM0.step machine)

/-- The machine reaches a configuration after exactly `t` steps whose next transition is `none`. -/
def BitMachineHaltsAt (machine : Turing.TM0.Machine Γ Λ)
    (input : List Γ) (t : ℕ) : Prop :=
  ∃ final, BitMachineAfter machine input t = some final ∧
    Turing.TM0.step machine final = none

/-- There are natural constants `c` and `k` such that every input reaches a halting
configuration within `c * input.length^k + c` steps. -/
def BitMachinePolynomialTime [Fintype Γ] [Fintype Λ]
    (machine : Turing.TM0.Machine Γ Λ) : Prop :=
  ∃ c k : ℕ, ∀ input : List Γ, ∃ t : ℕ,
    t ≤ c * input.length ^ k + c ∧ BitMachineHaltsAt machine input t

/-- If the machine reaches a halting configuration at step `t`, its exact-step execution at step
`t + 1` is `none`. -/
theorem bitMachineAfter_succ_of_halts {machine : Turing.TM0.Machine Γ Λ}
    {input : List Γ} {t : ℕ} (h : BitMachineHaltsAt machine input t) :
    BitMachineAfter machine input (t + 1) = none := by
  rcases h with ⟨final, hrun, hstop⟩
  simp [BitMachineAfter, hrun, hstop]

end Qatlib.Concepts.ClassicalTape.TapeCompilation
