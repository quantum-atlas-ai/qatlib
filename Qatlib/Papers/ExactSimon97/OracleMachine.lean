/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CircuitLang.XorOracle
public import Mathlib.Data.Fintype.Pi

@[expose] public section

/-!
# The ExactSimon97 oracle machine: first executable slice

A finite instruction-machine interface towards the computable oracle-machine
model of Theorem 9 and Corollary 10 of
ExactSimon97 ([BrassardHoyer1997], quant-ph/9704027v1). A classical oracle machine
is a *finite program* over the standard register layout of the toolkit
(`Qatlib.Concepts.CircuitLang.XorOracle.OReg`: address block, answer bit, work block): an explicit
deterministic step function reads the instruction at the program counter and
applies its register update, an `oracle` instruction consulting the oracle
function `Addr a → Bool` through the standard `xorInto` update. The consulted
oracle is code-enumerable: on the finite address space every oracle function is
realized by a finite first-match lookup code (`oracle_is_code`), so no classical
choice function sneaks into the interface.

The first machine lemmas are proved: the annotated step relation is functional
(`stepRel_det`, via `stepRel_iff`), and finite-depth execution is total by
structural fuel recursion, splits over fuel (`exec_add`), fixes halting
configurations (`step_halted`, `exec_halted`), and is fuel-insensitive once a
halting configuration is reached (`exec_mono`) — the precise sense in which
finite-depth execution terminates. A concrete single-query program runs the
interface for real (`one_query_exec`).

Honest non-coverage: this is the machine interface layer only. It does not model
success events or success probabilities, adaptive query transcripts, Theorem 9's
lower bound, oracle diagonalization with future-query isolation, or `QP^O`
complexity classes, and it does not yet endow `Qatlib.Papers.ExactSimon97.MainResults.ClProc` with these
execution semantics (`ClProc` remains a raw cost/success profile). Per DESIGN
§12.8, conditional assembly is not a full oracle program: nothing here is
presented as the original Corollary 10.

## Main statements

* `stepRel_iff`: the annotated step relation and the step function agree.
* `stepRel_det`: the step relation is deterministic.
* `oracle_is_code`: every oracle on the finite address space is code-enumerable.
* `exec_halted` / `exec_mono`: finite-depth execution halts stably and ignores
  excess fuel once halted.
* `one_query_exec`: the single-query program computes one `xorInto` update.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CircuitLang.XorOracle

namespace Qatlib.Papers.ExactSimon97.OracleMachine

variable {a w : ℕ}

/-- One instruction of the oracle machine over the standard register layout. -/
inductive Instr (a w : ℕ) : Type
  /-- Consult the oracle: XOR the oracle bit of the address block into the answer
  bit. -/
  | oracle : Instr a w
  /-- Flip one address bit of the query address. -/
  | flipA (i : Fin a) : Instr a w
  /-- Flip one work bit of the scratch memory. -/
  | flipW (i : Fin w) : Instr a w
  /-- Halt: the configuration is terminal. -/
  | halt : Instr a w
  deriving DecidableEq

/-- A finite program: the instruction list, read at the program counter. -/
abbrev Prog (a w : ℕ) : Type := List (Instr a w)

/-- The instruction read at program counter `k`; past the program end the machine
reads `halt`, so every configuration has a next instruction. -/
def instrAt (P : Prog a w) (k : ℕ) : Instr a w :=
  P.getD k Instr.halt

/-- Flip one address bit of the standard oracle register. -/
def flipAddr (i : Fin a) (x : OReg a w) : OReg a w :=
  (Function.update x.1 i (¬ x.1 i), x.2.1, x.2.2)

/-- Flip one work bit of the standard oracle register. -/
def flipWork (i : Fin w) (x : OReg a w) : OReg a w :=
  (x.1, x.2.1, Function.update x.2.2 i (¬ x.2.2 i))

/-- A machine configuration: program counter plus the full standard oracle
register (address block, answer bit, work block). -/
structure Conf (a w : ℕ) : Type where
  /-- The program counter. -/
  pc : ℕ
  /-- The address/answer/work register. -/
  reg : OReg a w

/-- The explicit deterministic step function: read the instruction at the program
counter, apply its register update — an `oracle` instruction consults the oracle
function `f` through the standard `xorInto` update — and advance the program
counter; a `halt` configuration is a fixed point. -/
def step (f : Addr a → Bool) (P : Prog a w) (c : Conf a w) : Conf a w :=
  match instrAt P c.pc with
  | Instr.oracle => ⟨c.pc + 1, xorInto f c.reg⟩
  | Instr.flipA i => ⟨c.pc + 1, flipAddr i c.reg⟩
  | Instr.flipW i => ⟨c.pc + 1, flipWork i c.reg⟩
  | Instr.halt => c

/-- The step equation at an oracle instruction: one consultation, one advance. -/
theorem step_oracle (f : Addr a → Bool) (P : Prog a w) (c : Conf a w)
    (h : instrAt P c.pc = Instr.oracle) :
    step f P c = ⟨c.pc + 1, xorInto f c.reg⟩ := by
  unfold step
  rw [h]

/-- The step equation at an address flip. -/
theorem step_flipA (f : Addr a → Bool) (P : Prog a w) (c : Conf a w) {i : Fin a}
    (h : instrAt P c.pc = Instr.flipA i) :
    step f P c = ⟨c.pc + 1, flipAddr i c.reg⟩ := by
  unfold step
  rw [h]

/-- The step equation at a work flip. -/
theorem step_flipW (f : Addr a → Bool) (P : Prog a w) (c : Conf a w) {i : Fin w}
    (h : instrAt P c.pc = Instr.flipW i) :
    step f P c = ⟨c.pc + 1, flipWork i c.reg⟩ := by
  unfold step
  rw [h]

/-- The step equation at a halt instruction: a fixed point. -/
theorem step_halt (f : Addr a → Bool) (P : Prog a w) (c : Conf a w)
    (h : instrAt P c.pc = Instr.halt) : step f P c = c := by
  unfold step
  rw [h]

/-- The annotated step relation, one constructor per instruction, each carrying
the proof that the program really reads that instruction at the program counter.
This is the form a transcript-consuming argument would use. -/
inductive StepRel (f : Addr a → Bool) (P : Prog a w) :
    Conf a w → Conf a w → Prop where
  /-- An oracle step consults `f` once through `xorInto` and advances. -/
  | oracle {c : Conf a w} (h : instrAt P c.pc = Instr.oracle) :
      StepRel f P c ⟨c.pc + 1, xorInto f c.reg⟩
  /-- An address-bit flip advances. -/
  | flipA {c : Conf a w} {i : Fin a} (h : instrAt P c.pc = Instr.flipA i) :
      StepRel f P c ⟨c.pc + 1, flipAddr i c.reg⟩
  /-- A work-bit flip advances. -/
  | flipW {c : Conf a w} {i : Fin w} (h : instrAt P c.pc = Instr.flipW i) :
      StepRel f P c ⟨c.pc + 1, flipWork i c.reg⟩
  /-- A halting configuration steps to itself. -/
  | halt {c : Conf a w} (h : instrAt P c.pc = Instr.halt) :
      StepRel f P c c

/-- The annotated relation and the step function present the same semantics:
relational and functional readings of one machine agree. -/
theorem stepRel_iff (f : Addr a → Bool) (P : Prog a w) (c t : Conf a w) :
    StepRel f P c t ↔ step f P c = t := by
  constructor
  · intro h
    cases h with
    | oracle h => exact step_oracle f P c h
    | flipA h => exact step_flipA f P c h
    | flipW h => exact step_flipW f P c h
    | halt h => exact step_halt f P c h
  · intro h
    cases hi : instrAt P c.pc with
    | oracle =>
        rw [step_oracle f P c hi] at h
        subst h
        exact StepRel.oracle hi
    | flipA =>
        rw [step_flipA f P c hi] at h
        subst h
        exact StepRel.flipA hi
    | flipW =>
        rw [step_flipW f P c hi] at h
        subst h
        exact StepRel.flipW hi
    | halt =>
        rw [step_halt f P c hi] at h
        subst h
        exact StepRel.halt hi

/-- The step relation is deterministic: a configuration has at most one
successor. -/
theorem stepRel_det (f : Addr a → Bool) (P : Prog a w) {c t₁ t₂ : Conf a w}
    (h₁ : StepRel f P c t₁) (h₂ : StepRel f P c t₂) : t₁ = t₂ := by
  rw [stepRel_iff] at h₁ h₂
  exact h₁.symm.trans h₂

/-- A halting configuration: the program reads `halt` at the program counter. -/
def halted (P : Prog a w) (c : Conf a w) : Prop :=
  instrAt P c.pc = Instr.halt

/-- Halting is decidable: the instruction read is decidable data. -/
instance haltedDecidable (P : Prog a w) (c : Conf a w) :
    Decidable (halted P c) :=
  inferInstanceAs (Decidable (instrAt P c.pc = Instr.halt))

/-- Halting configurations are fixed points of the step function. -/
theorem step_halted (f : Addr a → Bool) (P : Prog a w) (c : Conf a w)
    (h : halted P c) : step f P c = c := by
  unfold halted at h
  exact step_halt f P c h

/-- Finite-depth execution: iterate the step function `k` times from `c`. The
recursion is structural in the fuel, so every finite-depth run terminates by
construction. -/
def exec (f : Addr a → Bool) (P : Prog a w) : ℕ → Conf a w → Conf a w
  | 0, c => c
  | k + 1, c => exec f P k (step f P c)

/-- Fuel splits over execution: running `j + k` steps is running `j` steps and
then `k` further steps from the reached configuration. -/
theorem exec_add (f : Addr a → Bool) (P : Prog a w) (j k : ℕ) (c : Conf a w) :
    exec f P (j + k) c = exec f P k (exec f P j c) := by
  induction j generalizing c with
  | zero =>
      rw [Nat.zero_add]
      rfl
  | succ j ih =>
      have e1 : j + 1 + k = j + k + 1 := Nat.add_right_comm j 1 k
      rw [e1]
      simp only [exec]
      exact ih (step f P c)

/-- A halting configuration is stable under finite-depth execution: any fuel
budget leaves it unchanged. -/
theorem exec_halted (f : Addr a → Bool) (P : Prog a w) (c : Conf a w)
    (h : halted P c) (k : ℕ) : exec f P k c = c := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show exec f P k (step f P c) = c
      rw [step_halted f P c h]
      exact ih

/-- Termination of finite-depth execution: once execution reaches a halting
configuration within the fuel budget, additional fuel does not change the
result. -/
theorem exec_mono (f : Addr a → Bool) (P : Prog a w) (c : Conf a w) {k m : ℕ}
    (hkm : k ≤ m) (h : halted P (exec f P k c)) :
    exec f P m c = exec f P k c := by
  obtain ⟨j, hj⟩ := Nat.le.dest hkm
  subst hj
  rw [exec_add]
  exact exec_halted f P _ h _

/-- Decode an oracle value from a finite code by first-match lookup; addresses
not in the code decode to the default bit. -/
def codeLookup (dflt : Bool) : List (Addr a × Bool) → Addr a → Bool
  | [], _ => dflt
  | p :: L, x => if p.1 = x then p.2 else codeLookup dflt L x

/-- First-match lookup is sound on consistent codes: when the code contains
`(x, b)` and every coded entry at address `x` has value `b`, the decode returns
`b`. -/
theorem codeLookup_eq (dflt : Bool) :
    ∀ (L : List (Addr a × Bool)) (x : Addr a) (b : Bool),
      (x, b) ∈ L → (∀ q ∈ L, q.1 = x → q.2 = b) → codeLookup dflt L x = b := by
  intro L
  induction L with
  | nil =>
      intro x b hmem _
      cases hmem
  | cons p L ih =>
      intro x b hmem hall
      obtain ⟨y, v⟩ := p
      by_cases hp : y = x
      · have hb : v = b := hall (y, v) List.mem_cons_self hp
        simp [codeLookup, hp, hb]
      · have hmem' : (x, b) ∈ L := by
          rcases List.mem_cons.1 hmem with h | h
          · injection h with hy _
            exact absurd hy.symm hp
          · exact h
        simp only [codeLookup, hp]
        exact ih x b hmem' (fun q hq => hall q (List.mem_cons_of_mem _ hq))

/-- Every oracle function on the finite address space is code-enumerable: the
truth table coded along the enumerated addresses decodes back to the function at
every input. The machine interface therefore only ever consults oracle data
given by finite code. -/
theorem oracle_is_code (dflt : Bool) (f : Addr a → Bool) (x : Addr a) :
    codeLookup dflt ((Fintype.elems (α := Addr a)).toList.map fun y => (y, f y)) x =
      f x := by
  refine codeLookup_eq dflt _ x (f x) ?_ ?_
  · exact List.mem_map.2 ⟨x, by simpa using Fintype.complete x, rfl⟩
  · intro q hq hqx
    obtain ⟨y, _hy, hqy⟩ := List.mem_map.1 hq
    subst hqy
    have hyx : y = x := by simpa using hqx
    subst hyx
    rfl

/-- The single-query program: consult the oracle once, then halt. -/
def oneQueryProg : Prog a w := [Instr.oracle, Instr.halt]

/-- The interface is executable: running the single-query program for two steps
from program counter zero consults the oracle exactly once through the standard
`xorInto` update, reaches a halting configuration, and every larger fuel budget
returns the same configuration. -/
theorem one_query_exec (f : Addr a → Bool) (x : OReg a w) :
    exec f oneQueryProg 2 ⟨0, x⟩ = ⟨1, xorInto f x⟩ ∧
      halted oneQueryProg (exec f oneQueryProg 2 ⟨0, x⟩) ∧
      ∀ m, 2 ≤ m → exec f oneQueryProg m ⟨0, x⟩ = ⟨1, xorInto f x⟩ := by
  have h0 : instrAt oneQueryProg 0 = (Instr.oracle : Instr a w) := rfl
  have h1 : instrAt oneQueryProg 1 = (Instr.halt : Instr a w) := rfl
  have hh : halted oneQueryProg ⟨1, xorInto f x⟩ := h1
  have hex2 : exec f oneQueryProg 2 ⟨0, x⟩ = ⟨1, xorInto f x⟩ := by
    show exec f oneQueryProg 1 (step f oneQueryProg ⟨0, x⟩) = ⟨1, xorInto f x⟩
    rw [step_oracle f oneQueryProg ⟨0, x⟩ h0]
    show exec f oneQueryProg 0 (step f oneQueryProg ⟨1, xorInto f x⟩) = _
    rw [step_halt f oneQueryProg ⟨1, xorInto f x⟩ h1]
    rfl
  refine ⟨hex2, ?_, ?_⟩
  · rw [hex2]
    exact hh
  · intro m hm
    rw [exec_mono f oneQueryProg ⟨0, x⟩ hm (by rw [hex2]; exact hh), hex2]

end Qatlib.Papers.ExactSimon97.OracleMachine
