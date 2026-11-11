/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Lean.Elab.Tactic.Omega

set_option backward.isDefEq.respectTransparency false

/-! An explicit finite arithmetic access model for phase recovery.

Events retain the actual operands of the listed primitive model. A visit is
one abstract indexed read with an index and length, not a traversal-level
model of getD or length. Clog is one named natural primitive. Pattern/control
steps, legacy counter updates, tuple construction, logging/price evaluation,
input serialization and their allocation overhead are not charged separately.
Named rational operations, indexed accesses, constructed list cells and
parameter arithmetic have explicit events; this does not enumerate all
natural-number operations or host instructions.
their prices are not claims about the implementation of Lean's rationals,
GCD, memory allocation, or host bit time. Any such refinement must justify
its operand-dependent prices separately. Positive prices prevent a zero
ledger from certifying a nonempty execution.

The operational program constructs both the value and events. A standalone
`Run` value is not an execution certificate: consumers must identify it with
the actual interpreter at the original represented input.
-/
set_option autoImplicit false

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution

/-- Primitive natural operations whose actual operands remain in the trace. -/
inductive NatOp where
  | add | sub | mul | pow | clog
  deriving Repr, DecidableEq

/-- Concrete arithmetic operands and represented finite-data accesses. -/
inductive Event where
  | add (a b : ℚ)
  | sub (a b : ℚ)
  | mul (a b : ℚ)
  | div (a b : ℚ)
  | neg (a : ℚ)
  | abs (a : ℚ)
  | compare (a b : ℚ)
  | cast (n : ℕ)
  | natural (op : NatOp) (a b : ℕ)
  | inputRat (a : ℚ)
  | inputNat (n : ℕ)
  | visit (index length : ℕ)
  | allocate (cells : ℕ)
  deriving Repr

/-- One actual value together with the primitive events that produced it. -/
structure Run (α : Type) where
  data : α
  log : List Event

/-- Access the actual returned data through a reusable proved evaluation boundary. -/
def Run.value {α : Type} (run : Run α) : α := run.data

/-- Access the complete actual event list through its proved evaluation boundary. -/
def Run.events {α : Type} (run : Run α) : List Event := run.log

/-- A concrete run returns exactly the data stored by its computation. -/
@[simp] theorem value_mk {α : Type} (data : α) (events : List Event) :
    (Run.mk data events).value = data := rfl

/-- A concrete run retains exactly the event sequence stored by its computation. -/
@[simp] theorem events_mk {α : Type} (data : α) (events : List Event) :
    (Run.mk data events).events = events := rfl

instance : Monad Run where
  pure a := ⟨a, []⟩
  bind r f := let s := f r.value; ⟨s.value, r.events ++ s.events⟩

/-- Returning a value performs no primitive operation. -/
@[simp] theorem value_pure {α : Type} (a : α) : (pure a : Run α).value = a := rfl

/-- Sequential composition returns the value of the continuation at the actual result. -/
@[simp] theorem value_bind {α β : Type} (r : Run α) (f : α → Run β) :
    (r >>= f).value = (f r.value).value := rfl

/-- Pure return has no execution events. -/
@[simp] theorem events_pure {α : Type} (a : α) : (pure a : Run α).events = [] := rfl

/-- Sequential composition preserves both complete event lists in order. -/
@[simp] theorem events_bind {α β : Type} (r : Run α) (f : α → Run β) :
    (r >>= f).events = r.events ++ (f r.value).events := rfl

/-- Record one concrete primitive operation with its computed result. -/
def emit {α : Type} (event : Event) (value : α) : Run α := ⟨value, [event]⟩

/-- Emitting an operation preserves its actual result. -/
@[simp] theorem value_emit {α : Type} (event : Event) (value : α) :
    (emit event value).value = value := rfl

/-- Emitting one operation records precisely that concrete primitive event. -/
@[simp] theorem events_emit {α : Type} (event : Event) (value : α) :
    (emit event value).events = [event] := rfl

/-- An explicit price model charges every recorded operation positively. -/
structure PriceModel where
  price : Event → ℕ
  positive : ∀ event, 1 ≤ price event

/-- Unit primitive cost is an arithmetic/access model, not host bit time. -/
def unitPrice : PriceModel := ⟨fun _ => 1, fun _ => Nat.le_refl 1⟩

/-- Charge the complete actual trace, including failure-path work. -/
def charge (model : PriceModel) (events : List Event) : ℕ :=
  (events.map model.price).sum

/-- Sequential execution pays the sum of its two complete traces. -/
theorem charge_append (model : PriceModel) (xs ys : List Event) :
    charge model (xs ++ ys) = charge model xs + charge model ys := by
  simp [charge]

/-- Positive primitive prices charge at least the number of actual events. -/
theorem length_le_charge (model : PriceModel) (events : List Event) :
    events.length ≤ charge model events := by
  induction events with
  | nil => simp [charge]
  | cons event rest ih =>
    have hp := model.positive event
    simp only [List.length_cons, charge, List.map_cons, List.sum_cons] at *
    omega

/-- A nonempty actual trace cannot have a certified zero budget. -/
theorem nonempty_charge_pos (model : PriceModel) (events : List Event)
    (hne : events ≠ []) : 0 < charge model events := by
  have hl : 0 < events.length := List.length_pos_iff.mpr hne
  exact hl.trans_le (length_le_charge model events)

/-- Unit primitive pricing counts precisely the complete actual event list. -/
theorem unit_charge (events : List Event) : charge unitPrice events = events.length := by
  simp [charge, unitPrice]

-- Keep kernel conversion from repeatedly unfolding concrete recursive
-- arithmetic inside a structure projection. The public value equations above
-- remain proved equalities; the executable computation is unchanged.
attribute [irreducible] Run.value Run.events

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
