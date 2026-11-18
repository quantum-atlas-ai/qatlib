/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CostModels.Profile

@[expose] public section

/-! # Compilation cost contracts against source budgets

This module fixes the toolkit contract for compiled-resource claims: the cost
of a compiled product is measured off the produced artifact, and only
afterwards compared with the a-priori source budget. The `CompileCert` type
makes the order of derivation explicit — a certificate carries the product
together with a proof that the product's measured counts fit the budget. The
constructor requires that proof from its caller, and an
unmodeled field can never satisfy a constrained budget slot
(`optLeNoneNeg`, `budgetNoOpaque`).
-/

set_option autoImplicit false

namespace Qatlib.Concepts.CostModels.Budget

open Qatlib.Concepts.CostModels.Profile

/-- Budget check for one field: a constrained slot (`some k`) must be met by a
modeled measurement `some a` with `a ≤ k`; an unconstrained slot (`none`)
demands nothing. A `none` measurement never vacuously satisfies a constrained
slot. -/
def optLe (m b : Option ℕ) : Prop :=
  match b with
  | none => True
  | some k => ∃ a, m = some a ∧ a ≤ k

/-- Budget conformance of a measured profile `m` against a source budget `b`:
every field the budget constrains is met by a modeled measurement not
exceeding it. The measurement is on the left, the budget on the right. -/
def BudgetLe (m b : CostProfile) : Prop :=
  optLe m.queries b.queries ∧ optLe m.macroGates b.macroGates ∧
    optLe m.oneQ b.oneQ ∧ optLe m.twoQ b.twoQ ∧ optLe m.tCount b.tCount ∧
    optLe m.depth b.depth ∧ optLe m.width b.width

/-- An unmodeled measurement never meets a constrained budget slot. -/
theorem optLeNoneNeg {k : ℕ} : ¬ optLe none (some k) := by
  simp [optLe]

/-- A profile with unmodeled query count cannot conform to any budget that
constrains queries: leaving a measurement open cannot yield the final
bound. -/
theorem budgetNoOpaque {k : ℕ} {b : CostProfile} (hb : b.queries = some k) :
    ¬ BudgetLe opaqueProfile b := by
  intro h
  exact optLeNoneNeg (by rw [← hb]; exact h.1)

/-- Budget conformance follows from the seven per-field checks. This is the
introduction route on measurements; nothing about the budget alone can
produce conformance. -/
theorem budgetLeIntro {m b : CostProfile}
    (h1 : optLe m.queries b.queries) (h2 : optLe m.macroGates b.macroGates)
    (h3 : optLe m.oneQ b.oneQ) (h4 : optLe m.twoQ b.twoQ)
    (h5 : optLe m.tCount b.tCount) (h6 : optLe m.depth b.depth)
    (h7 : optLe m.width b.width) : BudgetLe m b :=
  ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- Enlarging a constrained budget slot preserves conformance: the comparison
is between a fixed measurement and the source budget. -/
theorem optLeWeaken {m : Option ℕ} {k l : ℕ} (hkl : k ≤ l)
    (h : optLe m (some k)) : optLe m (some l) := by
  have ⟨a, hm, ha⟩ := h
  exact ⟨a, hm, ha.trans hkl⟩

/-- Compilation cost certificate over an abstract product type: `counts`
reads measured counts off an actual compiled product `out`, and `fits` proves
that this measurement meets the source budget. The bound is a derived
property of the measured product. Constructing a certificate requires the
product together with a proof that its measured counts fit the budget;
the certificate type does not itself derive that proof. -/
structure CompileCert {α : Type*} (counts : α → CostProfile)
    (budget : CostProfile) where
  /-- The actual compiled product whose counts are measured. -/
  out : α
  /-- Proof that the measured counts of `out` meet the source budget. -/
  fits : BudgetLe (counts out) budget

/-- A certificate yields a query bound phrased on the measured product
itself: the final bound is read off `counts cert.out`, never off the budget
alone. -/
theorem certQueryBound {α : Type*} {counts : α → CostProfile}
    {budget : CostProfile} (cert : CompileCert counts budget) {k : ℕ}
    (hk : budget.queries = some k) :
    ∃ a, (counts cert.out).queries = some a ∧ a ≤ k := by
  have h : optLe (counts cert.out).queries (some k) := by
    rw [← hk]; exact cert.fits.1
  have ⟨a, hm, ha⟩ := h
  exact ⟨a, hm, ha⟩

end Qatlib.Concepts.CostModels.Budget
