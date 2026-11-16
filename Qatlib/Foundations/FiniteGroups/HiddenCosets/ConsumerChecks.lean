/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.FiniteGroups.HiddenCosets.Intersection
public import Mathlib.Data.ZMod.Basic

@[expose] public section


/-! # Real nonempty and empty coset-intersection regressions

The positive two-element example changes representatives and uses distinct
subgroups; the negative example consists of genuinely disjoint singleton
cosets. No success or cost fields are supplied.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
open Qatlib.Foundations.FiniteGroups.HiddenCosets.Intersection

namespace Qatlib.Foundations.FiniteGroups.HiddenCosets.ConsumerChecks

/-- A bottom-subgroup coset is the literal singleton of its representative. -/
theorem bottomCoset {G : Type*} [Group G] (x : G) : coset x ⊥ = {x} := by
  ext z
  simp only [coset, Set.mem_ofPred_eq, Subgroup.mem_bot, Set.mem_singleton_iff]
  constructor
  · intro h
    have hh := congrArg (fun w : G => x * w) h
    simpa only [← mul_assoc, mul_inv_cancel, one_mul, mul_one] using hh
  · rintro rfl
    simp

/-- Distinct singleton cosets have an actual empty intersection. -/
theorem bottomEmpty {G : Type*} [Group G] (x y : G) (hxy : x ≠ y) :
    coset x ⊥ ∩ coset y ⊥ = ∅ := by
  rw [bottomCoset, bottomCoset]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨rfl, h⟩
  exact hxy h

/-- The identity in a concrete nontrivial finite two-element group. -/
def e0 : Multiplicative (ZMod 2) := Multiplicative.ofAdd 0

/-- The nonidentity element of the concrete finite group. -/
def e1 : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

/-- The chosen elements really are distinct, so the negative test is satisfiable. -/
theorem distinctTwo : e0 ≠ e1 := by decide

/-- An actual disjoint pair, rather than an assumed-empty intersection. -/
theorem emptyTwo : coset e0 ⊥ ∩ coset e1 ⊥ = ∅ :=
  bottomEmpty e0 e1 distinctTwo

/-- Nonempty intersection with different representatives and different subgroups. -/
theorem nonemptyTwo : coset e0 ⊤ ∩ coset e1 ⊥ = {e1} := by
  have h : e1 ∈ coset e0 ⊤ ∩ coset e1 ⊥ := by
    constructor <;> simp [coset]
  rw [interAt ⊤ ⊥ e0 e1 e1 h]
  simpa using bottomCoset e1

end Qatlib.Foundations.FiniteGroups.HiddenCosets.ConsumerChecks
