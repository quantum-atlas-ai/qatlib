/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# HybridModel — input model and entropic complexity

Wu--Yang--Yao, fixed arXiv:2511.17227v2 (PDF SHA-256
`88dc3b11f969fcbdb870262fc72332b6d474fff8d050e005fdbc8ef8b1fbf992`).

This module records the paper's input conventions (Section 2.4) and the entropic
complexity measure of Definition 2.2, together with Proposition 2.3: a measure
that can be lowered by at most one by fixing a single coordinate can be lowered
by at most `|J \ K|` by fixing a whole coordinate set.

Boundary: this file only fixes the gadget, the composed function and the
iteration lemma. It does not contain any communication lower bound, and it does
not claim that degree or block sensitivity are entropic (that is Proposition
2.4 and Proposition 2.5, in `SensitivityEntropic`).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LiftingWu25.ProtocolSetup

open Finset

/-- `Λ = {0,1}^b`: the alphabet of one gadget coordinate. -/
abbrev Lambda (b : ℕ) := Fin b → Bool

/-- The inner-product gadget `G(x,y) = ⟨x,y⟩ mod 2` over the Boolean domain. -/
def gadget {b : ℕ} (x y : Lambda b) : Bool :=
  (∑ i : Fin b, (if x i then (1 : ZMod 2) else 0) * (if y i then (1 : ZMod 2) else 0)) = 1

/-- `G^J(x,y)`: the gadget evaluated on each coordinate of `J`. Coordinates outside
`J` are set to `false`, so that the result is an assignment on the whole universe. -/
def gadgetOn {ι : Type*} [DecidableEq ι] {b : ℕ} (J : Finset ι) (x y : ι → Lambda b) :
    ι → Bool :=
  fun i => if i ∈ J then gadget (x i) (y i) else false

/-- The composed function `f ∘ G^n = f(G^J(x,y))` of Section 2.4, with `J` the set of
coordinates carrying the gadget. -/
def composed {ι : Type*} [DecidableEq ι] {b : ℕ} (J : Finset ι)
    (f : (ι → Bool) → ℝ) (x y : ι → Lambda b) : ℝ :=
  f (gadgetOn J x y)

/-- A complexity measure of Boolean functions on a fixed finite coordinate universe `ι`
(Definition 2.2; `C(·)` in the paper ranges over functions on any coordinate set,
which we encode by allowing the function to depend on all of `ι`). -/
abbrev Measure (ι : Type*) := ((ι → Bool) → ℝ) → ℝ

/-- Fix the coordinates in `D` to the assignment `z` and leave every other coordinate
free. This is `f_{K,z}` with `D = J \ K` in the paper. -/
def restrict {ι : Type*} [DecidableEq ι] (D : Finset ι) (f : (ι → Bool) → ℝ)
    (z : ι → Bool) : (ι → Bool) → ℝ :=
  fun x => f (fun i => if i ∈ D then z i else x i)

/-- Definition 2.2: `C` is entropic when, for every function and every coordinate,
some value of that coordinate lowers `C` by at most one. -/
def Entropic {ι : Type*} [DecidableEq ι] (C : Measure ι) : Prop :=
  ∀ (f : (ι → Bool) → ℝ) (i : ι), ∃ z : Bool, C (restrict {i} f (fun _ => z)) ≥ C f - 1

/-- `restrict` of the empty set is the function itself. -/
theorem restrict_empty {ι : Type*} [DecidableEq ι] (f : (ι → Bool) → ℝ) (z : ι → Bool) :
    restrict ∅ f z = f := by
  funext x
  exact congrArg f (funext fun i => by simp)

/-- Restricting by a set that does not contain `a` commutes with first restricting by `{a}`:
`(f_{D,z})_{a,za} = f_{D ∪ {a},z'}` for the assignment `z'` that agrees with `z` on `D` and
equals `za` at `a`. -/
theorem restrict_insert {ι : Type*} [DecidableEq ι] (D : Finset ι) (a : ι) (ha : a ∉ D)
    (f : (ι → Bool) → ℝ) (za : Bool) (z : ι → Bool) :
    restrict (insert a D) f (Function.update z a za)
      = restrict D (restrict {a} f (fun _ => za)) z := by
  funext x
  refine congrArg f (funext fun i => ?_)
  by_cases hia : i = a
  · subst hia
    simp
  · by_cases hiD : i ∈ D
    · simp [hia, hiD]
    · have hnot : i ∉ insert a D := by simp [Finset.mem_insert, hia, hiD]
      simp [hia, hiD, hnot]

/-- Proposition 2.3: if `C` is entropic then fixing the coordinates in `D` lowers `C` by at
most `|D|`. Taking `D = J \ K` is the paper's statement `C(f_{K,z}) ≥ C(f) - (|J| - |K|)`. -/
theorem entropic_iterate {ι : Type*} [DecidableEq ι] (C : Measure ι) (hC : Entropic C)
    (D : Finset ι) (f : (ι → Bool) → ℝ) :
    ∃ z : ι → Bool, C (restrict D f z) ≥ C f - (D.card : ℝ) := by
  induction D using Finset.induction_on generalizing f with
  | empty =>
      exact ⟨fun _ => false, by rw [restrict_empty, Finset.card_empty]; push_cast; linarith⟩
  | insert a D ha ih =>
      obtain ⟨za, hza⟩ := hC f a
      obtain ⟨z, hz⟩ := ih (restrict {a} f (fun _ => za))
      refine ⟨Function.update z a za, ?_⟩
      rw [restrict_insert D a ha f za z]
      have hcard : ((insert a D).card : ℝ) = (D.card : ℝ) + 1 := by
        rw [Finset.card_insert_of_notMem ha]
        push_cast
        ring
      rw [hcard]
      linarith

end Qatlib.Papers.LiftingWu25.ProtocolSetup
