/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Tactic
public import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
public import Qatlib.Papers.BettiNumber25.MainResults.Estimators.SourceEstimator

@[expose] public section


set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Papers.BettiNumber25.MainResults.Estimators
open scoped BigOperators

namespace Qatlib.Papers.BettiNumber25.MainResults.Estimators

/-- Complement formula for the mass of an event. -/
theorem eventMass_congr {X : Type*} [Fintype X] (p : FinDist X) {E F : X → Prop}
    (h : ∀ x, E x ↔ F x) [DecidablePred E] [DecidablePred F] :
    eventMass p E = eventMass p F := by
  unfold eventMass
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h x

/-- The mass of the impossible event is zero. -/
theorem eventMass_impossible {X : Type*} [Fintype X] (p : FinDist X) :
    eventMass p (fun _ => False) = 0 := by
  simp [eventMass]

open Classical in
/-- The finite union bound for event masses over an arbitrary index type. -/
theorem eventMass_bUnion_le {X : Type*} [Fintype X] (p : FinDist X) {ι : Type*}
    [DecidableEq ι] (F : ι → X → Prop) [∀ i, DecidablePred (F i)] :
    ∀ (s : Finset ι), eventMass p (fun x => ∃ i ∈ s, F i x)
      ≤ ∑ i ∈ s, eventMass p (F i) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      have hE : ∀ x : X, (∃ i ∈ (∅ : Finset ι), F i x) ↔ False := by intro x; simp
      rw [eventMass_congr p hE, eventMass_impossible]
      simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have hE : ∀ x : X, (∃ i ∈ insert a s, F i x) ↔ (F a x ∨ ∃ i ∈ s, F i x) := by
        intro x; simp [Finset.mem_insert]
      rw [eventMass_congr p hE]
      calc eventMass p (fun x => F a x ∨ ∃ i ∈ s, F i x)
          ≤ eventMass p (F a) + eventMass p (fun x => ∃ i ∈ s, F i x) :=
            eventMass_or_le p _ _
        _ ≤ eventMass p (F a) + ∑ i ∈ s, eventMass p (F i) :=
            add_le_add_right ih (eventMass p (F a))

open Classical in
/-- Event mass is the expectation of its zero-one indicator. -/
theorem eventMass_eq_expect {X : Type*} [Fintype X] (p : FinDist X) (E : X → Prop)
    [DecidablePred E] :
    eventMass p E = p.expect (fun x => if E x then (1 : ℝ) else 0) := by
  simp [eventMass, FinDist.expect, Finset.sum_filter]

open Classical in
/-- The mass of a coordinate event under the product law equals its marginal mass. -/
theorem eventMass_coord {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {d : ℕ}
    (P : Fin d → FinDist Ω) (j : Fin d) (E : Ω → Prop) [DecidablePred E] :
    eventMass (independent P) (fun ω => E (ω j)) = eventMass (P j) E := by
  have h1 := independent_expect_coord P j (fun x => if E x then (1 : ℝ) else 0)
  calc eventMass (independent P) (fun ω => E (ω j))
      = (independent P).expect (fun ω => if E (ω j) then (1 : ℝ) else 0) :=
        eventMass_eq_expect _ _
    _ = (P j).expect (fun x => if E x then (1 : ℝ) else 0) := h1
    _ = eventMass (P j) E := (eventMass_eq_expect _ _).symm

end Qatlib.Papers.BettiNumber25.MainResults.Estimators
