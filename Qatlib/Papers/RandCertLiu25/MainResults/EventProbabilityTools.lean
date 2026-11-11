/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

/-!
# Finite event-probability tools for the RandCertLiu25 sampling lemmas

Elementary consequences of `FinDist.probEvent` used by Lemma 15 (ℓ∞
approximation by a union bound) and Lemma 16 (promise-problem correctness):
complements and the union bound over an arbitrary finite index type.

These are paper-local tools; they only restate finite probability arithmetic
and do not change the shared `FinDist` layer.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.RandCertLiu25.MainResults.EventProbabilityTools

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- The event mass of the complement is one minus the event mass. -/
theorem probEvent_compl {X : Type*} [Fintype X] [DecidableEq X] (p : FinDist X)
    {L : ℕ} (E : (Fin L → X) → Prop) [DecidablePred E] :
    p.probEvent (fun ω => ¬ E ω) = 1 - p.probEvent E := by
  classical
  have h := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (Fin L → X))) (p := E)
    (f := fun ω => p.probOf ω)
  have htot : ∑ ω : Fin L → X, p.probOf ω = 1 := p.sum_probOf L
  unfold FinDist.probEvent
  linarith

/-- Pointwise nonnegativity of the product mass. -/
theorem probOf_nonneg {X : Type*} [Fintype X] (p : FinDist X) {L : ℕ}
    (ω : Fin L → X) : 0 ≤ p.probOf ω := by
  unfold FinDist.probOf
  exact Finset.prod_nonneg (fun i _ => p.nonneg (ω i))

/-- Event mass depends only on the event, not its presentation. -/
theorem probEvent_congr {X : Type*} [Fintype X] [DecidableEq X] (p : FinDist X)
    {L : ℕ} {E F : (Fin L → X) → Prop} [DecidablePred E] [DecidablePred F]
    (h : ∀ ω, E ω ↔ F ω) : p.probEvent E = p.probEvent F := by
  classical
  unfold FinDist.probEvent
  congr 1
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h ω

/-- Event mass is monotone in the event. -/
theorem probEvent_mono {X : Type*} [Fintype X] [DecidableEq X] (p : FinDist X)
    {L : ℕ} {E F : (Fin L → X) → Prop} [DecidablePred E] [DecidablePred F]
    (h : ∀ ω, E ω → F ω) : p.probEvent E ≤ p.probEvent F := by
  classical
  unfold FinDist.probEvent
  have hsub : (Finset.univ.filter E) ⊆ (Finset.univ.filter F) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact h ω hω
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun ω _ _ => probOf_nonneg p ω)

/-- Event mass never exceeds one. -/
theorem probEvent_le_one {X : Type*} [Fintype X] [DecidableEq X] (p : FinDist X)
    {L : ℕ} (E : (Fin L → X) → Prop) [DecidablePred E] : p.probEvent E ≤ 1 := by
  classical
  unfold FinDist.probEvent
  have hsub : (Finset.univ.filter E) ⊆ (Finset.univ : Finset (Fin L → X)) :=
    Finset.filter_subset _ _
  have hle : ∑ ω ∈ Finset.univ.filter E, p.probOf ω ≤ ∑ ω : Fin L → X, p.probOf ω :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ω _ _ => probOf_nonneg p ω)
  rw [p.sum_probOf L] at hle
  exact hle

/-- Splitting an event by a decidable predicate: `Pr[E] = Pr[E ∧ F] + Pr[E ∧ ¬F]`. -/
theorem probEvent_and_compl {X : Type*} [Fintype X] [DecidableEq X] (p : FinDist X)
    {L : ℕ} (E F : (Fin L → X) → Prop) [DecidablePred E] [DecidablePred F] :
    p.probEvent E = p.probEvent (fun ω => E ω ∧ F ω) +
      p.probEvent (fun ω => E ω ∧ ¬ F ω) := by
  classical
  unfold FinDist.probEvent
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hE : E ω <;> by_cases hF : F ω <;> simp [hE, hF]

/-- **Union bound over a finite index type.**  For a finite family of events
`E x`, the mass of their union is at most the sum of the masses. -/
theorem probEvent_exists_le_sum {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) {L : ℕ} (E : X → (Fin L → X) → Prop)
    [∀ x, DecidablePred (E x)] :
    p.probEvent (fun ω => ∃ x, E x ω) ≤ ∑ x, p.probEvent (E x) := by
  classical
  unfold FinDist.probEvent
  have hpoint : ∀ ω : Fin L → X,
      (if ∃ x, E x ω then (1 : ℝ) else 0) * p.probOf ω ≤
        ∑ x, (if E x ω then (1 : ℝ) else 0) * p.probOf ω := by
    intro ω
    by_cases h : ∃ x, E x ω
    · rw [if_pos h]
      obtain ⟨x0, hx0⟩ := h
      have hsingle : (if E x0 ω then (1 : ℝ) else 0) * p.probOf ω ≤
          ∑ x, (if E x ω then (1 : ℝ) else 0) * p.probOf ω :=
        Finset.single_le_sum (f := fun x => (if E x ω then (1 : ℝ) else 0) * p.probOf ω)
          (fun i _ => by
            have hp : (0 : ℝ) ≤ p.probOf ω := probOf_nonneg p ω
            by_cases hi : E i ω <;> simp [hi, hp]) (Finset.mem_univ x0)
      simpa [if_pos hx0] using hsingle
    · rw [if_neg h, zero_mul]
      exact Finset.sum_nonneg (fun x _ => by
        have hp : (0 : ℝ) ≤ p.probOf ω := probOf_nonneg p ω
        by_cases hx : E x ω <;> simp [hx, hp])
  have hleft : ∑ ω ∈ Finset.univ.filter (fun ω => ∃ x, E x ω), p.probOf ω =
      ∑ ω, (if ∃ x, E x ω then (1 : ℝ) else 0) * p.probOf ω := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> simp
  have hright : ∑ x, ∑ ω ∈ Finset.univ.filter (fun ω => E x ω), p.probOf ω =
      ∑ x, ∑ ω, (if E x ω then (1 : ℝ) else 0) * p.probOf ω := by
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> simp
  rw [hleft, hright]
  calc ∑ ω, (if ∃ x, E x ω then (1 : ℝ) else 0) * p.probOf ω
      ≤ ∑ ω, ∑ x, (if E x ω then (1 : ℝ) else 0) * p.probOf ω :=
        Finset.sum_le_sum (fun ω _ => hpoint ω)
    _ = ∑ x, ∑ ω, (if E x ω then (1 : ℝ) else 0) * p.probOf ω := Finset.sum_comm

end Qatlib.Papers.RandCertLiu25.MainResults.EventProbabilityTools
