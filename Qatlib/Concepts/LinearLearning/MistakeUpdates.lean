/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MarginGeometry.MistakeProgress
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Deterministic mistake updates and margin termination

This module defines a finite labeled `Dataset` and a deterministic perceptron-style update rule:
`increment` selects the least index with nonpositive signed score, and `run` accumulates these
updates from zero. The score, norm, and margin estimates connect this concrete rule to the
geometric mistake-prefix bound, in the perceptron setting discussed in [WiebeKapoorSvore2016].

For features of norm at most one and a unit separator of positive margin `γ`, the sequence stops
before `verificationBudget γ` and stays fixed. The theorem `first_stop_bound` gives a stopping
index satisfying the bound `γ ^ 2 * M ≤ 1`.

## Main statements

* `actual_prefix_bound`: the margin bound on the number of active updates.
* `exists_termination`: termination before the verification budget.
* `verified_output`: strict separation and stability at the budget iterate.
* `first_stop_bound`: a first stopping index with the margin bound.

## References

* [Wiebe, Kapoor, and Svore, 2016][WiebeKapoorSvore2016]
-/

namespace Qatlib.Concepts.LinearLearning.MistakeUpdates
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}

/-- A finite dataset of feature vectors with Boolean labels indicating the positive class. -/
structure Dataset (N : ℕ) (E : Type*) where
  feature : Fin N → E
  positive : Fin N → Bool

/-- The feature vector for a positive label and its negative for a negative label. -/
def signedDatum (D : Dataset N E) (i : Fin N) : E :=
  if D.positive i then D.feature i else -D.feature i

/-- The indices whose signed data have nonpositive inner product with the current weight vector. -/
def mistakes (D : Dataset N E) (w : E) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun i => ⟪w,signedDatum D i⟫_ℝ≤0)

/-- The signed datum at the least mistaken index, or zero when there are no mistakes. -/
def increment (D : Dataset N E) (w : E) : E :=
  if h : (mistakes D w).Nonempty then signedDatum D ((mistakes D w).min' h) else 0

/-- The deterministic mistake-update sequence starting at zero and adding the selected increment
at each step. -/
def run (D : Dataset N E) : ℕ → E
  | 0 => 0
  | n+1 => run D n+increment D (run D n)

/-- An index is a mistake exactly when its signed datum has nonpositive score under the weight
vector. -/
theorem mem_mistakes (D : Dataset N E) (w : E) (i : Fin N) :
    i∈mistakes D w ↔ ⟪w,signedDatum D i⟫_ℝ≤0 := by
  classical
  simp [mistakes]

/-- The mistake set is empty exactly when every signed datum has strictly positive score. -/
theorem mistakes_empty_iff (D : Dataset N E) (w : E) :
    mistakes D w=∅ ↔ ∀ i,0<⟪w,signedDatum D i⟫_ℝ := by
  classical
  simp only [Finset.eq_empty_iff_forall_notMem,mem_mistakes,not_le]

/-- The update increment is zero when the mistake set is empty. -/
theorem increment_of_empty (D : Dataset N E) (w : E) (h : mistakes D w=∅) :
    increment D w=0 := by
  simp [increment,h]

/-- The current weight vector has nonpositive inner product with its update increment. -/
theorem increment_score (D : Dataset N E) (w : E) : ⟪w,increment D w⟫_ℝ≤0 := by
  classical
  unfold increment
  split_ifs with h
  · exact (mem_mistakes D w _).1 (Finset.min'_mem _ h)
  · simp

/-- If every feature has norm at most one, every update increment has norm at most one. -/
theorem increment_norm (D : Dataset N E) (w : E) (hunit : ∀ i,‖D.feature i‖≤1) :
    ‖increment D w‖≤1 := by
  classical
  unfold increment
  split_ifs with h
  · unfold signedDatum
    split_ifs <;> simpa using hunit ((mistakes D w).min' h)
  · simp

/-- If all signed data have margin at least `γ` against `u` and a mistake exists, the chosen
increment has margin at least `γ` against `u`. -/
theorem increment_margin (D : Dataset N E) (w u : E) (γ : ℝ)
    (hmargin : ∀ i,γ≤⟪u,signedDatum D i⟫_ℝ) (h : (mistakes D w).Nonempty) :
    γ≤⟪u,increment D w⟫_ℝ := by
  simp only [increment,dif_pos h]
  exact hmargin _

/-- Once an iterate has no mistakes, every later iterate equals it. -/
theorem run_absorbing (D : Dataset N E) (n : ℕ) (h : mistakes D (run D n)=∅) :
    ∀ k,run D (n+k)=run D n := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ,run,ih,increment_of_empty D _ h,add_zero]

/-- For features of norm at most one and a unit separator with positive margin `γ`, any prefix
of `M` active updates satisfies `γ ^ 2 * M ≤ 1`. -/
theorem actual_prefix_bound (D : Dataset N E) (u : E) (hu : ‖u‖=1) (γ : ℝ) (hγ : 0<γ)
    (hunit : ∀ i,‖D.feature i‖≤1) (hmargin : ∀ i,γ≤⟪u,signedDatum D i⟫_ℝ)
    (M : ℕ) (hactive : ∀ n<M,(mistakes D (run D n)).Nonempty) : γ^2*(M:ℝ)≤1 := by
  exact Qatlib.Foundations.MarginGeometry.MistakeProgress.mistake_prefix_bound
    u hu (run D) (fun n => increment D (run D n)) M γ hγ rfl
    (fun _ _ => rfl) (fun n _ => increment_norm D _ hunit)
    (fun n _ => increment_score D _) (fun n hn => increment_margin D _ u γ hmargin (hactive n hn))

/-- The natural verification budget `Nat.ceil (1 / γ ^ 2) + 1`. -/
def verificationBudget (γ : ℝ) : ℕ := Nat.ceil (1/γ^2)+1

/-- For features of norm at most one and a unit separator with positive margin `γ`, the update
sequence reaches an empty mistake set before `verificationBudget γ`. -/
theorem exists_termination (D : Dataset N E) (u : E) (hu : ‖u‖=1) (γ : ℝ) (hγ : 0<γ)
    (hunit : ∀ i,‖D.feature i‖≤1) (hmargin : ∀ i,γ≤⟪u,signedDatum D i⟫_ℝ) :
    ∃ n<verificationBudget γ,mistakes D (run D n)=∅ := by
  classical
  by_contra h
  have ha : ∀ n<verificationBudget γ,(mistakes D (run D n)).Nonempty := by
    intro n hn
    apply Finset.nonempty_iff_ne_empty.2
    intro he
    exact h ⟨n,hn,he⟩
  have hb := actual_prefix_bound D u hu γ hγ hunit hmargin (verificationBudget γ)
    ha
  have hc : 1/γ^2≤(Nat.ceil (1/γ^2):ℝ) := Nat.le_ceil _
  have hpos : 0<γ^2 := sq_pos_of_pos hγ
  have hmul : 1≤(Nat.ceil (1/γ^2):ℝ)*γ^2 := (div_le_iff₀ hpos).1 hc
  simp only [verificationBudget,Nat.cast_add,Nat.cast_one] at hb
  nlinarith

/-- Under unit feature bounds and positive margin separation by a unit vector, the iterate at
the verification budget has strictly positive scores on all signed data and remains constant
thereafter. -/
theorem verified_output (D : Dataset N E) (u : E) (hu : ‖u‖=1) (γ : ℝ) (hγ : 0<γ)
    (hunit : ∀ i,‖D.feature i‖≤1) (hmargin : ∀ i,γ≤⟪u,signedDatum D i⟫_ℝ) :
    (∀ i,0<⟪run D (verificationBudget γ),signedDatum D i⟫_ℝ) ∧
      ∀ k,run D (verificationBudget γ+k)=run D (verificationBudget γ) := by
  obtain ⟨n,hn,he⟩ := exists_termination D u hu γ hγ hunit hmargin
  have hr : run D (verificationBudget γ)=run D n := by
    have hh := run_absorbing D n he (verificationBudget γ-n)
    rwa [Nat.add_sub_of_le (Nat.le_of_lt hn)] at hh
  have hfinal : mistakes D (run D (verificationBudget γ))=∅ := by rw [hr];exact he
  exact ⟨(mistakes_empty_iff D _).1 hfinal,run_absorbing D _ hfinal⟩

/-- Under unit feature bounds and positive margin separation by a unit vector, there is a first
stopping index `M` with `γ ^ 2 * M ≤ 1`; all scores are then positive, every earlier iterate
has a mistake, and all later iterates are equal. -/
theorem first_stop_bound (D : Dataset N E) (u : E) (hu : ‖u‖=1) (γ : ℝ) (hγ : 0<γ)
    (hunit : ∀ i,‖D.feature i‖≤1) (hmargin : ∀ i,γ≤⟪u,signedDatum D i⟫_ℝ) :
    ∃ M : ℕ,γ^2*(M:ℝ)≤1 ∧ (∀ i,0<⟪run D M,signedDatum D i⟫_ℝ) ∧
      (∀ n<M,(mistakes D (run D n)).Nonempty) ∧ ∀ k,run D (M+k)=run D M := by
  classical
  have h : ∃ n,mistakes D (run D n)=∅ := by
    obtain ⟨n,_,hn⟩ := exists_termination D u hu γ hγ hunit hmargin
    exact ⟨n,hn⟩
  let M := Nat.find h
  have he : mistakes D (run D M)=∅ := Nat.find_spec h
  have ha : ∀ n<M,(mistakes D (run D n)).Nonempty := by
    intro n hn
    apply Finset.nonempty_iff_ne_empty.2
    intro hz
    have hm : M≤n := Nat.find_min' h hz
    omega
  exact ⟨M,actual_prefix_bound D u hu γ hγ hunit hmargin M ha,
    (mistakes_empty_iff D _).1 he,ha,run_absorbing D M he⟩

end
end Qatlib.Concepts.LinearLearning.MistakeUpdates
