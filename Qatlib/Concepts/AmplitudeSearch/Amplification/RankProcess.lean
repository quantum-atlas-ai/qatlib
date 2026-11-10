/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

inductive Experiment (α : Type) where
  | pure : α → Experiment α
  | uniform (n : ℕ) : (Fin (n + 1) → Experiment α) → Experiment α

namespace Experiment

variable {α β : Type}

def map (f : α → β) : Experiment α → Experiment β
  | .pure a => .pure (f a)
  | .uniform n branches => .uniform n (fun k => map f (branches k))

def expect : Experiment α → (α → ℚ) → ℚ
  | .pure a, f => f a
  | .uniform n branches, f => (∑ k, expect (branches k) f) / (n + 1 : ℚ)

def All (P : α → Prop) : Experiment α → Prop
  | .pure a => P a
  | .uniform _ branches => ∀ k, All P (branches k)

@[simp] theorem expect_map (e : Experiment α) (g : α → β) (f : β → ℚ) :
    (e.map g).expect f = e.expect (fun a => f (g a)) := by
  induction e with
  | pure a => rfl
  | uniform n branches ih => simp only [map, expect, ih]

@[simp] theorem all_map (e : Experiment α) (g : α → β) (P : β → Prop) :
    (e.map g).All P ↔ e.All (fun a => P (g a)) := by
  induction e with
  | pure a => rfl
  | uniform n branches ih => simp only [map, All, ih]

theorem all_mono (e : Experiment α) {P Q : α → Prop} (h : e.All P)
    (hpq : ∀ a, P a → Q a) : e.All Q := by
  induction e with
  | pure a => exact hpq a h
  | uniform n branches ih => exact fun k => ih k (h k)

@[simp] theorem expect_const (e : Experiment α) (c : ℚ) :
    e.expect (fun _ => c) = c := by
  induction e with
  | pure a => rfl
  | uniform n branches ih =>
    simp only [expect, ih, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    have hn : (n : ℚ) + 1 ≠ 0 := by positivity
    field_simp

theorem expect_congr (e : Experiment α) {f g : α → ℚ}
    (h : e.All (fun a => f a = g a)) : e.expect f = e.expect g := by
  induction e with
  | pure a => exact h
  | uniform n branches ih =>
    unfold expect
    congr 1
    exact Finset.sum_congr rfl (fun k _ => ih k (h k))

theorem expect_nonneg (e : Experiment α) {f : α → ℚ}
    (h : e.All (fun a => 0 ≤ f a)) : 0 ≤ e.expect f := by
  induction e with
  | pure a => exact h
  | uniform n branches ih =>
    exact div_nonneg (Finset.sum_nonneg (fun k _ => ih k (h k))) (by positivity)

theorem expect_mono (e : Experiment α) {f g : α → ℚ}
    (h : e.All (fun a => f a ≤ g a)) : e.expect f ≤ e.expect g := by
  induction e with
  | pure a => exact h
  | uniform n branches ih =>
    exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum (fun k _ => ih k (h k))) (by positivity)

theorem expect_add (e : Experiment α) (f g : α → ℚ) :
    e.expect (fun a => f a + g a) = e.expect f + e.expect g := by
  induction e with
  | pure a => rfl
  | uniform n branches ih => simp only [expect, ih, Finset.sum_add_distrib, add_div]

def probability (e : Experiment α) (P : α → Prop) [DecidablePred P] : ℚ :=
  e.expect (fun a => if P a then 1 else 0)

@[simp] theorem probability_true (e : Experiment α) : e.probability (fun _ => True) = 1 := by
  simp [probability]

@[simp] theorem probability_false (e : Experiment α) : e.probability (fun _ => False) = 0 := by
  simp [probability]

theorem all_of_forall (e : Experiment α) {P : α → Prop} (h : ∀ a, P a) : e.All P := by
  induction e with
  | pure a => exact h a
  | uniform n branches ih => exact ih

theorem probability_nonneg (e : Experiment α) (P : α → Prop) [DecidablePred P] :
    0 ≤ e.probability P := by
  apply expect_nonneg
  apply all_of_forall
  intro a
  split_ifs <;> norm_num

theorem probability_le_one (e : Experiment α) (P : α → Prop) [DecidablePred P] :
    e.probability P ≤ 1 := by
  calc
    _ ≤ e.expect (fun _ => 1) := by
      apply expect_mono
      apply all_of_forall
      intro a
      split_ifs <;> norm_num
    _ = 1 := expect_const e 1

theorem probability_disjoint_union (e : Experiment α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ a, ¬ (P a ∧ Q a)) :
    e.probability (fun a => P a ∨ Q a) = e.probability P + e.probability Q := by
  unfold probability
  rw [← expect_add]
  apply expect_congr
  apply all_of_forall
  intro a
  by_cases hp : P a <;> by_cases hq : Q a <;> simp_all

end Experiment

def rankExperiment : ℕ → Experiment (List ℕ)
  | 0 => .pure []
  | t + 1 => .uniform t (fun k => (rankExperiment k.val).map (List.cons (k.val + 1)))
termination_by t => t

def ValidTrace : ℕ → List ℕ → Prop
  | t, [] => t = 0
  | t, k :: ks => 1 ≤ k ∧ k ≤ t ∧ ValidTrace (k - 1) ks

theorem rankExperiment_valid (t : ℕ) : (rankExperiment t).All (ValidTrace t) := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero => simp [rankExperiment, Experiment.All, ValidTrace]
    | succ t =>
      simp only [rankExperiment, Experiment.All, Experiment.all_map]
      intro k
      apply Experiment.all_mono _ (ih k.val k.isLt)
      intro trace htrace
      simpa only [ValidTrace, Nat.add_sub_cancel] using
        (show 1 ≤ k.val + 1 ∧ k.val + 1 ≤ t + 1 ∧ ValidTrace k.val trace from
          ⟨by omega, by omega, htrace⟩)

theorem ValidTrace.length_le {t : ℕ} {trace : List ℕ} (h : ValidTrace t trace) :
    trace.length ≤ t := by
  induction trace generalizing t with
  | nil => simp
  | cons k ks ih =>
    obtain ⟨hk, hkt, htail⟩ := h
    have hlen := ih htail
    simp only [List.length_cons]
    omega

theorem ValidTrace.mem_bounds {t r : ℕ} {trace : List ℕ} (h : ValidTrace t trace)
    (hr : r ∈ trace) : 1 ≤ r ∧ r ≤ t := by
  induction trace generalizing t with
  | nil => simp at hr
  | cons k ks ih =>
    obtain ⟨hk, hkt, htail⟩ := h
    rcases List.mem_cons.mp hr with h | h
    · subst r; exact ⟨hk, hkt⟩
    · obtain ⟨hr1, hrk⟩ := ih htail h
      exact ⟨hr1, by omega⟩

theorem ValidTrace.strictly_decreasing {t : ℕ} {trace : List ℕ} (h : ValidTrace t trace) :
    trace.Pairwise (fun a b => b < a) := by
  induction trace generalizing t with
  | nil => exact List.Pairwise.nil
  | cons k ks ih =>
    obtain ⟨hk, _, htail⟩ := h
    apply List.Pairwise.cons
    · intro r hr
      have hb := htail.mem_bounds hr
      omega
    · exact ih htail

theorem rankExperiment_terminates (t : ℕ) :
    (rankExperiment t).All (fun trace => trace.length ≤ t ∧
      trace.Pairwise (fun a b => b < a)) := by
  exact Experiment.all_mono _ (rankExperiment_valid t)
    (fun _ h => ⟨h.length_le, h.strictly_decreasing⟩)

def hitProbability (t r : ℕ) : ℚ :=
  (rankExperiment t).probability (fun trace => r ∈ trace)

structure DistinctRankedTable (N : ℕ) (α : Type) [LinearOrder α] where
  value : Fin N → α
  indexOfRank : Fin N ≃ Fin N
  increasing : StrictMono (fun r => value (indexOfRank r))

namespace DistinctRankedTable

variable {N : ℕ} {α : Type} [LinearOrder α]

theorem distinct (T : DistinctRankedTable N α) : Function.Injective T.value := by
  intro i j h
  have hh : T.value (T.indexOfRank (T.indexOfRank.symm i)) =
      T.value (T.indexOfRank (T.indexOfRank.symm j)) := by simpa using h
  have hr := T.increasing.injective hh
  exact T.indexOfRank.symm.injective hr

theorem smaller_iff (T : DistinctRankedTable N α) (r s : Fin N) :
    T.value (T.indexOfRank r) < T.value (T.indexOfRank s) ↔ r < s :=
  T.increasing.lt_iff_lt

def smallerIndexEquiv (T : DistinctRankedTable N α) (threshold : Fin N) :
    Fin threshold.val ≃ {j : Fin N // T.value j < T.value (T.indexOfRank threshold)} where
  toFun k := ⟨T.indexOfRank ⟨k.val, lt_trans k.isLt threshold.isLt⟩,
    T.increasing k.isLt⟩
  invFun j := ⟨(T.indexOfRank.symm j.val).val, by
    apply (T.smaller_iff _ threshold).mp
    simpa using j.property⟩
  left_inv k := by
    apply Fin.ext
    simp
  right_inv j := by
    apply Subtype.ext
    exact T.indexOfRank.apply_symm_apply j.val

end DistinctRankedTable

structure UniformSuccessfulSearch where
  output : (t : ℕ) → Experiment (Fin (t + 1))
  uniform : ∀ (t : ℕ) (f : Fin (t + 1) → ℚ),
    (output t).expect f = (∑ k, f k) / (t + 1 : ℚ)

def uniformSuccessfulSearch : UniformSuccessfulSearch where
  output t := .uniform t (fun k => .pure k)
  uniform _ _ := rfl

end Qatlib.Concepts.AmplitudeSearch.Amplification
