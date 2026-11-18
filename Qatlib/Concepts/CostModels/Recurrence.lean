/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.CostRecurrences.UniformCosts
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Card
public import Qatlib.Concepts.CostModels.Profile
public import Qatlib.Concepts.CostModels.Compose

@[expose] public section

/-!
# Prime-factor cost recurrences fed by measured profiles

A recursion step followed by its child segments is a serial cost tree; its
measured query total is the modeled fold of the component query counts
(`recQuerySum`), which is exactly the shape the serial algebra provides for
recursion consumption. Instantiated on one step segment per distinct prime
factor of `N - 1`, the folded total is `q N + ∑ p ∈ (N-1).primeFactors, q p`
(`facQueryEq`), matching the step premise of the public
`cost_induction_closed`; `kidsLe` bridges the public bound on the number of
children, and `hstepFeed` is the explicit-premise feed of child bounds.

These are interface shapes over measured counts, not end-to-end
running-time theorems: the child bounds enter as premises to be discharged
per algorithm, consistent with the QPrimality95 binding note that
conditional arithmetic must not be passed off as a runtime conclusion.

## Main statements

* `recQuerySum`: a step segment followed by a child list costs the modeled
  fold, with unmodeled counts absorbing.
* `recFoldSum`: a fully modeled child list folds to the modeled sum.
* `facQueryEq`: the factor-recurrence tree at `N` measures exactly
  `q N + ∑ p ∈ (N - 1).primeFactors, q p` queries.
* `kidsLe`: the number of child segments is at most `Nat.log 2 (N - 1)`.
* `hstepFeed`: with child bounds and the step bound as explicit premises,
  the measured tree total exists and is bounded — an interface shape, not a
  running-time theorem.
* `foldNoneAbsorb` / `recOpaqueNone`: one unmodeled child leaves the folded
  total unmodeled.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.CostRecurrences.UniformCosts
open Qatlib.Concepts.CostModels.Profile
open Qatlib.Concepts.CostModels.Compose

namespace Qatlib.Concepts.CostModels.Recurrence

/-- A recursion step segment `s` followed by serially composed child segments
`ps` costs the modeled fold: `s.queries` combined with each child's query
count, with any unmodeled count absorbing. This is the `costAppend` /
`listQueryFold` reading of a recursion step feeding its sub-calls. -/
theorem recQuerySum (s : CostProfile) (ps : List CostProfile) :
    (treeCost (.app (.leaf s) (treeOfList ps))).queries
      = optAdd s.queries ((ps.map CostProfile.queries).foldr optAdd (some 0)) := by
  have h : (treeCost (.app (.leaf s) (treeOfList ps))).queries
      = optAdd s.queries (treeCost (treeOfList ps)).queries := rfl
  rw [h, listQueryFold]

/-- A child list whose query counts are all modeled through `g` folds to the
modeled sum of the `g` values: the count-level statement that a fully
measured recursion step has a fully measured total. -/
theorem recFoldSum {α : Type*} (g : α → ℕ) (P : α → CostProfile)
    (hP : ∀ x, (P x).queries = some (g x)) (xs : List α) :
    ((xs.map P).map CostProfile.queries).foldr optAdd (some 0)
      = some ((xs.map g).sum) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.map_cons, List.map_cons, List.foldr_cons, hP x, ih]
      simp [optAdd, List.sum_cons]

/-- The measured profile of one recurrence step at `N` carrying `q N` oracle
queries; every other field is unmodeled. -/
def facStepProf (q : ℕ → ℕ) (N : ℕ) : CostProfile where
  queries := some (q N)
  macroGates := none
  oneQ := none
  twoQ := none
  tCount := none
  depth := none
  width := none

/-- The factor-recurrence cost tree at `N`: the step segment at the root,
followed by one child segment per distinct prime factor of `N - 1`. The
child list enumerates `Finset.toList`, so the tree itself is
noncomputable; every theorem about it is unaffected. -/
noncomputable def facTree (q : ℕ → ℕ) (N : ℕ) : CostTree :=
  .app (.leaf (facStepProf q N))
    (treeOfList ((N - 1).primeFactors.toList.map (facStepProf q)))

/-- The measured query total of the factor-recurrence tree at `N` is the
step count plus one child count per distinct prime factor of `N - 1` — the
exact step shape of the public `cost_induction_closed`, read off a measured
profile tree instead of assumed. -/
theorem facQueryEq (q : ℕ → ℕ) (N : ℕ) :
    (treeCost (facTree q N)).queries
      = some (q N + ∑ p ∈ (N - 1).primeFactors, q p) := by
  unfold facTree
  rw [recQuerySum,
    recFoldSum q (facStepProf q) (fun x => rfl) ((N - 1).primeFactors.toList),
    Finset.sum_map_toList]
  rfl

/-- The number of child segments of the factor-recurrence tree at `N` is at
most the base-two logarithm of `N - 1`, bridging the public
`card_primeFactors_le_log2`; `3 ≤ N` is exactly `2 ≤ N - 1`. -/
theorem kidsLe (N : ℕ) (hN : 3 ≤ N) :
    (N - 1).primeFactors.toList.length ≤ Nat.log 2 (N - 1) := by
  have h2 : 2 ≤ N - 1 := by omega
  rw [Finset.length_toList]
  exact card_primeFactors_le_log2 _ h2

/-- Feeding lemma for the public `cost_induction_closed` induction: if every
child's measured query count is bounded by `P` and the step-plus-children
total is bounded by `P N`, then the factor-recurrence tree has a measured
query total bounded by `P N`. Interface shape only, NOT an end-to-end
running-time theorem: the child bounds and the step bound are explicit
premises that a concrete algorithm must discharge against its own measured
counts. -/
theorem hstepFeed (q P : ℕ → ℕ) (N : ℕ)
    (hchild : ∀ p ∈ (N - 1).primeFactors, q p ≤ P p)
    (hstep : q N + ∑ p ∈ (N - 1).primeFactors, P p ≤ P N) :
    ∃ t, (treeCost (facTree q N)).queries = some t ∧ t ≤ P N := by
  refine ⟨q N + ∑ p ∈ (N - 1).primeFactors, q p, facQueryEq q N, ?_⟩
  calc q N + ∑ p ∈ (N - 1).primeFactors, q p
      ≤ q N + ∑ p ∈ (N - 1).primeFactors, P p :=
        Nat.add_le_add_left (Finset.sum_le_sum hchild) (q N)
    _ ≤ P N := hstep

/-- If any child segment's query count is unmodeled, the folded serial total
is unmodeled — the count-side mirror of `budgetNoOpaque`. -/
theorem foldNoneAbsorb (ps : List CostProfile) (p : CostProfile)
    (hp : p ∈ ps) (hnone : p.queries = none) :
    (ps.map CostProfile.queries).foldr optAdd (some 0) = none := by
  induction ps with
  | nil => exact absurd hp (by simp)
  | cons r ps ih =>
      rcases List.mem_cons.mp hp with h | h
      · subst h
        rw [List.map_cons, List.foldr_cons, hnone]
        rfl
      · rw [List.map_cons, List.foldr_cons, ih h]
        cases r.queries <;> rfl

/-- A recursion step feeding one fully unmodeled child has an unmodeled
query total: unmodeled children never fold to a fake zero count. -/
theorem recOpaqueNone (s : CostProfile) :
    (treeCost (.app (.leaf s) (treeOfList [opaqueProfile]))).queries = none := by
  rw [recQuerySum, foldNoneAbsorb [opaqueProfile] opaqueProfile (by simp) rfl]
  cases s.queries <;> rfl

/-- Positive instance at `N = 3`: the only child factor is `2`, so the
measured total is `q 3 + q 2`, decided on the concrete factor set. -/
theorem facThreeEq (q : ℕ → ℕ) :
    (treeCost (facTree q 3)).queries = some (q 3 + q 2) := by
  have h : (3 - 1).primeFactors = ({2} : Finset ℕ) := by
    show (2 : ℕ).primeFactors = {2}
    exact Nat.Prime.primeFactors Nat.prime_two
  rw [facQueryEq q 3, h]
  simp

end Qatlib.Concepts.CostModels.Recurrence
