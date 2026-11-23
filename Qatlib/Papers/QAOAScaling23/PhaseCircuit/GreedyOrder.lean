/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Int.Basic

@[expose] public section

/-!
# Greedy phase-term scheduling

Implement Algorithm 2 of arXiv:2308.02342v2. The first remaining term seeds
each locality group, and the first maximum breaks ties. Each selected
occurrence is removed, including in the loop. Two-body terms are inserted
after their first matching four-body term, or appended when none matches.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QAOAScaling23.PhaseCircuit

/-- A CNOT pair in the ordered notation of the source. -/
abbrev WirePair (n : ℕ) := Fin n × Fin n

/-- The ordered top and bottom pairs of one four-body phase term. -/
structure FourBodyTerm (n : ℕ) where
  top : WirePair n
  bottom : WirePair n
deriving DecidableEq

/-- Either a four-body phase term or a two-body phase term. -/
abbrev PhaseTerm (n : ℕ) := Sum (FourBodyTerm n) (WirePair n)

/-- A repeated pair earns one point; a blocking pair costs one point. -/
def greedyScore {n : ℕ} (tops bottoms : List (WirePair n)) (term : FourBodyTerm n) : ℤ :=
  (if term.top ∈ tops ∨ term.bottom ∈ bottoms then 1 else -1) -
    (if bottoms.any (fun p => p.2 == term.top.1) ||
        tops.any (fun p => p.2 == term.bottom.1) then 1 else 0)

/-- Select the first term attaining the maximum score. -/
def chooseHighest {n : ℕ} (tops bottoms : List (WirePair n)) :
    FourBodyTerm n → List (FourBodyTerm n) → FourBodyTerm n
  | best, [] => best
  | best, term :: rest =>
      chooseHighest tops bottoms
        (if greedyScore tops bottoms best < greedyScore tops bottoms term then term else best) rest

/-- The chosen term is present and its score dominates every remaining score. -/
theorem chooseHighest_spec {n : ℕ} (tops bottoms : List (WirePair n))
    (a : FourBodyTerm n) (xs : List (FourBodyTerm n)) :
    let picked := chooseHighest tops bottoms a xs
    picked ∈ a :: xs ∧ ∀ t ∈ a :: xs, greedyScore tops bottoms t ≤ greedyScore tops bottoms picked := by
  induction xs generalizing a with
  | nil => simp [chooseHighest]
  | cons b xs ih =>
      let next := if greedyScore tops bottoms a < greedyScore tops bottoms b then b else a
      obtain ⟨hm, hmax⟩ := ih next
      have hb : greedyScore tops bottoms b ≤ greedyScore tops bottoms next := by
        by_cases h : greedyScore tops bottoms a < greedyScore tops bottoms b
        · simp [next, h]
        · simpa [next, h] using Int.le_of_not_gt h
      have ha : greedyScore tops bottoms a ≤ greedyScore tops bottoms next := by
        by_cases h : greedyScore tops bottoms a < greedyScore tops bottoms b
        · simpa [next, h] using Int.le_of_lt h
        · simp [next, h]
      change chooseHighest tops bottoms next xs ∈ a :: b :: xs ∧ _
      refine ⟨?_, ?_⟩
      · rcases List.mem_cons.mp hm with h | h
        · rw [h]
          by_cases h' : greedyScore tops bottoms a < greedyScore tops bottoms b <;> simp [next, h']
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
      · intro t ht
        change greedyScore tops bottoms t ≤ greedyScore tops bottoms (chooseHighest tops bottoms next xs)
        rcases List.mem_cons.mp ht with rfl | ht
        · exact Int.le_trans ha (hmax next (by simp))
        · rcases List.mem_cons.mp ht with rfl | ht
          · exact Int.le_trans hb (hmax next (by simp))
          · exact hmax _ (List.mem_cons_of_mem _ ht)

/-- Emit the best term at every step and erase exactly the selected occurrence. -/
def scheduleGroupTail {n : ℕ} :
    ℕ → List (WirePair n) → List (WirePair n) → List (FourBodyTerm n) → List (FourBodyTerm n)
  | 0, _, _, xs => xs
  | _ + 1, _, _, [] => []
  | fuel + 1, tops, bottoms, a :: xs =>
      let term := chooseHighest tops bottoms a xs
      term :: scheduleGroupTail fuel (term.top :: tops) (term.bottom :: bottoms)
        ((a :: xs).erase term)

/-- The loop preserves multiplicities, including duplicates of a chosen term. -/
private theorem scheduleGroupTail_perm {n : ℕ} (fuel : ℕ) (tops bottoms : List (WirePair n))
    (xs : List (FourBodyTerm n)) :
    (scheduleGroupTail fuel tops bottoms xs).Perm xs := by
  induction fuel generalizing tops bottoms xs with
  | zero => simp [scheduleGroupTail]
  | succ fuel ih =>
      cases xs with
      | nil => simp [scheduleGroupTail]
      | cons a xs =>
          let picked := chooseHighest tops bottoms a xs
          have hp : picked ∈ a :: xs := (chooseHighest_spec tops bottoms a xs).1
          exact (List.Perm.cons picked (ih _ _ _)).trans (List.perm_cons_erase hp).symm

/-- The head is the deterministic seed of the locality group. -/
def scheduleGroup {n : ℕ} : List (FourBodyTerm n) → List (FourBodyTerm n)
  | [] => []
  | a :: xs => a :: scheduleGroupTail xs.length [a.top] [a.bottom] xs

/-- Scheduling an isolated locality group preserves all occurrences. -/
theorem scheduleGroup_perm {n : ℕ} (xs : List (FourBodyTerm n)) :
    (scheduleGroup xs).Perm xs := by
  cases xs with
  | nil => rfl
  | cons a xs => exact List.Perm.cons a (scheduleGroupTail_perm xs.length _ _ xs)

/-- Group four-body terms by the difference of the indices in their top pair. -/
def sameLocality {n : ℕ} (a b : FourBodyTerm n) : Bool :=
  a.top.2.val - a.top.1.val == b.top.2.val - b.top.1.val

/-- Traverse the groups in order of their first input occurrence. -/
def scheduleLocalities {n : ℕ} : ℕ → List (FourBodyTerm n) → List (FourBodyTerm n)
  | 0, xs => xs
  | _ + 1, [] => []
  | fuel + 1, a :: xs =>
      let group := xs.filter (sameLocality a)
      let other := xs.filter (fun t => !(sameLocality a t))
      scheduleGroup (a :: group) ++ scheduleLocalities fuel other

/-- The two complementary filters are a partition as lists with multiplicity. -/
private theorem filter_partition_perm {α : Type*} (f : α → Bool) (xs : List α) :
    (xs.filter f ++ xs.filter (fun x => !f x)).Perm xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases h : f x with
      | true => simpa [List.filter_cons, h] using List.Perm.cons x ih
      | false =>
          simpa [List.filter_cons, h] using
            (List.perm_middle (a := x) (l₁ := xs.filter f)).trans (List.Perm.cons x ih)

/-- Group selection preserves every four-body occurrence. -/
private theorem scheduleLocalities_perm {n : ℕ} (fuel : ℕ) (xs : List (FourBodyTerm n)) :
    (scheduleLocalities fuel xs).Perm xs := by
  induction fuel generalizing xs with
  | zero => rfl
  | succ fuel ih =>
      cases xs with
      | nil => rfl
      | cons a xs =>
          change (scheduleGroup (a :: xs.filter (sameLocality a)) ++
            scheduleLocalities fuel (xs.filter (fun t => !(sameLocality a t)))).Perm _
          exact ((scheduleGroup_perm _).append (ih _)).trans
            (List.Perm.cons a (filter_partition_perm (sameLocality a) xs))

/-- Insert a two-body phase after its first compatible four-body term, or append it. -/
def insertTwoBody {n : ℕ} (pair : WirePair n) : List (PhaseTerm n) → List (PhaseTerm n)
  | [] => [.inr pair]
  | .inl term :: rest =>
      if pair = term.top ∨ pair = term.bottom then .inl term :: .inr pair :: rest
      else .inl term :: insertTwoBody pair rest
  | .inr previous :: rest => .inr previous :: insertTwoBody pair rest

/-- Inserting a two-body term adds exactly one occurrence to the list. -/
private theorem insertTwoBody_perm {n : ℕ} (pair : WirePair n) (xs : List (PhaseTerm n)) :
    (insertTwoBody pair xs).Perm (.inr pair :: xs) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      cases a with
      | inl term =>
          by_cases h : pair = term.top ∨ pair = term.bottom
          · simpa [insertTwoBody, h] using List.Perm.swap (.inr pair) (.inl term) xs
          · simpa [insertTwoBody, h] using
              (List.Perm.cons (.inl term) ih).trans (List.Perm.swap (.inr pair) (.inl term) xs)
      | inr previous =>
          exact (List.Perm.cons (.inr previous) ih).trans (List.Perm.swap (.inr pair) (.inr previous) xs)

/-- Insert the two-body terms in their input order. -/
def insertTwoBodyList {n : ℕ} (xs : List (PhaseTerm n)) : List (WirePair n) → List (PhaseTerm n)
  | [] => xs
  | pair :: rest => insertTwoBodyList (insertTwoBody pair xs) rest

/-- The sequence of insertions consumes the input with its original multiplicities. -/
private theorem insertTwoBodyList_perm {n : ℕ} (xs : List (PhaseTerm n)) (rest : List (WirePair n)) :
    (insertTwoBodyList xs rest).Perm (xs ++ rest.map Sum.inr) := by
  induction rest generalizing xs with
  | nil => simp [insertTwoBodyList]
  | cons p rest ih =>
      have hp := (insertTwoBody_perm p xs).trans (List.perm_append_singleton (.inr p) xs).symm
      simpa [insertTwoBodyList, List.append_assoc] using
        (ih (insertTwoBody p xs)).trans (hp.append_right (rest.map Sum.inr))

/-- The corrected ordering of all two- and four-body phase terms in Algorithm 2. -/
def greedyOrder {n : ℕ} (four : List (FourBodyTerm n)) (two : List (WirePair n)) : List (PhaseTerm n) :=
  insertTwoBodyList ((scheduleLocalities four.length four).map Sum.inl) two

/-- The corrected scheduler emits precisely the original multiset and the original total length. -/
theorem greedy_emits_perm {n : ℕ} (four : List (FourBodyTerm n)) (two : List (WirePair n)) :
    (greedyOrder four two).Perm (four.map Sum.inl ++ two.map Sum.inr) ∧
      (greedyOrder four two).length = four.length + two.length := by
  unfold greedyOrder
  have hp := (insertTwoBodyList_perm _ two).trans
    (((scheduleLocalities_perm four.length four).map Sum.inl).append_right (two.map Sum.inr))
  exact ⟨hp, by simpa only [List.length_append, List.length_map] using hp.length_eq⟩

end Qatlib.Papers.QAOAScaling23.PhaseCircuit
