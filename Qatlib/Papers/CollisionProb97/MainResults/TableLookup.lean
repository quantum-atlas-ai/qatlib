/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

/-!
# Lookup and collision recovery in record lists

This module defines list-based lookup, internal collision detection, and recovery of a matching
input from a stored function value. These operations provide the classical record handling for
[BrassardHoyerTapp1998Collision].

The soundness and completeness lemmas certify returned records, and `internal_none_unique` shows
that absence of an internal collision forces uniqueness of inputs at each stored value.

## Main statements

* `lookup_sound`: A successful lookup returns an input whose record with value `z` occurs in the
  list and satisfies `allow`.
* `internal_sound`: A pair returned by `internal` consists of distinct inputs occurring in
  records with a common value.
* `internal_none_unique`: If no internal collision is found, two records with the same value
  must have the same input.
* `recover_exists`: If the value in `p` occurs in the record list, recovery returns a matching
  stored input paired with `p.1`.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Collision]
-/

set_option autoImplicit false
namespace Qatlib.Papers.CollisionProb97.MainResults.TableLookup
variable {S R : Type} [DecidableEq S] [DecidableEq R]

/-- Scans a record list for the first input with value `z` that satisfies the Boolean predicate
`allow`. -/
def lookup : List (S × R) → R → (S → Bool) → Option S
  | [], _, _ => none
  | (s, v) :: L, z, allow => if v = z ∧ allow s = true then some s else lookup L z allow

omit [DecidableEq S] in

/-- A successful lookup returns an input whose record with value `z` occurs in the list and
satisfies `allow`. -/
theorem lookup_sound (L : List (S × R)) (z : R) (allow : S → Bool) (s : S)
    (h : lookup L z allow = some s) : (s, z) ∈ L ∧ allow s = true := by
  induction L with
  | nil => simp [lookup] at h
  | cons p L ih =>
    rcases p with ⟨t, v⟩
    by_cases hc : v = z ∧ allow t = true
    · simp only [lookup, if_pos hc, Option.some.injEq] at h
      subst s
      exact ⟨by simp [hc.1], hc.2⟩
    · simp only [lookup, if_neg hc] at h
      obtain ⟨hm, ha⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hm, ha⟩

omit [DecidableEq S] in

/-- If an allowed record with value `z` occurs in the list, lookup returns some input. -/
theorem lookup_complete (L : List (S × R)) (z : R) (allow : S → Bool) (s : S)
    (hs : (s, z) ∈ L) (ha : allow s = true) : ∃ t, lookup L z allow = some t := by
  induction L with
  | nil => simp at hs
  | cons p L ih =>
    rcases p with ⟨t, v⟩
    by_cases hc : v = z ∧ allow t = true
    · exact ⟨t, by simp [lookup, hc]⟩
    · have ht : (s, z) ∈ L := by
        rcases List.mem_cons.mp hs with hsh | hst
        · cases hsh
          exact False.elim (hc ⟨rfl, ha⟩)
        · exact hst
      obtain ⟨u, hu⟩ := ih ht
      exact ⟨u, by simpa only [lookup, if_neg hc] using hu⟩

/-- Searches a record list for two distinct inputs with the same stored value. -/
def internal : List (S × R) → Option (S × S)
  | [] => none
  | (s, v) :: L =>
    match lookup L v (fun t => decide (t ≠ s)) with
    | some t => some (s, t)
    | none => internal L

/-- A pair returned by `internal` consists of distinct inputs occurring in records with a common
value. -/
theorem internal_sound (L : List (S × R)) (s t : S) (h : internal L = some (s, t)) :
    s ≠ t ∧ ∃ z, (s, z) ∈ L ∧ (t, z) ∈ L := by
  induction L with
  | nil => simp [internal] at h
  | cons p L ih =>
    rcases p with ⟨u, v⟩
    cases hl : lookup L v (fun w => decide (w ≠ u)) with
    | none =>
      have ht : internal L = some (s, t) := by simpa only [internal, hl] using h
      obtain ⟨hst, z, hs, ht⟩ := ih ht
      exact ⟨hst, z, List.mem_cons_of_mem _ hs, List.mem_cons_of_mem _ ht⟩
    | some w =>
      have hp : (u, w) = (s, t) := by simpa only [internal, hl, Option.some.injEq] using h
      cases hp
      obtain ⟨hw, hwu⟩ := lookup_sound L v _ t hl
      have hne : t ≠ s := of_decide_eq_true hwu
      exact ⟨Ne.symm hne, v, List.mem_cons_self, List.mem_cons_of_mem _ hw⟩

/-- If no internal collision is found, two records with the same value must have the same input. -/
theorem internal_none_unique (L : List (S × R)) (s t : S) (z : R)
    (hn : internal L = none) (hs : (s, z) ∈ L) (ht : (t, z) ∈ L) : s = t := by
  induction L generalizing s t z with
  | nil => simp at hs
  | cons p L ih =>
    rcases p with ⟨u, v⟩
    cases hl : lookup L v (fun w => decide (w ≠ u)) with
    | some w =>
      have hbad : some (u, w) = none := by simpa only [internal, hl] using hn
      cases hbad
    | none =>
      have htail : internal L = none := by simpa only [internal, hl] using hn
      rcases List.mem_cons.mp hs with hsh | hst
      · cases hsh
        rcases List.mem_cons.mp ht with hth | htt
        · cases hth
          rfl
        · by_contra hne
          obtain ⟨w, hw⟩ :=
              lookup_complete L z (fun w => decide (w ≠ s)) t htt (by simpa using Ne.symm hne)
          rw [hl] at hw
          contradiction
      · rcases List.mem_cons.mp ht with hth | htt
        · cases hth
          by_contra hne
          obtain ⟨w, hw⟩ := lookup_complete L z (fun w => decide (w ≠ t)) s hst (by simpa using hne)
          rw [hl] at hw
          contradiction
        · exact ih s t z htail hst htt

/-- Looks up a stored input matching the value in `p` and pairs it with the input component of
`p`. -/
def recover {X : Type} (L : List (S × R)) (p : X × R) : Option (S × X) :=
  (lookup L p.2 (fun _ => true)).map fun s => (s, p.1)

omit [DecidableEq S] in

/-- If the value in `p` occurs in the record list, recovery returns a matching stored input
paired with `p.1`. -/
theorem recover_exists {X : Type} (L : List (S × R)) (p : X × R)
    (h : ∃ s, (s, p.2) ∈ L) : ∃ s, recover L p = some (s, p.1) ∧ (s, p.2) ∈ L := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨t, ht⟩ := lookup_complete L p.2 (fun _ => true) s hs rfl
  exact ⟨t, by simp [recover, ht], (lookup_sound L p.2 _ t ht).1⟩

end Qatlib.Papers.CollisionProb97.MainResults.TableLookup
