/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AnyCircuit08.MainResults.Basic

/-!
# Reachability of Pauli strings

The relation `PauliSupport` models the possible updates of a distinct coordinate pair, and
`PauliReach` is its reflexive transitive closure. For at least two coordinates every nonzero
Pauli string reaches every other nonzero string, while the zero string reaches only itself
[HallgrenHarrow2008].

## Main statements

* `pauliSupport_self`: gives self-loops when there are at least two coordinates.
* `pauliSupport_irreducible`: proves reachability between nonzero strings.
* `pauliReach_zero_iff`: characterizes reachability from zero.

## References

* [Hallgren and Harrow, 2008][HallgrenHarrow2008]
-/

namespace Qatlib.Papers.AnyCircuit08.MainResults

set_option autoImplicit false

/-- The Pauli string whose labels are all zero. -/
def pauliZero (n : ℕ) : PauliString n := 0

/-- The Pauli string whose labels are all one. -/
def pauliAllOnes (n : ℕ) : PauliString n := fun _ => 1

/-- The relation allowing an unchanged string on a zero coordinate pair, or an update from a
nonzero pair to a nonzero pair at two distinct coordinates [HallgrenHarrow2008]. -/
def PauliSupport {n : ℕ} (p q : PauliString n) : Prop :=
  (∃ i j : Fin n, i ≠ j ∧ p i = 0 ∧ p j = 0 ∧ q = p) ∨
  (∃ (i j : Fin n) (a b : Fin 4), i ≠ j ∧ (p i ≠ 0 ∨ p j ≠ 0) ∧ (a ≠ 0 ∨ b ≠ 0) ∧
      q = Function.update (Function.update p i a) j b)

/-- The reflexive transitive closure of `PauliSupport`. -/
def PauliReach {n : ℕ} (p q : PauliString n) : Prop :=
  Relation.ReflTransGen PauliSupport p q

/-- Updating a function at an argument with its existing value leaves the function unchanged. -/
theorem update_self_eq {α : Type*} {β : Type*} [DecidableEq α] (f : α → β) (a : α) :
    Function.update f a (f a) = f := by
  funext x
  by_cases hx : x = a
  · subst hx; rw [Function.update_self]
  · rw [Function.update_of_ne hx]

/-- Changing one coordinate is supported when a distinct auxiliary coordinate makes both the
source pair and target pair nonzero. -/
theorem pauliSupport_set {n : ℕ} (p : PauliString n) (k m : Fin n) (hkm : k ≠ m)
    (v : Fin 4) (hsrc : p k ≠ 0 ∨ p m ≠ 0) (htgt : v ≠ 0 ∨ p m ≠ 0) :
    PauliSupport p (Function.update p k v) := by
  refine Or.inr ⟨k, m, v, p m, hkm, hsrc, htgt, ?_⟩
  rw [show Function.update (Function.update p k v) m (p m)
        = Function.update (Function.update p k v) m ((Function.update p k v) m) from by
        rw [Function.update_of_ne hkm.symm]]
  exact (update_self_eq (Function.update p k v) m).symm

/-- Every Pauli string has a supported self-loop when `n ≥ 2` [HallgrenHarrow2008]. -/
theorem pauliSupport_self {n : ℕ} (hn : 2 ≤ n) (p : PauliString n) :
    PauliSupport p p := by
  by_cases hp : p = 0
  · refine Or.inl ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_, ?_, ?_, ?_⟩
    · intro h
      have := congrArg Fin.val h
      simp at this
    · subst hp; simp
    · subst hp; simp
    · rfl
  · obtain ⟨m, hm⟩ : ∃ m : Fin n, p m ≠ 0 := by
      by_contra h
      push Not at h
      exact hp (funext h)
    obtain ⟨k, hk⟩ : ∃ k : Fin n, k ≠ m := by
      by_cases hm0 : (m : ℕ) = 0
      · refine ⟨⟨1, by omega⟩, ?_⟩
        intro h
        have h1 : ((⟨1, by omega⟩ : Fin n) : ℕ) = (m : ℕ) := congrArg Fin.val h
        simp at h1
        omega
      · refine ⟨⟨0, by omega⟩, ?_⟩
        intro h
        have h1 : ((⟨0, by omega⟩ : Fin n) : ℕ) = (m : ℕ) := congrArg Fin.val h
        simp at h1
        omega
    refine Or.inr ⟨m, k, p m, p k, hk.symm, Or.inl hm, Or.inl hm, ?_⟩
    rw [show Function.update (Function.update p m (p m)) k (p k) = p from by
        rw [update_self_eq]
        exact update_self_eq p k]

/-- For `n ≥ 2`, any two Pauli strings sharing a coordinate where both are nonzero are related
by `PauliReach`. -/
theorem pauliReach_of_anchor {n : ℕ} (hn : 2 ≤ n) (p q : PauliString n) (m : Fin n)
    (hp : p m ≠ 0) (hq : q m ≠ 0) : PauliReach p q := by
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : Fin n, k₀ ≠ m := by
    by_cases hm0 : (m : ℕ) = 0
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro h
      have h1 : ((⟨1, by omega⟩ : Fin n) : ℕ) = (m : ℕ) := congrArg Fin.val h
      simp at h1
      omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro h
      have h1 : ((⟨0, by omega⟩ : Fin n) : ℕ) = (m : ℕ) := congrArg Fin.val h
      simp at h1
      omega
  have key : ∀ s : Finset (Fin n), m ∉ s →
      PauliReach p (fun x => if x ∈ s then q x else p x) := by
    apply Finset.induction
    · intro _
      have h0 : (fun x : Fin n => if x ∈ (∅ : Finset (Fin n)) then q x else p x) = p := by
        funext x; simp
      rw [h0]
      exact Relation.ReflTransGen.refl
    · intro k s hk ih hnot
      have hnot' : m ∉ s := fun h => hnot (Finset.mem_insert_of_mem h)
      have hkm : k ≠ m := fun h => hnot (h ▸ Finset.mem_insert_self k s)
      have ih' := ih hnot'
      set f : PauliString n := fun x => if x ∈ s then q x else p x with hf
      have hfm : f m ≠ 0 := by
        have hm' : f m = p m := by simp [hf, hnot']
        rw [hm']; exact hp
      have step : PauliSupport f (Function.update f k (q k)) :=
        pauliSupport_set f k m hkm (q k) (Or.inr hfm) (Or.inr hfm)
      have heqfun : (fun x : Fin n => if x ∈ insert k s then q x else p x)
          = Function.update f k (q k) := by
        funext x
        by_cases hxk : x = k
        · subst hxk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hxk]
          by_cases hxs : x ∈ s
          · simp [hf, hxs]
          · simp [hf, hxs, hxk]
      rw [heqfun]
      exact Relation.ReflTransGen.tail ih' step
  have hstep1 : PauliReach p (Function.update q m (p m)) := by
    have hall := key (Finset.univ.erase m) (by simp)
    have heq : (fun x : Fin n => if x ∈ Finset.univ.erase m then q x else p x)
        = Function.update q m (p m) := by
      funext x
      by_cases hxm : x = m
      · subst hxm; simp
      · have hx : x ∈ Finset.univ.erase m :=
          Finset.mem_erase.mpr ⟨hxm, Finset.mem_univ x⟩
        simp [hx, Function.update_of_ne hxm]
    rwa [heq] at hall
  have hstep2 : PauliSupport (Function.update q m (p m)) q := by
    have hs := pauliSupport_set (Function.update q m (p m)) m k₀ hk₀.symm (q m)
      (Or.inl (by rw [Function.update_self]; exact hp)) (Or.inl hq)
    have heq : Function.update (Function.update q m (p m)) m (q m) = q := by
      funext x
      by_cases hxm : x = m
      · subst hxm; rw [Function.update_self]
      · rw [Function.update_of_ne hxm, Function.update_of_ne hxm]
    rwa [heq] at hs
  exact Relation.ReflTransGen.tail hstep1 hstep2

/-- For `n ≥ 2`, every nonzero Pauli string can reach the all-ones string. -/
theorem pauliReach_allOnes {n : ℕ} (hn : 2 ≤ n) (p : PauliString n) (hp : p ≠ 0) :
    PauliReach p (pauliAllOnes n) := by
  obtain ⟨m, hm⟩ : ∃ m : Fin n, p m ≠ 0 := by
    by_contra h
    push Not at h
    exact hp (funext h)
  exact pauliReach_of_anchor hn p (pauliAllOnes n) m hm (by simp [pauliAllOnes])

/-- For `n ≥ 2`, the all-ones string can reach every nonzero Pauli string. -/
theorem pauliReach_from_allOnes {n : ℕ} (hn : 2 ≤ n) (q : PauliString n) (hq : q ≠ 0) :
    PauliReach (pauliAllOnes n) q := by
  obtain ⟨m, hm⟩ : ∃ m : Fin n, q m ≠ 0 := by
    by_contra h
    push Not at h
    exact hq (funext h)
  exact pauliReach_of_anchor hn (pauliAllOnes n) q m (by simp [pauliAllOnes]) hm

/-- For `n ≥ 2`, any nonzero Pauli string can reach any other nonzero Pauli string
[HallgrenHarrow2008]. -/
theorem pauliSupport_irreducible {n : ℕ} (hn : 2 ≤ n) (p q : PauliString n)
    (hp : p ≠ 0) (hq : q ≠ 0) : PauliReach p q :=
  Relation.ReflTransGen.trans (pauliReach_allOnes hn p hp) (pauliReach_from_allOnes hn q hq)

/-- A supported transition from the zero Pauli string can only end at zero. -/
theorem pauliSupport_zero {n : ℕ} (q : PauliString n) (h : PauliSupport (0 : PauliString n) q) :
    q = 0 := by
  rcases h with ⟨i, j, _, _, _, rfl⟩ | ⟨i, j, a, b, _, hsrc, _, rfl⟩
  · rfl
  · simp at hsrc

/-- The stationary weight of a nonzero Pauli string is at most `(1 / 4) ^ n`
[HallgrenHarrow2008]. -/
theorem stationaryWeight_ne_zero_le {n : ℕ} {p : PauliString n} (hp : p ≠ 0) :
    stationaryWeight n p ≤ (1 / 4 : ℝ) ^ n := by
  rw [stationaryWeight, if_neg hp]
  have h4 : (0:ℝ) < (4:ℝ) ^ n := by positivity
  have h2 : (0:ℝ) < (2:ℝ) ^ n := by positivity
  have hle : (4:ℝ) ^ n ≤ (4:ℝ) ^ n + (2:ℝ) ^ n := le_add_of_nonneg_right h2.le
  have h1 : 1 / ((4:ℝ) ^ n + (2:ℝ) ^ n) ≤ 1 / (4:ℝ) ^ n :=
    one_div_le_one_div_of_le h4 hle
  refine le_trans h1 ?_
  rw [show (1 / 4 : ℝ) ^ n = 1 / (4:ℝ) ^ n by rw [div_pow]; norm_num]

/-- A Pauli string is reachable from zero exactly when it is zero [HallgrenHarrow2008]. -/
theorem pauliReach_zero_iff {n : ℕ} (q : PauliString n) :
    PauliReach (0 : PauliString n) q ↔ q = 0 := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hstep ih =>
        subst ih
        exact pauliSupport_zero _ hstep
  · intro h
    subst h
    exact Relation.ReflTransGen.refl

end Qatlib.Papers.AnyCircuit08.MainResults
