/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/-!
# Hypercube neighbors and permutation counts

The functions `hammingDist` and `flip` describe Boolean configurations and single-coordinate
moves on the hypercube. The module characterizes distance-one neighbors, proves that each
configuration has `N` neighbors, and records the factorial count of coordinate permutations used
to label trajectories [AltshulerKroviRoland2010].

## Main statements

* `hammingDist_eq_one_iff_flip`: characterizes distance-one configurations.
* `card_neighbors`: counts the neighbors of a configuration.
* `card_trajectories`: counts permutations of `Fin n`.

## References

* [Altshuler et al., 2010][AltshulerKroviRoland2010]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AndersonLoc09.MainResults

/-- The number of coordinates on which two Boolean configurations differ. -/
def hammingDist {N : ℕ} (x y : Fin N → Bool) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ y i)).card

/-- The Boolean configuration obtained by negating the value of `x` at coordinate `i`. -/
def flip {N : ℕ} (x : Fin N → Bool) (i : Fin N) : Fin N → Bool :=
  Function.update x i (!x i)

/-- Flipping coordinate `i` negates the value at that coordinate. -/
theorem flip_self {N : ℕ} (x : Fin N → Bool) (i : Fin N) : flip x i i = !x i := by
  unfold flip
  exact Function.update_self i (!x i) x

/-- Flipping coordinate `i` preserves the value at every distinct coordinate. -/
theorem flip_of_ne {N : ℕ} (x : Fin N → Bool) {i j : Fin N} (h : j ≠ i) :
    flip x i j = x j := by
  unfold flip
  exact Function.update_of_ne h (!x i) x

/-- The Hamming distance from a Boolean configuration to itself is zero. -/
theorem hammingDist_self {N : ℕ} (x : Fin N → Bool) : hammingDist x x = 0 := by
  unfold hammingDist
  simp

/-- Hamming distance between Boolean configurations is symmetric. -/
theorem hammingDist_comm {N : ℕ} (x y : Fin N → Bool) :
    hammingDist x y = hammingDist y x := by
  unfold hammingDist
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ne_comm

/-- Flipping one coordinate gives a configuration at Hamming distance one from the original. -/
theorem hammingDist_flip {N : ℕ} (x : Fin N → Bool) (i : Fin N) :
    hammingDist (flip x i) x = 1 := by
  unfold hammingDist
  have hset : (Finset.univ.filter (fun j => flip x i j ≠ x j)) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      by_contra hj
      rw [flip_of_ne x hj] at h
      exact h rfl
    · intro hj
      subst hj
      rw [flip_self]
      simp
  rw [hset]
  simp

/-- For a fixed configuration, distinct coordinates yield distinct flipped configurations. -/
theorem flip_injective {N : ℕ} (x : Fin N → Bool) : Function.Injective (flip x) := by
  intro i j h
  by_contra hij
  have h1 : flip x i i = !x i := flip_self x i
  have h2 : flip x j i = x i := flip_of_ne x hij
  have hcon := congrFun h i
  rw [h1, h2] at hcon
  cases hxi : x i <;> simp [hxi] at hcon

/-- A configuration has Hamming distance one from `x` exactly when it is obtained by flipping
one coordinate of `x`. -/
theorem hammingDist_eq_one_iff_flip {N : ℕ} (x y : Fin N → Bool) :
    hammingDist y x = 1 ↔ ∃ i, y = flip x i := by
  constructor
  · intro hy
    unfold hammingDist at hy
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hy
    refine ⟨i, ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj
      have hmem : j ∈ Finset.univ.filter (fun j => y j ≠ x j) := by
        rw [hi]
        simp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      rw [flip_self]
      cases hyj : y j <;> cases hxj : x j <;> simp_all
    · have hnot : j ∉ Finset.univ.filter (fun j => y j ≠ x j) := by
        rw [hi]
        simp [hj]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hnot
      rw [flip_of_ne x hj, hnot]
  · rintro ⟨i, rfl⟩
    exact hammingDist_flip x i

/-- Every Boolean configuration on `N` coordinates has exactly `N` configurations at Hamming
distance one [AltshulerKroviRoland2010]. -/
theorem card_neighbors {N : ℕ} (x : Fin N → Bool) :
    (Finset.univ.filter (fun y : Fin N → Bool => hammingDist y x = 1)).card = N := by
  have himg : (Finset.univ.filter (fun y : Fin N → Bool => hammingDist y x = 1))
      = Finset.univ.image (flip x) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hy
      obtain ⟨i, rfl⟩ := (hammingDist_eq_one_iff_flip x y).mp hy
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact hammingDist_flip x i
  rw [himg, Finset.card_image_of_injective _ (flip_injective x), Finset.card_univ,
    Fintype.card_fin]

/-- There are `n.factorial` permutations of `Fin n`, the coordinate orderings used to label
trajectories [AltshulerKroviRoland2010]. -/
theorem card_trajectories (n : ℕ) :
    Fintype.card (Equiv.Perm (Fin n)) = n.factorial := by
  rw [Fintype.card_perm, Fintype.card_fin]

end Qatlib.Papers.AndersonLoc09.MainResults
