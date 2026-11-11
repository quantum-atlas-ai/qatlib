/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Multiplicative orbit leaders modulo N

Multiplication by a unit partitions `ZMod N` into the finite orbits `orbitFinset`. The least
residue in each orbit is a leader, and the leader orbits cover all residues without overlap,
giving `sum_orbit_card_eq`.

This development forms part of the formalization of [GeraciVanBussel2007].

## Main statements

* `exists_leader`: Every multiplication orbit contains a leader.
* `sum_orbit_card_eq`: The cardinalities of the leader orbits sum to `N`.

## References

* [Geraci and Van Bussel, 2007][GeraciVanBussel2007]
-/

set_option autoImplicit false

namespace Qatlib.Papers.WeightEnum07.OrbitSieve

variable {N : ℕ} [NeZero N]

/-- The permutation of `ZMod N` given by multiplication by the unit `u`. See
[GeraciVanBussel2007]. -/
def mulUnitEquiv (u : (ZMod N)ˣ) : ZMod N ≃ ZMod N where
  toFun a := (u : ZMod N) * a
  invFun a := ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * a
  left_inv a := by
    show ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((u : ZMod N) * a) = a
    have h : ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (u : ZMod N) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [← mul_assoc, h, one_mul]
  right_inv a := by
    show (u : ZMod N) * (((u⁻¹ : (ZMod N)ˣ) : ZMod N) * a) = a
    have h : (u : ZMod N) * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [← mul_assoc, h, one_mul]

/-- The finite multiplication orbit of `a`, obtained from powers of `u` below its order. -/
noncomputable def orbitFinset (u : (ZMod N)ˣ) (a : ZMod N) : Finset (ZMod N) :=
  (Finset.range (orderOf u)).image (fun j => ((u ^ j : (ZMod N)ˣ) : ZMod N) * a)

/-- Membership in the orbit means that some power of `u` with exponent below its order sends `a`
to `b`. -/
lemma mem_orbitFinset {u : (ZMod N)ˣ} {a b : ZMod N} :
    b ∈ orbitFinset u a ↔
      ∃ j, j < orderOf u ∧ ((u ^ j : (ZMod N)ˣ) : ZMod N) * a = b := by
  rw [orbitFinset, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, Finset.mem_range.mp hj, h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, Finset.mem_range.mpr hj, h⟩

/-- Every natural power of `u` sends `a` to an element of its orbit. -/
lemma pow_mul_mem (u : (ZMod N)ˣ) (a : ZMod N) (j : ℕ) :
    ((u ^ j : (ZMod N)ˣ) : ZMod N) * a ∈ orbitFinset u a := by
  rw [mem_orbitFinset]
  exact ⟨j % orderOf u, Nat.mod_lt _ (orderOf_pos u), by rw [pow_mod_orderOf]⟩

/-- Every residue belongs to its own multiplication orbit. -/
lemma self_mem_orbitFinset (u : (ZMod N)ˣ) (a : ZMod N) : a ∈ orbitFinset u a := by
  simpa using pow_mul_mem u a 0

/-- The orbit of an element belonging to the orbit of `a` is contained in the orbit of `a`. -/
lemma orbit_subset_of_mem {u : (ZMod N)ˣ} {a b : ZMod N} (hb : b ∈ orbitFinset u a) :
    orbitFinset u b ⊆ orbitFinset u a := by
  intro c hc
  rw [mem_orbitFinset] at hb
  obtain ⟨k, _hk, hbk⟩ := hb
  rw [mem_orbitFinset] at hc
  obtain ⟨m, _hm, rfl⟩ := hc
  rw [← hbk]
  have hEq : ((u ^ m : (ZMod N)ˣ) : ZMod N) * (((u ^ k : (ZMod N)ˣ) : ZMod N) * a) =
      ((u ^ (m + k) : (ZMod N)ˣ) : ZMod N) * a := by
    rw [pow_add]
    push_cast
    ring
  rw [hEq]
  exact pow_mul_mem u a (m + k)

/-- Membership in a multiplication orbit is symmetric. -/
lemma self_mem_of_mem {u : (ZMod N)ˣ} {a b : ZMod N} (hb : b ∈ orbitFinset u a) :
    a ∈ orbitFinset u b := by
  rw [mem_orbitFinset] at hb
  obtain ⟨k, hk, hbk⟩ := hb
  have hmem := pow_mul_mem u (((u ^ k : (ZMod N)ˣ) : ZMod N) * a) (orderOf u - k)
  have heq : ((u ^ (orderOf u - k) : (ZMod N)ˣ) : ZMod N) *
      (((u ^ k : (ZMod N)ˣ) : ZMod N) * a) = a := by
    have hpow : (u ^ (orderOf u - k) * u ^ k : (ZMod N)ˣ) = 1 := by
      rw [← pow_add, Nat.sub_add_cancel (le_of_lt hk), pow_orderOf_eq_one]
    calc ((u ^ (orderOf u - k) : (ZMod N)ˣ) : ZMod N) *
          (((u ^ k : (ZMod N)ˣ) : ZMod N) * a)
        = ((u ^ (orderOf u - k) * u ^ k : (ZMod N)ˣ) : ZMod N) * a := by
          rw [Units.val_mul]; ring
      _ = (1 : ZMod N) * a := by rw [hpow, Units.val_one]
      _ = a := one_mul a
  rw [heq, hbk] at hmem
  exact hmem

/-- Elements in the same multiplication orbit have equal orbit finsets. See
[GeraciVanBussel2007]. -/
lemma orbit_eq_of_mem {u : (ZMod N)ˣ} {a b : ZMod N} (hb : b ∈ orbitFinset u a) :
    orbitFinset u b = orbitFinset u a := by
  exact Finset.Subset.antisymm (orbit_subset_of_mem hb) (orbit_subset_of_mem (self_mem_of_mem hb))

/-- The residue `l` has least natural representative among the elements of its multiplication
orbit. -/
def IsLeader (u : (ZMod N)ˣ) (l : ZMod N) : Prop :=
  ∀ b ∈ orbitFinset u l, l.val ≤ b.val

/-- Every multiplication orbit contains a leader. See [GeraciVanBussel2007]. -/
lemma exists_leader (u : (ZMod N)ˣ) (a : ZMod N) :
    ∃ l ∈ orbitFinset u a, IsLeader u l := by
  obtain ⟨l, hl, hmin⟩ :=
    Finset.exists_min_image (orbitFinset u a) ZMod.val ⟨a, self_mem_orbitFinset u a⟩
  refine ⟨l, hl, ?_⟩
  have hle := orbit_eq_of_mem hl
  intro b hb
  rw [hle] at hb
  exact hmin b hb

/-- The finite set of least-residue representatives of multiplication orbits. -/
noncomputable def leaders (u : (ZMod N)ˣ) : Finset (ZMod N) := by
  classical
  exact Finset.univ.filter (fun l => IsLeader u l)

/-- The union of the orbits indexed by leaders contains every residue modulo `N`. -/
lemma univ_subset_biUnion (u : (ZMod N)ˣ) :
    (Finset.univ : Finset (ZMod N)) ⊆ (leaders u).biUnion (orbitFinset u) := by
  classical
  intro a _
  obtain ⟨l, hl, hlead⟩ := exists_leader u a
  have hle : l ∈ leaders u := by
    simp only [leaders, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hlead
  exact Finset.mem_biUnion.mpr ⟨l, hle, self_mem_of_mem hl⟩

/-- Orbits indexed by distinct leaders are disjoint. -/
lemma leaders_pairwiseDisjoint (u : (ZMod N)ˣ) :
    (leaders u : Set (ZMod N)).PairwiseDisjoint (orbitFinset u) := by
  classical
  intro l1 hl1 l2 hl2 hne
  change Disjoint (orbitFinset u l1) (orbitFinset u l2)
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  have hlead1 : IsLeader u l1 := (Finset.mem_filter.mp hl1).2
  have hlead2 : IsLeader u l2 := (Finset.mem_filter.mp hl2).2
  have heq : orbitFinset u l1 = orbitFinset u l2 := by
    have h1 : orbitFinset u x = orbitFinset u l1 := orbit_eq_of_mem hx1
    have h2 : orbitFinset u x = orbitFinset u l2 := orbit_eq_of_mem hx2
    rw [← h1, h2]
  have hmem1 : l1 ∈ orbitFinset u l2 := by
    rw [← heq]; exact self_mem_orbitFinset u l1
  have hmem2 : l2 ∈ orbitFinset u l1 := by
    rw [heq]; exact self_mem_orbitFinset u l2
  have hv1 : l2.val ≤ l1.val := hlead2 l1 hmem1
  have hv2 : l1.val ≤ l2.val := hlead1 l2 hmem2
  exact hne (ZMod.val_injective N (le_antisymm hv2 hv1))

/-- The cardinalities of the leader orbits sum to `N`. See [GeraciVanBussel2007]. -/
theorem sum_orbit_card_eq (u : (ZMod N)ˣ) :
    ∑ l ∈ leaders u, (orbitFinset u l).card = N := by
  classical
  have hcover : (Finset.univ : Finset (ZMod N)) = (leaders u).biUnion (orbitFinset u) := by
    exact Finset.Subset.antisymm (univ_subset_biUnion u) (fun x _ => Finset.mem_univ x)
  have hcard := Finset.card_biUnion (leaders_pairwiseDisjoint u)
  rw [← hcard, ← hcover, Finset.card_univ, ZMod.card]

/-- Every multiplication orbit is nonempty. -/
lemma orbitFinset_nonempty (u : (ZMod N)ˣ) (a : ZMod N) : (orbitFinset u a).Nonempty :=
  ⟨a, self_mem_orbitFinset u a⟩

/-- Every multiplication orbit has positive cardinality. -/
lemma orbitFinset_card_pos (u : (ZMod N)ˣ) (a : ZMod N) : 0 < (orbitFinset u a).card :=
  Finset.card_pos.mpr (orbitFinset_nonempty u a)

end Qatlib.Papers.WeightEnum07.OrbitSieve
