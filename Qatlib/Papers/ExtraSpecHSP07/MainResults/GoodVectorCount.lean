/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExtraSpecHSP07.MainResults.Defs
import Qatlib.Papers.ExtraSpecHSP07.MainResults.GoodVectorBasic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Counting good vectors over finite fields

`Constructible`, `psMap`, and `tripleMap` give an explicit family of good vectors in `(ZMod
p)^4`. Fiber bounds for a quadratic map yield cardinality and probability lower bounds for
`goodSet` when `p` is an odd prime. The construction follows [IvanyosSanselmeSantha2007].

## Main statements

* `constructible_good`: the explicit witness construction gives a good vector.
* `lemma7_card`: bounds twice the number of good vectors below by `(p - 9) * p^3`.
* `lemma7_probability`: gives the corresponding rational probability bound.

## References

* [Ivanyos et al., 2007][IvanyosSanselmeSantha2007]
-/

set_option autoImplicit false

namespace Qatlib.Papers.ExtraSpecHSP07.MainResults

open scoped BigOperators

/-- Characterizes a witness by the vanishing of its weighted linear and quadratic sums. -/
theorem isWitness_iff {p : ℕ} (u : Fin 4 → ZMod p) (j : Fin 4 → (ZMod p)ˣ) :
    IsWitness p u j ↔
      (∑ i, u i * (j i : ZMod p) = 0) ∧
        (∑ i, u i * (j i : ZMod p) ^ 2 = 0) := by
  unfold IsWitness
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have hsplit : (∑ i, u i * (j i : ZMod p)) =
        (∑ i, u i * ((j i : ZMod p) - (j i : ZMod p) ^ 2)) +
          ∑ i, u i * (j i : ZMod p) ^ 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [hsplit, h1, h2, add_zero]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have hsplit : (∑ i, u i * ((j i : ZMod p) - (j i : ZMod p) ^ 2)) =
        (∑ i, u i * (j i : ZMod p)) - ∑ i, u i * (j i : ZMod p) ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [hsplit, h1, h2, sub_zero]

/-- The four-coordinate vector with entries `u1`, `u2`, `u3`, and `u4`. -/
def vec4 {p : ℕ} (u1 u2 u3 u4 : ZMod p) : Fin 4 → ZMod p := ![u1, u2, u3, u4]

/-- The coordinate of `vec4 u1 u2 u3 u4` at index zero is `u1`. -/
@[simp] lemma vec4_zero {p : ℕ} (u1 u2 u3 u4 : ZMod p) :
    vec4 u1 u2 u3 u4 (0 : Fin 4) = u1 := by simp [vec4]

/-- The coordinate of `vec4 u1 u2 u3 u4` at index one is `u2`. -/
@[simp] lemma vec4_one {p : ℕ} (u1 u2 u3 u4 : ZMod p) :
    vec4 u1 u2 u3 u4 (1 : Fin 4) = u2 := by simp [vec4]

/-- The coordinate of `vec4 u1 u2 u3 u4` at index two is `u3`. -/
@[simp] lemma vec4_two {p : ℕ} (u1 u2 u3 u4 : ZMod p) :
    vec4 u1 u2 u3 u4 (2 : Fin 4) = u3 := by simp [vec4]

/-- The coordinate of `vec4 u1 u2 u3 u4` at index three is `u4`. -/
@[simp] lemma vec4_three {p : ℕ} (u1 u2 u3 u4 : ZMod p) :
    vec4 u1 u2 u3 u4 (3 : Fin 4) = u4 := by simp [vec4]

/-- The existence of unit coordinates `j1` and `j2` satisfying the witness equations with
remaining coordinates `1` and `-1`. -/
def Constructible {p : ℕ} (u1 u2 u3 u4 : ZMod p) : Prop :=
  ∃ j1 j2 : (ZMod p)ˣ,
    u1 * (j1 : ZMod p) + u2 * (j2 : ZMod p) + u3 - u4 = 0 ∧
      u1 * (j1 : ZMod p) ^ 2 + u2 * (j2 : ZMod p) ^ 2 + u3 + u4 = 0

/-- A constructible four-coordinate vector is good. -/
theorem constructible_good {p : ℕ} (u1 u2 u3 u4 : ZMod p)
    (h : Constructible u1 u2 u3 u4) : IsGoodVector p (vec4 u1 u2 u3 u4) := by
  obtain ⟨j1, j2, h1, h2⟩ := h
  refine ⟨![j1, j2, 1, -1], ?_⟩
  rw [isWitness_iff]
  constructor
  · simpa [vec4, Fin.sum_univ_four, sub_eq_add_neg] using h1
  · simpa [vec4, Fin.sum_univ_four] using h2

/-- A finite set of roots of a quadratic polynomial with nonzero leading coefficient has at most
two elements. -/
theorem quad_roots_le_two {K : Type*} [Field K] (s : Finset K) {a b c : K}
    (ha : a ≠ 0) (hs : ∀ x ∈ s, a * x ^ 2 + b * x + c = 0) : s.card ≤ 2 := by
  by_contra h
  rw [not_le, Finset.two_lt_card_iff] at h
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := h
  have hx0 := hs x hx
  have hy0 := hs y hy
  have hz0 := hs z hz
  have e1 : (x - y) * (a * (x + y) + b) = 0 := by
    have h := sub_eq_zero.mpr (hx0.trans hy0.symm)
    linear_combination h
  have h1 : a * (x + y) + b = 0 := by
    rcases mul_eq_zero.mp e1 with h' | h'
    · exact absurd (sub_eq_zero.mp h') hxy
    · exact h'
  have e2 : (x - z) * (a * (x + z) + b) = 0 := by
    have h := sub_eq_zero.mpr (hx0.trans hz0.symm)
    linear_combination h
  have h2 : a * (x + z) + b = 0 := by
    rcases mul_eq_zero.mp e2 with h' | h'
    · exact absurd (sub_eq_zero.mp h') hxz
    · exact h'
  have e3 : a * (y - z) = 0 := by
    have h := sub_eq_zero.mpr (h1.trans h2.symm)
    linear_combination h
  rcases mul_eq_zero.mp e3 with h' | h'
  · exact ha h'
  · exact hyz (sub_eq_zero.mp h')

/-- The pair of weighted quadratic and linear sums of the coordinates of `q`. -/
def psMap {p : ℕ} (u1 u2 : ZMod p) (q : ZMod p × ZMod p) : ZMod p × ZMod p :=
  (u1 * q.1 ^ 2 + u2 * q.2 ^ 2, u1 * q.1 + u2 * q.2)

/-- Each fiber of `psMap u1 u2` in a finite set has at most two elements when both weights and
their sum are nonzero. -/
theorem psMap_fiber_le_two {p : ℕ} [Fact p.Prime] {u1 u2 : ZMod p}
    (h1 : u1 ≠ 0) (h2 : u2 ≠ 0) (h12 : u1 + u2 ≠ 0)
    (s : Finset (ZMod p × ZMod p)) (t : ZMod p × ZMod p) :
    (s.filter (fun q => psMap u1 u2 q = t)).card ≤ 2 := by
  classical
  set F := s.filter (fun q => psMap u1 u2 q = t) with hF
  have hinj : Set.InjOn (fun q : ZMod p × ZMod p => q.1) ↑F := by
    intro q hq q' hq' heq
    simp only [Finset.mem_coe, hF, Finset.mem_filter] at hq hq'
    have hqP : psMap u1 u2 q = t := hq.2
    have hqP' : psMap u1 u2 q' = t := hq'.2
    change q.1 = q'.1 at heq
    have hS : u1 * q.1 + u2 * q.2 = u1 * q'.1 + u2 * q'.2 := by
      have := congrArg Prod.snd (hqP.trans hqP'.symm)
      simpa [psMap] using this
    rw [heq] at hS
    have hmul : u2 * q.2 = u2 * q'.2 := by linear_combination hS
    have hsub : u2 * (q.2 - q'.2) = 0 := by linear_combination hmul
    have hq2 : q.2 = q'.2 := by
      rcases mul_eq_zero.mp hsub with h' | h'
      · exact absurd h' h2
      · exact sub_eq_zero.mp h'
    exact Prod.ext heq hq2
  have hcard : (F.image (fun q => q.1)).card = F.card := Finset.card_image_of_injOn hinj
  have hcoef : u1 * u2 + u1 ^ 2 ≠ 0 := by
    have he : u1 * u2 + u1 ^ 2 = u1 * (u1 + u2) := by ring
    rw [he]
    exact mul_ne_zero h1 h12
  have hroot : ∀ x ∈ F.image (fun q => q.1),
      (u1 * u2 + u1 ^ 2) * x ^ 2 + (-2 * t.2 * u1) * x + (t.2 ^ 2 - t.1 * u2) = 0 := by
    intro x hx
    obtain ⟨q, hq, hqx⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_coe, hF, Finset.mem_filter] at hq
    have hqP : psMap u1 u2 q = t := hq.2
    have hP1 : u1 * q.1 ^ 2 + u2 * q.2 ^ 2 = t.1 := by
      have := congrArg Prod.fst hqP
      simpa [psMap] using this
    have hP2 : u1 * q.1 + u2 * q.2 = t.2 := by
      have := congrArg Prod.snd hqP
      simpa [psMap] using this
    rw [← hqx]
    linear_combination u2 * hP1 + (u1 * q.1 - u2 * q.2 - t.2) * hP2
  have hle : (F.image (fun q => q.1)).card ≤ 2 :=
    quad_roots_le_two (F.image (fun q => q.1)) hcoef hroot
  rw [← hcard]
  exact hle

/-- The pair `(-(t.1 + t.2) / 2, (t.2 - t.1) / 2)` used to complete a constructible vector. -/
noncomputable def tripleMap {p : ℕ} (t : ZMod p × ZMod p) : ZMod p × ZMod p :=
  (-(t.1 + t.2) * (2 : ZMod p)⁻¹, (t.2 - t.1) * (2 : ZMod p)⁻¹)

/-- The completion map `tripleMap` is injective over `ZMod p` when `p` is prime and two is
nonzero. -/
theorem tripleMap_inj {p : ℕ} [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) :
    Function.Injective (@tripleMap p) := by
  intro a b hab
  simp only [tripleMap, Prod.mk.injEq] at hab
  obtain ⟨hA, hB⟩ := hab
  have h2c : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have ha : a.1 + a.2 = b.1 + b.2 := by
    linear_combination (-2) * hA + (-(a.1 + a.2) + (b.1 + b.2)) * h2c
  have hb : a.2 - a.1 = b.2 - b.1 := by
    linear_combination 2 * hB + (-(a.2 - a.1) + (b.2 - b.1)) * h2c
  have hmul1 : (2 : ZMod p) * a.1 = 2 * b.1 := by linear_combination ha - hb
  have hmul2 : (2 : ZMod p) * a.2 = 2 * b.2 := by linear_combination ha + hb
  exact Prod.ext (mul_left_cancel₀ h2 hmul1) (mul_left_cancel₀ h2 hmul2)

/-- The finite set of nonzero elements of `ZMod p`. -/
def nz (p : ℕ) [NeZero p] : Finset (ZMod p) := Finset.univ.filter (fun x => x ≠ 0)

/-- Membership in `nz p` is equivalent to being nonzero. -/
@[simp] theorem mem_nz {p : ℕ} [NeZero p] {x : ZMod p} : x ∈ nz p ↔ x ≠ 0 := by
  simp [nz]

/-- There are `p - 1` nonzero elements of `ZMod p` for prime `p`. -/
theorem card_nz {p : ℕ} [Fact p.Prime] [NeZero p] : (nz p).card = p - 1 := by
  have h : nz p = Finset.univ.erase (0 : ZMod p) := by
    ext x
    simp [nz]
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]

/-- The finite set of pairs of nonzero elements of `ZMod p`. -/
def psDom (p : ℕ) [NeZero p] : Finset (ZMod p × ZMod p) := nz p ×ˢ nz p

/-- Membership in `psDom p` is equivalent to both coordinates being nonzero. -/
@[simp] theorem mem_psDom {p : ℕ} [NeZero p] {q : ZMod p × ZMod p} :
    q ∈ psDom p ↔ q.1 ≠ 0 ∧ q.2 ≠ 0 := by
  simp [psDom, mem_nz]

/-- The set `psDom p` has cardinality `(p - 1) * (p - 1)` for prime `p`. -/
theorem card_psDom {p : ℕ} [Fact p.Prime] [NeZero p] :
    (psDom p).card = (p - 1) * (p - 1) := by
  rw [psDom, Finset.card_product, card_nz]

/-- The finite set of pairs with nonzero coordinates and nonzero coordinate sum. -/
def pairSet (p : ℕ) [NeZero p] : Finset (ZMod p × ZMod p) :=
  (nz p ×ˢ nz p).filter (fun q => q.1 + q.2 ≠ 0)

/-- Characterizes membership in `pairSet p` by nonvanishing of both coordinates and their sum. -/
@[simp] theorem mem_pairSet {p : ℕ} [NeZero p] {q : ZMod p × ZMod p} :
    q ∈ pairSet p ↔ q.1 ≠ 0 ∧ q.2 ≠ 0 ∧ q.1 + q.2 ≠ 0 := by
  simp [pairSet, mem_nz, and_assoc]

/-- The finite set of pairs of nonzero elements whose sum is zero. -/
def badSet (p : ℕ) [NeZero p] : Finset (ZMod p × ZMod p) :=
  (nz p ×ˢ nz p).filter (fun q => q.1 + q.2 = 0)

/-- For prime `p`, exactly `p - 1` pairs of nonzero elements have sum zero. -/
theorem card_badSet {p : ℕ} [Fact p.Prime] [NeZero p] : (badSet p).card = p - 1 := by
  classical
  have himg : badSet p = (nz p).image (fun u1 => (u1, -u1)) := by
    ext q
    constructor
    · intro hq
      rw [badSet, Finset.mem_filter, Finset.mem_product] at hq
      obtain ⟨⟨hq1, hq2⟩, hq0⟩ := hq
      refine Finset.mem_image.mpr ⟨q.1, hq1, ?_⟩
      have hq2' : q.2 = -q.1 := by linear_combination hq0
      exact Prod.ext rfl hq2'.symm
    · intro hq
      obtain ⟨u1, hu1, hqeq⟩ := Finset.mem_image.mp hq
      rw [← hqeq]
      rw [badSet, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact hu1
      · simpa using hu1
      · simp
  rw [himg, Finset.card_image_of_injOn]
  · exact card_nz
  · intro a _ b _ hab
    simpa using congrArg Prod.fst hab

/-- For an odd prime `p`, `pairSet p` has cardinality `(p - 1) * (p - 2)`. -/
theorem card_pairSet {p : ℕ} [Fact p.Prime] [NeZero p] (hodd : p ≠ 2) :
    (pairSet p).card = (p - 1) * (p - 2) := by
  classical
  have hpair : pairSet p = (nz p ×ˢ nz p) \ badSet p := by
    rw [pairSet, badSet, Finset.filter_not]
  have hsub : badSet p ⊆ nz p ×ˢ nz p := Finset.filter_subset _ _
  rw [hpair, Finset.card_sdiff_of_subset hsub, Finset.card_product, card_nz, card_badSet]
  have h1 : p - 1 = (p - 2) + 1 := by
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  calc (p - 1) * (p - 1) - (p - 1)
      = (p - 1) * ((p - 2) + 1) - (p - 1) := by rw [h1]
    _ = ((p - 1) * (p - 2) + (p - 1)) - (p - 1) := by rw [Nat.mul_add, Nat.mul_one]
    _ = (p - 1) * (p - 2) := Nat.add_sub_cancel _ _

/-- The image of the nonzero-coordinate domain under the weighted quadratic-linear map
determined by `r`. -/
noncomputable def imgSet (p : ℕ) [NeZero p] (r : ZMod p × ZMod p) :
    Finset (ZMod p × ZMod p) := by
  classical
  exact (psDom p).image (psMap r.1 r.2)

/-- An element lies in `imgSet p r` exactly when it is the image under `psMap r.1 r.2` of an
element of `psDom p`. -/
theorem mem_imgSet {p : ℕ} [NeZero p] (r : ZMod p × ZMod p) (t : ZMod p × ZMod p) :
    t ∈ imgSet p r ↔ ∃ q ∈ psDom p, psMap r.1 r.2 q = t := by
  simp [imgSet]

/-- The four-coordinate vectors obtained by adjoining the `tripleMap` completion of each element
of `imgSet p r` to `r`. -/
noncomputable def cvSet (p : ℕ) [NeZero p] (r : ZMod p × ZMod p) :
    Finset (Fin 4 → ZMod p) := by
  classical
  exact (imgSet p r).image (fun t => vec4 r.1 r.2 (tripleMap t).1 (tripleMap t).2)

/-- The completion construction preserves the cardinality of `imgSet p r` when two is nonzero. -/
theorem card_cvSet {p : ℕ} [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (r : ZMod p × ZMod p) : (cvSet p r).card = (imgSet p r).card := by
  classical
  rw [cvSet, Finset.card_image_of_injOn]
  intro a _ b _ hab
  have h1 : (tripleMap a).1 = (tripleMap b).1 := by
    have := congrArg (fun f : Fin 4 → ZMod p => f 2) hab
    simpa using this
  have h2' : (tripleMap a).2 = (tripleMap b).2 := by
    have := congrArg (fun f : Fin 4 → ZMod p => f 3) hab
    simpa using this
  exact tripleMap_inj h2 (Prod.ext h1 h2')

/-- The finite set of all good four-coordinate vectors over `ZMod p`. -/
noncomputable def goodSet (p : ℕ) [NeZero p] : Finset (Fin 4 → ZMod p) := by
  classical
  exact Finset.univ.filter (fun u => IsGoodVector p u)

/-- Membership in `goodSet p` is equivalent to the good-vector predicate. -/
@[simp] theorem mem_goodSet {p : ℕ} [NeZero p] {u : Fin 4 → ZMod p} :
    u ∈ goodSet p ↔ IsGoodVector p u := by
  classical
  simp [goodSet]

/-- The vectors constructed from a pair in `pairSet p` are good when two is nonzero. -/
theorem cvSet_subset_good {p : ℕ} [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    {r : ZMod p × ZMod p} (hr : r ∈ pairSet p) : cvSet p r ⊆ goodSet p := by
  classical
  intro x hx
  obtain ⟨t, ht, hxt⟩ := Finset.mem_image.mp hx
  obtain ⟨q, hq, hqt⟩ := Finset.mem_image.mp ht
  have hq1 : q.1 ≠ 0 := (mem_psDom.mp hq).1
  have hq2 : q.2 ≠ 0 := (mem_psDom.mp hq).2
  have h2c : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have key1 : ∀ P S : ZMod p, S + (-(P + S) * 2⁻¹) - ((S - P) * 2⁻¹) = 0 := by
    intro P S
    linear_combination (-S) * h2c
  have key2 : ∀ P S : ZMod p, P + (-(P + S) * 2⁻¹) + ((S - P) * 2⁻¹) = 0 := by
    intro P S
    linear_combination (-P) * h2c
  have hcon : Constructible r.1 r.2 (tripleMap t).1 (tripleMap t).2 := by
    refine ⟨Units.mk0 q.1 hq1, Units.mk0 q.2 hq2, ?_, ?_⟩
    · rw [← hqt]
      have h := key1 (r.1 * q.1 ^ 2 + r.2 * q.2 ^ 2) (r.1 * q.1 + r.2 * q.2)
      simpa [psMap, tripleMap, Units.val_mk0] using h
    · rw [← hqt]
      have h := key2 (r.1 * q.1 ^ 2 + r.2 * q.2 ^ 2) (r.1 * q.1 + r.2 * q.2)
      simpa [psMap, tripleMap, Units.val_mk0] using h
  have hgood : IsGoodVector p (vec4 r.1 r.2 (tripleMap t).1 (tripleMap t).2) :=
    constructible_good r.1 r.2 _ _ hcon
  rw [goodSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [← hxt]
  exact hgood

/-- The union of the constructed vector sets over all pairs in `pairSet p`. -/
noncomputable def CVec (p : ℕ) [NeZero p] : Finset (Fin 4 → ZMod p) := by
  classical
  exact (pairSet p).biUnion (fun r => cvSet p r)

/-- For an odd prime `p`, every vector in `CVec p` is good. -/
theorem CVec_subset_good {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) :
    CVec p ⊆ goodSet p := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hp1 | hp2
    · exact (Fact.out : p.Prime).ne_one hp1
    · exact hodd hp2
  intro x hx
  rw [CVec, Finset.mem_biUnion] at hx
  obtain ⟨r, hr, hxr⟩ := hx
  exact cvSet_subset_good h2 hr hxr

/-- For an odd prime `p`, twice the cardinality of `CVec p` is at least `(p - 1) * (p - 2) * (p
- 1)^2`. -/
theorem CVec_card_ge {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) :
    (p - 1) * (p - 2) * (p - 1) ^ 2 ≤ 2 * (CVec p).card := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hp1 | hp2
    · exact (Fact.out : p.Prime).ne_one hp1
    · exact hodd hp2
  have hdisj : (pairSet p : Set (ZMod p × ZMod p)).PairwiseDisjoint (fun r => cvSet p r) := by
    intro r _ r' _ hne
    change Disjoint (cvSet p r) (cvSet p r')
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨t, _, hxt⟩ := Finset.mem_image.mp hx
    obtain ⟨t', _, hxt'⟩ := Finset.mem_image.mp hx'
    have heq : vec4 r.1 r.2 (tripleMap t).1 (tripleMap t).2 =
        vec4 r'.1 r'.2 (tripleMap t').1 (tripleMap t').2 := hxt.trans hxt'.symm
    have h1 : r.1 = r'.1 := by
      have := congrArg (fun f : Fin 4 → ZMod p => f 0) heq
      simpa using this
    have h2' : r.2 = r'.2 := by
      have := congrArg (fun f : Fin 4 → ZMod p => f 1) heq
      simpa using this
    exact hne (Prod.ext h1 h2')
  have hcard := Finset.card_biUnion (s := pairSet p) (t := fun r => cvSet p r) hdisj
  have hper : ∀ r ∈ pairSet p, (p - 1) ^ 2 ≤ 2 * (cvSet p r).card := by
    intro r hr
    have hmem := mem_pairSet.mp hr
    have hfib : ∀ t, ((psDom p).filter (fun q => psMap r.1 r.2 q = t)).card ≤ 2 :=
      fun t => psMap_fiber_le_two hmem.1 hmem.2.1 hmem.2.2 (psDom p) t
    have hsum := Finset.card_eq_sum_card_image (psMap r.1 r.2) (psDom p)
    have hle : (psDom p).card ≤ 2 * (imgSet p r).card := by
      rw [hsum]
      calc (∑ t ∈ (psDom p).image (psMap r.1 r.2),
              ((psDom p).filter (fun q => psMap r.1 r.2 q = t)).card)
          ≤ ∑ t ∈ (psDom p).image (psMap r.1 r.2), 2 := by
            exact Finset.sum_le_sum (fun t _ => hfib t)
        _ = ((psDom p).image (psMap r.1 r.2)).card * 2 :=
            Finset.sum_const_nat (fun _ _ => rfl)
        _ = 2 * (imgSet p r).card := by rw [imgSet, Nat.mul_comm]
    rw [card_psDom] at hle
    rw [card_cvSet h2]
    calc (p - 1) ^ 2 = (p - 1) * (p - 1) := by ring
      _ ≤ 2 * (imgSet p r).card := hle
  calc (p - 1) * (p - 2) * (p - 1) ^ 2
      = (pairSet p).card * (p - 1) ^ 2 := by rw [card_pairSet hodd]
    _ = ∑ r ∈ pairSet p, (p - 1) ^ 2 := by
          rw [Finset.sum_const_nat (fun _ _ => rfl)]
    _ ≤ ∑ r ∈ pairSet p, 2 * (cvSet p r).card := Finset.sum_le_sum hper
    _ = 2 * ∑ r ∈ pairSet p, (cvSet p r).card := by rw [Finset.mul_sum]
    _ = 2 * (CVec p).card := by rw [← hcard, CVec]

/-- For `p ≥ 3`, the natural-number expression `(p - 9) * p^3` is at most `(p - 1) * (p - 2) *
(p - 1)^2`. -/
theorem arith_key {p : ℕ} (hp : 3 ≤ p) :
    (p - 9) * p ^ 3 ≤ (p - 1) * (p - 2) * (p - 1) ^ 2 := by
  by_cases h9 : p < 9
  · have hz : p - 9 = 0 := Nat.sub_eq_zero_of_le (by omega)
    simp [hz]
  · push_neg at h9
    have hp9 : 9 ≤ p := by omega
    have hcast9 : ((p - 9 : ℕ) : ℤ) = (p : ℤ) - 9 := by
      rw [Nat.cast_sub hp9]; norm_num
    have hcast1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    have hcast2 : ((p - 2 : ℕ) : ℤ) = (p : ℤ) - 2 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    have hmain : ((p - 9) * p ^ 3 : ℕ) ≤ ((p - 1) * (p - 2) * (p - 1) ^ 2 : ℕ) := by
      have hZ : (((p - 9) * p ^ 3 : ℕ) : ℤ) ≤ (((p - 1) * (p - 2) * (p - 1) ^ 2 : ℕ) : ℤ) := by
        push_cast
        rw [hcast9, hcast1, hcast2]
        have hp3 : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
        nlinarith [hp3, sq_nonneg (p : ℤ), sq_nonneg ((p : ℤ) - 3),
          mul_nonneg (show (0 : ℤ) ≤ (p : ℤ) by omega) (sq_nonneg ((p : ℤ) - 3))]
      exact_mod_cast hZ
    exact hmain

/-- For an odd prime `p`, twice the number of good vectors is at least `(p - 9) * p^3`, with
subtraction in natural numbers. This is the cardinality estimate for Lemma 7 of
[IvanyosSanselmeSantha2007]. -/
theorem lemma7_card {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) :
    (p - 9) * p ^ 3 ≤ 2 * (goodSet p).card := by
  classical
  have h3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hCV : CVec p ⊆ goodSet p := CVec_subset_good hodd
  have hcard : (CVec p).card ≤ (goodSet p).card := Finset.card_le_card hCV
  calc (p - 9) * p ^ 3 ≤ (p - 1) * (p - 2) * (p - 1) ^ 2 := arith_key h3
    _ ≤ 2 * (CVec p).card := CVec_card_ge hodd
    _ ≤ 2 * (goodSet p).card := by omega

/-- The fraction of good vectors is at least `((p - 9 : ℕ) : ℚ) / (2 * p)` for an odd prime `p`.
This is the rational probability form of Lemma 7 of [IvanyosSanselmeSantha2007]. -/
theorem lemma7_probability {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) :
    ((p - 9 : ℕ) : ℚ) / (2 * (p : ℚ)) ≤
      ((goodSet p).card : ℚ) / ((p : ℚ) ^ 4) := by
  classical
  have hcard := lemma7_card hodd
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hden : (0 : ℚ) < 2 * (p : ℚ) := by positivity
  have hp4 : (0 : ℚ) < (p : ℚ) ^ 4 := by positivity
  by_cases h9 : p < 9
  · have hz : (p - 9 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hz, Nat.cast_zero, zero_div]
    positivity
  · push_neg at h9
    have hp9 : 9 ≤ p := by omega
    have hcast9 : ((p - 9 : ℕ) : ℚ) = (p : ℚ) - 9 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    have hc : ((p : ℚ) - 9) * (p : ℚ) ^ 3 ≤ 2 * ((goodSet p).card : ℚ) := by
      rw [← hcast9]
      exact_mod_cast hcard
    rw [div_le_div_iff₀ hden hp4, hcast9]
    have hmul : ((p : ℚ) - 9) * (p : ℚ) ^ 3 * (p : ℚ) ≤
        (2 * ((goodSet p).card : ℚ)) * (p : ℚ) :=
      mul_le_mul_of_nonneg_right hc (le_of_lt hp0)
    nlinarith [hmul]

end Qatlib.Papers.ExtraSpecHSP07.MainResults
