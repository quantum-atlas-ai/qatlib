/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JuntaLearning07.MainResults.JuntaLearningDefs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Sqrt

/-!
# Addressing functions far from juntas

This module formalizes the addressing-function construction underlying the rejecting family in
[AticiServedio2007], Lemma III.6. `addressingFun` reads a leaf coordinate selected by address
bits, while `IsAddressingShape` embeds distinct address and leaf coordinates into an ambient
Boolean cube.

The address slices `addrSlice` isolate each fixed address. `addrSlice_sum_half` shows that a
comparison function ignoring the selected leaf disagrees on exactly half of such a slice;
counting these slices gives `addressing_far_one_six` under the stated address, leaf, and
junta-size assumptions.

## Main statements

- `addressing_dependsOnlyOn` bounds dependence by the designated address and leaf coordinates.
- `addressing_support_card` and `addressing_support_card_of_shape` count their union as `r + R`.
* `addrSliceEquiv` identifies a fixed address slice with assignments to the remaining
  coordinates, giving `addrSlice_card`.
* `addrSlice_sum_half` proves exact half-slice disagreement when the selected leaf is absent
  from the comparison support.
* `addressing_far_one_six` proves distance at least `1 / 6` from every `k`-junta for the
  specified parameters.

## References

* [Atici and Servedio, 2007][AticiServedio2007], Quantum Algorithms for Learning and Testing
  Juntas, Lemma III.6.
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.JuntaLearning07.MainResults

open scoped BigOperators

variable {n : ℕ}

/-- The Boolean addressing function that reads the first `r` bits, uses `dec` to select one of
the next `R` bits, and returns that selected leaf bit. -/
def addressingFun (r R : ℕ) (dec : (Fin r → Bool) → Fin R)
    (x : Fin (r + R) → Bool) : Bool :=
  x (Fin.natAdd r (dec (fun j => x (Fin.castAdd R j))))

/-- The property that `f` returns a leaf bit selected by the address bits through `dec`, with
injective address and leaf coordinate maps having disjoint images. -/
def IsAddressingShape (r R : ℕ) (addr : Fin r → Fin n) (leaf : Fin R → Fin n)
    (dec : (Fin r → Bool) → Fin R) (f : (Fin n → Bool) → Bool) : Prop :=
  Function.Injective addr ∧ Function.Injective leaf ∧
    (∀ i j, addr i ≠ leaf j) ∧
    ∀ x, f x = x (leaf (dec (fun j => x (addr j))))

/-- A function of addressing shape depends only on the union of its designated address and leaf
coordinates. -/
theorem addressing_dependsOnlyOn {r R : ℕ} {addr : Fin r → Fin n}
    {leaf : Fin R → Fin n} {dec : (Fin r → Bool) → Fin R}
    {f : (Fin n → Bool) → Bool}
    (hshape : IsAddressingShape (n := n) r R addr leaf dec f) :
    dependsOnlyOn (Finset.image addr Finset.univ ∪ Finset.image leaf Finset.univ) f := by
  obtain ⟨haddr, hleaf, hdisj, hrepr⟩ := hshape
  intro x y hxy
  rw [hrepr x, hrepr y]
  have hxaddr : (fun j => x (addr j)) = (fun j => y (addr j)) := by
    funext j
    exact hxy (addr j) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩))
  rw [hxaddr]
  exact hxy (leaf (dec (fun j => y (addr j))))
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩))

/-- If the address and leaf coordinate maps are injective and have disjoint images, their union
contains exactly `r + R` coordinates. -/
theorem addressing_support_card {r R : ℕ} {addr : Fin r → Fin n}
    {leaf : Fin R → Fin n}
    (haddr : Function.Injective addr) (hleaf : Function.Injective leaf)
    (hdisj : ∀ i j, addr i ≠ leaf j) :
    (Finset.image addr Finset.univ ∪ Finset.image leaf Finset.univ).card = r + R := by
  have hcardA : (Finset.image addr Finset.univ).card = r := by
    rw [Finset.card_image_of_injective _ haddr, Finset.card_univ, Fintype.card_fin]
  have hcardL : (Finset.image leaf Finset.univ).card = R := by
    rw [Finset.card_image_of_injective _ hleaf, Finset.card_univ, Fintype.card_fin]
  have hdisj' : Disjoint (Finset.image addr Finset.univ) (Finset.image leaf Finset.univ) := by
    rw [Finset.disjoint_left]
    intro a ha hl
    rw [Finset.mem_image] at ha hl
    obtain ⟨i, _, rfl⟩ := ha
    obtain ⟨j, _, hj⟩ := hl
    exact hdisj i j hj.symm
  rw [Finset.card_union_of_disjoint hdisj', hcardA, hcardL]

/-- For a function of addressing shape, the union of the designated address and leaf coordinates
has cardinality `r + R`. -/
theorem addressing_support_card_of_shape {r R : ℕ} {addr : Fin r → Fin n}
    {leaf : Fin R → Fin n} {dec : (Fin r → Bool) → Fin R}
    {f : (Fin n → Bool) → Bool}
    (hshape : IsAddressingShape (n := n) r R addr leaf dec f) :
    (Finset.image addr Finset.univ ∪ Finset.image leaf Finset.univ).card = r + R := by
  obtain ⟨haddr, hleaf, hdisj, _⟩ := hshape
  exact addressing_support_card haddr hleaf hdisj

open Qatlib.Concepts.ProbabilityCore.DistributionAA

open scoped BigOperators

variable {n : ℕ}

/-- The finite set of Boolean-cube inputs whose coordinates selected by `addr` agree with the
fixed address assignment `a`. -/
def addrSlice {n r : ℕ} (addr : Fin r → Fin n) (a : Fin r → Bool) :
    Finset (Fin n → Bool) :=
  Finset.univ.filter (fun x => ∀ j, x (addr j) = a j)

/-- An input belongs to an address slice exactly when every designated address coordinate has
its prescribed value. -/
theorem mem_addrSlice {n r : ℕ} {addr : Fin r → Fin n} {a : Fin r → Bool}
    {x : Fin n → Bool} :
    x ∈ addrSlice addr a ↔ ∀ j, x (addr j) = a j := by
  simp [addrSlice]

/-- For an injective address map, identifies inputs with fixed address bits with arbitrary
Boolean assignments to coordinates outside the address image. -/
noncomputable def addrSliceEquiv {n r : ℕ} {addr : Fin r → Fin n}
    (hadj : Function.Injective addr) (a : Fin r → Bool) :
    {x : Fin n → Bool // ∀ j, x (addr j) = a j} ≃
      ({i : Fin n // i ∉ Finset.image addr Finset.univ} → Bool) where
  toFun x := fun i => x.1 i.1
  invFun y :=
    ⟨fun i => if h : i ∈ Finset.image addr Finset.univ then
        a (Classical.choose (Finset.mem_image.mp h)) else y ⟨i, h⟩, by
      intro j
      have hmem : addr j ∈ Finset.image addr Finset.univ :=
        Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
      have hc : Classical.choose (Finset.mem_image.mp hmem) = j :=
        hadj (Classical.choose_spec (Finset.mem_image.mp hmem)).2
      simp only [dif_pos hmem, hc]⟩
  left_inv x := by
    ext i
    by_cases h : i ∈ Finset.image addr Finset.univ
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp h
      have hc : Classical.choose (Finset.mem_image.mp h) = j :=
        hadj (Classical.choose_spec (Finset.mem_image.mp h)).2
      simp only [dif_pos h, hc]
      exact (x.2 j).symm
    · simp only [dif_neg h]
  right_inv y := by
    ext i
    simp only [dif_neg i.2]

/-- Fixing the `r` coordinates of an injective address map leaves exactly `2 ^ (n - r)`
Boolean-cube inputs. -/
theorem addrSlice_card {n r : ℕ} {addr : Fin r → Fin n}
    (hadj : Function.Injective addr) (a : Fin r → Bool) :
    (addrSlice addr a).card = 2 ^ (n - r) := by
  classical
  have h1 : (addrSlice addr a).card =
      Fintype.card {x : Fin n → Bool // ∀ j, x (addr j) = a j} := by
    rw [addrSlice]
    exact (Fintype.card_subtype (fun x : Fin n → Bool => ∀ j, x (addr j) = a j)).symm
  have hfree : Fintype.card {i : Fin n // i ∉ Finset.image addr Finset.univ} = n - r := by
    rw [Fintype.card_subtype]
    have hfil : (Finset.univ.filter (fun i : Fin n => i ∉ Finset.image addr Finset.univ))
        = Finset.univ \ Finset.image addr Finset.univ := by
      ext i
      simp
    rw [hfil, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Finset.card_image_of_injective _ hadj]
    simp [Fintype.card_fin]
  rw [h1, Fintype.card_congr (addrSliceEquiv hadj a), Fintype.card_fun, hfree]
  simp [Fintype.card_bool]

/-- On an address slice selecting leaf `l`, a function of addressing shape disagrees with any
comparison function ignoring that leaf on exactly half of the slice. -/
theorem addrSlice_sum_half {n r R : ℕ} {addr : Fin r → Fin n}
    {leaf : Fin R → Fin n} {dec : (Fin r → Bool) → Fin R}
    {f : (Fin n → Bool) → Bool}
    (hshape : IsAddressingShape (n := n) r R addr leaf dec f)
    {J : Finset (Fin n)} {g : (Fin n → Bool) → Bool} (hdep : dependsOnlyOn J g)
    {l : Fin R} (hl : leaf l ∉ J) {a : Fin r → Bool} (ha : dec a = l) :
    (∑ x ∈ addrSlice addr a, (if f x = g x then (0 : ℝ) else 1)) =
      ((addrSlice addr a).card : ℝ) / 2 := by
  classical
  obtain ⟨haddr, hleaf, hdisj, hrepr⟩ := hshape
  have hf_eq : ∀ x ∈ addrSlice addr a, f x = x (leaf l) := by
    intro x hx
    rw [hrepr x]
    have hxa : (fun j => x (addr j)) = a := funext (fun j => (mem_addrSlice.mp hx) j)
    rw [hxa, ha]
  have hflip_slice : ∀ x ∈ addrSlice addr a, cubeFlip x (leaf l) ∈ addrSlice addr a := by
    intro x hx
    rw [mem_addrSlice] at hx ⊢
    intro j
    have hne : addr j ≠ leaf l := hdisj j l
    simp [cubeFlip, hne, hx j]
  have hflip_g : ∀ x, g (cubeFlip x (leaf l)) = g x := by
    intro x
    apply hdep
    intro j hj
    have hne : j ≠ leaf l := by
      intro h
      exact hl (h ▸ hj)
    simp [cubeFlip, hne]
  have hpair : ∀ x ∈ addrSlice addr a,
      (if f x = g x then (0 : ℝ) else 1) +
        (if f (cubeFlip x (leaf l)) = g (cubeFlip x (leaf l)) then (0 : ℝ) else 1) = 1 := by
    intro x hx
    have hfx : f x = x (leaf l) := hf_eq x hx
    have hfl : (cubeFlip x (leaf l)) (leaf l) = !x (leaf l) := by
      simp [cubeFlip]
    have hfx' : f (cubeFlip x (leaf l)) = !x (leaf l) := by
      rw [hf_eq (cubeFlip x (leaf l)) (hflip_slice x hx), hfl]
    rw [hfx, hfx', hflip_g x]
    cases x (leaf l) <;> cases g x <;> simp
  have hreindex : ∑ x ∈ addrSlice addr a,
        (if f (cubeFlip x (leaf l)) = g (cubeFlip x (leaf l)) then (0 : ℝ) else 1) =
      ∑ x ∈ addrSlice addr a, (if f x = g x then (0 : ℝ) else 1) := by
    refine Finset.sum_nbij' (fun x => cubeFlip x (leaf l)) (fun x => cubeFlip x (leaf l))
      ?_ ?_ ?_ ?_ ?_
    · intro x hx
      exact hflip_slice x hx
    · intro x hx
      exact hflip_slice x hx
    · intro x _
      exact cube_flip_involution x (leaf l)
    · intro x _
      exact cube_flip_involution x (leaf l)
    · intro x _
      rfl
  have htwice : 2 * (∑ x ∈ addrSlice addr a, (if f x = g x then (0 : ℝ) else 1)) =
      ((addrSlice addr a).card : ℝ) := by
    rw [two_mul]
    calc (∑ x ∈ addrSlice addr a, (if f x = g x then (0 : ℝ) else 1)) +
          ∑ x ∈ addrSlice addr a, (if f x = g x then (0 : ℝ) else 1)
        = (∑ x ∈ addrSlice addr a, (if f x = g x then (0 : ℝ) else 1)) +
            ∑ x ∈ addrSlice addr a,
              (if f (cubeFlip x (leaf l)) = g (cubeFlip x (leaf l)) then (0 : ℝ) else 1) := by
          rw [hreindex]
      _ = ∑ x ∈ addrSlice addr a,
            ((if f x = g x then (0 : ℝ) else 1) +
              (if f (cubeFlip x (leaf l)) = g (cubeFlip x (leaf l)) then (0 : ℝ) else 1)) := by
          rw [Finset.sum_add_distrib]
      _ = ∑ _x ∈ addrSlice addr a, (1 : ℝ) :=
          Finset.sum_congr rfl (fun x hx => hpair x hx)
      _ = ((addrSlice addr a).card : ℝ) := by simp
  have hgoal := htwice
  rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
  linarith

/-- An addressing-shape function is at distance at least `1 / 6` from every `k`-junta when `dec`
is surjective, `r ≥ 1`, `R = 2 ^ r`, `k = r + R / 2`, and `6 * r < R`. This gives the
addressing-function separation associated with Lemma III.6 of [AticiServedio2007]. -/
theorem addressing_far_one_six {n r R k : ℕ} {addr : Fin r → Fin n}
    {leaf : Fin R → Fin n} {dec : (Fin r → Bool) → Fin R}
    {f : (Fin n → Bool) → Bool}
    (hshape : IsAddressingShape (n := n) r R addr leaf dec f)
    (hsurj : Function.Surjective dec) (hr : 1 ≤ r) (hR : R = 2 ^ r)
    (hk : k = r + R / 2) (hbig : 6 * r < R) :
    farFromJunta k (1 / 6) f := by
  classical
  have hshape' : IsAddressingShape (n := n) r R addr leaf dec f := hshape
  obtain ⟨haddr, hleaf, hdisj, hrepr⟩ := hshape
  intro g hg
  obtain ⟨J, hJcard, hJdep⟩ := hg
  have hrle : r ≤ n := by
    have h := Fintype.card_le_of_injective addr haddr
    simpa [Fintype.card_fin] using! h
  have heven : R = 2 * (R / 2) := by
    have hdvd : 2 ∣ 2 ^ r := ⟨2 ^ (r - 1), by rw [← pow_succ', Nat.sub_add_cancel hr]⟩
    rw [hR]
    exact (Nat.mul_div_cancel' hdvd).symm
  let jin : Finset (Fin R) := Finset.univ.filter (fun l => leaf l ∈ J)
  let bad : Finset (Fin R) := Finset.univ.filter (fun l => leaf l ∉ J)
  let good : Finset (Fin r → Bool) := Finset.univ.filter (fun a => dec a ∈ bad)
  have hbad_eq : bad = Finset.univ \ jin := by
    ext l
    simp [bad, jin]
  have hjin_card : jin.card ≤ k := by
    have himg : jin.image leaf ⊆ J := by
      intro i hi
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_filter.mp hl).2
    calc jin.card = (jin.image leaf).card := (Finset.card_image_of_injective jin hleaf).symm
      _ ≤ J.card := Finset.card_le_card himg
      _ ≤ k := hJcard
  have hbad_card : R - k ≤ bad.card := by
    rw [hbad_eq, Finset.card_sdiff_of_subset (Finset.subset_univ jin), Finset.card_univ,
      Fintype.card_fin]
    omega
  have hgood_card : bad.card ≤ good.card := by
    have hinj : Function.Injective (fun l : Fin R => Classical.choose (hsurj l)) := by
      intro l1 l2 h
      have h' : Classical.choose (hsurj l1) = Classical.choose (hsurj l2) := h
      calc l1 = dec (Classical.choose (hsurj l1)) := (Classical.choose_spec (hsurj l1)).symm
        _ = dec (Classical.choose (hsurj l2)) := by rw [h']
        _ = l2 := Classical.choose_spec (hsurj l2)
    have himg : bad.image (fun l => Classical.choose (hsurj l)) ⊆ good := by
      intro a ha
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ha
      simp only [good, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [Classical.choose_spec (hsurj l)]
      exact hl
    calc bad.card = (bad.image (fun l => Classical.choose (hsurj l))).card :=
          (Finset.card_image_of_injective bad hinj).symm
      _ ≤ good.card := Finset.card_le_card himg
  have hslice_disj : ∀ a ∈ good, ∀ a' ∈ good, a ≠ a' →
      Disjoint (addrSlice addr a) (addrSlice addr a') := by
    intro a _ a' _ hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    apply hne
    funext j
    rw [← mem_addrSlice.mp hx j, mem_addrSlice.mp hx' j]
  have hpairwise : Set.PairwiseDisjoint (↑good) (fun a => addrSlice addr a) := by
    intro a ha a' ha' hne
    exact hslice_disj a ha a' ha' hne
  have hhalf : ∀ a ∈ good,
      (∑ x ∈ addrSlice addr a, (if f x = g x then (0 : ℝ) else 1)) =
        ((addrSlice addr a).card : ℝ) / 2 := by
    intro a ha
    have hbadmem : dec a ∈ bad := (Finset.mem_filter.mp ha).2
    have hl : leaf (dec a) ∉ J := (Finset.mem_filter.mp hbadmem).2
    exact addrSlice_sum_half hshape' hJdep hl rfl
  have htotal : (∑ a ∈ good, ((addrSlice addr a).card : ℝ) / 2) ≤
      ∑ x : Fin n → Bool, (if f x = g x then (0 : ℝ) else 1) := by
    calc (∑ a ∈ good, ((addrSlice addr a).card : ℝ) / 2)
        = ∑ a ∈ good, ∑ x ∈ addrSlice addr a,
            (if f x = g x then (0 : ℝ) else 1) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact (hhalf a ha).symm
      _ = ∑ x ∈ good.biUnion (fun a => addrSlice addr a),
            (if f x = g x then (0 : ℝ) else 1) := (Finset.sum_biUnion hpairwise).symm
      _ ≤ ∑ x : Fin n → Bool, (if f x = g x then (0 : ℝ) else 1) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun x _ _ => by positivity)
  have hsum_eq : (∑ a ∈ good, ((addrSlice addr a).card : ℝ) / 2)
      = (good.card : ℝ) * (2 : ℝ) ^ (n - r) / 2 := by
    have hconst : ∀ a ∈ good, ((addrSlice addr a).card : ℝ) / 2
        = ((2 ^ (n - r) : ℕ) : ℝ) / 2 := by
      intro a _
      rw [addrSlice_card haddr a]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    push_cast
    ring
  have hdis_def : disagreement f g =
      ((2 : ℝ) ^ n)⁻¹ * ∑ x : Fin n → Bool, (if f x = g x then (0 : ℝ) else 1) := rfl
  have hlower : ((2 : ℝ) ^ n)⁻¹ * ((good.card : ℝ) * (2 : ℝ) ^ (n - r) / 2) ≤
      disagreement f g := by
    rw [hdis_def]
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← hsum_eq]
    exact htotal
  have hpow_split : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - r) * (2 : ℝ) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hrle]
  have hLHS : ((2 : ℝ) ^ n)⁻¹ * ((good.card : ℝ) * (2 : ℝ) ^ (n - r) / 2)
      = (good.card : ℝ) / (2 * (2 : ℝ) ^ r) := by
    rw [hpow_split]
    set A : ℝ := (2 : ℝ) ^ (n - r) with hAdef
    set B : ℝ := (2 : ℝ) ^ r with hBdef
    set c : ℝ := (good.card : ℝ) with hcdef
    have hA : A ≠ 0 := by rw [hAdef]; positivity
    have hB : B ≠ 0 := by rw [hBdef]; positivity
    field_simp
  rw [hLHS] at hlower
  have hgood_ge : (R : ℝ) / 2 - (r : ℝ) ≤ (good.card : ℝ) := by
    have h1 : (bad.card : ℝ) ≤ (good.card : ℝ) := by exact_mod_cast hgood_card
    have hkR : k ≤ R := by omega
    have hcast : ((R - k : ℕ) : ℝ) = (R : ℝ) - (k : ℝ) := by
      rw [Nat.cast_sub hkR]
    have h2 : (R : ℝ) - (k : ℝ) ≤ (bad.card : ℝ) := by
      rw [← hcast]
      exact_mod_cast hbad_card
    have hkR' : (k : ℝ) = (r : ℝ) + ((R / 2 : ℕ) : ℝ) := by
      rw [hk]
      push_cast
      ring
    have hhalfR : ((R / 2 : ℕ) : ℝ) = (R : ℝ) / 2 := by
      have h : (R : ℝ) = 2 * ((R / 2 : ℕ) : ℝ) := by
        have h' := congrArg (fun m : ℕ => (m : ℝ)) heven
        push_cast at h'
        linarith
      linarith
    linarith
  have hRpow : (R : ℝ) = (2 : ℝ) ^ r := by
    rw [hR]
    push_cast
    ring
  have hfin : (1 / 6 : ℝ) ≤ (good.card : ℝ) / (2 * (2 : ℝ) ^ r) := by
    rw [hRpow] at hgood_ge
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (2 : ℝ) ^ r)]
    have hb : (6 : ℝ) * (r : ℝ) < (2 : ℝ) ^ r := by
      have hc : ((6 * r : ℕ) : ℝ) < (R : ℝ) := by exact_mod_cast hbig
      rw [hRpow] at hc
      push_cast at hc
      linarith
    linarith
  exact le_trans hfin hlower

end Qatlib.Papers.JuntaLearning07.MainResults
