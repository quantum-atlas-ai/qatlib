/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoncommHSP98.MainResults.Lemma4Born

/-!
# Dihedral subgroup reduction and query accounting

This module equips `DihPt` with its group structure and studies the rotation subgroup `Rot`.
Generators of the rotational part, together with one reflection when present, generate the
hidden subgroup. For a divisor `M` of `N`, `redD` reduces the rotation coordinate modulo `M`;
the coset promise descends when the hidden subgroup contains its kernel.

The final results combine reflection recovery with rotational generators and give explicit
real-valued probability and logarithmic query estimates for the reduction. This development
accompanies [EttingerHoyer1999].

## Main statements

* `closure_union_generates`: rotational generators and a reflection generate the subgroup.
* `quotient_promise`: the hiding promise descends through `redD`.
* `recovery_from_order_two`: combines quotient-image equality and subgroup generation.
* `query_accounting`: bounds the product of the repetition factor and per-run query estimate.

## References

* [Ettinger and Hoyer, 1999][EttingerHoyer1999]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators
set_option warningAsError false

namespace Qatlib.Papers.NoncommHSP98.MainResults

/-- The dihedral inverse, negating the rotation coordinate exactly when the binary coordinate is
zero. -/
def dihInv (N : ℕ) (x : DihPt N) : DihPt N :=
  (if x.2 = 0 then -x.1 else x.1, x.2)

/-- Dihedral coordinate multiplication is associative. -/
lemma dihMul_assoc (N : ℕ) (x y z : DihPt N) :
    dihMul N (dihMul N x y) z = dihMul N x (dihMul N y z) := by
  obtain ⟨a1, b1⟩ := x; obtain ⟨a2, b2⟩ := y; obtain ⟨a3, b3⟩ := z
  rcases zmod2_cases b1 with h1 | h1 <;> rcases zmod2_cases b2 with h2 | h2 <;>
    rcases zmod2_cases b3 with h3 | h3 <;>
    subst h1 <;> subst h2 <;> subst h3 <;>
    simp only [dihMul, zmod2_one_add_one, zero_add, add_zero] <;>
    ext <;> simp
  all_goals ring

/-- Adding the residue of two to a binary residue leaves it unchanged. -/
lemma zmod2_two_add (b : ZMod 2) : (2 : ZMod 2) + b = b := by
  rcases zmod2_cases b with h | h <;> subst h <;> decide

/-- The dihedral inverse multiplied on the left cancels to `(0, 0)`. -/
lemma dihInv_mul_cancel (N : ℕ) (x : DihPt N) : dihMul N (dihInv N x) x = (0, 0) := by
  obtain ⟨a, b⟩ := x
  rcases zmod2_cases b with h | h <;> subst h <;>
    simp only [dihMul, dihInv, zmod2_one_add_one, zero_add] <;>
    ext <;> simp

instance dihGroup (N : ℕ) : Group (DihPt N) where
  mul := dihMul N
  one := (0, 0)
  inv := dihInv N
  npow := @npowRec (DihPt N) ⟨(0, 0)⟩ ⟨dihMul N⟩
  zpow := @zpowRec (DihPt N) ⟨(0, 0)⟩ ⟨dihMul N⟩ ⟨dihInv N⟩ (@npowRec (DihPt N) ⟨(0, 0)⟩ ⟨dihMul N⟩)
  mul_assoc := dihMul_assoc N
  one_mul := dihMul_zero_left N
  mul_one := dihMul_zero_right N
  inv_mul_cancel := dihInv_mul_cancel N

/-- Every binary residue adds to itself to give zero. -/
lemma zmod2_add_self (b : ZMod 2) : b + b = 0 := by
  rcases zmod2_cases b with h | h <;> subst h <;> simp

/-- The dihedral rotation subgroup consisting of points with binary coordinate zero. -/
def Rot (N : ℕ) : Subgroup (DihPt N) where
  carrier := {x | x.2 = 0}
  one_mem' := rfl
  mul_mem' := by
    intro x y hx hy
    change x.2 + y.2 = 0
    have hx' : x.2 = 0 := hx
    have hy' : y.2 = 0 := hy
    rw [hx', hy', add_zero]
  inv_mem' := by
    intro x hx
    change x.2 = 0
    exact hx

/-- A dihedral point belongs to `Rot N` exactly when its binary coordinate is zero. -/
@[simp] lemma mem_Rot {N : ℕ} {x : DihPt N} : x ∈ Rot N ↔ x.2 = 0 := Iff.rfl

instance rotNormal (N : ℕ) : (Rot N).Normal where
  conj_mem := by
    intro n hn g
    change (g.2 + n.2) + g.2 = 0
    have hn' : n.2 = 0 := hn
    rw [hn', add_zero, zmod2_add_self]

/-- Multiplying `x` on the right by the inverse of `y` and then by `y` recovers `x`. -/
lemma dihMul_inv_right (N : ℕ) (x y : DihPt N) :
    dihMul N (dihMul N x (dihInv N y)) y = x := by
  obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y
  rcases zmod2_cases b with hb | hb <;> rcases zmod2_cases d with hd | hd <;>
    subst hb <;> subst hd <;>
    simp only [dihMul, dihInv, zmod2_one_add_one, zero_add, add_zero] <;>
    ext <;> simp

/-- A dihedral point multiplied by its inverse is `(0, 0)`. -/
lemma dihMul_inv_right_cancel (N : ℕ) (x : DihPt N) :
    dihMul N x (dihInv N x) = (0, 0) := by
  obtain ⟨a, b⟩ := x
  rcases zmod2_cases b with hb | hb <;> subst hb <;> simp [dihMul, dihInv]

/-- The product of one reflection in `H` with the inverse of another belongs to `H ⊓ Rot N`. -/
theorem mul_inv_mem_inter_rot {N : ℕ} {H : Subgroup (DihPt N)} {h k : DihPt N}
    (hh : h ∈ H) (hk : k ∈ H) (hb : h.2 = 1) (kb : k.2 = 1) :
    dihMul N h (dihInv N k) ∈ H ⊓ Rot N := by
  refine (Subgroup.mem_inf).mpr ⟨?_, ?_⟩
  · exact H.mul_mem hh (H.inv_mem hk)
  · show (dihMul N h (dihInv N k)).2 = 0
    simp [dihMul, dihInv, hb, kb]

/-- If `X1` generates the rotational part of `H`, adjoining any reflection in `H` generates all
of `H`. -/
theorem closure_union_generates {N : ℕ} {H : Subgroup (DihPt N)}
    (X1 : Set (DihPt N)) (hX1 : X1 ⊆ H ⊓ Rot N)
    (hgen : Subgroup.closure X1 = H ⊓ Rot N)
    {h : DihPt N} (hh : h ∈ H) (hb : h.2 = 1) :
    Subgroup.closure (X1 ∪ {h}) = H := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | rfl
    · exact (hX1 hx).1
    · exact hh
  · intro k hk
    by_cases hk0 : k.2 = 0
    · have hk1 : k ∈ H ⊓ Rot N := (Subgroup.mem_inf).mpr ⟨hk, hk0⟩
      rw [← hgen] at hk1
      exact Subgroup.closure_mono (Set.subset_union_left) hk1
    · have hk1 : k.2 = 1 := by
        rcases zmod2_cases k.2 with h | h
        · exact absurd h hk0
        · exact h
      have hmem : dihMul N k (dihInv N h) ∈ H ⊓ Rot N :=
        mul_inv_mem_inter_rot hk hh hk1 hb
      rw [← hgen] at hmem
      have hk_eq : k = dihMul N (dihMul N k (dihInv N h)) h :=
        (dihMul_inv_right N k h).symm
      rw [hk_eq]
      exact Subgroup.mul_mem (Subgroup.closure (X1 ∪ {h}))
        (Subgroup.closure_mono (Set.subset_union_left) hmem)
        (Subgroup.subset_closure (Or.inr rfl))

/-- If `H` equals its rotational part, any set generating that part already generates `H`. -/
theorem closure_generates_of_rot_eq {N : ℕ} {H : Subgroup (DihPt N)}
    (X1 : Set (DihPt N)) (hgen : Subgroup.closure X1 = H ⊓ Rot N)
    (htriv : H = H ⊓ Rot N) :
    Subgroup.closure X1 = H := by
  rw [hgen, htriv, inf_assoc, inf_idem]

/-- The hidden-subgroup promise restricts to the rotation subgroup with hidden subgroup `H ⊓ Rot
N`. This is a reduction step for Theorem 2 of [EttingerHoyer1999]. -/
theorem restrict_promise {N : ℕ} {H : Subgroup (DihPt N)} {R : Type*}
    {γ : DihPt N → R} (hγ : FulfillsPromise H γ) :
    (∀ x y, x ∈ Rot N → y ∈ Rot N →
      (∃ h ∈ H ⊓ Rot N, dihMul N x h = y) → γ x = γ y) ∧
    (∀ x y, x ∈ Rot N → y ∈ Rot N → γ x = γ y →
      ∃ h ∈ H ⊓ Rot N, dihMul N x h = y) := by
  constructor
  · intro x y _ _ ⟨h, hh, hmul⟩
    exact hγ.1 x y ⟨h, hh.1, hmul⟩
  · intro x y hx hy heq
    obtain ⟨h, hh, hmul⟩ := hγ.2 x y heq
    refine ⟨h, (Subgroup.mem_inf).mpr ⟨hh, ?_⟩, hmul⟩
    have hsnd : y.2 = x.2 + h.2 := by
      have := congrArg Prod.snd hmul
      simpa [dihMul] using! this.symm
    have hx0 : x.2 = 0 := hx
    have hy0 : y.2 = 0 := hy
    rw [hx0, zero_add, hy0] at hsnd
    exact hsnd.symm

/-- The reduction of a dihedral point from modulus `N` to a divisor `M`, preserving its binary
coordinate. -/
def redD (N M : ℕ) (_hM : M ∣ N) (x : DihPt N) : DihPt M :=
  ((ZMod.cast x.1 : ZMod M), x.2)

/-- The first coordinate of `redD N M hM x` is the cast of `x.1` to `ZMod M`. -/
@[simp] lemma redD_fst {N M : ℕ} (hM : M ∣ N) (x : DihPt N) :
    (redD N M hM x).1 = (ZMod.cast x.1 : ZMod M) := rfl

/-- The map `redD` preserves the binary coordinate. -/
@[simp] lemma redD_snd {N M : ℕ} (hM : M ∣ N) (x : DihPt N) :
    (redD N M hM x).2 = x.2 := rfl

/-- The reduction map sends `(0, 0)` to `(0, 0)`. -/
lemma redD_zero {N M : ℕ} (hM : M ∣ N) : redD N M hM (0, 0) = (0, 0) := by
  ext <;> simp [redD]

/-- The map `redD` preserves dihedral multiplication. -/
lemma redD_dihMul {N M : ℕ} (hM : M ∣ N) (x y : DihPt N) :
    redD N M hM (dihMul N x y) = dihMul M (redD N M hM x) (redD N M hM y) := by
  obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y
  rcases zmod2_cases b with hb | hb <;> subst hb <;>
    simp [redD, dihMul, ZMod.cast_add hM, ZMod.cast_neg hM]

/-- The map `redD` commutes with dihedral inversion. -/
lemma redD_dihInv {N M : ℕ} (hM : M ∣ N) (x : DihPt N) :
    redD N M hM (dihInv N x) = dihInv M (redD N M hM x) := by
  obtain ⟨a, b⟩ := x
  rcases zmod2_cases b with hb | hb <;> subst hb <;>
    simp [redD, dihInv, ZMod.cast_neg hM]

/-- The reduction map `redD` is surjective. -/
lemma redD_surjective {N M : ℕ} (hM : M ∣ N) :
    Function.Surjective (redD N M hM) := by
  intro y
  obtain ⟨a, ha⟩ := ZMod.castHom_surjective hM y.1
  refine ⟨(a, y.2), ?_⟩
  ext
  · show (ZMod.cast a : ZMod M) = y.1
    rw [← ZMod.castHom_apply]
    exact ha
  · rfl

/-- Two points have the same reduction exactly when their binary coordinates agree and their
rotation-coordinate difference casts to zero modulo `M`. -/
lemma redD_eq_iff {N M : ℕ} (hM : M ∣ N) {x y : DihPt N} :
    redD N M hM x = redD N M hM y ↔
      ZMod.castHom hM (ZMod M) (x.1 - y.1) = 0 ∧ x.2 = y.2 := by
  constructor
  · intro h
    have h1 : ZMod.castHom hM (ZMod M) x.1 = ZMod.castHom hM (ZMod M) y.1 :=
      congrArg (fun z : DihPt M => z.1) h
    have h2 : x.2 = y.2 := congrArg (fun z : DihPt M => z.2) h
    rw [map_sub, h1, sub_self, h2]
    simp
  · rintro ⟨h1, h2⟩
    ext
    · have hsub : ZMod.castHom hM (ZMod M) x.1 - ZMod.castHom hM (ZMod M) y.1 = 0 := by
        rw [← map_sub]; exact h1
      exact sub_eq_zero.mp hsub
    · exact h2

/-- If the kernel of `redD` is contained in `H`, an oracle fulfilling the promise for `H` is
constant on every fiber of `redD`. -/
theorem redD_fiber_const {N M : ℕ} (hM : M ∣ N) {H : Subgroup (DihPt N)}
    (hker : ∀ x, redD N M hM x = (0, 0) → x ∈ H)
    {R : Type*} {γ : DihPt N → R} (hγ : FulfillsPromise H γ)
    {x y : DihPt N} (hxy : redD N M hM x = redD N M hM y) : γ x = γ y := by
  have hz : redD N M hM (dihMul N (dihInv N x) y) = (0, 0) := by
    rw [redD_dihMul, redD_dihInv, hxy]
    exact dihInv_mul_cancel M (redD N M hM y)
  have hmem : dihMul N (dihInv N x) y ∈ H := hker _ hz
  refine hγ.1 x y ⟨dihMul N (dihInv N x) y, hmem, ?_⟩
  show dihMul N x (dihMul N (dihInv N x) y) = y
  rw [← dihMul_assoc, dihMul_inv_right_cancel, dihMul_zero_left]

/-- If the kernel of `redD` is contained in `H`, an oracle fulfilling the promise for `H`
factors through a function on `DihPt M`. -/
theorem exists_quotient_function {N M : ℕ} (hM : M ∣ N) {H : Subgroup (DihPt N)}
    (hker : ∀ x, redD N M hM x = (0, 0) → x ∈ H)
    {R : Type*} {γ : DihPt N → R} (hγ : FulfillsPromise H γ) :
    ∃ γ2 : DihPt M → R, ∀ x : DihPt N, γ2 (redD N M hM x) = γ x := by
  classical
  refine ⟨fun y => γ (Classical.choose (redD_surjective hM y)), ?_⟩
  intro x
  exact (redD_fiber_const hM hker hγ
    (Classical.choose_spec (redD_surjective hM (redD N M hM x))))

/-- The image subgroup of `H` under reduction from modulus `N` to `M`. -/
def imageSub (N M : ℕ) (hM : M ∣ N) (H : Subgroup (DihPt N)) :
    Subgroup (DihPt M) where
  carrier := redD N M hM '' (H : Set (DihPt N))
  one_mem' := ⟨(0, 0), H.one_mem, redD_zero hM⟩
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨dihMul N x y, H.mul_mem hx hy, redD_dihMul hM x y⟩
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨dihInv N x, H.inv_mem hx, redD_dihInv hM x⟩

/-- Membership in `imageSub N M hM H` is equivalent to being the reduction of an element of `H`. -/
@[simp] lemma mem_imageSub {N M : ℕ} (hM : M ∣ N) {H : Subgroup (DihPt N)}
    {y : DihPt M} :
    y ∈ imageSub N M hM H ↔ ∃ x ∈ H, redD N M hM x = y := Iff.rfl

/-- If the kernel of `redD` is contained in `H`, an oracle hiding `H` descends to a function
hiding a subgroup of `DihPt M`. This is the quotient reduction used for Theorem 2 of
[EttingerHoyer1999]. -/
theorem quotient_promise {N M : ℕ} (hM : M ∣ N) {H : Subgroup (DihPt N)}
    (hker : ∀ x, redD N M hM x = (0, 0) → x ∈ H)
    {R : Type*} {γ : DihPt N → R} (hγ : FulfillsPromise H γ) :
    ∃ (γ2 : DihPt M → R) (H2 : Subgroup (DihPt M)),
      (∀ x : DihPt N, γ2 (redD N M hM x) = γ x) ∧ FulfillsPromise H2 γ2 := by
  classical
  obtain ⟨γ2, hγ2⟩ := exists_quotient_function hM hker hγ
  refine ⟨γ2, imageSub N M hM H, hγ2, ?_, ?_⟩
  · intro a b ⟨h, hh, hab⟩
    obtain ⟨z, hz, rfl⟩ := (mem_imageSub hM).mp hh
    obtain ⟨x, rfl⟩ := redD_surjective hM a
    obtain ⟨y, rfl⟩ := redD_surjective hM b
    have hEq : redD N M hM (dihMul N x z) = redD N M hM y := by
      rw [redD_dihMul]
      exact hab
    have hγxz : γ (dihMul N x z) = γ y := redD_fiber_const hM hker hγ hEq
    calc γ2 (redD N M hM x) = γ x := hγ2 x
      _ = γ (dihMul N x z) := hγ.1 x (dihMul N x z) ⟨z, hz, rfl⟩
      _ = γ y := hγxz
      _ = γ2 (redD N M hM y) := (hγ2 y).symm
  · intro a b hab
    obtain ⟨x, rfl⟩ := redD_surjective hM a
    obtain ⟨y, rfl⟩ := redD_surjective hM b
    have hxy : γ x = γ y := by
      rw [← hγ2 x, ← hγ2 y, hab]
    obtain ⟨h, hh, hhxy⟩ := hγ.2 x y hxy
    refine ⟨redD N M hM h, ⟨h, hh, rfl⟩, ?_⟩
    show dihMul M (redD N M hM x) (redD N M hM h) = redD N M hM y
    rw [← redD_dihMul]
    exact congrArg (redD N M hM) hhxy

/-- If every rotation in `H` reduces to the identity, all reflections in `H` have the same
reduced image. -/
theorem image_second_one_unique {N M : ℕ} (hM : M ∣ N) {H : Subgroup (DihPt N)}
    (hH1ker : ∀ x ∈ H, x.2 = 0 → redD N M hM x = (0, 0))
    {x y : DihPt N} (hx : x ∈ H) (hy : y ∈ H) (hx1 : x.2 = 1) (hy1 : y.2 = 1) :
    redD N M hM x = redD N M hM y := by
  have hmem : dihMul N x (dihInv N y) ∈ H ⊓ Rot N :=
    mul_inv_mem_inter_rot hx hy hx1 hy1
  have hz : redD N M hM (dihMul N x (dihInv N y)) = (0, 0) :=
    hH1ker _ hmem.1 hmem.2
  rw [redD_dihMul, redD_dihInv] at hz
  have hcongr := congrArg (fun z : DihPt M => dihMul M z (redD N M hM y)) hz
  simpa [dihMul_inv_right] using! hcongr

/-- If rotational generators are known and all rotations in `H` reduce to the identity, any two
reflections in `H` have the same reduced image, and adjoining one to the rotational
generators generates `H`. See Theorem 2 of [EttingerHoyer1999]. -/
theorem recovery_from_order_two {N M : ℕ} (hM : M ∣ N) {H : Subgroup (DihPt N)}
    (X1 : Set (DihPt N)) (hX1 : X1 ⊆ H ⊓ Rot N)
    (hgen : Subgroup.closure X1 = H ⊓ Rot N)
    (hH1ker : ∀ x ∈ H, x.2 = 0 → redD N M hM x = (0, 0))
    {x y : DihPt N} (hx : x ∈ H) (hy : y ∈ H) (hx1 : x.2 = 1) (hy1 : y.2 = 1) :
    redD N M hM x = redD N M hM y ∧ Subgroup.closure (X1 ∪ {x}) = H :=
  ⟨image_second_one_unique hM hH1ker hx hy hx1 hy1,
   closure_union_generates X1 hX1 hgen hx hx1⟩

/-- For `N ≥ 2`, the product `(1 - 1 / N) * (1 - 1 / (2 * N))` is strictly greater than `1 - 2 /
N`. See [EttingerHoyer1999]. -/
theorem success_prob_gt {N : ℕ} (hN : 2 ≤ N) :
    1 - 2 / (N : ℝ) < (1 - 1 / (N : ℝ)) * (1 - 1 / (2 * (N : ℝ))) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hkey : (1 - 1 / (N : ℝ)) * (1 - 1 / (2 * (N : ℝ))) - (1 - 2 / (N : ℝ))
      = 1 / (2 * (N : ℝ)) + 1 / (2 * (N : ℝ) ^ 2) := by
    field_simp
    ring
  have hpos : 0 < 1 / (2 * (N : ℝ)) + 1 / (2 * (N : ℝ) ^ 2) := by positivity
  linarith

/-- The real-valued repetition factor `log (2 * N) / log (2 * M)`. -/
noncomputable def repCount (N M : ℕ) : ℝ :=
  Real.log (2 * (N : ℝ)) / Real.log (2 * (M : ℝ))

/-- The per-run real query estimate `89 * log M / log 2 + 7`. -/
noncomputable def perRun (M : ℕ) : ℝ :=
  89 * Real.log (M : ℝ) / Real.log 2 + 7

/-- For `N ≥ 2` and `1 ≤ M ≤ N`, the repetition factor times the per-run estimate is at most `95
* log (2 * N) / log 2`. -/
theorem query_accounting {N M : ℕ} (hN : 2 ≤ N) (hM1 : 1 ≤ M) (_hMN : M ≤ N) :
    repCount N M * perRun M ≤ 95 * (Real.log (2 * (N : ℝ)) / Real.log 2) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hLM0 : 0 ≤ Real.log (M : ℝ) := by
    have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
    exact (Real.log_nonneg this)
  have hLM : 0 < Real.log (2 * (M : ℝ)) := by
    apply Real.log_pos
    have hM1' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
    linarith
  have hLN : 0 < Real.log (2 * (N : ℝ)) := by
    apply Real.log_pos
    have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hLM' : Real.log (2 * (M : ℝ)) = Real.log 2 + Real.log (M : ℝ) :=
    Real.log_mul (by norm_num) (ne_of_gt hMpos)
  have hLN' : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log (N : ℝ) :=
    Real.log_mul (by norm_num) (ne_of_gt hNpos)
  unfold repCount perRun
  rw [hLM', hLN']
  have hper : 89 * Real.log (M : ℝ) / Real.log 2 + 7
      = (89 * Real.log (M : ℝ) + 7 * Real.log 2) / Real.log 2 := by
    field_simp
  rw [hper]
  have hden : (0 : ℝ) < Real.log 2 + Real.log (M : ℝ) := by linarith
  rw [div_mul_div_comm]
  rw [div_le_iff₀ (by positivity)]
  field_simp
  nlinarith [h2, hLM0, hLN, hden]

end Qatlib.Papers.NoncommHSP98.MainResults
