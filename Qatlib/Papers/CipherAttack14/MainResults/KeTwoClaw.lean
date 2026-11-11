/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Defs

set_option backward.isDefEq.respectTransparency false

/-!
# CipherAttack14 — KE₂ as a claw-finding (element distinctness) instance

Fixed source: M. Kaplan, *Quantum attacks against iterated block ciphers*,
arXiv:1410.1434v2 (2015).  Section 2, printed pages 4–6:

* Definition 3 (p. 4) introduces `KE2^{P,C}`: the input is a public collection
  `F = {F_1, …, F_N}` of permutations of `[M]`, with the promise that a unique
  pair `(k_1, k_2)` satisfies `F_{k_2}(F_{k_1}(P)) = C`; the output is that pair.
* The remark after Definition 3 (p. 4) proves that the complexity of the problem
  does not depend on the pair `(P, C)`: conjugating every permutation of an input
  by the transposition that swaps `P ↔ P'` and `C ↔ C'` maps an algorithm for
  `KE2^{P,C}` to one for `KE2^{P',C'}`.
* The proof of Theorem 2 (p. 5) reduces `KE2^{P,C}` to the claw-finding instance
  `G_1(x) = F_x(P)`, `G_2(y) = F_y^{-1}(C)`: the unique claw is the key pair.
* Definition 2 and the paragraph after it (p. 4) note that claw finding is element
  distinctness on the cut function obtained by concatenating the two lists.

This module records exactly those reductions as theorems about the underlying key
collection: the meet-in-the-middle identity, the equality of the key-pair and claw
solution sets (hence their cardinalities, so the uniqueness promise transfers),
the conjugation invariance of the problem, and the cut of the claw instance into a
single element-distinctness function on `Fin N × Bool`.  It does not build a query
or space ledger, so it does not by itself cover the time and memory statements of
Theorem 2 nor the Ω bound of Theorem 3.
-/

set_option autoImplicit false

namespace Qatlib.Papers.CipherAttack14.MainResults

open Finset

variable {N M : ℕ}

/-- Source Section 2 (p. 4): a block-cipher key family is a public collection
`F = {F_1, …, F_N}` of permutations of the block space `[M]`; the key space is
`[N]`.  An attacker may query both `F_k` and `F_k^{-1}`. -/
abbrev PermFamily (N M : ℕ) := Fin N → Equiv.Perm (Fin M)

/-- The forward list `G_1(k) = F_k(P)` of the claw instance built in the proof of
Theorem 2 (p. 5). -/
def forwardList (F : PermFamily N M) (P : Fin M) : Fin N → Fin M := fun k => F k P

/-- The inverse list `G_2(k) = F_k^{-1}(C)` of the claw instance built in the proof
of Theorem 2 (p. 5). -/
def inverseList (F : PermFamily N M) (C : Fin M) : Fin N → Fin M := fun k => (F k).symm C

/-- Source Definition 3 (p. 4): the set of key pairs consistent with the known
plaintext/ciphertext pair `(P, C)`.  The problem assumes it is a singleton. -/
def keyPairs (F : PermFamily N M) (P C : Fin M) : Finset (Fin N × Fin N) :=
  univ.filter fun kk => F kk.2 (F kk.1 P) = C

/-- The claw set of the two lists `G_1`, `G_2` (source Definition 2, p. 4). -/
def claws (F : PermFamily N M) (P C : Fin M) : Finset (Fin N × Fin N) :=
  univ.filter fun kk => forwardList F P kk.1 = inverseList F C kk.2

/-- The decision version `d-KE2^{P,C}` (source p. 5): does some key pair map `P`
to `C` through the double encryption? -/
def dKE2 (F : PermFamily N M) (P C : Fin M) : Prop :=
  ∃ k1 k2 : Fin N, F k2 (F k1 P) = C

/-- Membership in the key-pair set: the defining equation `F_{k_2}(F_{k_1}(P)) = C` of
source Definition 3 (p. 4). -/
@[simp] theorem mem_keyPairs {F : PermFamily N M} {P C : Fin M} {kk : Fin N × Fin N} :
    kk ∈ keyPairs F P C ↔ F kk.2 (F kk.1 P) = C := by
  simp [keyPairs]

/-- Membership in the claw set: `G_1(k_1) = G_2(k_2)` for the two lists of the proof
of Theorem 2 (p. 5). -/
@[simp] theorem mem_claws {F : PermFamily N M} {P C : Fin M} {kk : Fin N × Fin N} :
    kk ∈ claws F P C ↔ forwardList F P kk.1 = inverseList F C kk.2 := by
  simp [claws]

/-- The meet-in-the-middle identity of the proof of Theorem 2 (p. 5): a key pair
encrypts `P` to `C` through two applications exactly when the forward list and the
inverse list collide at that pair.  Both directions use that `F_b` is a permutation,
which is what makes the inverse permutations available to the attacker. -/
theorem meetsInTheMiddle (F : PermFamily N M) (P C : Fin M) (a b : Fin N) :
    F b (F a P) = C ↔ forwardList F P a = inverseList F C b := by
  unfold forwardList inverseList
  constructor
  · intro h
    simpa using congrArg (fun x => (F b).symm x) h
  · intro h
    simpa using congrArg (fun x => F b x) h

/-- The key pairs of `KE2^{P,C}` are exactly the claws of the two lists of the
proof of Theorem 2 (p. 5). -/
theorem keyPairs_eq_claws (F : PermFamily N M) (P C : Fin M) :
    keyPairs F P C = claws F P C := by
  ext kk
  rw [mem_keyPairs, mem_claws]
  exact meetsInTheMiddle F P C kk.1 kk.2

/-- Consequently the claw search returns the key pair, and the uniqueness promise
of Definition 3 is exactly the uniqueness promise of the claw instance. -/
theorem keyPairs_card_eq_claws_card (F : PermFamily N M) (P C : Fin M) :
    (keyPairs F P C).card = (claws F P C).card := by
  rw [keyPairs_eq_claws]

/-- The promise of Definition 3 transfers to the claw instance: the two solution
sets have the same members, so they have the same unique element. -/
theorem unique_keyPair_iff_unique_claw (F : PermFamily N M) (P C : Fin M)
    (kk : Fin N × Fin N) :
    (∀ kk' ∈ keyPairs F P C, kk' = kk) ↔ ∀ kk' ∈ claws F P C, kk' = kk := by
  rw [keyPairs_eq_claws]

/-- Source p. 5, decision form: `d-KE2^{P,C}` holds exactly when the two lists
`G_1`, `G_2` share a value. -/
theorem dKE2_iff_claw (F : PermFamily N M) (P C : Fin M) :
    dKE2 F P C ↔ ∃ k1 k2 : Fin N, forwardList F P k1 = inverseList F C k2 := by
  constructor
  · rintro ⟨k1, k2, h⟩
    exact ⟨k1, k2, (meetsInTheMiddle F P C k1 k2).1 h⟩
  · rintro ⟨k1, k2, h⟩
    exact ⟨k1, k2, (meetsInTheMiddle F P C k1 k2).2 h⟩

/-- The conjugated key family of the remark after Definition 3 (p. 4): every
permutation of the input is conjugated by `σ` before running an algorithm for
`KE2^{P,C}`. -/
def conjugateFamily (σ : Equiv.Perm (Fin M)) (F : PermFamily N M) : PermFamily N M :=
  fun k => σ.trans ((F k).trans σ.symm)

/-- The pointwise formula for the conjugation of the remark after Definition 3
(p. 4): the conjugated permutation sends `x` to `σ^{-1}(F_k(σ x))`. -/
theorem conjugateFamily_apply (σ : Equiv.Perm (Fin M)) (F : PermFamily N M) (k : Fin N)
    (x : Fin M) : conjugateFamily σ F k x = σ.symm (F k (σ x)) := by
  simp [conjugateFamily]

/-- The remark after Definition 3 (p. 4): if `σ` sends the new plaintext/ciphertext
pair `(P', C')` to `(P, C)`, conjugating every permutation by `σ` is a bijection of
the key-pair sets of `KE2^{P',C'}` and `KE2^{P,C}`.  This is the statement that the
complexity of the problem is independent of the known pair. -/
theorem mem_conjugate_keyPairs (σ : Equiv.Perm (Fin M)) (F : PermFamily N M)
    (P P' C C' : Fin M) (hP : σ P' = P) (hC : σ C' = C) (kk : Fin N × Fin N) :
    kk ∈ keyPairs (conjugateFamily σ F) P' C' ↔ kk ∈ keyPairs F P C := by
  rw [mem_keyPairs, mem_keyPairs]
  simp only [conjugateFamily_apply, Equiv.apply_symm_apply]
  rw [← hP, ← hC, Equiv.symm_apply_eq]

/-- The key-pair sets of `KE2^{P',C'}` and `KE2^{P,C}` are equinumerous under
conjugation, and the conjugation is injective on families, so an attack on one
pair transfers to the other with the same query and memory cost. -/
theorem keyPairs_conjugate (σ : Equiv.Perm (Fin M)) (F : PermFamily N M)
    (P P' C C' : Fin M) (hP : σ P' = P) (hC : σ C' = C) :
    keyPairs (conjugateFamily σ F) P' C' = keyPairs F P C := by
  ext kk
  exact mem_conjugate_keyPairs σ F P P' C C' hP hC kk

/-- The cut function of Definition 2 and the following paragraph (p. 4): the claw
instance on the two lists of size `N` is the element-distinctness instance on the
single function over the disjoint union `Fin N ⊕ Fin N` (`2N` points). -/
def cutFunction (F : PermFamily N M) (P C : Fin M) : Fin N ⊕ Fin N → Fin M
  | Sum.inl k => forwardList F P k
  | Sum.inr k => inverseList F C k

/-- The value of the cut function on the forward list, i.e. `G_1`. -/
theorem cutFunction_inl (F : PermFamily N M) (P C : Fin M) (k : Fin N) :
    cutFunction F P C (Sum.inl k) = forwardList F P k := rfl

/-- The value of the cut function on the inverse list, i.e. `G_2`. -/
theorem cutFunction_inr (F : PermFamily N M) (P C : Fin M) (k : Fin N) :
    cutFunction F P C (Sum.inr k) = inverseList F C k := rfl

/-- The cut instance has `2N` points, the constant-factor inflation by which the
paper transfers element-distinctness bounds to claw finding (p. 4). -/
theorem cut_domain_card (N : ℕ) : Fintype.card (Fin N ⊕ Fin N) = N + N := by
  simp [Fintype.card_sum]

/-- Source p. 4: cutting an element-distinctness input into two lists preserves
collisions.  Here in the direction used for `KE2`: a collision of the cut function
is a claw, provided each list is injective on the key space.  Injectivity of a list
holds whenever the key family is injective, and the latter follows from the
uniqueness promise of Definition 3. -/
theorem cut_collision_iff_claw (F : PermFamily N M) (P C : Fin M)
    (hF : Function.Injective (forwardList F P)) (hG : Function.Injective (inverseList F C)) :
    (∃ x y : Fin N ⊕ Fin N, x ≠ y ∧ cutFunction F P C x = cutFunction F P C y) ↔
      ∃ a b : Fin N, forwardList F P a = inverseList F C b := by
  constructor
  · rintro ⟨x, y, hne, heq⟩
    cases x with
    | inl a =>
      cases y with
      | inl b =>
        exact absurd (hF (by simpa [cutFunction] using heq)) fun h => hne (by simp [h])
      | inr b => exact ⟨a, b, by simpa [cutFunction] using heq⟩
    | inr a =>
      cases y with
      | inl b => exact ⟨b, a, by simpa [cutFunction] using heq.symm⟩
      | inr b =>
        exact absurd (hG (by simpa [cutFunction] using heq)) fun h => hne (by simp [h])
  · rintro ⟨a, b, h⟩
    exact ⟨Sum.inl a, Sum.inr b, by simp, by simpa [cutFunction] using h⟩

/-- Combining the two reductions: `d-KE2^{P,C}` holds exactly when the cut
element-distinctness instance on `Fin N ⊕ Fin N` has a collision.  This is the
route by which the paper transfers the `Θ(N^{2/3})` bounds for element
distinctness and claw finding to `KE2` in Theorem 1 and Theorem 2. -/
theorem dKE2_iff_cut_collision (F : PermFamily N M) (P C : Fin M)
    (hF : Function.Injective (forwardList F P)) (hG : Function.Injective (inverseList F C)) :
    dKE2 F P C ↔ ∃ x y : Fin N ⊕ Fin N, x ≠ y ∧ cutFunction F P C x = cutFunction F P C y := by
  rw [dKE2_iff_claw, cut_collision_iff_claw F P C hF hG]

end Qatlib.Papers.CipherAttack14.MainResults
