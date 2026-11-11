/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinBool08.MainResults.MaioranaMcFarland.Lemma4
import Qatlib.Papers.NonlinBool08.MainResults.BentCore.BentFacts
import Qatlib.Papers.NonlinBool08.MainResults.MaioranaMcFarland.ClassicalQueries
import Mathlib.Logic.Equiv.Fintype

/-!
# Nonadaptive query bounds for a permutation oracle

Defines a strengthened permutation oracle and deterministic algorithms with fixed finite query
sets. A permutation-extension argument gives the numerical lower bound `sqrt_lower_bound`;
additional query identities show that a nonempty collection of full basis-query blocks
determines the second shift component. See [Roetteler2008].

## Main statements

* `exists_perm_extend`: compatible restrictions extend to a permutation.
* `sqrt_lower_bound`: the stated small-query inequality precludes recovery of every shift.
* `cover_s2_determines`: equal full query blocks force equal second shift components.

## References

* [Roetteler, 2008][Roetteler2008]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.NonlinBool08.MainResults.MaioranaMcFarland

open Qatlib.Papers.NonlinBool08.MainResults.BentCore

/-- The query-point type consisting of a pair of length-`m` binary vectors. -/
abbrev QPt (m : ℕ) : Type := BVec m × BVec m

/-- The strengthened oracle returning `(π p.1, π p.2, π (p.2 + s))` at query point `p`. -/
def strongOracle {m : ℕ} (π : Equiv.Perm (BVec m)) (s : BVec m) :
    QPt m → BVec m × BVec m × BVec m :=
  fun p => (π p.1, π p.2, π (p.2 + s))

/-- If each of the translates of `Dv` by `s` and by `s'` is disjoint from `Dv`, a permutation
fixes `Dv` and maps each `y + s'` to `y + s`. See [Roetteler, Theorem 9][Roetteler2008]. -/
theorem exists_perm_extend {m : ℕ} (Dv : Finset (BVec m)) {s s' : BVec m}
    (hDs' : ∀ y ∈ Dv, y + s' ∉ Dv) (hDs : ∀ y ∈ Dv, y + s ∉ Dv) :
    ∃ τ : Equiv.Perm (BVec m), (∀ y ∈ Dv, τ y = y) ∧ (∀ y ∈ Dv, τ (y + s') = y + s) := by
  classical
  let f : ↥Dv ⊕ ↥Dv → BVec m :=
    Sum.elim (fun d => (d : BVec m)) (fun y => (y : BVec m) + s')
  let g : ↥Dv ⊕ ↥Dv → BVec m :=
    Sum.elim (fun d => (d : BVec m)) (fun y => (y : BVec m) + s)
  have hf : Function.Injective f := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · simp only [f, Sum.elim_inl] at hab
      exact congrArg Sum.inl (Subtype.ext hab)
    · exfalso
      simp only [f, Sum.elim_inl, Sum.elim_inr] at hab
      exact hDs' (b : BVec m) b.2 (by rw [← hab]; exact a.2)
    · exfalso
      simp only [f, Sum.elim_inl, Sum.elim_inr] at hab
      exact hDs' (a : BVec m) a.2 (by rw [hab]; exact b.2)
    · simp only [f, Sum.elim_inr] at hab
      exact congrArg Sum.inr (Subtype.ext (add_right_cancel hab))
  have hg : Function.Injective g := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · simp only [g, Sum.elim_inl] at hab
      exact congrArg Sum.inl (Subtype.ext hab)
    · exfalso
      simp only [g, Sum.elim_inl, Sum.elim_inr] at hab
      exact hDs (b : BVec m) b.2 (by rw [← hab]; exact a.2)
    · exfalso
      simp only [g, Sum.elim_inl, Sum.elim_inr] at hab
      exact hDs (a : BVec m) a.2 (by rw [hab]; exact b.2)
    · simp only [g, Sum.elim_inr] at hab
      exact congrArg Sum.inr (Subtype.ext (add_right_cancel hab))
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨σ, ?_, ?_⟩
  · intro y hy
    exact hσ (Sum.inl ⟨y, hy⟩)
  · intro y hy
    exact hσ (Sum.inr ⟨y, hy⟩)

/-- The finite set of pairwise sums of elements of `Dv`, which are also their binary
differences. -/
def diffSet {m : ℕ} (Dv : Finset (BVec m)) : Finset (BVec m) :=
  (Dv ×ˢ Dv).image (fun p : BVec m × BVec m => p.1 + p.2)

/-- The pairwise difference set has cardinality at most the square of the cardinality of `Dv`. -/
lemma card_diffSet_le {m : ℕ} (Dv : Finset (BVec m)) :
    (diffSet Dv).card ≤ Dv.card ^ 2 := by
  refine le_trans (Finset.card_image_le) ?_
  rw [Finset.card_product, sq]

/-- A vector belongs to the binary difference set exactly when translating some element of `Dv`
by it gives another element of `Dv`. -/
lemma mem_diffSet_iff {m : ℕ} (Dv : Finset (BVec m)) (t : BVec m) :
    t ∈ diffSet Dv ↔ ∃ y ∈ Dv, y + t ∈ Dv := by
  constructor
  · intro ht
    obtain ⟨⟨d₁, d₂⟩, hmem, hsum⟩ := Finset.mem_image.mp ht
    rw [Finset.mem_product] at hmem
    dsimp only at hmem hsum
    refine ⟨d₁, hmem.1, ?_⟩
    have hdt : d₁ + t = d₂ := by
      rw [← hsum, ← add_assoc, BentCore.add_self_bvec, zero_add]
    rw [hdt]
    exact hmem.2
  · rintro ⟨y, hy, hyt⟩
    refine Finset.mem_image.mpr ⟨(y + t, y), ?_, ?_⟩
    · rw [Finset.mem_product]; exact ⟨hyt, hy⟩
    · show (y + t, y).1 + (y + t, y).2 = t
      have hyt' : (y + t) + y = t := by
        rw [add_comm (y + t) y, ← add_assoc, BentCore.add_self_bvec, zero_add]
      exact hyt'

/-- A deterministic algorithm specified by a fixed finite query set and a decoder from its
strengthened-oracle answers to a shift. -/
structure NonAdaptiveAlg (m : ℕ) where

  qset : Finset (QPt m)

  decide : (↥qset → BVec m × BVec m × BVec m) → BVec m

/-- If `4 * (2 * A.qset.card) ^ 2 + 1 < 2 ^ m`, the fixed-query algorithm `A` fails to recover
the shift for some permutation and shift. See [Roetteler, Theorem 9][Roetteler2008]. -/
theorem sqrt_lower_bound {m : ℕ} (A : NonAdaptiveAlg m)
    (hcard : 4 * (2 * A.qset.card) ^ 2 + 1 < 2 ^ m) :
    ¬ ∀ (π : Equiv.Perm (BVec m)) (s : BVec m),
        A.decide (fun p : ↥A.qset => strongOracle π s p) = s := by
  intro hcorr
  classical
  set Dv : Finset (BVec m) := A.qset.image Prod.fst ∪ A.qset.image Prod.snd with hDv
  have hDvcard : Dv.card ≤ 2 * A.qset.card := by
    have h1 : (A.qset.image Prod.fst).card ≤ A.qset.card := Finset.card_image_le
    have h2 : (A.qset.image Prod.snd).card ≤ A.qset.card := Finset.card_image_le
    have h3 : Dv.card ≤ (A.qset.image Prod.fst).card + (A.qset.image Prod.snd).card :=
      Finset.card_union_le _ _
    omega
  have hdiff_lt : (diffSet Dv).card + 1 < 2 ^ m := by
    have h1 : (diffSet Dv).card ≤ Dv.card ^ 2 := card_diffSet_le Dv
    have h2 : Dv.card ^ 2 ≤ (2 * A.qset.card) ^ 2 := Nat.pow_le_pow_left hDvcard 2
    have h3 : (2 * A.qset.card) ^ 2 + 1 < 2 ^ m := by nlinarith [hcard]
    omega

  have hne_univ : diffSet Dv ≠ Finset.univ := by
    intro h
    rw [h, Finset.card_univ, BentCore.card_bvec_nat] at hdiff_lt
    omega
  obtain ⟨s, hs⟩ : ∃ s : BVec m, s ∉ diffSet Dv := by
    by_contra h
    push_neg at h
    exact hne_univ (Finset.eq_univ_of_forall h)

  have hne_univ' : diffSet Dv ∪ {s} ≠ Finset.univ := by
    intro h
    have hle : (diffSet Dv ∪ {s}).card ≤ (diffSet Dv).card + 1 := by
      have := Finset.card_union_le (diffSet Dv) ({s} : Finset (BVec m))
      simpa using this
    rw [h, Finset.card_univ, BentCore.card_bvec_nat] at hle
    omega
  obtain ⟨s', hs'⟩ : ∃ s' : BVec m, s' ∉ diffSet Dv ∪ {s} := by
    by_contra h
    push_neg at h
    exact hne_univ' (Finset.eq_univ_of_forall h)
  have hs'1 : s' ∉ diffSet Dv := fun h => hs' (Finset.mem_union_left _ h)
  have hs'ne : s' ≠ s := by
    intro h
    exact hs' (Finset.mem_union_right _ (h ▸ Finset.mem_singleton_self s))

  have hcond : ∀ t : BVec m, t ∉ diffSet Dv ↔ ∀ y ∈ Dv, y + t ∉ Dv := by
    intro t
    rw [mem_diffSet_iff]
    push_neg
    exact Iff.rfl
  have hDs' : ∀ y ∈ Dv, y + s' ∉ Dv := (hcond s').mp hs'1
  have hDs : ∀ y ∈ Dv, y + s ∉ Dv := (hcond s).mp hs
  obtain ⟨τ, hfix, hshift⟩ := exists_perm_extend Dv hDs' hDs

  have hfun : (fun p : ↥A.qset => strongOracle τ s' (p : QPt m))
      = (fun p : ↥A.qset => strongOracle (1 : Equiv.Perm (BVec m)) s (p : QPt m)) := by
    funext p
    have h1 : (p : QPt m).1 ∈ Dv :=
      Finset.mem_union_left _ (Finset.mem_image_of_mem _ p.2)
    have h2 : (p : QPt m).2 ∈ Dv :=
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ p.2)
    simp only [strongOracle, hfix (p : QPt m).1 h1, hfix (p : QPt m).2 h2,
      hshift (p : QPt m).2 h2, Equiv.Perm.one_apply]
  have hinst : A.decide (fun p : ↥A.qset => strongOracle τ s' (p : QPt m)) = s := by
    rw [hfun]
    exact hcorr 1 s
  have hinst' : A.decide (fun p : ↥A.qset => strongOracle τ s' (p : QPt m)) = s' :=
    hcorr τ s'
  exact hs'ne (hinst'.symm.trans hinst)

/-- At a basis first coordinate and arbitrary second coordinate `y`, the shifted function
returns a bit of `π (y + s.2)` plus its dot product with `s.1`. -/
lemma mmGs_basis_apply {m : ℕ} (π : Equiv.Perm (BVec m)) (s : BVec m × BVec m)
    (y : BVec m) (i : Fin m) :
    mmGs π s (Pi.single i (1 : ZMod 2), y)
      = (π (y + s.2)) i + dot s.1 (π (y + s.2)) := by
  simp only [mmGs, mm, Prod.fst_add, Prod.snd_add, Pi.zero_apply, zero_add, add_zero]
  have hdot : dot (Pi.single i (1 : ZMod 2) + s.1) (π (y + s.2))
      = dot (Pi.single i (1 : ZMod 2)) (π (y + s.2)) + dot s.1 (π (y + s.2)) := by
    show dotProduct (Pi.single i (1 : ZMod 2) + s.1) (π (y + s.2))
        = dotProduct (Pi.single i (1 : ZMod 2)) (π (y + s.2)) + dotProduct s.1 (π (y + s.2))
    exact add_dotProduct _ _ _
  rw [hdot]
  congr 1
  rw [show dot (Pi.single i (1 : ZMod 2)) (π (y + s.2))
      = dot (π (y + s.2)) (Pi.single i (1 : ZMod 2)) from by
    simp only [dot]; rw [dotProduct_comm]]
  rw [dot_single]
  simp

/-- At zero first coordinate and second coordinate `y`, the shifted function equals `dot s.1 (π
(y + s.2))`. -/
lemma mmGs_zero_apply {m : ℕ} (π : Equiv.Perm (BVec m)) (s : BVec m × BVec m) (y : BVec m) :
    mmGs π s (0, y) = dot s.1 (π (y + s.2)) := by
  simp [mmGs, mm]

/-- If two shifts give equal zero and all first-coordinate basis-query answers over a nonempty
set of second coordinates, their second components are equal. See [Roetteler, Theorem
9][Roetteler2008]. -/
theorem cover_s2_determines {m : ℕ} (π : Equiv.Perm (BVec m)) (Y : Finset (BVec m))
    (hY : Y.Nonempty) {s s' : BVec m × BVec m}
    (h1 : ∀ y ∈ Y, ∀ i : Fin m,
      mmGs π s (Pi.single i (1 : ZMod 2), y) = mmGs π s' (Pi.single i (1 : ZMod 2), y))
    (h2 : ∀ y ∈ Y, mmGs π s (0, y) = mmGs π s' (0, y)) :
    s.2 = s'.2 := by
  classical
  obtain ⟨y₀, hy₀⟩ := hY
  have hvec : π (y₀ + s.2) = π (y₀ + s'.2) := by
    funext i
    have hi := h1 y₀ hy₀ i
    have hz := h2 y₀ hy₀
    rw [mmGs_basis_apply, mmGs_basis_apply] at hi
    rw [mmGs_zero_apply, mmGs_zero_apply] at hz
    rw [hz] at hi
    exact add_right_cancel hi
  have hshift : y₀ + s.2 = y₀ + s'.2 := π.injective hvec
  exact add_left_cancel hshift

end Qatlib.Papers.NonlinBool08.MainResults.MaioranaMcFarland
