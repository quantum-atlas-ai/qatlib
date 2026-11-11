/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Difference sets and the influence of their characteristic functions

Source: Martin Roetteler, *Quantum algorithms for abelian difference sets and
applications to dihedral hidden subgroups*, fixed arXiv:1608.02005v1 (5 Aug 2016),
Definition 4 (p. 5) and Lemma 1 (p. 11).

The paper works with a finite abelian group `A` written additively, a subset `D ⊆ A`
of size `k`, and calls `D` a `(v,k,λ)`-difference set when in the group algebra
`ℂ[A]` the multiset of differences `ΔD = {x - y : x, y ∈ D}` covers every nonzero
element exactly `λ` times and the identity exactly `k` times (Definition 4, eq. (1)).
Equivalently, for every nonzero `g` the number of `d ∈ D` with `d - g ∈ D` is `λ`;
this is the formulation used by `IsDifferenceSet` below (the identity is then
automatically covered `k` times, which is why it is not a parameter).

Lemma 1 (p. 11) states that the *influence*
`γ_v(f) = Pr_x[f(x) ≠ f(x + v)]`
of the characteristic function `f` of a difference set satisfies
`γ_v(f) = 2(k - λ) / |A|` for every `v ≠ 0`.  The paper's proof (eqs. (6)–(8))
rewrites the probability as a double count,
`γ_v(f) = (|D| + |v + D| - 2|D ∩ (v + D)|) / |A|`,
and uses the difference-set condition `|D ∩ (v + D)| = λ`.

This file gives the double-counting identity in exact natural-number form
(`card_filter_charFun_ne_add`) and Lemma 1 as a statement about real-valued
influences (`lemma1_influence_eq`).
-/

namespace Qatlib.Papers.DihedralSub16.MainResults

open Finset

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- arXiv:1608.02005v1, Definition 4 (p. 5), in the equivalent "counting"
form: every nonzero `g ∈ A` occurs exactly `lam` times as a difference `d - g`
with `d ∈ D`.  (The occurrence of `0` is then `|D|` automatically.) -/
def IsDifferenceSet (D : Finset A) (lam : ℕ) : Prop :=
  ∀ g : A, g ≠ 0 → (D.filter (fun d => d - g ∈ D)).card = lam

/-- The `{0,1}`-valued characteristic function of a finite set `D`. -/
def charFun (D : Finset A) : A → Bool := fun x => decide (x ∈ D)

/-- The influence `γ_v(f) = Pr_x[f(x) ≠ f(x + v)]` of a Boolean function on a finite
abelian group, as a real number (arXiv:1608.02005v1, §3.2, p. 11). -/
noncomputable def influence (f : A → Bool) (v : A) : ℝ :=
  ((Finset.univ.filter (fun x => f x ≠ f (x + v))).card : ℝ) / (Fintype.card A : ℝ)

omit [Fintype A] in
/-- Membership in the translate `D - v` is membership of `x + v` in `D`. -/
theorem mem_image_sub_iff (D : Finset A) (v x : A) :
    x ∈ D.image (fun d => d - v) ↔ x + v ∈ D := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨d, hd, rfl⟩
    rw [sub_add_cancel]
    exact hd
  · intro h
    exact ⟨x + v, h, add_sub_cancel_right x v⟩

/-- The set of inputs at which the characteristic function of `D` changes under the
shift `x ↦ x + v` is the symmetric difference of `D` and its translate `D - v`. -/
theorem filter_charFun_ne_eq (D : Finset A) (v : A) :
    (Finset.univ.filter (fun x => charFun D x ≠ charFun D (x + v)))
      = (D ∪ D.image (fun d => d - v)) \ (D ∩ D.image (fun d => d - v)) := by
  ext x
  simp only [mem_filter, mem_univ, true_and, mem_sdiff, mem_union, mem_inter,
    mem_image_sub_iff D v x, charFun]
  constructor
  · intro h
    by_cases hx : x ∈ D <;> by_cases hxv : x + v ∈ D <;> simp_all
  · rintro ⟨h1, h2⟩
    by_cases hx : x ∈ D <;> by_cases hxv : x + v ∈ D <;> simp_all

/-- Double counting behind Lemma 1: the number of inputs `x` at which the
characteristic function of `D` changes under `x ↦ x + v`, plus twice the number of
`d ∈ D` with `d + v ∈ D`, equals `2|D|`.  (Equivalently, the symmetric difference of
`D` and `D - v` has size `2(k - λ)` when `D` is a difference set.) -/
theorem card_filter_charFun_ne_add (D : Finset A) (v : A) :
    (Finset.univ.filter (fun x => charFun D x ≠ charFun D (x + v))).card
        + 2 * (D.filter (fun d => d + v ∈ D)).card = 2 * D.card := by
  rw [filter_charFun_ne_eq]
  set E : Finset A := D.image (fun d => d - v) with hE
  have hEcard : E.card = D.card := by
    refine Finset.card_image_of_injective D ?_
    intro a b hab
    have h := congrArg (fun z => z + v) hab
    simpa using h
  have hIeq : (D ∩ E).card = (D.filter (fun d => d + v ∈ D)).card := by
    congr 1
    ext x
    simp only [mem_inter, mem_filter, hE, mem_image_sub_iff D v x]
  have hSub : D ∩ E ⊆ D ∪ E :=
    Finset.inter_subset_left.trans Finset.subset_union_left
  have hsd : ((D ∪ E) \ (D ∩ E)).card + (D ∩ E).card = (D ∪ E).card :=
    Finset.card_sdiff_add_card_eq_card hSub
  have hun : (D ∪ E).card + (D ∩ E).card = D.card + E.card :=
    Finset.card_union_add_card_inter D E
  omega

/-- arXiv:1608.02005v1, Lemma 1 (p. 11): for the characteristic function `f` of a
`(v,k,λ)`-difference set `D` in a finite abelian group `A` and every nonzero
`v ∈ A`, the influence is `γ_v(f) = 2(k - λ)/|A|`. -/
theorem lemma1_influence_eq (D : Finset A) (lam : ℕ) (hD : IsDifferenceSet D lam)
    (v : A) (hv : v ≠ 0) :
    influence (charFun D) v = 2 * ((D.card : ℝ) - (lam : ℝ)) / (Fintype.card A : ℝ) := by
  have hI : (D.filter (fun d => d + v ∈ D)).card = lam := by
    have h := hD (-v) (neg_ne_zero.mpr hv)
    simpa [sub_eq_add_neg] using h
  have hcount := card_filter_charFun_ne_add D v
  rw [hI] at hcount
  have hcast : ((Finset.univ.filter (fun x => charFun D x ≠ charFun D (x + v))).card : ℝ)
      = 2 * ((D.card : ℝ) - (lam : ℝ)) := by
    have hc : ((Finset.univ.filter (fun x => charFun D x ≠ charFun D (x + v))).card : ℝ)
        + 2 * (lam : ℝ) = 2 * (D.card : ℝ) := by
      exact_mod_cast hcount
    linarith
  rw [influence, hcast]

end Qatlib.Papers.DihedralSub16.MainResults
