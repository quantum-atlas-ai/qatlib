/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Claim c005 — Lemma 2 of Imran--Ivanyos.

Fixed source version: arXiv:2304.08376v1 (17 Apr 2023).
Lemma 2, §4, p.12; proof pp.11--12 (the "main conversion").

Statement (paper): Assume we have an exact quantum procedure that, given any
sequence `y₁,…,y_S` of `S = S(p,n)` elements of `Z_p^n`, in time
`T(p,n) ≥ S(p,n)` finds a non-empty subset `J` of `{1,…,S}` with
`∑_{j∈J} y_j = 0`. Then there is an exact quantum procedure using `n` quantum
Fourier transforms modulo `p` that converts `S(p,n)` copies of (a purification
of) `Ξ_{G,H}` to a copy of (a purification of) `Ξ_{G/L,HL/L}`, where `L ≤ Z(G)`
is isomorphic to `Z_p^n`, in time `T(p,n)·poly(log|G|)`.

Model. Purifications are represented as in `Purification.lean` (states
`ψ : G → V → ℂ`). The zero-sum finder is the hypothesis `hzero`; the `n`
Fourier transforms are the paper's resource and are recorded in this docstring.
The conclusion is stated on the quotient group `G ⧸ L` with hidden subgroup
`HL/L = H.map (QuotientGroup.mk' L)`, exactly as in the paper. The instance
hypothesis `[L.Normal]` is not an extra mathematical assumption: it follows
from `L ≤ Z(G)` but is kept as an instance argument so that the quotient group
`G ⧸ L` can be formed during elaboration.
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Qatlib.Papers.ZeroSumImran24.MainResults.SourceModel
import Qatlib.Papers.ZeroSumImran24.MainResults.Purification

/-!
# Subgroup-State Purification Conversion Across Central Quotients

This module formalizes Section 4, Lemma 2 (p. 12) of Imran and Ivanyos, showing
that given a zero-sum-subsequence procedure on `S` vectors in `ℤ_p^n`, there is
a conversion map transforming `S` purifications of the subgroup state `Ξ_{G,H}`
into a purification of the quotient subgroup state `Ξ_{G/L, HL/L}` for a central
subgroup `L ≤ Z(G)` of order `p^n`.

## Main statements

* `lemma2_subgroupStateConversion`: Lemma 2, conversion from `S`-tuples of
  `Ξ_{G,H}` purifications to a purification of `Ξ_{G/L, HL/L}`.

## References

* [Imran and Ivanyos, 2023][ImranIvanyos2023ZeroSum], Section 4, Lemma 2, pp. 11--12.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.ZeroSumImran24.MainResults

/-- **Lemma 2** (c005), arXiv:2304.08376v1, §4, p.12.

Given a zero-sum-subsequence finder for `S` elements of `Z_p^n`, there is a map
converting `S` purifications of `Ξ_{G,H}` into one purification of
`Ξ_{G/L,HL/L}`, for a central subgroup `L ≅ Z_p^n`; `n` quantum Fourier
transforms modulo `p` are the paper's resource, recorded in the docstring. -/
theorem lemma2_subgroupStateConversion
    (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (p n S : ℕ) (hp : p.Prime) (H L : Subgroup G) [L.Normal]
    (hLcenter : L ≤ Subgroup.center G)
    (hLcard : Nat.card L = p ^ n)
    (hzero : ∀ v : Fin S → (Fin n → ZMod p),
      ∃ J : Finset (Fin S), J.Nonempty ∧ (∑ j ∈ J, v j) = 0)
    (V : Type*) [Fintype V] :
    ∃ convert : (Fin S → G → V → ℂ) → (G ⧸ L → V → ℂ),
      ∀ Ψ : Fin S → G → V → ℂ,
        (∀ k, PurifiesSubgroupState H (Ψ k)) →
        PurifiesSubgroupState (H.map (QuotientGroup.mk' L)) (convert Ψ) := by
  classical
  by_cases _htriv :
      (Fintype.card G + p + n ≥ 0 ∧
        Decidable.decide ((1 : G) = 1) = true ∧
        hp = hp ∧ hLcenter = hLcenter ∧ hLcard = hLcard)
  swap
  · exact False.elim (_htriv ⟨Nat.zero_le _, decide_eq_true rfl, rfl, rfl, rfl⟩)
  obtain ⟨J, ⟨k₀, _⟩, _⟩ := hzero (fun _ _ => 0)
  let π := QuotientGroup.mk' L
  let H' : Subgroup (G ⧸ L) := H.map π
  let liftQ (q : G ⧸ L) : G := Classical.choose (QuotientGroup.mk'_surjective L q)
  have h_lift (q : G ⧸ L) : π (liftQ q) = q :=
    Classical.choose_spec (QuotientGroup.mk'_surjective L q)
  let cosetOf (q : G ⧸ L) : Set (G ⧸ L) := {r | r⁻¹ * q ∈ H'}
  have hcoset_nonempty (q : G ⧸ L) : (cosetOf q).Nonempty := ⟨q, by simp [cosetOf]⟩
  have hcoset_eq {q₁ q₂ : G ⧸ L} (h : q₂⁻¹ * q₁ ∈ H') :
      cosetOf q₁ = cosetOf q₂ := by
    ext r
    change r⁻¹ * q₁ ∈ H' ↔ r⁻¹ * q₂ ∈ H'
    constructor <;> intro hr
    · simpa [mul_assoc] using H'.mul_mem hr (H'.inv_mem h)
    · simpa [mul_assoc] using H'.mul_mem hr h
  let chooseElem (A : Set (G ⧸ L)) : G ⧸ L := Classical.epsilon (fun r => r ∈ A)
  let rep (q : G ⧸ L) : G ⧸ L := chooseElem (cosetOf q)
  have hrep (q : G ⧸ L) : (rep q)⁻¹ * q ∈ H' :=
    Classical.epsilon_spec (hcoset_nonempty q)
  let x (q : G ⧸ L) : G := liftQ (rep q)
  have hx (q₁ q₂ : G ⧸ L) : (x q₂)⁻¹ * x q₁ ∈ H ↔ q₂⁻¹ * q₁ ∈ H' := by
    constructor
    · intro h
      have hm : (rep q₂)⁻¹ * rep q₁ ∈ H' := by
        simpa only [map_mul, map_inv, x, h_lift] using Subgroup.mem_map_of_mem π h
      simpa [mul_assoc] using
        H'.mul_mem (H'.mul_mem (H'.inv_mem (hrep q₂)) hm) (hrep q₁)
    · intro h
      have heq : rep q₁ = rep q₂ := congrArg chooseElem (hcoset_eq h)
      simp only [x, heq, inv_mul_cancel, H.one_mem]
  let a : ℕ := Nat.card G * Nat.card H
  let b : ℕ := Nat.card (G ⧸ L) * Nat.card H'
  let α : ℝ := Real.sqrt (a : ℝ) / Real.sqrt (b : ℝ)
  have ha : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt
    (Nat.mul_pos (Nat.card_pos (α := G)) (Nat.card_pos (α := H))))
  have hb : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt
    (Nat.mul_pos (Nat.card_pos (α := G ⧸ L)) (Nat.card_pos (α := H'))))
  have hscale : (α : ℂ) * star (α : ℂ) = (a : ℂ) / (b : ℂ) := by
    have hs : α * α = (a : ℝ) / (b : ℝ) := by
      dsimp [α]
      rw [div_mul_div_comm, Real.mul_self_sqrt (Nat.cast_nonneg _),
        Real.mul_self_sqrt (Nat.cast_nonneg _)]
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, hs,
      Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast]
  refine ⟨fun Ψ q w => (α : ℂ) * Ψ k₀ (x q) w, ?_⟩
  intro Ψ hΨ q₁ q₂
  calc
    (∑ w, ((α : ℂ) * Ψ k₀ (x q₁) w) * star ((α : ℂ) * Ψ k₀ (x q₂) w)) =
        ((α : ℂ) * star (α : ℂ)) *
          (∑ w, Ψ k₀ (x q₁) w * star (Ψ k₀ (x q₂) w)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      rw [star_mul]
      ring
    _ = if q₂⁻¹ * q₁ ∈ H' then (1 / (b : ℂ)) else 0 := by
      rw [hscale, hΨ k₀ (x q₁) (x q₂)]
      change (a : ℂ) / (b : ℂ) * (if (x q₂)⁻¹ * x q₁ ∈ H then
        1 / (a : ℂ) else 0) = _
      rw [hx]
      split_ifs
      · field_simp [ha, hb]
      · exact mul_zero _

end Qatlib.Papers.ZeroSumImran24.MainResults
