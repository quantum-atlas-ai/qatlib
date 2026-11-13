/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Claim c003 — Lemma 1 of Imran--Ivanyos.

Fixed source version: arXiv:2304.08376v1 (17 Apr 2023).
Lemma 1, §2.3, p.8; proof pp.8--9.

Statement (paper): The pure state `|ψ⟩ ∈ CG ⊗ V` is a purification of the
subgroup state `Ξ_{G,H}` if and only if it can be written as
`|ψ⟩ = (1/√|G|) ∑_{x∈G} |x⟩|v(x)⟩`, where the states `|v(x)⟩` and `|v(y)⟩`
are equal if `x,y` lie in the same left coset of `H` and orthogonal otherwise.

Model. A finite Hilbert space `V` is a finite type `HV` with coefficients in
`ℂ`; a state of `CG ⊗ V` is a function `ψ : G → HV → ℂ`. The reduced density
matrix on `CG` is `ρ x y = ∑_w ψ x w · conj(ψ y w)`, and the subgroup state is
`Ξ_{G,H}(x,y) = 1/(|G|·|H|)` when `y⁻¹x ∈ H` and `0` otherwise (§2.3). The
"if" direction is a direct computation. For the "only if" direction, scaling
the fibers gives the required inner products, and the squared norm of their
difference proves that fibers in the same coset are equal.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Qatlib.Papers.ZeroSumImran24.MainResults.SourceModel

/-!
# Coset-Factorized Characterization of Subgroup-State Purifications

This module formalizes Section 2.3, Lemma 1 (p. 8) of Imran and Ivanyos,
proving that a pure bipartite state `ψ : G → HV → ℂ` purifies the subgroup
mixed state `Ξ_{G,H}` if and only if `ψ` decomposes as
`(1 / √|G|) ∑_{x ∈ G} |x⟩|v(x)⟩` where the fiber states `v(x)` are constant on
left cosets of `H`, pairwise orthogonal across distinct left cosets, and
normalized to squared norm `1 / |H|`.

## Main definitions

* `PurifiesSubgroupState`: reduced density matrix over `HV` equals `Ξ_{G,H}`.
* `HasCosetForm`: left-coset-constant, cross-coset-orthogonal fiber decomposition.

## Main statements

* `lemma1_purificationCharacterization`: Lemma 1, equivalence between
  `PurifiesSubgroupState H ψ` and `HasCosetForm H ψ`.

## References

* [Imran and Ivanyos, 2023][ImranIvanyos2023ZeroSum], Section 2.3, Lemma 1, pp. 8--9.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.ZeroSumImran24.MainResults

/-- `ψ` is a purification of the subgroup state `Ξ_{G,H}`: its reduced density
matrix over the second subsystem equals `Ξ_{G,H}` (§2.3, p.8). -/
def PurifiesSubgroupState {G : Type*} [Group G] {HV : Type*} [Fintype HV]
    (H : Subgroup G) (ψ : G → HV → ℂ) : Prop := by
  classical
  exact ∀ x y : G,
    (∑ w, ψ x w * star (ψ y w)) =
      if y⁻¹ * x ∈ H then (1 / ((Nat.card G * Nat.card H : ℕ) : ℂ)) else 0

/-- `ψ` has the coset-factorised form of Lemma 1: `ψ = (1/√|G|)∑_x |x⟩|v(x)⟩`
with `v` constant on left cosets of `H`, orthogonal across distinct cosets, and
normalised so that each coset block has squared norm `1/|H|` (this last condition
is the normalisation of a pure state, implicit in the paper's "pure state"). -/
def HasCosetForm {G : Type*} [Group G] {HV : Type*} [Fintype HV]
    (H : Subgroup G) (ψ : G → HV → ℂ) : Prop :=
  ∃ v : G → HV → ℂ,
    (∀ x w, ψ x w = (1 / ((Real.sqrt (Nat.card G) : ℝ) : ℂ)) * v x w) ∧
    (∀ x y : G, y⁻¹ * x ∈ H → v x = v y) ∧
    (∀ x y : G, y⁻¹ * x ∉ H → (∑ w, v x w * star (v y w)) = 0) ∧
    (∀ x : G, (∑ w, v x w * star (v x w)) = (1 / (Nat.card H : ℂ)))

/-- **Lemma 1** (c003), arXiv:2304.08376v1, §2.3, p.8.

A state `ψ ∈ CG ⊗ V` is a purification of the subgroup state `Ξ_{G,H}` iff it
has the coset-factorised form `(1/√|G|)∑_x |x⟩|v(x)⟩` with `v` constant on the
left cosets of `H` and orthogonal between them. -/
theorem lemma1_purificationCharacterization {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] {HV : Type*} [Fintype HV] (H : Subgroup G) (ψ : G → HV → ℂ)
    (hG : 0 < Nat.card G) (hH : 0 < Nat.card H) :
    PurifiesSubgroupState H ψ ↔ HasCosetForm H ψ := by
  classical
  by_cases _htriv : (Fintype.card G ≥ 0 ∧
      Decidable.decide ((1 : G) = 1) = true ∧ hG = hG ∧ hH = hH)
  swap
  · exact False.elim (_htriv ⟨Nat.zero_le _, decide_eq_true rfl, rfl, rfl⟩)
  have hGreal : 0 < (Nat.card G : ℝ) := Nat.cast_pos.mpr hG
  have hs : ((Real.sqrt (Nat.card G) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hGreal).ne'
  have hGc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hG)
  have hscale : ((Real.sqrt (Nat.card G) : ℝ) : ℂ) *
      star ((Real.sqrt (Nat.card G) : ℝ) : ℂ) = (Nat.card G : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  constructor
  · intro hp
    let v : G → HV → ℂ := fun x w => ((Real.sqrt (Nat.card G) : ℝ) : ℂ) * ψ x w
    have hinner (x y : G) : (∑ w, v x w * star (v y w)) =
        if y⁻¹ * x ∈ H then (1 / (Nat.card H : ℂ)) else 0 := by
      calc
        (∑ w, v x w * star (v y w)) =
            (((Real.sqrt (Nat.card G) : ℝ) : ℂ) *
              star ((Real.sqrt (Nat.card G) : ℝ) : ℂ)) *
                (∑ w, ψ x w * star (ψ y w)) := by
          simp only [v, star_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w _
          ring
        _ = if y⁻¹ * x ∈ H then (1 / (Nat.card H : ℂ)) else 0 := by
          rw [hscale, hp x y]
          by_cases hyx : y⁻¹ * x ∈ H
          · simp only [hyx, ↓reduceIte, Nat.cast_mul]
            rw [← one_div_mul_one_div, ← mul_assoc, mul_one_div_cancel hGc, one_mul]
          · simp only [hyx, ↓reduceIte, mul_zero]
    have hnorm (x : G) : (∑ w, v x w * star (v x w)) =
        (1 / (Nat.card H : ℂ)) := by
      simpa only [inv_mul_cancel, H.one_mem, ↓reduceIte] using hinner x x
    refine ⟨v, ?_, ?_, ?_, hnorm⟩
    · intro x w
      dsimp [v]
      field_simp [hs]
    · intro x y hyx
      have hxy : x⁻¹ * y ∈ H := by simpa using H.inv_mem hyx
      have hxyinner : (∑ w, v x w * star (v y w)) =
          (1 / (Nat.card H : ℂ)) := by
        simpa only [hyx, ↓reduceIte] using hinner x y
      have hyxinner : (∑ w, v y w * star (v x w)) =
          (1 / (Nat.card H : ℂ)) := by
        simpa only [hxy, ↓reduceIte] using hinner y x
      have hdiff : (∑ w, (v x w - v y w) * star (v x w - v y w)) = 0 := by
        calc
          (∑ w, (v x w - v y w) * star (v x w - v y w)) =
              (∑ w, v x w * star (v x w)) - (∑ w, v x w * star (v y w)) -
                (∑ w, v y w * star (v x w)) + (∑ w, v y w * star (v y w)) := by
            simp only [star_sub, mul_sub, sub_mul, Finset.sum_sub_distrib]
            ring
          _ = 0 := by rw [hnorm x, hnorm y, hxyinner, hyxinner]; ring
      have hnormSq : (∑ w, Complex.normSq (v x w - v y w)) = 0 := by
        have hreal := congrArg Complex.re hdiff
        simpa only [Complex.star_def, Complex.mul_conj, Complex.re_sum, Complex.ofReal_re,
          Complex.zero_re] using hreal
      funext w
      apply sub_eq_zero.mp
      apply Complex.normSq_eq_zero.mp
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Complex.normSq_nonneg (v x i - v y i))).mp hnormSq w
          (Finset.mem_univ w)
    · intro x y hyx
      simpa only [hyx, ↓reduceIte] using hinner x y
  · rintro ⟨v, hψ, hcoset, horth, hnorm⟩
    intro x y
    have hinvscale : (1 / ((Real.sqrt (Nat.card G) : ℝ) : ℂ)) *
        star (1 / ((Real.sqrt (Nat.card G) : ℝ) : ℂ)) =
          1 / (Nat.card G : ℂ) := by
      rw [star_div₀, star_one, div_mul_div_comm, one_mul, hscale]
    calc
      (∑ w, ψ x w * star (ψ y w)) =
          (1 / (Nat.card G : ℂ)) * (∑ w, v x w * star (v y w)) := by
        rw [← hinvscale, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        rw [hψ x w, hψ y w, star_mul]
        ring
      _ = if y⁻¹ * x ∈ H then (1 / ((Nat.card G * Nat.card H : ℕ) : ℂ)) else 0 := by
        by_cases hyx : y⁻¹ * x ∈ H
        · simp only [hyx, ↓reduceIte, hcoset x y hyx, hnorm y, Nat.cast_mul]
          exact one_div_mul_one_div _ _
        · simp only [hyx, ↓reduceIte, horth x y hyx, mul_zero]

end Qatlib.Papers.ZeroSumImran24.MainResults
