/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Tactic

/-!
# Perturbation bounds for mixer exponential words

This module applies contractive evolution estimates to `mixerExp` and telescopes perturbations
through products of matrix contractions. The resulting `mixer_word_error_bound` controls a
change of Hermitian mixer by the sum of absolute mixer angles, providing the word estimate used
in [ZhouAnLiu2026].

## Main statements

* `norm_mixerExp_sub_le`: For Hermitian generators, the distance between mixer exponentials is
  at most the absolute angle times the distance between the generators.
* `wordProd_pair_sub_le`: For paired lists of contractions with specified nonnegative factor
  error bounds, the product distance is at most the sum of those bounds.
* `mixer_word_error_bound`: For Hermitian mixer and cost generators, the paired word distance is
  bounded by the sum of absolute mixer angles times `‖R - R'‖`.

## References

* [Zhou et al., 2026][ZhouAnLiu2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped Matrix.Norms.L2Operator ComplexOrder
open Matrix

open Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel

namespace Qatlib.Papers.ProjectorQAOA26.StageStability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The matrix evolution `evolution (Complex.I • R) β` associated with a mixer generator and a
real angle. -/
def mixerExp (R : Matrix ι ι ℂ) (β : ℝ) : Matrix ι ι ℂ :=
  evolution (Complex.I • R) β

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in

/-- Multiplying a Hermitian matrix by the imaginary unit gives a matrix whose conjugate
transpose is its negative. -/
theorem conjTranspose_I_smul (R : Matrix ι ι ℂ) (hR : Rᴴ = R) :
    (Complex.I • R)ᴴ = -(Complex.I • R) := by
  rw [Matrix.conjTranspose_smul, hR]
  have hstar : star Complex.I = -Complex.I := by
    simp [Complex.conj_I]
  rw [hstar, neg_smul]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in

/-- For a matrix whose conjugate transpose is its negative, its sum with its conjugate transpose
is positive semidefinite. -/
theorem posSemidef_of_conjTranspose_eq_neg {A : Matrix ι ι ℂ} (hA : Aᴴ = -A) :
    (A + Aᴴ).PosSemidef := by
  have hzero : A + Aᴴ = 0 := by rw [hA, add_neg_cancel]
  rw [hzero]
  exact Matrix.PosSemidef.zero

omit [Nonempty ι] in

/-- The mixer exponential can be written using the negated generator and negated time. -/
theorem mixerExp_eq_neg_gen (R : Matrix ι ι ℂ) (β : ℝ) :
    mixerExp R β = evolution (-(Complex.I • R)) (-β) := by
  unfold mixerExp evolution
  congr 1
  rw [neg_neg, smul_neg, neg_smul]

omit [Nonempty ι] in

/-- For Hermitian generators, the distance between mixer exponentials is at most the absolute
angle times the distance between the generators. -/
theorem norm_mixerExp_sub_le (R R' : Matrix ι ι ℂ) (hR : Rᴴ = R) (hR' : R'ᴴ = R')
    (β : ℝ) :
    ‖mixerExp R β - mixerExp R' β‖ ≤ |β| * ‖R - R'‖ := by
  have hgen : ‖(Complex.I • R) - (Complex.I • R')‖ = ‖R - R'‖ := by
    rw [← smul_sub, norm_smul]
    simp
  by_cases hβ : 0 ≤ β
  · rw [abs_of_nonneg hβ]
    have h := norm_evolution_sub_le (Complex.I • R) (Complex.I • R')
      (posSemidef_of_conjTranspose_eq_neg (conjTranspose_I_smul R hR))
      (posSemidef_of_conjTranspose_eq_neg (conjTranspose_I_smul R' hR')) hβ
    simpa only [mixerExp, hgen] using! h
  · have hβneg : β < 0 := lt_of_not_ge hβ
    rw [abs_of_neg hβneg]
    have hβ' : 0 ≤ -β := by linarith
    have hneg : ‖(-(Complex.I • R)) - (-(Complex.I • R'))‖ = ‖R - R'‖ := by
      have hsub : (-(Complex.I • R)) - (-(Complex.I • R'))
          = -((Complex.I • R) - (Complex.I • R')) := by abel
      rw [hsub, norm_neg, hgen]
    have hskew : (-(Complex.I • R))ᴴ = -(-(Complex.I • R)) := by
      rw [Matrix.conjTranspose_neg, conjTranspose_I_smul R hR, neg_neg]
    have hskew' : (-(Complex.I • R'))ᴴ = -(-(Complex.I • R')) := by
      rw [Matrix.conjTranspose_neg, conjTranspose_I_smul R' hR', neg_neg]
    have h := norm_evolution_sub_le (-(Complex.I • R)) (-(Complex.I • R'))
      (posSemidef_of_conjTranspose_eq_neg hskew)
      (posSemidef_of_conjTranspose_eq_neg hskew') hβ'
    calc ‖mixerExp R β - mixerExp R' β‖
        = ‖evolution (-(Complex.I • R)) (-β) - evolution (-(Complex.I • R')) (-β)‖ := by
          rw [mixerExp_eq_neg_gen, mixerExp_eq_neg_gen]
      _ ≤ (-β) * ‖R - R'‖ := by simpa only [hneg] using! h

omit [Nonempty ι] in

/-- The mixer exponential of a Hermitian generator has operator norm at most one. -/
theorem norm_mixerExp_le_one (R : Matrix ι ι ℂ) (hR : Rᴴ = R) (β : ℝ) :
    ‖mixerExp R β‖ ≤ 1 := by
  by_cases hβ : 0 ≤ β
  · have h := norm_evolution_le_one (Complex.I • R)
      (posSemidef_of_conjTranspose_eq_neg (conjTranspose_I_smul R hR)) hβ
    simpa only [mixerExp] using! h
  · rw [mixerExp_eq_neg_gen]
    have hβ' : 0 ≤ -β := by linarith
    have hskew : (-(Complex.I • R))ᴴ = -(-(Complex.I • R)) := by
      rw [Matrix.conjTranspose_neg, conjTranspose_I_smul R hR, neg_neg]
    exact norm_evolution_le_one (-(Complex.I • R))
      (posSemidef_of_conjTranspose_eq_neg hskew) hβ'

/-- The ordered product of a list of matrices, with the empty product equal to the identity. -/
def wordProd : List (Matrix ι ι ℂ) → Matrix ι ι ℂ
  | [] => 1
  | A :: rest => A * wordProd rest

/-- A product of matrix factors with operator norms at most one also has operator norm at most
one. -/
theorem wordProd_norm_le_one : ∀ (l : List (Matrix ι ι ℂ)),
    (∀ A ∈ l, ‖A‖ ≤ 1) → ‖wordProd l‖ ≤ 1
  | [], _ => by
    simp only [wordProd]
    exact le_of_eq (CStarRing.norm_one (E := Matrix ι ι ℂ))
  | A :: t, h => by
    rw [wordProd]
    calc ‖A * wordProd t‖ ≤ ‖A‖ * ‖wordProd t‖ := norm_mul_le A _
      _ ≤ 1 * 1 :=
        mul_le_mul (h A (by simp))
          (wordProd_norm_le_one t (fun B hB => h B (by simp [hB])))
          (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- For paired lists of contractions with specified nonnegative factor error bounds, the product
distance is at most the sum of those bounds. -/
theorem wordProd_pair_sub_le (l : List (Matrix ι ι ℂ × Matrix ι ι ℂ × ℝ))
    (hA : ∀ p ∈ l, ‖p.1‖ ≤ 1) (hB : ∀ p ∈ l, ‖p.2.1‖ ≤ 1)
    (hAB : ∀ p ∈ l, ‖p.1 - p.2.1‖ ≤ p.2.2)
    (hc : ∀ p ∈ l, 0 ≤ p.2.2) :
    ‖wordProd (l.map (fun p => p.1)) - wordProd (l.map (fun p => p.2.1))‖
      ≤ (l.map (fun p => p.2.2)).sum := by
  induction l with
  | nil => simp [wordProd]
  | cons p t ih =>
    obtain ⟨A, B, c⟩ := p
    have hA' : ‖A‖ ≤ 1 := hA (A, B, c) (by simp)
    have hB' : ‖B‖ ≤ 1 := hB (A, B, c) (by simp)
    have hAB' : ‖A - B‖ ≤ c := hAB (A, B, c) (by simp)
    have hc' : 0 ≤ c := hc (A, B, c) (by simp)
    have ihA : ∀ p ∈ t, ‖p.1‖ ≤ 1 := fun q hq => hA q (by simp [hq])
    have ihB : ∀ p ∈ t, ‖p.2.1‖ ≤ 1 := fun q hq => hB q (by simp [hq])
    have ihAB : ∀ p ∈ t, ‖p.1 - p.2.1‖ ≤ p.2.2 := fun q hq => hAB q (by simp [hq])
    have ihc : ∀ p ∈ t, 0 ≤ p.2.2 := fun q hq => hc q (by simp [hq])
    have ih := ih ihA ihB ihAB ihc
    have hY : ‖wordProd (t.map (fun p => p.2.1))‖ ≤ 1 := by
      refine wordProd_norm_le_one _ ?_
      intro M hM
      rw [List.mem_map] at hM
      obtain ⟨q, hq, rfl⟩ := hM
      exact ihB q hq
    simp only [List.map_cons, List.sum_cons, wordProd]
    have hsplit : A * wordProd (t.map (fun p => p.1))
          - B * wordProd (t.map (fun p => p.2.1))
        = A * (wordProd (t.map (fun p => p.1))
              - wordProd (t.map (fun p => p.2.1)))
          + (A - B) * wordProd (t.map (fun p => p.2.1)) := by
      noncomm_ring
    rw [hsplit]
    calc ‖A * (wordProd (t.map (fun p => p.1))
            - wordProd (t.map (fun p => p.2.1)))
          + (A - B) * wordProd (t.map (fun p => p.2.1))‖
        ≤ ‖A * (wordProd (t.map (fun p => p.1))
              - wordProd (t.map (fun p => p.2.1)))‖
          + ‖(A - B) * wordProd (t.map (fun p => p.2.1))‖ := norm_add_le _ _
      _ ≤ ‖A‖ * ‖wordProd (t.map (fun p => p.1))
              - wordProd (t.map (fun p => p.2.1))‖
          + ‖A - B‖ * ‖wordProd (t.map (fun p => p.2.1))‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 1 * (t.map (fun p => p.2.2)).sum + c * 1 :=
        add_le_add
          (mul_le_mul hA' ih (norm_nonneg _) zero_le_one)
          (mul_le_mul hAB' hY (norm_nonneg _) hc')
      _ = c + (t.map (fun p => p.2.2)).sum := by ring

/-- The real mixer and cost angles specifying one alternating layer. -/
structure MixerLayer where
  β : ℝ
  γ : ℝ

/-- The paired layer matrices for two mixer generators, each accompanied by the bound `|β| * ‖R
- R'‖`. -/
def mixerLayerFactors (l : List MixerLayer) (R R' C : Matrix ι ι ℂ) :
    List (Matrix ι ι ℂ × Matrix ι ι ℂ × ℝ) :=
  l.map (fun d =>
    (mixerExp R d.β * mixerExp C d.γ,
     mixerExp R' d.β * mixerExp C d.γ,
     |d.β| * ‖R - R'‖))

/-- Summing absolute mixer angles multiplied by a common scalar equals the angle sum multiplied
by that scalar. -/
theorem sum_abs_beta_mul (l : List MixerLayer) (δ : ℝ) :
    (l.map (fun d => |d.β| * δ)).sum = (l.map (fun d => |d.β|)).sum * δ := by
  induction l with
  | nil => simp
  | cons d t ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

/-- For Hermitian mixer and cost generators, the paired word distance is bounded by the sum of
absolute mixer angles times `‖R - R'‖`. -/
theorem mixer_word_error_bound (l : List MixerLayer) (R R' C : Matrix ι ι ℂ)
    (hR : Rᴴ = R) (hR' : R'ᴴ = R') (hC : Cᴴ = C) :
    ‖wordProd ((mixerLayerFactors l R R' C).map (fun p => p.1))
      - wordProd ((mixerLayerFactors l R R' C).map (fun p => p.2.1))‖
      ≤ (l.map (fun d => |d.β|)).sum * ‖R - R'‖ := by
  have hA : ∀ p ∈ mixerLayerFactors l R R' C, ‖p.1‖ ≤ 1 := by
    intro p hp
    simp only [mixerLayerFactors, List.mem_map] at hp
    obtain ⟨d, _, rfl⟩ := hp
    calc ‖mixerExp R d.β * mixerExp C d.γ‖
        ≤ ‖mixerExp R d.β‖ * ‖mixerExp C d.γ‖ := norm_mul_le _ _
      _ ≤ 1 * 1 :=
        mul_le_mul (norm_mixerExp_le_one R hR d.β) (norm_mixerExp_le_one C hC d.γ)
          (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hB : ∀ p ∈ mixerLayerFactors l R R' C, ‖p.2.1‖ ≤ 1 := by
    intro p hp
    simp only [mixerLayerFactors, List.mem_map] at hp
    obtain ⟨d, _, rfl⟩ := hp
    calc ‖mixerExp R' d.β * mixerExp C d.γ‖
        ≤ ‖mixerExp R' d.β‖ * ‖mixerExp C d.γ‖ := norm_mul_le _ _
      _ ≤ 1 * 1 :=
        mul_le_mul (norm_mixerExp_le_one R' hR' d.β) (norm_mixerExp_le_one C hC d.γ)
          (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hAB : ∀ p ∈ mixerLayerFactors l R R' C, ‖p.1 - p.2.1‖ ≤ p.2.2 := by
    intro p hp
    simp only [mixerLayerFactors, List.mem_map] at hp
    obtain ⟨d, _, rfl⟩ := hp
    show ‖mixerExp R d.β * mixerExp C d.γ - mixerExp R' d.β * mixerExp C d.γ‖
      ≤ |d.β| * ‖R - R'‖
    rw [← sub_mul]
    calc ‖(mixerExp R d.β - mixerExp R' d.β) * mixerExp C d.γ‖
        ≤ ‖mixerExp R d.β - mixerExp R' d.β‖ * ‖mixerExp C d.γ‖ := norm_mul_le _ _
      _ ≤ (|d.β| * ‖R - R'‖) * 1 :=
        mul_le_mul (norm_mixerExp_sub_le R R' hR hR' d.β) (norm_mixerExp_le_one C hC d.γ)
          (norm_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))
      _ = |d.β| * ‖R - R'‖ := mul_one _
  have hc : ∀ p ∈ mixerLayerFactors l R R' C, 0 ≤ p.2.2 := by
    intro p hp
    simp only [mixerLayerFactors, List.mem_map] at hp
    obtain ⟨d, _, rfl⟩ := hp
    exact mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have htel := wordProd_pair_sub_le (mixerLayerFactors l R R' C) hA hB hAB hc
  calc ‖wordProd ((mixerLayerFactors l R R' C).map (fun p => p.1))
        - wordProd ((mixerLayerFactors l R R' C).map (fun p => p.2.1))‖
      ≤ ((mixerLayerFactors l R R' C).map (fun p => p.2.2)).sum := htel
    _ = (l.map (fun d => |d.β| * ‖R - R'‖)).sum := by
        simp only [mixerLayerFactors, List.map_map, Function.comp_def]
    _ = (l.map (fun d => |d.β|)).sum * ‖R - R'‖ := sum_abs_beta_mul l ‖R - R'‖

end Qatlib.Papers.ProjectorQAOA26.StageStability
