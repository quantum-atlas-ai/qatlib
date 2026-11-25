/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ApproxDegree20.MainResults.Definitions.PaperMeasures
public import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

@[expose] public section

/-!
# Sensitivity graph: row sums and operator-norm bounds

Source: arXiv:2010.12629v1, Definition 7 and Appendix A.3–A.4 (pages 6 and 31–33).

`Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds.sensAdjacency f` is the adjacency
matrix of the sensitivity graph of a Boolean function `f : (I → Bool) → Bool`: two inputs
are joined when they differ in exactly one coordinate and the value of `f` changes.
`spectralSensitivity f` is its `L2` operator norm `λ(f)`.

This module collects the structure shared by the spectral sensitivity bounds of the paper:

* `flipBit_injective`, `filter_ne_flipBit`, `eq_flipBit_of_card_filter_eq_one`: the
  Hamming-distance-one relation is exactly the single-coordinate flip;
* `sensAdjacency_symm`: the adjacency matrix is symmetric;
* `rowSum_sensAdjacency`, `colSum_sensAdjacency`: the absolute row and column sums are the
  vertex sensitivities `s_x(f)`;
* `mulVec_coord_norm_le`: the action of the matrix on a vector is bounded coordinatewise by
  the absolute row sums;
* `sq_sum_mul_le_sum_mul_sum_sq`: the weighted Cauchy–Schwarz inequality;
* `norm_le_of_rowSum_colSum_le`: the Schur test `‖A‖ ≤ C` from absolute row and column sums
  bounded by `C`;
* `mulVec_normSq_le`: the per-row squared estimate used by the individual bounds.

Everything is stated for an arbitrary finite coordinate type `I`; the paper's `{0,1}^n` is
recovered with `I = Fin n`. The optimal measures `SA(f)` and `Q(f)` play no role here.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds (sensAdjacency spectralSensitivity)
open Qatlib.Papers.ApproxDegree20.MainResults.Definitions
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.ApproxDegree20.MainResults.Spectral

variable {I : Type} [Fintype I] [DecidableEq I]

/-! ## The Hamming-distance-one relation -/

omit [Fintype I] in
/-- Flipping a coordinate is injective in the coordinate, because distinct flips disagree at the
flipped coordinate. -/
theorem flipBit_injective (x : I → Bool) : Function.Injective (flipBit x) := by
  intro i j hij
  by_contra hne
  have hi : flipBit x i i = !(x i) := by simp [flipBit]
  have hj : flipBit x j i = x i := by simp [flipBit, hne]
  have h := congrFun hij i
  rw [hi, hj] at h
  cases hx : x i <;> simp [hx] at h

/-- The only coordinate at which `x` and the flip of `x` at `i` differ is `i` itself. -/
theorem filter_ne_flipBit (x : I → Bool) (i : I) :
    (Finset.univ.filter (fun j => x j ≠ flipBit x i j)) = {i} := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, flipBit,
    Function.update_apply]
  by_cases hji : j = i
  · subst hji
    cases x j <;> simp
  · rw [ite_eq_right hji]
    constructor
    · intro h
      exact absurd rfl h
    · intro h
      exact absurd h hji

/-- A Hamming-distance-one neighbour of `x` is the flip of `x` at the unique differing
coordinate. -/
theorem eq_flipBit_of_card_filter_eq_one {x y : I → Bool}
    (h : (Finset.univ.filter (fun i => x i ≠ y i)).card = 1) : ∃ i, y = flipBit x i := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
  refine ⟨i, ?_⟩
  funext j
  have hmem : (j ∈ Finset.univ.filter (fun k => x k ≠ y k)) ↔ j = i := by
    rw [hi]
    simp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  by_cases hji : j = i
  · subst hji
    have hne : x j ≠ y j := hmem.mpr rfl
    have hflip : flipBit x j j = !(x j) := by simp [flipBit]
    rw [hflip]
    cases hx : x j <;> cases hy : y j <;> simp_all
  · have heq : x j = y j := by
      by_contra hne
      exact hji (hmem.mp hne)
    simp only [flipBit, Function.update_apply]
    rw [ite_eq_right hji, ← heq]

/-! ## Symmetry and row sums -/

omit [DecidableEq I] in
/-- The sensitivity graph is undirected: the adjacency matrix is symmetric. -/
theorem sensAdjacency_symm (f : (I → Bool) → Bool) (x y : I → Bool) :
    sensAdjacency f y x = sensAdjacency f x y := by
  have hcard : (Finset.univ.filter (fun i => y i ≠ x i)).card
      = (Finset.univ.filter (fun i => x i ≠ y i)).card := by
    congr 1
    exact Finset.filter_congr fun i _ => ne_comm
  simp only [sensAdjacency, hcard]
  by_cases h1 : (Finset.univ.filter (fun i => x i ≠ y i)).card = 1
  · by_cases h : f x = f y
    · simp [h1, h]
    · simp [h1, h, Ne.symm h]
  · simp [h1]

/-- The neighbours of `x` carrying a nonzero adjacency entry are exactly the flips of `x` at the
coordinates where `f` is sensitive. -/
theorem mem_image_flipBit_iff (f : (I → Bool) → Bool) (x y : I → Bool) :
    y ∈ (sensitiveAt f x).image (flipBit x) ↔
      (Finset.univ.filter (fun i => x i ≠ y i)).card = 1 ∧ f x ≠ f y := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [filter_ne_flipBit]
      simp
    · have h := hi
      simp only [sensitiveAt, Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact Ne.symm h
  · rintro ⟨h1, h2⟩
    obtain ⟨i, rfl⟩ := eq_flipBit_of_card_filter_eq_one h1
    exact ⟨i, by
      simp only [sensitiveAt, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Ne.symm h2, rfl⟩

/-- The absolute row sum of the sensitivity graph at `x` is the vertex sensitivity `s_x(f)`. -/
theorem rowSum_sensAdjacency (f : (I → Bool) → Bool) (x : I → Bool) :
    (∑ y, ‖sensAdjacency f x y‖) = (sensitivityAt f x : ℝ) := by
  have hterm : ∀ y : I → Bool, ‖sensAdjacency f x y‖
      = if y ∈ (sensitiveAt f x).image (flipBit x) then (1 : ℝ) else 0 := by
    intro y
    simp only [sensAdjacency]
    by_cases h : (Finset.univ.filter (fun i => x i ≠ y i)).card = 1 ∧ f x ≠ f y
    · rw [ite_eq_left h, norm_one, ite_eq_left ((mem_image_flipBit_iff f x y).mpr h)]
    · rw [ite_eq_right h, norm_zero, ite_eq_right (fun hc => h ((mem_image_flipBit_iff f x y).mp hc))]
  calc (∑ y, ‖sensAdjacency f x y‖)
      = ∑ y, if y ∈ (sensitiveAt f x).image (flipBit x) then (1 : ℝ) else 0 :=
        Finset.sum_congr rfl fun y _ => hterm y
    _ = (((sensitiveAt f x).image (flipBit x)).card : ℝ) := by
        rw [Finset.sum_ite_mem]
        simp
    _ = (sensitivityAt f x : ℝ) := by
        rw [Finset.card_image_of_injective _ (flipBit_injective x)]
        simp only [sensitivityAt]

/-- The absolute column sum of the sensitivity graph at `y` is the vertex sensitivity
`s_y(f)`. -/
theorem colSum_sensAdjacency (f : (I → Bool) → Bool) (y : I → Bool) :
    (∑ x, ‖sensAdjacency f x y‖) = (sensitivityAt f y : ℝ) := by
  rw [← rowSum_sensAdjacency f y]
  exact Finset.sum_congr rfl fun x _ => by rw [sensAdjacency_symm]

/-- The vertex sensitivity is bounded by the maximum sensitivity. -/
theorem sensitivityAt_le_sensitivity (f : (I → Bool) → Bool) (x : I → Bool) :
    sensitivityAt f x ≤ sensitivity f := by
  unfold sensitivity
  exact Finset.le_sup (f := fun y => sensitivityAt f y) (Finset.mem_univ x)

/-- The vertex sensitivity at a `0`-input is bounded by the one-sided sensitivity `s₀(f)`. -/
theorem sensitivityAt_le_s0 (f : (I → Bool) → Bool) {x : I → Bool} (hx : f x = false) :
    sensitivityAt f x ≤ s0 f := by
  unfold s0
  exact Finset.le_sup (f := fun y => sensitivityAt f y) (by simp [hx])

/-- The vertex sensitivity at a `1`-input is bounded by the one-sided sensitivity `s₁(f)`. -/
theorem sensitivityAt_le_s1 (f : (I → Bool) → Bool) {x : I → Bool} (hx : f x = true) :
    sensitivityAt f x ≤ s1 f := by
  unfold s1
  exact Finset.le_sup (f := fun y => sensitivityAt f y) (by simp [hx])

/-- The absolute row sum at `x` is bounded by the maximum sensitivity `s(f)`. -/
theorem rowSum_le_sensitivity (f : (I → Bool) → Bool) (x : I → Bool) :
    (∑ y, ‖sensAdjacency f x y‖) ≤ (sensitivity f : ℝ) := by
  rw [rowSum_sensAdjacency]
  exact_mod_cast sensitivityAt_le_sensitivity f x

/-- The absolute row sum at a `0`-input is bounded by the one-sided sensitivity `s₀(f)`. -/
theorem rowSum_le_s0 (f : (I → Bool) → Bool) {x : I → Bool} (hx : f x = false) :
    (∑ y, ‖sensAdjacency f x y‖) ≤ (s0 f : ℝ) := by
  rw [rowSum_sensAdjacency]
  exact_mod_cast sensitivityAt_le_s0 f hx

/-- The absolute row sum at a `1`-input is bounded by the one-sided sensitivity `s₁(f)`. -/
theorem rowSum_le_s1 (f : (I → Bool) → Bool) {x : I → Bool} (hx : f x = true) :
    (∑ y, ‖sensAdjacency f x y‖) ≤ (s1 f : ℝ) := by
  rw [rowSum_sensAdjacency]
  exact_mod_cast sensitivityAt_le_s1 f hx

/-- The spectral sensitivity is nonnegative. -/
theorem spectralSensitivity_nonneg (f : (I → Bool) → Bool) : 0 ≤ spectralSensitivity f := by
  simp only [spectralSensitivity]
  exact norm_nonneg _

/-! ## Action on vectors -/

/-- The coordinate of `A v` at `x` is bounded by the absolute row sum against `v`. -/
theorem mulVec_coord_norm_le (A : Matrix (I → Bool) (I → Bool) ℂ) (v : QState (I → Bool))
    (x : I → Bool) :
    ‖(A *ᵥ v) x‖ ≤ ∑ y, ‖A x y‖ * ‖v y‖ := by
  calc ‖(A *ᵥ v) x‖ = ‖∑ y, A x y * v y‖ := by
        simp only [Matrix.mulVec, dotProduct]
    _ ≤ ∑ y, ‖A x y * v y‖ := norm_sum_le _ _
    _ = ∑ y, ‖A x y‖ * ‖v y‖ :=
        Finset.sum_congr rfl fun y _ => norm_mul _ _

/-- Weighted Cauchy–Schwarz: `(∑ aᵢ bᵢ)² ≤ (∑ aᵢ)(∑ aᵢ bᵢ²)` for nonnegative weights `a`. -/
theorem sq_sum_mul_le_sum_mul_sum_sq {α : Type*} (s : Finset α) (a b : α → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i * b i) ^ 2 ≤ (∑ i ∈ s, a i) * (∑ i ∈ s, a i * (b i) ^ 2) := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s ha (fun i hi => ?_) (fun i hi => ?_)
  · exact mul_nonneg (ha i hi) (sq_nonneg _)
  · rw [show (a i * b i) ^ 2 = a i * (a i * (b i) ^ 2) from by ring]

/-- Per-row estimate: the squared coordinate of `A v` is bounded by the absolute row sum times
the weighted row sum of `v`. -/
theorem mulVec_normSq_le (A : Matrix (I → Bool) (I → Bool) ℂ) (v : QState (I → Bool))
    (x : I → Bool) :
    ‖(A *ᵥ v) x‖ ^ 2
      ≤ (∑ y, ‖A x y‖) * (∑ y, ‖A x y‖ * ‖v y‖ ^ 2) := by
  have hnn : 0 ≤ ∑ y, ‖A x y‖ * ‖v y‖ :=
    Finset.sum_nonneg fun y _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq : ‖(A *ᵥ v) x‖ ^ 2 ≤ (∑ y, ‖A x y‖ * ‖v y‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hnn).mpr (mulVec_coord_norm_le A v x)
  refine hsq.trans ?_
  have h := sq_sum_mul_le_sum_mul_sum_sq (Finset.univ : Finset (I → Bool))
    (fun y => ‖A x y‖) (fun y => ‖v y‖) (fun _ _ => norm_nonneg _)
  simpa using h

set_option maxHeartbeats 800000 in
/-- The Schur test: absolute row and column sums bounded by `C` bound the operator norm by
`C`. -/
theorem norm_le_of_rowSum_colSum_le (A : Matrix (I → Bool) (I → Bool) ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ x, (∑ y, ‖A x y‖) ≤ C) (hcol : ∀ y, (∑ x, ‖A x y‖) ≤ C) : ‖A‖ ≤ C := by
  refine l2_opNorm_le_of_mulVec_le hC A fun v => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp ?_
  calc ‖toEuclidean_fromVec (A *ᵥ v)‖ ^ 2
      = ∑ x, ‖(A *ᵥ v) x‖ ^ 2 := norm_toEuclidean_fromVec_sq _
    _ ≤ ∑ x, (∑ y, ‖A x y‖) * (∑ y, ‖A x y‖ * ‖v y‖ ^ 2) :=
        Finset.sum_le_sum fun x _ => mulVec_normSq_le A v x
    _ ≤ ∑ x, C * (∑ y, ‖A x y‖ * ‖v y‖ ^ 2) :=
        Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_right (hrow x) (Finset.sum_nonneg fun y _ => by positivity)
    _ = C * ∑ x, ∑ y, ‖A x y‖ * ‖v y‖ ^ 2 := by rw [Finset.mul_sum]
    _ = C * ∑ y, (∑ x, ‖A x y‖) * ‖v y‖ ^ 2 := by
        rw [Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun y _ => (Finset.sum_mul ..).symm
    _ ≤ C * ∑ y, C * ‖v y‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) hC
        exact mul_le_mul_of_nonneg_right (hcol y) (by positivity)
    _ = C ^ 2 * ∑ y, ‖v y‖ ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, sq]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ = (C * ‖toEuclidean_fromVec v‖) ^ 2 := by
        rw [mul_pow, norm_toEuclidean_fromVec_sq]

end Qatlib.Papers.ApproxDegree20.MainResults.Spectral
