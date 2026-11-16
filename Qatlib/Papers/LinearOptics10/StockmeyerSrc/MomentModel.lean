/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.ProbabilityCore.Concentration.ComplexMoments
public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.Gaussian
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # Actual scalar Gaussian moments and the historical graph-count model

The original graph definition counts only tuples of vertex permutations,
forgetting parallel-edge labels, and then uses a uniform multiplicity-matrix
law. Already n=1 gives legacyMk=1 for every k, whereas the actual Gaussian
moment is k factorial. A concrete weighted candidate is tested for n=1;
no general matrix Wick/graph enumeration theorem is asserted.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.MomentModel
open Qatlib.Concepts.CountingClasses.ClassTransport
open Qatlib.Foundations.ProbabilityCore.Concentration

/-- The actual normalized determinant squared in the immutable source. -/
def detMomentVar {n : ℕ} (X : Fin n → Fin n → ℂ) : ℝ :=
  Complex.normSq (Matrix.det (Matrix.of X)) / (n.factorial : ℝ)

/-- The exact actual determinant power integral, with its original real exponent. -/
def detMoment (n : ℕ) (alpha : ℝ) : ℝ :=
  ∫ X : Fin n → Fin n → ℂ, detMomentVar X ^ alpha * loGaussianMatDensity n X ∂volume

/-- The original real row and column degree predicate on a multiplicity matrix. -/
abbrev IsRegular {n : ℕ} (k : ℕ) (G : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  (∀ i, ∑ j, G i j = k) ∧ (∀ j, ∑ i, G i j = k)

/-- The original tuple count forgets individual parallel-edge labels. -/
def tupleCount {n : ℕ} (k : ℕ) (G : Matrix (Fin n) (Fin n) ℕ) : ℕ :=
  (Finset.univ.filter (fun f : Fin k → Equiv.Perm (Fin n) =>
    ∀ i j, (Finset.univ.filter (fun t : Fin k => f t i = j)).card = G i j)).card

/-- The actual finite set of regular bounded multiplicity matrices used by the old definition. -/
def graphSet (n k : ℕ) : Finset (Matrix (Fin n) (Fin n) (Fin (k+1))) :=
  Finset.univ.filter (fun G => IsRegular k (fun i j => (G i j : ℕ)))

/-- The exact historical uniform graph average, explicitly marked as a diagnostic model. -/
def legacyMk (n k : ℕ) : ℝ :=
  (∑ G ∈ graphSet n k, (tupleCount k (fun i j => (G i j : ℕ)) : ℝ)) /
    ((graphSet n k).card : ℝ)

/-- A concrete graph-weighted candidate retaining tuple multiplicity and edge factorials. -/
def weightedMk (n k : ℕ) : ℝ :=
  (∑ G ∈ graphSet n k, (tupleCount k (fun i j => (G i j : ℕ)) : ℝ)^2 *
    ∏ i, ∏ j, ((G i j : ℕ).factorial : ℝ)) / (n.factorial : ℝ)^k

/-- The sole regular one-vertex graph has k parallel edges. -/
def singleGraph (k : ℕ) : Matrix (Fin 1) (Fin 1) (Fin (k+1)) :=
  fun _ _ => ⟨k, Nat.lt_succ_self k⟩

/-- All one-vertex permutation tuples are the same, independently of the edge count. -/
theorem tupleOne (k : ℕ) : tupleCount k (fun _ _ : Fin 1 => k) = 1 := by
  classical
  unfold tupleCount
  trans (Finset.univ : Finset (Fin k → Equiv.Perm (Fin 1))).card
  · apply congrArg Finset.card
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    intro i j
    have he : (Finset.univ.filter (fun t : Fin k => f t i = j)) = Finset.univ := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact Subsingleton.elim _ _
    rw [he]
    exact Fintype.card_fin k
  · simp

/-- The regular one-vertex graph set is a singleton for every natural edge count. -/
theorem graphOne (k : ℕ) : graphSet 1 k = {singleGraph k} := by
  ext G
  simp only [graphSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hG
    funext i j
    apply Fin.ext
    change (G i j : ℕ) = k
    have hj : j = 0 := Subsingleton.elim _ _
    simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, hj] using hG.1 i
  · rintro rfl
    constructor <;> intro i <;> simp [singleGraph]

/-- The actual old graph average is one in every one-vertex degree. -/
theorem legacyOne (k : ℕ) : legacyMk 1 k = 1 := by
  simp [legacyMk, graphOne, singleGraph, tupleOne]

/-- Retaining edge factorials gives k factorial in the one-vertex weighted candidate. -/
theorem weightedOne (k : ℕ) : weightedMk 1 k = (k.factorial : ℝ) := by
  simp [weightedMk, graphOne, singleGraph, tupleOne]

/-- Actual one-by-one matrix volume integrates exactly as complex plane volume. -/
theorem oneIntegral (f : ℂ → ℝ) :
    (∫ X : Fin 1 → Fin 1 → ℂ, f (X 0 0) ∂volume) = ∫ z : ℂ, f z ∂volume := by
  calc
    _ = ∫ y : Fin 1 → ℂ, f (y 0) ∂volume := by
      convert (volume_preserving_funUnique (Fin 1) (Fin 1 → ℂ)).integral_comp'
        (fun y : Fin 1 → ℂ => f (y 0))
        using 1
      apply integral_congr_ae
      filter_upwards [] with X
      congr 2
    _ = _ := by
      convert (volume_preserving_funUnique (Fin 1) ℂ).integral_comp' f using 1
      apply integral_congr_ae
      filter_upwards [] with X
      congr 2

/-- Every actual scalar-matrix permanent moment is k factorial, with no moment premise. -/
theorem oneModeMoment (k : ℕ) :
    (∫ X : Fin 1 → Fin 1 → ℂ,
      EmptyBoundary.permMomentVar X ^ k * loGaussianMatDensity 1 X ∂volume) =
        (k.factorial : ℝ) := by
  have hm (X : Fin 1 → Fin 1 → ℂ) : EmptyBoundary.permMomentVar X = Complex.normSq (X 0 0) := by
    unfold EmptyBoundary.permMomentVar
    rw [Matrix.permanent_eq_elem_of_subsingleton _ 0]
    simp
  have hd (X : Fin 1 → Fin 1 → ℂ) :
      loGaussianMatDensity 1 X = Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift.density (X 0 0) := by
    simp [loGaussianMatDensity, loGaussianDensity,
      Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift.density]
  simp_rw [hm, hd]
  calc
    _ = ∫ z : ℂ, Complex.normSq z ^ k * Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift.density z ∂volume :=
      oneIntegral (fun z => Complex.normSq z ^ k * Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift.density z)
    _ = _ := ComplexMoments.radialMoment k

/-- The actual determinant real-power formula holds in dimension one for every alpha>-1. -/
theorem oneDetPower (alpha : ℝ) (ha : -1 < alpha) :
    detMoment 1 alpha = Real.Gamma (alpha+1) := by
  have hm (X : Fin 1 → Fin 1 → ℂ) : detMomentVar X = Complex.normSq (X 0 0) := by
    simp [detMomentVar]
  have hd (X : Fin 1 → Fin 1 → ℂ) :
      loGaussianMatDensity 1 X = Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift.density (X 0 0) := by
    simp [loGaussianMatDensity, loGaussianDensity,
      Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift.density]
  unfold detMoment
  simp_rw [hm, hd]
  calc
    _ = ∫ z : ℂ, Complex.normSq z ^ alpha * Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift.density z ∂volume :=
      oneIntegral (fun z => Complex.normSq z ^ alpha * Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift.density z)
    _ = _ := ComplexMoments.radialPower alpha ha

/-- The dimension-one real-exponent family satisfies the exact Gamma product source formula. -/
theorem oneDetSource (alpha : ℝ) (ha : -1 < alpha) :
    detMoment 1 alpha = ((Nat.factorial 1 : ℝ)^(-alpha)) *
      ∏ j ∈ Finset.Icc (1 : ℕ) 1, Real.Gamma ((j : ℝ)+alpha) / Real.Gamma (j : ℝ) := by
  rw [oneDetPower alpha ha]
  simp [add_comm]

/-- The actual one-mode fourth permanent moment agrees with the fixed-source n+1 value. -/
theorem oneFourth :
    (∫ X : Fin 1 → Fin 1 → ℂ,
      EmptyBoundary.permMomentVar X ^ 2 * loGaussianMatDensity 1 X ∂volume) = (1 : ℝ)+1 := by
  rw [oneModeMoment]
  norm_num

/-- Every actual empty-matrix permanent moment is one under the genuine volume law. -/
theorem zeroMoment (k : ℕ) :
    (∫ X : Fin 0 → Fin 0 → ℂ,
      EmptyBoundary.permMomentVar X ^ k * loGaussianMatDensity 0 X ∂volume) = 1 := by
  have hm (X : Fin 0 → Fin 0 → ℂ) : EmptyBoundary.permMomentVar X = 1 := by
    simp [EmptyBoundary.permMomentVar, Matrix.permanent_isEmpty]
  simp_rw [hm, one_pow, one_mul]
  exact Gaussian.matrixMass 0

/-- The complete original universal higher-moment formula with its exact old graph model. -/
def LegacyMoments : Prop := ∀ n k : ℕ, 1 ≤ k →
  (∫ X : Fin n → Fin n → ℂ,
    EmptyBoundary.permMomentVar X ^ k * loGaussianMatDensity n X ∂volume) = legacyMk n k

/-- The full original graph-moment target fails at positive n=1,k=2: two is not one. -/
theorem legacyRefuted : ¬LegacyMoments := by
  intro h
  have hk := h 1 2 (by decide)
  rw [oneModeMoment, legacyOne] at hk
  norm_num at hk

/-- The weighted candidate has the correct actual moments throughout the one-mode family. -/
theorem correctedOne (k : ℕ) :
    (∫ X : Fin 1 → Fin 1 → ℂ,
      EmptyBoundary.permMomentVar X ^ k * loGaussianMatDensity 1 X ∂volume) = weightedMk 1 k := by
  rw [oneModeMoment, weightedOne]

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.MomentModel
