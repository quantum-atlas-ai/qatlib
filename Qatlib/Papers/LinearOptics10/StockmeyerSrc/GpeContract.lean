/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.Gaussian
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section


/-! # Actual Gaussian event masses and the old solver advantage contract

The historical lower bound on delta holds for every natural dimension.
Already n1 forces delta1 at least one half, making the required success
mass at least five quarters. This diagnoses inconsistent old premises;
it is not used to manufacture a proof of a counting complexity theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.GpeContract
open Qatlib.Concepts.CountingClasses.ClassTransport

/-- The genuine product complex Gaussian matrix density is pointwise nonnegative. -/
theorem densityNonneg (n : ℕ) (X : Fin n → Fin n → ℂ) : 0 ≤ loGaussianMatDensity n X := by
  apply Finset.prod_nonneg
  intro i _
  apply Finset.prod_nonneg
  intro j _
  exact mul_nonneg (inv_nonneg.mpr Real.pi_pos.le) (Real.exp_pos _).le

/-- The actual matrix Gaussian event mass, for an arbitrary predicate on genuine matrices. -/
def eventMass (n : ℕ) (P : (Fin n → Fin n → ℂ) → Prop) : ℝ :=
  ∫ X : Fin n → Fin n → ℂ,
    (if P X then (1 : ℝ) else 0)*loGaussianMatDensity n X ∂volume

/-- No actual Gaussian event can have mass greater than one, even for an unmeasurable predicate. -/
theorem eventLeOne (n : ℕ) (P : (Fin n → Fin n → ℂ) → Prop) : eventMass n P ≤ 1 := by
  have hi : Integrable (loGaussianMatDensity n) volume :=
    Integrable.of_integral_ne_zero (by rw [Gaussian.matrixMass]; norm_num)
  have hn : ∀ X, 0 ≤ (if P X then (1 : ℝ) else 0)*loGaussianMatDensity n X := by
    intro X
    split_ifs <;> simp [densityNonneg]
  have hu : ∀ X, (if P X then (1 : ℝ) else 0)*loGaussianMatDensity n X ≤ loGaussianMatDensity n X := by
    intro X
    split_ifs <;> simp [densityNonneg]
  have he := integral_mono_of_nonneg (Filter.Eventually.of_forall hn) hi
    (Filter.Eventually.of_forall hu)
  simpa only [eventMass, Gaussian.matrixMass] using he

/-- The literal all-dimension inverse polynomial advantage condition in the original target. -/
def Advantage (δ : ℕ → ℝ) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, 1/((n : ℝ)^c+1) ≤ δ n

/-- The actual old lower bound already forces at least one-half advantage in dimension one. -/
theorem advantageOne (δ : ℕ → ℝ) (hδ : Advantage δ) : (1/2 : ℝ) ≤ δ 1 := by
  obtain ⟨c, hc⟩ := hδ
  have he := hc 1
  norm_num at he
  exact he

/-- The original exact Gaussian permanent solver success predicate, with the genuine event integral. -/
def PermSolver (solve : (n : ℕ) → (Fin n → Fin n → ℂ) → ℂ) (δ : ℕ → ℝ) : Prop :=
  ∀ n, (∫ X : Fin n → Fin n → ℂ,
    (if solve n X = Matrix.permanent (Matrix.of X) then (1 : ℝ) else 0)*
      loGaussianMatDensity n X ∂volume) ≥ 3/4+δ n

/-- No exact solver can satisfy the original advantage and event-success premises together. -/
theorem permImpossible (δ : ℕ → ℝ) (solve : (n : ℕ) → (Fin n → Fin n → ℂ) → ℂ)
    (hδ : Advantage δ) : ¬PermSolver solve δ := by
  intro h
  have hl := advantageOne δ hδ
  have hs := h 1
  have hu := eventLeOne 1 (fun X => solve 1 X = Matrix.permanent (Matrix.of X))
  change (∫ X : Fin 1 → Fin 1 → ℂ,
    (if solve 1 X = Matrix.permanent (Matrix.of X) then (1 : ℝ) else 0)*
      loGaussianMatDensity 1 X ∂volume) ≤ 1 at hu
  linarith

/-- The original additive Gaussian squared-permanent solver predicate with its unchanged tolerance. -/
def SqSolver (solve : (n : ℕ) → (Fin n → Fin n → ℂ) → ℝ)
    (δ : ℕ → ℝ) (p : ℕ → ℝ → ℕ) : Prop :=
  ∀ n, (∫ X : Fin n → Fin n → ℂ,
    (if |solve n X-Complex.normSq (Matrix.permanent (Matrix.of X))| ≤
      ((2 : ℝ)^(p n (1/δ n)))⁻¹ then (1 : ℝ) else 0)*
      loGaussianMatDensity n X ∂volume) ≥ 3/4+δ n

/-- No squared-permanent solver meets the original success premises, for any accuracy function p. -/
theorem sqImpossible (δ : ℕ → ℝ) (p : ℕ → ℝ → ℕ)
    (solve : (n : ℕ) → (Fin n → Fin n → ℂ) → ℝ) (hδ : Advantage δ) : ¬SqSolver solve δ p := by
  intro h
  have hl := advantageOne δ hδ
  have hs := h 1
  have hu := eventLeOne 1 (fun X => |solve 1 X-Complex.normSq (Matrix.permanent (Matrix.of X))| ≤
    ((2 : ℝ)^(p 1 (1/δ 1)))⁻¹)
  change (∫ X : Fin 1 → Fin 1 → ℂ,
    (if |solve 1 X-Complex.normSq (Matrix.permanent (Matrix.of X))| ≤
      ((2 : ℝ)^(p 1 (1/δ 1)))⁻¹ then (1 : ℝ) else 0)*
      loGaussianMatDensity 1 X ∂volume) ≤ 1 at hu
  linarith

/-- The historical extensional reconstruction predicate allows arbitrary query
matrices and coefficients. It bounds the dimension/count but asserts neither
effective computation of queries/weights nor a Gaussian law for those queries. -/
def SharpBySolver (solve : (n : ℕ) → (Fin n → Fin n → ℂ) → ℂ) : Prop :=
  ∀ (f : List Bool → ℕ), InSharpP f →
    ∃ (d : ℕ → ℕ)
      (M : (x : List Bool) → Fin (d x.length) → (Fin (d x.length) → Fin (d x.length) → ℂ))
      (w : (x : List Bool) → Fin (d x.length) → ℂ),
      (∃ c : ℕ, ∀ L : ℕ, d L ≤ L ^ c + 1) ∧
      ∀ x : List Bool,
        (f x : ℝ) = (∑ t : Fin (d x.length), w x t * solve (d x.length) (M x t)).re


/-- The historical squared-solver reconstruction predicate has the same free
queries and weights, without an algorithm or a Gaussian query-law requirement. -/
def SharpBySq (solve : (n : ℕ) → (Fin n → Fin n → ℂ) → ℝ) : Prop :=
  ∀ (f : List Bool → ℕ), InSharpP f →
    ∃ (d : ℕ → ℕ)
      (M : (x : List Bool) → Fin (d x.length) → (Fin (d x.length) → Fin (d x.length) → ℂ))
      (w : (x : List Bool) → Fin (d x.length) → ℂ),
      (∃ c : ℕ, ∀ L : ℕ, d L ≤ L ^ c + 1) ∧
      ∀ x : List Bool,
        (f x : ℝ) = ∑ t : Fin (d x.length), w x t * solve (d x.length) (M x t)


end Qatlib.Papers.LinearOptics10.StockmeyerSrc.GpeContract
