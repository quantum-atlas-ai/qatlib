/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.SamplingModel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section


/-! # Actual scalar accuracy squaring for permanent values

Fixed source: Aaronson--Arkhipov, arXiv:1011.3245v1. Historical
contracts are preserved for explicit review; their names do not certify
efficient algorithms or source-level complexity theorems.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix Classical
open MeasureTheory
open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib.Concepts.CountingClasses.ClassTransport
open Qatlib.Papers.LinearOptics10.StockmeyerSrc
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.SquareReduce
open SamplingModel

/-- The exact old accuracy-squaring comparison on the same genuine matrix instance, without algorithmic encoding or runtime claims. -/
def SquaredFactor (P Q : EstimatorProblem) : Prop :=
  ∀ (g : ℕ → ℝ), (∃ c : ℕ, ∀ L : ℕ, 1 ≤ g L ∧ g L ≤ (L : ℝ) ^ c + 1) →
    ∃ c : ℕ, ∀ (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) (y : ℝ),
      n ≤ n ^ c + 1 ∧
        (|y - Q.Val n X| ≤ (g n - 1) * |Q.Val n X| →
          |y ^ 2 - P.Val n X| ≤ (g n ^ 2 - 1) * |P.Val n X|)

/-- A real multiplicative estimate of the genuine permanent norm squares to the stated squared-magnitude error bound. -/
theorem squareReduction (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ)
    (g y : ℝ) (_hg : 1 ≤ g)
    (hy : |y - gpeAbs.Val n X| ≤ (g - 1) * |gpeAbs.Val n X|) :
    |y ^ 2 - gpeSq.Val n X| ≤ (g ^ 2 - 1) * |gpeSq.Val n X| := by
  set v : ℝ := ‖Matrix.permanent X‖ with hvdef
  have hvnn : 0 ≤ v := by
    rw [hvdef]; positivity
  have hval : gpeAbs.Val n X = v := by
    simp [gpeAbs, hvdef]
  have hP : gpeSq.Val n X = v ^ 2 := by
    simp [gpeSq, hvdef, Complex.normSq_eq_norm_sq]
  have hyv : |y - v| ≤ (g - 1) * v := by
    have := hy
    rw [hval, abs_of_nonneg hvnn] at this
    exact this
  have hy1 : y - v ≤ (g - 1) * v := (abs_le.mp hyv).2
  have hy2 : -((g - 1) * v) ≤ y - v := (abs_le.mp hyv).1
  have hyu : y ≤ g * v := by nlinarith
  have hyl : (2 - g) * v ≤ y := by nlinarith
  have hsum : |y + v| ≤ (g + 1) * v := by
    rw [abs_le]
    constructor <;> nlinarith
  have hfac : 0 ≤ (g - 1) * v := by nlinarith
  have hmul : |y - v| * |y + v| ≤ ((g - 1) * v) * ((g + 1) * v) :=
    mul_le_mul hyv hsum (abs_nonneg _) hfac
  have hsq : |y ^ 2 - v ^ 2| = |y - v| * |y + v| := by
    rw [← abs_mul, show (y - v) * (y + v) = y ^ 2 - v ^ 2 by ring]
  calc |y ^ 2 - gpeSq.Val n X| = |y ^ 2 - v ^ 2| := by rw [hP]
    _ = |y - v| * |y + v| := hsq
    _ ≤ ((g - 1) * v) * ((g + 1) * v) := hmul
    _ = (g ^ 2 - 1) * v ^ 2 := by ring
    _ = (g ^ 2 - 1) * |gpeSq.Val n X| := by
      rw [hP, abs_of_nonneg (sq_nonneg v)]

/-- The entire original squared-factor comparison follows from the genuine scalar squaring inequality. -/
theorem squareFactor : SquaredFactor gpeSq gpeAbs := by
  intro g hg
  obtain ⟨c₀, hc₀⟩ := hg
  refine ⟨1, ?_⟩
  intro n X y
  have hgn : 1 ≤ g n := (hc₀ n).1
  refine ⟨by simp, ?_⟩
  intro hy
  exact squareReduction n X (g n) y hgn hy

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.SquareReduce
