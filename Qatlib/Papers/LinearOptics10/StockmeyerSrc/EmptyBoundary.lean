/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.Defs
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # Literal zero-dimensional boundary checks of the historical probability targets

Fixed arXiv:1011.3245v1. Historical targets quantify over every natural
matrix size; strict inequalities at n=0 can fail independently of any
Gaussian asymptotic theorem. These are model-boundary checks, not refutations
of the paper's positive-dimensional claims.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.EmptyBoundary
open Qatlib.Concepts.CountingClasses.ClassTransport

/-- The actual determinant event integral appearing in the complete old target. -/
def detProb (n : ℕ) (eps : ℝ) : ℝ :=
  ∫ X : Fin n → Fin n → ℂ,
    (if Complex.normSq (Matrix.det (Matrix.of X)) < eps ^ 2 * (n.factorial : ℝ)
      then (1 : ℝ) else 0) * loGaussianMatDensity n X ∂volume

/-- The empty determinant is one, so its event at epsilon=1/2 has exactly zero mass. -/
theorem detZero : detProb 0 (1/2) = 0 := by
  have hz : (fun X : Fin 0 → Fin 0 → ℂ =>
      (if Complex.normSq (Matrix.det (Matrix.of X)) < (1/2 : ℝ)^2 * (Nat.factorial 0 : ℝ)
        then (1 : ℝ) else 0) * loGaussianMatDensity 0 X) = 0 := by
    funext X
    norm_num
  unfold detProb
  rw [hz]
  simp

/-- The complete original determinant bound, with its unrestricted natural dimension. -/
def DetBound (beta : ℝ) : Prop := ∃ C : ℝ, 0 < C ∧
  ∀ (n : ℕ) (eps : ℝ), 0 < eps →
    detProb n eps < C * (n : ℝ)^(beta*(beta+2)/8) * eps^beta

/-- The original determinant target is false at the admissible beta=1 because it includes n=0. -/
theorem detRefuted : ¬DetBound 1 := by
  rintro ⟨C, _, hc⟩
  have hz := hc 0 (1/2) (by norm_num)
  rw [detZero] at hz
  norm_num at hz

/-- The actual normalized permanent-moment random variable in the historical source. -/
def permMomentVar {n : ℕ} (X : Fin n → Fin n → ℂ) : ℝ :=
  Complex.normSq (Matrix.permanent (Matrix.of X)) / (n.factorial : ℝ)

/-- The actual weak permanent event integral, with its original non-strict event. -/
def permProb (n : ℕ) (alpha : ℝ) : ℝ :=
  ∫ X : Fin n → Fin n → ℂ,
    (if alpha ≤ permMomentVar X then (1 : ℝ) else 0) * loGaussianMatDensity n X ∂volume

/-- The actual empty-matrix permanent event at alpha=0 has unit probability. -/
theorem permZero : permProb 0 0 = 1 := by
  norm_num [permProb, permMomentVar, loGaussianMatDensity, Complex.normSq_nonneg]
  simp [measureReal_def, Measure.volume_pi_eq_dirac (0 : Fin 0 → Fin 0 → ℂ)]

/-- The complete original weak anti-concentration target with its unrestricted inputs. -/
def WeakAll : Prop := ∀ (n : ℕ) (alpha : ℝ), alpha < 1 →
  permProb n alpha > (1-alpha)^2 / ((n : ℝ)+1)

/-- The literal strict weak bound fails at the admissible empty dimension and alpha=0. -/
theorem weakRefuted : ¬WeakAll := by
  intro h
  have hz := h 0 0 (by norm_num)
  rw [permZero] at hz
  norm_num at hz

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.EmptyBoundary
