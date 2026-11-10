/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DysonSeries22.Truncation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace Qatlib.Papers.DysonSeries22.TimeSteps
open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.DysonSeries22.ExactSource
open Qatlib.Papers.DysonSeries22.Truncation
open Qatlib.Foundations.TimeEvolution.DysonError
set_option warningAsError false
variable {I : Type} [Fintype I] [DecidableEq I]

def exactStep (A : ℝ → Matrix I I ℂ) (t : ℕ → ℝ) (n : ℕ) :
    EuclideanSpace ℂ I → EuclideanSpace ℂ I :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) (orderedEvolution (fun u => -A u) (t n) (t (n+1)))

def exactDriving (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (t : ℕ → ℝ) (n : ℕ) :=
  toEuclidean_fromVec (dysonSourceSeries A b (t n) (t (n+1)))

def finiteMarch (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (t : ℕ → ℝ)
    (K : ℕ) (x₀ : EuclideanSpace ℂ I) : ℕ → EuclideanSpace ℂ I :=
  affineTrajectory (fun n => (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) (truncatedEvolution A (t n) (t (n+1)) K))
    (fun n => truncatedSource A b (t n) (t (n+1)) K) x₀

theorem exactStep_nonexpansive (A : ℝ → Matrix I I ℂ) (hA : Continuous A)
    (hlog : HasNonpositiveLogNorm A) (t : ℕ → ℝ) (ht : ∀ n, t n ≤ t (n+1))
    (n : ℕ) (x z : EuclideanSpace ℂ I) :
    ‖exactStep A t n x - exactStep A t n z‖ ≤ ‖x-z‖ := by
  change ‖((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) _) x -
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) _) z‖ ≤ _
  rw [← map_sub]
  calc
    _ ≤ ‖orderedEvolution (fun u => -A u) (t n) (t (n+1))‖ * ‖x-z‖ :=
      Matrix.l2_opNorm_mulVec _ _
    _ ≤ 1 * ‖x-z‖ := mul_le_mul_of_nonneg_right (dissipative_contraction A hA hlog (ht n)) (norm_nonneg _)
    _ = _ := one_mul _

theorem ode_samples (A : ℝ → Matrix I I ℂ) (b x : ℝ → QState I)
    (hA : Continuous A) (hb : Continuous b)
    (hx : ∀ u, HasDerivAt x (A u *ᵥ x u + b u) u) (t : ℕ → ℝ) (n : ℕ) :
    affineTrajectory (exactStep A t) (exactDriving A b t)
      (toEuclidean_fromVec (x (t 0))) n = toEuclidean_fromVec (x (t n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [affineTrajectory,ih]
    have h := congrFun (solution_eq_initial_add_dyson A b x hA hb (t n) hx) (t (n+1))
    rw [h]
    rfl

def localDefect (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (t : ℕ → ℝ)
    (K : ℕ) (y : ℕ → EuclideanSpace ℂ I) (n : ℕ) : ℝ :=
  ‖orderedEvolution (fun u => -A u) (t n) (t (n+1)) - truncatedEvolution A (t n) (t (n+1)) K‖ * ‖y n‖ +
    ‖exactDriving A b t n - truncatedSource A b (t n) (t (n+1)) K‖

theorem finiteMarch_residual (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (t : ℕ → ℝ) (K : ℕ) (x₀ : EuclideanSpace ℂ I) (n : ℕ) :
    ‖finiteMarch A b t K x₀ (n+1) -
      (exactStep A t n (finiteMarch A b t K x₀ n) + exactDriving A b t n)‖ ≤
      localDefect A b t K (finiteMarch A b t K x₀) n := by
  let y := finiteMarch A b t K x₀
  let V := truncatedEvolution A (t n) (t (n+1)) K
  let W := orderedEvolution (fun u => -A u) (t n) (t (n+1))
  have hy :
      y (n+1) = (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) V (y n) + truncatedSource A b (t n)
      (t (n+1)) K := rfl
  change ‖y (n+1) - ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) W (y n) + _)‖ ≤ _
  rw [hy]
  have he : (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) V (y n) + truncatedSource A b (t n) (t (n+1)) K -
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) W (y n) + exactDriving A b t n) =
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) (V-W) (y n) +
      (truncatedSource A b (t n) (t (n+1)) K - exactDriving A b t n) := by
    rw [map_sub]
    simp only [ContinuousLinearMap.sub_apply]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (by
    simpa only [localDefect,V,W,norm_sub_rev] using!
      add_le_add (Matrix.l2_opNorm_mulVec (V-W) (y n))
        (le_refl ‖truncatedSource A b (t n) (t (n+1)) K - exactDriving A b t n‖))

theorem finiteMarch_error (A : ℝ → Matrix I I ℂ) (b x : ℝ → QState I)
    (hA : Continuous A) (hb : Continuous b) (hlog : HasNonpositiveLogNorm A)
    (hx : ∀ u, HasDerivAt x (A u *ᵥ x u + b u) u)
    (t : ℕ → ℝ) (ht : ∀ n, t n ≤ t (n+1)) (K n : ℕ) :
    ‖finiteMarch A b t K (toEuclidean_fromVec (x (t 0))) n - toEuclidean_fromVec (x (t n))‖ ≤
      ∑ j ∈ Finset.range n, localDefect A b t K
        (finiteMarch A b t K (toEuclidean_fromVec (x (t 0)))) j := by
  rw [← ode_samples A b x hA hb hx t n]
  apply residual_error_le _ _ _ _ _ rfl (exactStep_nonexpansive A hA hlog t ht)
  exact finiteMarch_residual A b t K _
end Qatlib.Papers.DysonSeries22.TimeSteps
