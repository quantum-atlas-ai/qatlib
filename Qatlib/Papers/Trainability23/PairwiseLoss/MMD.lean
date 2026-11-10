/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Papers.Trainability23.VarianceScaling.FiniteEnsemble
import Qatlib.Papers.Trainability23.PairwiseLoss.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring
set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.Trainability23.VarianceScaling

namespace Qatlib.Papers.Trainability23.PairwiseLoss

open scoped BigOperators

noncomputable def mmdLoss {X : Type*} [Fintype X] (K : X → X → ℝ) (p q : FinDist X) : ℝ :=
  ∑ x, ∑ y, q.prob x * q.prob y * K x y
    - 2 * ∑ x, ∑ y, q.prob x * p.prob y * K x y
    + ∑ x, ∑ y, p.prob x * p.prob y * K x y

theorem mmdLoss_self {X : Type*} [Fintype X] (K : X → X → ℝ) (p : FinDist X) :
    mmdLoss K p p = 0 := by
  unfold mmdLoss
  ring

def deltaKernel (X : Type*) [DecidableEq X] (x y : X) : ℝ := if x = y then 1 else 0

theorem mmdLoss_deltaKernel {X : Type*} [Fintype X] [DecidableEq X] (p q : FinDist X) :
    mmdLoss (deltaKernel X) p q = pairwiseLoss (fun a b : ℝ => (a - b) ^ 2) p.prob q.prob := by
  have diagQQ : ∀ x : X, ∑ y, q.prob x * q.prob y * deltaKernel X x y
      = q.prob x * q.prob x := by
    intro x
    rw [Finset.sum_eq_single x]
    · simp [deltaKernel]
    · intro y _ hy
      have hxy : x ≠ y := fun h => hy h.symm
      simp [deltaKernel, hxy]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  have diagQP : ∀ x : X, ∑ y, q.prob x * p.prob y * deltaKernel X x y
      = q.prob x * p.prob x := by
    intro x
    rw [Finset.sum_eq_single x]
    · simp [deltaKernel]
    · intro y _ hy
      have hxy : x ≠ y := fun h => hy h.symm
      simp [deltaKernel, hxy]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  have diagPP : ∀ x : X, ∑ y, p.prob x * p.prob y * deltaKernel X x y
      = p.prob x * p.prob x := by
    intro x
    rw [Finset.sum_eq_single x]
    · simp [deltaKernel]
    · intro y _ hy
      have hxy : x ≠ y := fun h => hy h.symm
      simp [deltaKernel, hxy]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  have hterm : ∀ x : X, (p.prob x - q.prob x) ^ 2
      = p.prob x * p.prob x - 2 * (q.prob x * p.prob x) + q.prob x * q.prob x := by
    intro x
    ring
  unfold mmdLoss pairwiseLoss
  rw [Finset.sum_congr rfl fun x _ => diagQQ x,
    Finset.sum_congr rfl fun x _ => diagQP x,
    Finset.sum_congr rfl fun x _ => diagPP x,
    Finset.sum_congr rfl fun x _ => hterm x]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem mmdLoss_deltaKernel_eq_zero_iff {X : Type*} [Fintype X] [DecidableEq X]
    (p q : FinDist X) :
    mmdLoss (deltaKernel X) p q = 0 ↔ ∀ x, p.prob x = q.prob x := by
  rw [mmdLoss_deltaKernel]
  unfold pairwiseLoss
  rw [Finset.sum_eq_zero_iff_of_nonneg fun x _ => sq_nonneg _]
  constructor
  · intro h x
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp (h x (Finset.mem_univ x)))
  · intro h x _
    rw [h x]
    ring

noncomputable def gaussianKernel {n : ℕ} (σ : ℝ) (x y : Fin n → ℝ) : ℝ :=
  ∏ i, Real.exp (-((x i - y i) ^ 2 / (2 * σ)))

theorem gaussianKernel_self {n : ℕ} (σ : ℝ) (x : Fin n → ℝ) :
    gaussianKernel σ x x = 1 := by
  simp [gaussianKernel]

theorem gaussianKernel_sum_form {n : ℕ} (σ : ℝ) (x y : Fin n → ℝ) :
    gaussianKernel σ x y = Real.exp (-(∑ i, (x i - y i) ^ 2) / (2 * σ)) := by
  have h : ∀ i : Fin n, -((x i - y i) ^ 2 / (2 * σ))
      = (x i - y i) ^ 2 * (-(2 * σ)⁻¹) := by
    intro i
    rw [div_eq_mul_inv]
    ring
  rw [gaussianKernel, ← Real.exp_sum]
  congr 1
  rw [Finset.sum_congr rfl fun i _ => h i, ← Finset.sum_mul, div_eq_mul_inv]
  ring

noncomputable def mmdLossFamily {X Θ : Type*} [Fintype X] (K : X → X → ℝ) (p : FinDist X)
    (q : Θ → FinDist X) (θ : Θ) : ℝ :=
  mmdLoss K p (q θ)

noncomputable def mmdVariance {X Θ : Type*} [Fintype X] [Fintype Θ] (P : FinDist Θ)
    (K : X → X → ℝ) (p : FinDist X) (q : Θ → FinDist X) : ℝ :=
  ensembleVariance P (mmdLossFamily K p q)

end Qatlib.Papers.Trainability23.PairwiseLoss
