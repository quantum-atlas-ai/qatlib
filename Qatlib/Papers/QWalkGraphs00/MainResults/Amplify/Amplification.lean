/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalkGraphs00.MainResults.Amplify

open scoped BigOperators

section Defs

variable {V : Type*} [Fintype V]
variable {π : V → ℝ} {ε : ℝ}

def l1Norm (f : V → ℝ) : ℝ := ∑ v, |f v|

def stochStep (P : V → V → ℝ) (σ : V → ℝ) : V → ℝ := fun u => ∑ v, σ v * P v u

structure AmplificationStep (π : V → ℝ) (ε : ℝ) where

  P : V → V → ℝ

  row_sum : ∀ v, ∑ u, P v u = 1

  pi_fixed : stochStep P π = π

  contract : ∀ τ : V → ℝ, (∑ v, τ v = 0) →
    l1Norm (stochStep P τ) ≤ ε * l1Norm τ

theorem stochStep_sub (P : V → V → ℝ) (σ π : V → ℝ) :
    stochStep P (σ - π) = stochStep P σ - stochStep P π := by
  funext u
  simp only [stochStep, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem stochStep_sum_zero (P : V → V → ℝ) (hrow : ∀ v, ∑ u, P v u = 1)
    (τ : V → ℝ) (hτ : ∑ v, τ v = 0) :
    ∑ u, stochStep P τ u = 0 := by
  simp only [stochStep]
  rw [Finset.sum_comm]
  calc ∑ v, ∑ u, τ v * P v u = ∑ v, τ v * ∑ u, P v u := by
        apply Finset.sum_congr rfl
        intro v _
        rw [Finset.mul_sum]
    _ = ∑ v, τ v := by
        apply Finset.sum_congr rfl
        intro v _
        rw [hrow v, mul_one]
    _ = 0 := hτ

theorem iterate_sum_zero (A : AmplificationStep (V := V) π ε) (k : ℕ) (τ : V → ℝ)
    (hτ : ∑ v, τ v = 0) :
    ∑ v, ((stochStep A.P)^[k] τ) v = 0 := by
  induction k with
  | zero => simpa using hτ
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact stochStep_sum_zero A.P A.row_sum _ ih

theorem amplification_iterate (P : V → V → ℝ) (hfix : stochStep P π = π) (k : ℕ)
    (σ : V → ℝ) :
    (stochStep P)^[k] σ - π = (stochStep P)^[k] (σ - π) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have h1 : stochStep P ((stochStep P)^[k] σ) - π
          = stochStep P ((stochStep P)^[k] σ) - stochStep P π := by
        conv_lhs => rw [← hfix]
      have h2 : stochStep P ((stochStep P)^[k] σ) - stochStep P π
          = stochStep P ((stochStep P)^[k] σ - π) := by
        rw [stochStep_sub]
      rw [h1, h2, ih]

end Defs

section Main

variable {V : Type*} [Fintype V]
variable {π : V → ℝ} {ε : ℝ}

theorem iterate_l1_le (A : AmplificationStep (V := V) π ε) (hε : 0 ≤ ε) (k : ℕ) :
    ∀ (τ : V → ℝ), (∑ v, τ v = 0) →
      l1Norm ((stochStep A.P)^[k] τ) ≤ ε ^ k * l1Norm τ := by
  induction k with
  | zero =>
      intro τ _
      simp
  | succ k ih =>
      intro τ hτ
      rw [Function.iterate_succ_apply']
      have hτ' : ∑ v, ((stochStep A.P)^[k] τ) v = 0 := iterate_sum_zero A k τ hτ
      calc l1Norm (stochStep A.P ((stochStep A.P)^[k] τ))
          ≤ ε * l1Norm ((stochStep A.P)^[k] τ) := A.contract _ hτ'
        _ ≤ ε * (ε ^ k * l1Norm τ) :=
            mul_le_mul_of_nonneg_left (ih τ hτ) hε
        _ = ε ^ (k + 1) * l1Norm τ := by ring

theorem lemma_5_1 (A : AmplificationStep (V := V) π ε) (hε : 0 ≤ ε) (k : ℕ)
    (σ : V → ℝ) (δ : ℝ)
    (hσ : ∑ v, σ v = 1) (hπ : ∑ v, π v = 1)
    (hδ : l1Norm (σ - π) ≤ δ) :
    l1Norm ((stochStep A.P)^[k] σ - π) ≤ ε ^ k * δ := by
  have hsum : ∑ v, (σ - π) v = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hσ, hπ, sub_self]
  have hiter := amplification_iterate A.P A.pi_fixed k σ
  rw [hiter]
  have hbound := iterate_l1_le A hε k (σ - π) hsum
  calc l1Norm ((stochStep A.P)^[k] (σ - π))
      ≤ ε ^ k * l1Norm (σ - π) := hbound
    _ ≤ ε ^ k * δ := by
        apply mul_le_mul_of_nonneg_left hδ
        positivity

end Main

end Qatlib.Papers.QWalkGraphs00.MainResults.Amplify
