/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.SwapEmbedding.GramStates
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

open Matrix Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.InvFreePhase
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open scoped ComplexConjugate

namespace Qatlib.Papers.ContDiscWalk08.SwapEmbedding

open Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum

variable {I : Type*} [Fintype I] [DecidableEq I]

def swapQState (ψ : QState (I × I)) : QState (I × I) := fun p => ψ (Prod.swap p)

theorem swapQState_add (ψ φ : QState (I × I)) :
    swapQState (ψ + φ) = swapQState ψ + swapQState φ := rfl

theorem swapQState_smul (c : ℂ) (ψ : QState (I × I)) :
    swapQState (c • ψ) = c • swapQState ψ := rfl

theorem swapGate_mulVec_eq (ψ : QState (I × I)) :
    SwapGate *ᵥ ψ = swapQState ψ := by
  rw [applyGate_swapGate]; rfl

theorem swapGate_mulVec_add (ψ φ : QState (I × I)) :
    SwapGate *ᵥ (ψ + φ) = SwapGate *ᵥ ψ + SwapGate *ᵥ φ := by
  rw [swapGate_mulVec_eq, swapGate_mulVec_eq, swapGate_mulVec_eq, swapQState_add]

theorem swapGate_mulVec_smul (c : ℂ) (ψ : QState (I × I)) :
    SwapGate *ᵥ (c • ψ) = c • (SwapGate *ᵥ ψ) := by
  rw [swapGate_mulVec_eq, swapGate_mulVec_eq, swapQState_smul]

theorem inner_add_left {J : Type*} [Fintype J] [DecidableEq J] (ψ φ θ : QState J) :
    Inner (ψ + φ) θ = Inner ψ θ + Inner φ θ := by
  rw [inner_apply, inner_apply, inner_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Pi.add_apply, map_add, add_mul]

theorem inner_add_right {J : Type*} [Fintype J] [DecidableEq J] (ψ φ θ : QState J) :
    Inner ψ (φ + θ) = Inner ψ φ + Inner ψ θ := by
  rw [inner_apply, inner_apply, inner_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Pi.add_apply, mul_add]

theorem inner_smul_left {J : Type*} [Fintype J] [DecidableEq J] (c : ℂ) (ψ φ : QState J) :
    Inner (c • ψ) φ = (starRingEnd ℂ) c * Inner ψ φ := by
  rw [inner_apply, inner_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem inner_smul_right {J : Type*} [Fintype J] [DecidableEq J] (c : ℂ) (ψ φ : QState J) :
    Inner ψ (c • φ) = c * Inner ψ φ := by
  rw [inner_apply, inner_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem sqrt_sq_cast (x : ℝ) (hx : 0 ≤ x) :
    (Real.sqrt x : ℂ) * (Real.sqrt x : ℂ) = (x : ℂ) := by
  have hcast : (Real.sqrt x : ℂ) * (Real.sqrt x : ℂ)
      = (((Real.sqrt x) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Real.sq_sqrt hx]

theorem sqrt_mul_conj_sqrt (x : ℝ) (hx : 0 ≤ x) :
    (Real.sqrt x : ℂ) * (starRingEnd ℂ) (Real.sqrt x : ℂ) = (x : ℂ) := by
  have h : (starRingEnd ℂ) ((Real.sqrt x : ℝ) : ℂ) = ((Real.sqrt x : ℝ) : ℂ) := by simp
  rw [h, mul_comm, sqrt_sq_cast x hx]

theorem conj_sqrt_mul_sqrt (x : ℝ) (hx : 0 ≤ x) :
    (starRingEnd ℂ) (Real.sqrt x : ℂ) * (Real.sqrt x : ℂ) = (x : ℂ) := by
  have h : (starRingEnd ℂ) ((Real.sqrt x : ℝ) : ℂ) = ((Real.sqrt x : ℝ) : ℂ) := by simp
  rw [h, sqrt_sq_cast x hx]

structure LazyData (I : Type*) [Fintype I] [DecidableEq I] where

  base : GramData I

  bot : I → QState (I × I)

  bot_orthonormal : ∀ j k : I, Inner (bot j) (bot k) = if j = k then 1 else 0

  bot_psi : ∀ j k : I, Inner (bot j) (GramData.gramState base k) = 0

  psi_bot : ∀ j k : I, Inner (GramData.gramState base j) (bot k) = 0

  bot_swap_psi : ∀ j k : I, Inner (bot j) (SwapGate *ᵥ GramData.gramState base k) = 0

  psi_swap_bot : ∀ j k : I, Inner (GramData.gramState base j) (SwapGate *ᵥ bot k) = 0

  bot_swap_bot : ∀ j k : I, Inner (bot j) (SwapGate *ᵥ bot k) = 0

namespace LazyData

variable (L : LazyData I)

def psi (L : LazyData I) (j : I) : QState (I × I) := GramData.gramState L.base j

def lazyState (L : LazyData I) (ε : ℝ) (j : I) : QState (I × I) :=
  ((Real.sqrt ε : ℝ) : ℂ) • L.psi j + ((Real.sqrt (1 - ε) : ℝ) : ℂ) • L.bot j

theorem inner_lazyState_self (L : LazyData I) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (j k : I) :
    Inner (L.lazyState ε j) (L.lazyState ε k) = if j = k then 1 else 0 := by
  have hε1' : 0 ≤ 1 - ε := by linarith
  by_cases hjk : j = k
  · subst hjk
    unfold lazyState
    rw [if_pos rfl]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      psi, GramData.inner_gramState_self, if_pos rfl, if_true, L.bot_orthonormal,
      L.bot_psi, L.psi_bot, mul_one, mul_zero, zero_add, add_zero]
    rw [sqrt_mul_conj_sqrt ε hε0, sqrt_mul_conj_sqrt (1 - ε) hε1']
    push_cast
    ring
  · unfold lazyState
    rw [if_neg hjk]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      psi, GramData.inner_gramState_self, if_neg hjk, if_false, L.bot_orthonormal,
      L.bot_psi, L.psi_bot, mul_one, mul_zero, zero_add, add_zero]

theorem inner_lazyState_swap (L : LazyData I) (ε : ℝ) (hε0 : 0 ≤ ε) (j k : I) :
    Inner (L.lazyState ε j) (SwapGate *ᵥ L.lazyState ε k)
      = (ε : ℂ) * (((L.base.C)⁻¹ : ℂ) * L.base.H j k) := by
  unfold lazyState
  rw [swapGate_mulVec_add, swapGate_mulVec_smul, swapGate_mulVec_smul]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    psi, GramData.inner_gramState_swap, L.bot_swap_psi, L.psi_swap_bot,
    L.bot_swap_bot, mul_zero, add_zero, mul_one]
  rw [← mul_assoc, sqrt_mul_conj_sqrt ε hε0]

def lazyIsometry (L : LazyData I) (ε : ℝ) : Matrix (I × I) I ℂ :=
  Matrix.of (fun p j => L.lazyState ε j p)

theorem lazyIsometry_conjTranspose_mul (L : LazyData I) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (L.lazyIsometry ε)ᴴ * L.lazyIsometry ε = 1 := by
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hconv : (∑ p : I × I, (L.lazyIsometry ε)ᴴ j p * L.lazyIsometry ε p k)
      = Inner (L.lazyState ε j) (L.lazyState ε k) := by
    rw [inner_apply]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rfl
  rw [hconv, L.inner_lazyState_self ε hε0 hε1 j k]

theorem inv_div_C (ε : ℝ) : ((L.base.C / ε)⁻¹ : ℝ) = ε / L.base.C := by
  rw [inv_div]

theorem lazyIsometry_gram (L : LazyData I) (ε : ℝ) (hε0 : 0 ≤ ε) :
    (L.lazyIsometry ε)ᴴ * SwapGate * L.lazyIsometry ε
      = ((((L.base.C / ε)⁻¹ : ℝ)) : ℂ) • L.base.H := by
  ext j k
  rw [Matrix.smul_apply, Matrix.mul_assoc, Matrix.mul_apply]
  change (∑ p : I × I, (starRingEnd ℂ) (L.lazyState ε j p) *
      (SwapGate *ᵥ L.lazyState ε k) p)
      = ((((L.base.C / ε)⁻¹ : ℝ)) : ℂ) * L.base.H j k
  rw [← inner_apply, L.inner_lazyState_swap ε hε0 j k]
  rw [L.inv_div_C ε]
  push_cast
  rw [div_eq_mul_inv]
  ring

def lazyWalkSetup (L : LazyData I) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    WalkSetup I where
  H := L.base.H
  isHermitian := L.base.isHermitian
  absNorm := L.base.C / ε
  absNorm_pos := div_pos L.base.C_pos hε
  T := L.lazyIsometry ε
  isometry := L.lazyIsometry_conjTranspose_mul ε hε.le hε1
  gram := L.lazyIsometry_gram ε hε.le

end LazyData

end Qatlib.Papers.ContDiscWalk08.SwapEmbedding
