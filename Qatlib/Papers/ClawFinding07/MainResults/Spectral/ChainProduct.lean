/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.ProjectorCS
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ClawFinding07.MainResults.Spectral

open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.WalkSearch.TwoLevelLower (IsTransitionMatrix)
open scoped BigOperators

def sqNorm {I : Type*} [Fintype I] (v : I → ℝ) : ℝ := ∑ i, (v i) ^ 2

def dot {I : Type*} [Fintype I] (u v : I → ℝ) : ℝ := ∑ i, u i * v i

def SpectralGapAtLeast {I : Type*} [Fintype I] (P : I → I → ℝ) (δ : ℝ) : Prop :=
  IsTransitionMatrix P ∧ (∀ i j, P i j = P j i) ∧
    ∀ v : I → ℝ, (∑ i, v i) = 0 → sqNorm (fun i => ∑ j, P i j * v j) ≤ (1 - δ) ^ 2 * sqNorm v

def act {I : Type*} [Fintype I] (P : I → I → ℝ) (v : I → ℝ) : I → ℝ :=
  fun i => ∑ j, P i j * v j

variable {I J : Type*} [Fintype I] [Fintype J]

def chainProduct (P : I → I → ℝ) (Q : J → J → ℝ) : (I × J) → (I × J) → ℝ :=
  fun p q => P p.1 q.1 * Q p.2 q.2

def SpectralGapEquals {I : Type*} [Fintype I] (P : I → I → ℝ) (δ : ℝ) : Prop :=
  SpectralGapAtLeast P δ ∧ ∀ δ', SpectralGapAtLeast P δ' → δ' ≤ δ

theorem act_const {P : I → I → ℝ} (hP : ∀ i, ∑ j, P i j = 1) (c : ℝ) :
    act P (fun _ => c) = fun _ => c := by
  funext i
  simp only [act]
  rw [← Finset.sum_mul, hP i, one_mul]

theorem sum_act {P : I → I → ℝ} (hc : ∀ j, ∑ i, P i j = 1)
    (v : I → ℝ) : ∑ i, act P v i = ∑ i, v i := by
  simp only [act]
  rw [Finset.sum_comm]
  calc ∑ j, ∑ i, P i j * v j = ∑ j, (∑ i, P i j) * v j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
      _ = ∑ j, v j := by simp [hc]

theorem sum_act_zero {P : I → I → ℝ} (hc : ∀ j, ∑ i, P i j = 1) {v : I → ℝ}
    (hv : ∑ i, v i = 0) : ∑ i, act P v i = 0 := by
  rw [sum_act hc v, hv]

theorem act_add (P : I → I → ℝ) (u v : I → ℝ) :
    act P (u + v) = act P u + act P v := by
  funext i
  simp only [act, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem act_sub (P : I → I → ℝ) (u v : I → ℝ) :
    act P (u - v) = act P u - act P v := by
  funext i
  simp only [act, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem act_zeroSum {P : I → I → ℝ} (hc : ∀ j, ∑ i, P i j = 1)
    {v : I → ℝ} (hv : ∑ i, v i = 0) : (∑ i, act P v i) = 0 :=
  sum_act_zero hc hv

theorem dot_one_zero {v : I → ℝ} (hv : ∑ i, v i = 0) :
    dot (fun _ : I => (1 : ℝ)) v = 0 := by
  simp only [dot, one_mul, hv]

theorem dot_prod_split {a : I → ℝ} {b : J → ℝ} (hb : ∑ j, b j = 0) :
    dot (fun p : I × J => a p.1) (fun p : I × J => b p.2) = 0 := by
  simp only [dot, Fintype.sum_prod_type, ← Finset.mul_sum, hb, mul_zero,
    Finset.sum_const_zero]

theorem sqNorm_prod_right {c : J → ℝ} :
    sqNorm (fun p : I × J => c p.2) = (Fintype.card I : ℝ) * sqNorm c := by
  simp only [sqNorm, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]

theorem sqNorm_prod_left {a : I → ℝ} :
    sqNorm (fun p : I × J => a p.1) = (Fintype.card J : ℝ) * sqNorm a := by
  simp only [sqNorm, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum]

theorem sqNorm_add_of_dot_zero {u v : I → ℝ} (h : dot u v = 0) :
    sqNorm (u + v) = sqNorm u + sqNorm v := by
  have h1 : sqNorm (u + v) = ∑ i, (u i ^ 2 + 2 * (u i * v i) + v i ^ 2) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply]
    ring
  have hd : ∑ i, u i * v i = 0 := h
  rw [h1]
  simp only [sqNorm, Finset.sum_add_distrib, ← Finset.mul_sum, hd, mul_zero]
  ring

end Qatlib.Papers.ClawFinding07.MainResults.Spectral
