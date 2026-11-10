/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.Execution.WorkspaceCP

namespace Qatlib.Concepts.BlockEncoding.EncodingCore

open Matrix

set_option linter.unusedSectionVars false

variable {J K I : Type*} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I]

theorem sum_fiber_mul_left {X : Type*} [Fintype X] [DecidableEq X] (p₀ : X) (F : X → ℂ) :
    ∑ p, (if p = p₀ then (1 : ℂ) else 0) * F p = F p₀ := by
  rw [Finset.sum_eq_single p₀]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem sum_fiber_mul_right {X : Type*} [Fintype X] [DecidableEq X] (p₀ : X) (F : X → ℂ) :
    ∑ p, F p * (if p = p₀ then (1 : ℂ) else 0) = F p₀ := by
  rw [Finset.sum_eq_single p₀]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

def encodingFiber (j₀ : J) : Matrix (J × I) I ℂ :=
  Matrix.of fun x i => if x.1 = j₀ ∧ x.2 = i then 1 else 0

theorem encodingFiber_apply (j₀ : J) (x : J × I) (i : I) :
    encodingFiber j₀ x i = if x = (j₀, i) then 1 else 0 := by
  obtain ⟨a, b⟩ := x
  by_cases h1 : a = j₀ <;> by_cases h2 : b = i <;> simp [encodingFiber, h1, h2]

theorem encodingFiber_conjTranspose (j₀ : J) (i : I) (x : J × I) :
    (encodingFiber j₀)ᴴ i x = if x = (j₀, i) then 1 else 0 := by
  rw [Matrix.conjTranspose_apply, encodingFiber_apply]
  by_cases hx : x = (j₀, i) <;> simp [hx]

def jointEncodingFiber (j₀ : J) (k₀ : K) : Matrix ((J × K) × I) I ℂ :=
  encodingFiber (j₀, k₀)

theorem encodingFiber_isIsometry (j₀ : J) : IsIsometry (encodingFiber (I := I) j₀) := by
  unfold IsIsometry
  ext i k
  by_cases hik : i = k
  · subst k
    calc ((encodingFiber j₀)ᴴ * encodingFiber j₀ : Matrix I I ℂ) i i
        = ∑ p, (encodingFiber j₀)ᴴ i p * encodingFiber j₀ p i := Matrix.mul_apply
      _ = ∑ p, (if p = (j₀, i) then (1 : ℂ) else 0) * (if p = (j₀, i) then 1 else 0) := by
          simp only [encodingFiber_conjTranspose, encodingFiber_apply]
      _ = ∑ p, (if p = (j₀, i) then (1 : ℂ) else 0) * 1 := by
          refine Finset.sum_congr rfl fun p _ => ?_
          by_cases hp : p = (j₀, i) <;> simp [hp]
      _ = 1 := by simp
      _ = (1 : Matrix I I ℂ) i i := by rw [Matrix.one_apply_eq]
  · have hterm : ∀ p : J × I, (encodingFiber j₀)ᴴ i p * encodingFiber j₀ p k = 0 := by
      intro p
      rw [encodingFiber_conjTranspose, encodingFiber_apply]
      by_cases hp : p = (j₀, i)
      · rw [if_pos hp, one_mul]
        refine if_neg ?_
        intro h
        exact hik (congrArg Prod.snd (hp.symm.trans h))
      · rw [if_neg hp, zero_mul]
    calc ((encodingFiber j₀)ᴴ * encodingFiber j₀ : Matrix I I ℂ) i k
        = ∑ p, (encodingFiber j₀)ᴴ i p * encodingFiber j₀ p k := Matrix.mul_apply
      _ = 0 := Finset.sum_eq_zero fun p _ => hterm p
      _ = (1 : Matrix I I ℂ) i k := by rw [Matrix.one_apply_ne hik]

theorem jointEncodingFiber_isIsometry (j₀ : J) (k₀ : K) :
    IsIsometry (jointEncodingFiber (I := I) j₀ k₀) :=
  encodingFiber_isIsometry (I := I) (j₀, k₀)

theorem compress_encodingFiber_eq (j₀ : J) (M : Matrix (J × I) (J × I) ℂ) (i₁ i₂ : I) :
    compress (encodingFiber j₀) M (encodingFiber j₀) i₁ i₂ = M (j₀, i₁) (j₀, i₂) := by
  have h1 : ∀ x : J × I,
      ∑ w : J × I, (encodingFiber j₀)ᴴ i₁ w * M w x = M (j₀, i₁) x := by
    intro x
    simp only [encodingFiber_conjTranspose]
    exact sum_fiber_mul_left (j₀, i₁) (fun w => M w x)
  calc compress (encodingFiber j₀) M (encodingFiber j₀) i₁ i₂
      = ∑ x : J × I,
          (∑ w : J × I, (encodingFiber j₀)ᴴ i₁ w * M w x) * encodingFiber j₀ x i₂ := by
        rw [compress]
        simp only [Matrix.mul_apply]
    _ = ∑ x : J × I, M (j₀, i₁) x * encodingFiber j₀ x i₂ :=
          Finset.sum_congr rfl fun x _ => by rw [h1 x]
    _ = ∑ x : J × I, M (j₀, i₁) x * (if x = (j₀, i₂) then (1 : ℂ) else 0) := by
        simp only [encodingFiber_apply]
    _ = M (j₀, i₁) (j₀, i₂) := sum_fiber_mul_right (j₀, i₂) (fun x => M (j₀, i₁) x)

end Qatlib.Concepts.BlockEncoding.EncodingCore
