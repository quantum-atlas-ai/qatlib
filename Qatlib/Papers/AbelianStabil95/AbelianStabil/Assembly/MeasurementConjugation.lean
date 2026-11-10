/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StabilizerAlg.NearUniformGen.MeasurementOperator.CompositeMeasure

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.StabilizerAlg.NearUniformGen.MeasurementOperator
open scoped BigOperators Classical

set_option linter.unusedSectionVars false

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.Assembly

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem permMatrix_mul {σ τ : I → I} :
    permMatrix σ * permMatrix τ = permMatrix (σ ∘ τ) := by
  ext i j
  simp only [Matrix.mul_apply, permMatrix, Matrix.of_apply]
  rw [Finset.sum_eq_single (τ j)]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h; exact absurd (Finset.mem_univ (τ j)) h

theorem permMatrix_mul_symm (p : Equiv.Perm I) :
    permMatrix p * permMatrix p.symm = 1 := by
  rw [permMatrix_mul]
  ext i j
  simp [permMatrix, Equiv.apply_symm_apply, Matrix.one_apply]

theorem permMatrix_symm_mul (p : Equiv.Perm I) :
    permMatrix p.symm * permMatrix p = 1 := by
  rw [permMatrix_mul]
  ext i j
  simp [permMatrix, Equiv.symm_apply_apply, Matrix.one_apply]

theorem permMatrix_conj_apply (p : Equiv.Perm I) (M : Matrix I I ℂ) (x y : I) :
    (permMatrix p.symm * M * permMatrix p) x y = M (p x) (p y) := by
  simp only [Matrix.mul_apply, permMatrix, Matrix.of_apply]
  rw [Finset.sum_eq_single (p y)]
  · rw [Finset.sum_eq_single (p x)]
    · simp [Equiv.symm_apply_apply]
    · intro w _ hw
      have hpx : ¬ (x = p.symm w) := by
        intro hx
        have hp : p x = w := by rw [hx, Equiv.apply_symm_apply]
        exact hw hp.symm
      simp [hpx]
    · intro h; exact absurd (Finset.mem_univ (p x)) h
  · intro z _ hz; simp [hz]
  · intro h; exact absurd (Finset.mem_univ (p y)) h

variable {A D Ω : Type*} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
  [Fintype Ω] [DecidableEq Ω]

theorem measOp_conj_prodPerm (branch : A → Ω) (V : Ω → Matrix D D ℂ)
    (σ : Equiv.Perm A) (τ : Equiv.Perm D) :
    permMatrix (σ.prodCongr τ).symm * measOp branch V * permMatrix (σ.prodCongr τ)
      = measOp (fun a => branch (σ a))
          (fun W => permMatrix τ.symm * V W * permMatrix τ) := by
  ext ⟨a, d⟩ ⟨a', d'⟩
  have hτ : (permMatrix τ.symm * V (branch (σ a)) * permMatrix τ) d d'
      = V (branch (σ a)) (τ d) (τ d') := by
    simpa using permMatrix_conj_apply τ (V (branch (σ a))) d d'
  rw [permMatrix_conj_apply (σ.prodCongr τ) (measOp branch V)]
  simp only [measOp, Matrix.of_apply, Equiv.prodCongr_apply]
  rw [hτ]
  by_cases ha : a = a'
  · subst ha; simp
  · have hσ : ¬ (σ a = σ a') := fun h => ha (σ.injective h)
    simp [ha, hσ]

end Qatlib.Papers.AbelianStabil95.AbelianStabil.Assembly
