/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Chebyshev
import Qatlib.Papers.TensorNetwork08.MainResults.StatDefs
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.TensorNetwork08.MainResults.Norm

open Classical
open scoped BigOperators

noncomputable def tensorNorm {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖v i‖ ^ 2)

noncomputable def diagTensor {n : ℕ} {C : Type*} [DecidableEq C] (a : Fin n) (α : C → ℂ)
    (x : Fin n → C) : ℂ :=
  if ∀ i, x i = x a then α (x a) else 0

theorem filter_diag_eq_image {n : ℕ} {C : Type*} [Fintype C] [DecidableEq C]
    (a : Fin n) :
    (Finset.univ.filter (fun x : Fin n → C => ∀ i, x i = x a))
      = Finset.univ.image (fun c : C => (fun _ : Fin n => c)) := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h
    exact ⟨x a, by funext i; exact (h i).symm⟩
  · rintro ⟨c, rfl⟩ i
    rfl

theorem tensorNorm_diagTensor {n : ℕ} {C : Type*} [Fintype C] [DecidableEq C]
    (a : Fin n) (α : C → ℂ) :
    tensorNorm (diagTensor a α) = Real.sqrt (∑ c : C, ‖α c‖ ^ 2) := by
  classical
  unfold tensorNorm
  congr 1
  have hpt : ∀ x : Fin n → C, ‖diagTensor a α x‖ ^ 2
      = if (∀ i, x i = x a) then ‖α (x a)‖ ^ 2 else 0 := by
    intro x
    by_cases h : ∀ i, x i = x a
    · simp [diagTensor, h]
    · simp [diagTensor, h]
  have hsum : (∑ x : Fin n → C, ‖diagTensor a α x‖ ^ 2)
      = ∑ x ∈ (Finset.univ.filter (fun x : Fin n → C => ∀ i, x i = x a)), ‖α (x a)‖ ^ 2 := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun x _ => by rw [hpt])
  rw [hsum, filter_diag_eq_image a]
  refine Finset.sum_image ?_
  intro c₁ _ c₂ _ h
  have := congrFun h a
  simpa using this

theorem deltaTensor_norm {n : ℕ} {C : Type*} [Fintype C] [DecidableEq C] (a : Fin n) :
    tensorNorm (diagTensor a (fun _ : C => (1 : ℂ))) = Real.sqrt (Fintype.card C) := by
  classical
  rw [tensorNorm_diagTensor (C := C)]
  congr 1
  have hone : ‖(1 : ℂ)‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_one]
  simp [hone]

theorem identityTensor_norm_eq {n m : ℕ} {C : Type*} [Fintype C] [DecidableEq C]
    (a : Fin n) (b : Fin m) (α : C → ℂ) :
    tensorNorm (diagTensor a α) = tensorNorm (diagTensor b α) := by
  rw [tensorNorm_diagTensor, tensorNorm_diagTensor]

theorem sup'_abs_le_sqrt_sum_sq {C : Type*} [Fintype C] [Nonempty C] (w : C → ℝ) :
    (Finset.univ.sup' Finset.univ_nonempty (fun c => |w c|))
      ≤ Real.sqrt (∑ c, |w c| ^ 2) := by
  classical
  refine Finset.sup'_le _ _ (fun c _ => ?_)
  rw [Real.le_sqrt (abs_nonneg _) (Finset.sum_nonneg (fun i _ => by positivity))]
  exact Finset.single_le_sum (f := fun i => |w i| ^ 2) (fun i _ => by positivity)
    (Finset.mem_univ c)

theorem sum_abs_le_sqrt_card_mul_sqrt_sum_sq {C : Type*} [Fintype C] (w : C → ℝ) :
    (∑ c, |w c|) ≤ Real.sqrt (Fintype.card C) * Real.sqrt (∑ c, |w c| ^ 2) := by
  classical
  have hsq : (∑ c, |w c|) ^ 2 ≤ (Fintype.card C : ℝ) * ∑ c, |w c| ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset C))
        (f := fun c => |w c|))
  have hnonneg : 0 ≤ ∑ c, |w c| := Finset.sum_nonneg (fun c _ => abs_nonneg _)
  have hsqrt : Real.sqrt ((∑ c, |w c|) ^ 2)
      ≤ Real.sqrt ((Fintype.card C : ℝ) * ∑ c, |w c| ^ 2) := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq hnonneg,
    Real.sqrt_mul (by positivity)] at hsqrt
  exact hsqrt

theorem sqrt_sum_sq_le_sum_abs {C : Type*} [Fintype C] (w : C → ℝ) :
    Real.sqrt (∑ c, |w c| ^ 2) ≤ ∑ c, |w c| := by
  classical
  have hsq : (∑ c, |w c| ^ 2) ≤ (∑ c, |w c|) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun c _ => abs_nonneg _)
  have hnonneg : 0 ≤ ∑ c, |w c| := Finset.sum_nonneg (fun c _ => abs_nonneg _)
  calc Real.sqrt (∑ c, |w c| ^ 2)
      ≤ Real.sqrt ((∑ c, |w c|) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ∑ c, |w c| := Real.sqrt_sq hnonneg

theorem abs_sq_eq_sq (w : ℝ) : |w| ^ 2 = w ^ 2 := by
  rw [sq_abs]

end Qatlib.Papers.TensorNetwork08.MainResults.Norm
