/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.FiniteGateWord.QmaCompleteness
import Qatlib.Concepts.TensorRegisters.RegisterModel.TensorRegisters
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

namespace Qatlib.Concepts.TensorRegisters.RegisterModel

open Qatlib Matrix
open scoped Classical BigOperators Kronecker

set_option autoImplicit false
noncomputable section

theorem energy_entries {I : Type} [Fintype I]
    (H : Matrix I I ℂ) (ψ : QState I) :
    energy H ψ = ∑ i, ∑ j,
      ((starRingEnd ℂ) (ψ i) * H i j * ψ j).re := by
  simp only [energy, inner_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum, Complex.re_sum, mul_assoc]

theorem entryBound_energy_lower {I : Type} [Fintype I]
    (H : Matrix I I ℂ) (hH : ∀ i j, ‖H i j‖ ≤ 1)
    (ψ : QState I) :
    -(Fintype.card I : ℝ) * mass ψ ≤ energy H ψ := by
  have hterm (i j : I) :
      -(‖ψ i‖ * ‖ψ j‖) ≤
        ((starRingEnd ℂ) (ψ i) * H i j * ψ j).re := by
    have hn : ‖(starRingEnd ℂ) (ψ i) * H i j * ψ j‖ ≤
        ‖ψ i‖ * ‖ψ j‖ := by
      change ‖star (ψ i) * H i j * ψ j‖ ≤ ‖ψ i‖ * ‖ψ j‖
      rw [norm_mul, norm_mul, norm_star]
      have h₁ := mul_le_mul_of_nonneg_left (hH i j) (norm_nonneg (ψ i))
      have h₂ := mul_le_mul_of_nonneg_right h₁ (norm_nonneg (ψ j))
      simpa only [mul_one] using h₂
    calc
      -(‖ψ i‖ * ‖ψ j‖) ≤
          -‖(starRingEnd ℂ) (ψ i) * H i j * ψ j‖ := neg_le_neg hn
      _ ≤ ((starRingEnd ℂ) (ψ i) * H i j * ψ j).re :=
        neg_le_of_abs_le (Complex.abs_re_le_norm _)
  have hneg : (∑ i : I, ∑ j : I, -(‖ψ i‖ * ‖ψ j‖)) =
      -(∑ i : I, ‖ψ i‖)^2 := by
    simp only [Finset.sum_neg_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, pow_two]
  have hsum : -(∑ i : I, ‖ψ i‖)^2 ≤ energy H ψ := by
    rw [← hneg, energy_entries]
    exact Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ => hterm i j
  have hCS : (∑ i : I, ‖ψ i‖)^2 ≤
      (Fintype.card I : ℝ) * mass ψ := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : I => ‖ψ i‖) (fun _ : I => (1 : ℝ))
    simpa [mass, mul_comm] using h
  calc
    -(Fintype.card I : ℝ) * mass ψ ≤ -(∑ i : I, ‖ψ i‖)^2 := by
      linarith
    _ ≤ energy H ψ := hsum

theorem mass_reindex {I J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (ψ : QState I) :
    mass (fun j : J => ψ (e.symm j)) = mass ψ := by
  exact e.symm.sum_comp (fun i : I => ‖ψ i‖^2)

theorem energy_reindex {I J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (H : Matrix I I ℂ) (ψ : QState I) :
    energy (Matrix.reindex e e H) (fun j : J => ψ (e.symm j)) =
      energy H ψ := by
  rw [energy_entries, energy_entries]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  calc
    (∑ j : J, ∑ k : J,
      ((starRingEnd ℂ) (ψ (e.symm j)) *
        H (e.symm j) (e.symm k) * ψ (e.symm k)).re) =
        ∑ j : J, ∑ i : I,
          ((starRingEnd ℂ) (ψ (e.symm j)) * H (e.symm j) i * ψ i).re := by
      apply Finset.sum_congr rfl
      intro j _
      exact e.symm.sum_comp (fun i : I =>
        ((starRingEnd ℂ) (ψ (e.symm j)) * H (e.symm j) i * ψ i).re)
    _ = ∑ i : I, ∑ k : I,
        ((starRingEnd ℂ) (ψ i) * H i k * ψ k).re :=
      e.symm.sum_comp (fun i : I => ∑ k : I,
        ((starRingEnd ℂ) (ψ i) * H i k * ψ k).re)

theorem kronecker_one_mulVec_apply {A B : Type}
    [Fintype A] [Fintype B] [DecidableEq B]
    (M : Matrix A A ℂ) (ψ : QState (A × B)) (a : A) (b : B) :
    ((M ⊗ₖ (1 : Matrix B B ℂ)) *ᵥ ψ) (a,b) =
      (M *ᵥ (fun a' : A => ψ (a',b))) a := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.one_apply, mul_ite, ite_mul]

theorem energy_tensor_one {A B : Type}
    [Fintype A] [Fintype B] [DecidableEq B]
    (M : Matrix A A ℂ) (ψ : QState (A × B)) :
    energy (M ⊗ₖ (1 : Matrix B B ℂ)) ψ =
      ∑ b : B, energy M (fun a : A => ψ (a,b)) := by
  simp only [energy, inner_apply, Complex.re_sum,
    Fintype.sum_prod_type, kronecker_one_mulVec_apply]
  exact Finset.sum_comm

theorem mass_fibers {A B : Type} [Fintype A] [Fintype B]
    (ψ : QState (A × B)) :
    (∑ b : B, mass (fun a : A => ψ (a,b))) = mass ψ := by
  simp only [mass, Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem partitionLift_energy_fibers {S A B : Type}
    [Fintype S] [Fintype A] [Fintype B] [DecidableEq B]
    (e : S ≃ A × B) (M : Matrix A A ℂ) (ψ : QState S) :
    energy (partitionLift e M) ψ =
      ∑ b : B, energy M (fun a : A => ψ (e.symm (a,b))) := by
  calc
    energy (partitionLift e M) ψ =
        energy (M ⊗ₖ (1 : Matrix B B ℂ))
          (fun p : A × B => ψ (e.symm p)) := by
      have h := energy_reindex e.symm
        (M ⊗ₖ (1 : Matrix B B ℂ))
        (fun p : A × B => ψ (e.symm p))
      simpa only [partitionLift, Equiv.symm_symm,
        Equiv.symm_apply_apply] using h
    _ = ∑ b : B, energy M (fun a : A => ψ (e.symm (a,b))) :=
      energy_tensor_one M (fun p : A × B => ψ (e.symm p))

theorem partition_mass_fibers {S A B : Type}
    [Fintype S] [Fintype A] [Fintype B]
    (e : S ≃ A × B) (ψ : QState S) :
    (∑ b : B, mass (fun a : A => ψ (e.symm (a,b)))) = mass ψ := by
  calc
    (∑ b : B, mass (fun a : A => ψ (e.symm (a,b)))) =
        mass (fun p : A × B => ψ (e.symm p)) :=
      mass_fibers (fun p : A × B => ψ (e.symm p))
    _ = mass ψ := mass_reindex e ψ

theorem partitionLift_energy_lower {S A B : Type}
    [Fintype S] [Fintype A] [Fintype B] [DecidableEq B]
    (e : S ≃ A × B) (M : Matrix A A ℂ)
    (hM : ∀ i j, ‖M i j‖ ≤ 1) (ψ : QState S) :
    -(Fintype.card A : ℝ) * mass ψ ≤ energy (partitionLift e M) ψ := by
  rw [partitionLift_energy_fibers]
  calc
    -(Fintype.card A : ℝ) * mass ψ =
        ∑ b : B, -(Fintype.card A : ℝ) *
          mass (fun a : A => ψ (e.symm (a,b))) := by
      rw [← partition_mass_fibers e ψ, Finset.mul_sum]
    _ ≤ ∑ b : B, energy M (fun a : A => ψ (e.symm (a,b))) :=
      Finset.sum_le_sum fun b _ =>
        entryBound_energy_lower M hM (fun a : A => ψ (e.symm (a,b)))

theorem partitionLift_five_qubit_energy_lower {S B : Type}
    [Fintype S] [Fintype B] [DecidableEq B]
    (k : ℕ) (hk : k ≤ 5) (e : S ≃ Reg k × B)
    (M : Matrix (Reg k) (Reg k) ℂ)
    (hM : ∀ i j, ‖M i j‖ ≤ 1) (ψ : QState S) :
    -(32 : ℝ) * mass ψ ≤ energy (partitionLift e M) ψ := by
  have hc : (Fintype.card (Reg k) : ℝ) ≤ 32 := by
    interval_cases k <;> norm_num [Reg]
  have hm : 0 ≤ mass ψ :=
    Finset.sum_nonneg (fun i _ => sq_nonneg ‖ψ i‖)
  calc
    -(32 : ℝ) * mass ψ ≤ -(Fintype.card (Reg k) : ℝ) * mass ψ :=
      mul_le_mul_of_nonneg_right (neg_le_neg hc) hm
    _ ≤ energy (partitionLift e M) ψ :=
      partitionLift_energy_lower e M hM ψ

end
end Qatlib.Concepts.TensorRegisters.RegisterModel
