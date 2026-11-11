/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Defs
import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Circuit composition and state transfer

This module defines the identity circuit `circId` and circuit composition `circComp`, and proves
closure of the circuit-size predicates under composition. It establishes transitivity of
`TransfersState` and propagates `Generable` and `QSamples` through state transfers;
`simulatable_zero` supplies the zero-Hamiltonian base case. The mathematical context is
[AharonovTaShma2007].

## Main statements

* `simulatable_zero`: The zero Hamiltonian is simulatable.
* `TransfersState.trans`: Efficient approximate state transfer is transitive.

## References

* [Aharonov and Ta‐Shma, 2007][AharonovTaShma2007]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabStateGen03.MainResults.Simulation

open Qatlib.Papers.AdiabStateGen03.MainResults

variable {n : ℕ}

/-- The circuit with identity operator and size zero. -/
def circId (n : ℕ) : Circuit n where
  unitary := 1
  size := 0
  contract := by
    intro ψ
    simp

/-- The operator of the identity circuit is the identity. -/
@[simp] lemma circId_unitary (n : ℕ) : (circId n).unitary = 1 := rfl

/-- The identity circuit satisfies `PolySize3` for every choice of time and accuracy parameters. -/
theorem polySize3_circId (n : ℕ) (t α : ℝ) : PolySize3 n t α (circId n) := by
  refine ⟨0, 0, ?_⟩
  simp [circId]

/-- The zero Hamiltonian is simulatable. -/
theorem simulatable_zero : Simulatable (0 : Ham n) := by
  intro t _ht α hα _hα1
  refine ⟨circId n, polySize3_circId n t α, ?_⟩
  have h : timeEvolution (0 : Ham n) t = 1 := by
    unfold timeEvolution toOp
    simp only [map_zero]
    have hz : (-t • Complex.I • (0 : Op n)) = 0 := by
      ext x
      simp
    rw [hz]
    exact NormedSpace.exp_zero
  rw [circId_unitary, h, sub_self, norm_zero]
  exact hα.le

/-- The circuit obtained by composing the operators of `C₁` and `C₂`, applying `C₂` first, and
adding their sizes. -/
def circComp (C₁ C₂ : Circuit n) : Circuit n where
  unitary := C₁.unitary.comp C₂.unitary
  size := C₁.size + C₂.size
  contract := by
    intro ψ
    calc ‖(C₁.unitary.comp C₂.unitary) ψ‖ = ‖C₁.unitary (C₂.unitary ψ)‖ := rfl
      _ ≤ ‖C₂.unitary ψ‖ := C₁.contract _
      _ ≤ ‖ψ‖ := C₂.contract ψ

/-- The operator of circuit composition is the composition of the two circuit operators. -/
@[simp] lemma circComp_unitary (C₁ C₂ : Circuit n) :
    (circComp C₁ C₂).unitary = C₁.unitary.comp C₂.unitary := rfl

/-- The size of a composed circuit is the sum of the component sizes. -/
@[simp] lemma circComp_size (C₁ C₂ : Circuit n) :
    (circComp C₁ C₂).size = C₁.size + C₂.size := rfl

/-- Composition preserves the polynomial circuit-size predicate `PolySize`. -/
theorem PolySize.circComp {C₁ C₂ : Circuit n} (h₁ : PolySize C₁) (h₂ : PolySize C₂) :
    PolySize (circComp C₁ C₂) := by
  obtain ⟨c₁, k₁, h₁⟩ := h₁
  obtain ⟨c₂, k₂, h₂⟩ := h₂
  refine ⟨c₁ + c₂, max k₁ k₂, ?_⟩
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hbase : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have e₁ : ((n : ℝ) + 1) ^ k₁ ≤ ((n : ℝ) + 1) ^ max k₁ k₂ :=
    pow_le_pow_right₀ hbase (Nat.le_max_left k₁ k₂)
  have e₂ : ((n : ℝ) + 1) ^ k₂ ≤ ((n : ℝ) + 1) ^ max k₁ k₂ :=
    pow_le_pow_right₀ hbase (Nat.le_max_right k₁ k₂)
  have h₁' : (C₁.size : ℝ) ≤ (c₁ : ℝ) * ((n : ℝ) + 1) ^ max k₁ k₂ + (c₁ : ℝ) := by
    calc (C₁.size : ℝ) ≤ (c₁ : ℝ) * ((n : ℝ) + 1) ^ k₁ + (c₁ : ℝ) := h₁
      _ ≤ (c₁ : ℝ) * ((n : ℝ) + 1) ^ max k₁ k₂ + (c₁ : ℝ) := by
          have : (0 : ℝ) ≤ (c₁ : ℝ) := Nat.cast_nonneg c₁
          nlinarith [mul_le_mul_of_nonneg_left e₁ this]
  have h₂' : (C₂.size : ℝ) ≤ (c₂ : ℝ) * ((n : ℝ) + 1) ^ max k₁ k₂ + (c₂ : ℝ) := by
    calc (C₂.size : ℝ) ≤ (c₂ : ℝ) * ((n : ℝ) + 1) ^ k₂ + (c₂ : ℝ) := h₂
      _ ≤ (c₂ : ℝ) * ((n : ℝ) + 1) ^ max k₁ k₂ + (c₂ : ℝ) := by
          have : (0 : ℝ) ≤ (c₂ : ℝ) := Nat.cast_nonneg c₂
          nlinarith [mul_le_mul_of_nonneg_left e₂ this]
  rw [circComp_size]
  push_cast
  nlinarith

/-- Composition preserves `PolySize3` at common positive time and accuracy parameters. -/
theorem PolySize3.circComp {C₁ C₂ : Circuit n} {t α : ℝ}
    (ht : 0 < t) (hα : 0 < α)
    (h₁ : PolySize3 n t α C₁) (h₂ : PolySize3 n t α C₂) :
    PolySize3 n t α (circComp C₁ C₂) := by
  obtain ⟨c₁, k₁, h₁⟩ := h₁
  obtain ⟨c₂, k₂, h₂⟩ := h₂
  refine ⟨c₁ + c₂, max k₁ k₂, ?_⟩
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hinv : (0 : ℝ) < 1 / α := by positivity
  have hbase : (1 : ℝ) ≤ (n : ℝ) + t + 1 / α + 1 := by linarith
  have e₁ : ((n : ℝ) + t + 1 / α + 1) ^ k₁
      ≤ ((n : ℝ) + t + 1 / α + 1) ^ max k₁ k₂ :=
    pow_le_pow_right₀ hbase (Nat.le_max_left k₁ k₂)
  have e₂ : ((n : ℝ) + t + 1 / α + 1) ^ k₂
      ≤ ((n : ℝ) + t + 1 / α + 1) ^ max k₁ k₂ :=
    pow_le_pow_right₀ hbase (Nat.le_max_right k₁ k₂)
  have h₁' : (C₁.size : ℝ)
      ≤ (c₁ : ℝ) * ((n : ℝ) + t + 1 / α + 1) ^ max k₁ k₂ + (c₁ : ℝ) := by
    calc (C₁.size : ℝ) ≤ (c₁ : ℝ) * ((n : ℝ) + t + 1 / α + 1) ^ k₁ + (c₁ : ℝ) := h₁
      _ ≤ (c₁ : ℝ) * ((n : ℝ) + t + 1 / α + 1) ^ max k₁ k₂ + (c₁ : ℝ) := by
          have : (0 : ℝ) ≤ (c₁ : ℝ) := Nat.cast_nonneg c₁
          nlinarith [mul_le_mul_of_nonneg_left e₁ this]
  have h₂' : (C₂.size : ℝ)
      ≤ (c₂ : ℝ) * ((n : ℝ) + t + 1 / α + 1) ^ max k₁ k₂ + (c₂ : ℝ) := by
    calc (C₂.size : ℝ) ≤ (c₂ : ℝ) * ((n : ℝ) + t + 1 / α + 1) ^ k₂ + (c₂ : ℝ) := h₂
      _ ≤ (c₂ : ℝ) * ((n : ℝ) + t + 1 / α + 1) ^ max k₁ k₂ + (c₂ : ℝ) := by
          have : (0 : ℝ) ≤ (c₂ : ℝ) := Nat.cast_nonneg c₂
          nlinarith [mul_le_mul_of_nonneg_left e₂ this]
  rw [circComp_size]
  push_cast
  nlinarith

/-- Efficient approximate state transfer is transitive. -/
theorem TransfersState.trans {ψ φ χ : State n}
    (h₁ : TransfersState ψ φ) (h₂ : TransfersState φ χ) : TransfersState ψ χ := by
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨C₁, hp₁, hd₁⟩ := h₁ (ε / 2) hε2
  obtain ⟨C₂, hp₂, hd₂⟩ := h₂ (ε / 2) hε2
  refine ⟨circComp C₂ C₁, PolySize.circComp hp₂ hp₁, ?_⟩
  rw [circComp_unitary]
  have hsplit : (C₂.unitary.comp C₁.unitary) ψ - χ
      = (C₂.unitary (C₁.unitary ψ) - C₂.unitary φ) + (C₂.unitary φ - χ) := by
    simp only [ContinuousLinearMap.comp_apply]
    abel
  rw [hsplit]
  calc ‖(C₂.unitary (C₁.unitary ψ) - C₂.unitary φ) + (C₂.unitary φ - χ)‖
      ≤ ‖C₂.unitary (C₁.unitary ψ) - C₂.unitary φ‖ + ‖C₂.unitary φ - χ‖ :=
        norm_add_le _ _
    _ ≤ ‖C₁.unitary ψ - φ‖ + ‖C₂.unitary φ - χ‖ := by
        refine add_le_add ?_ le_rfl
        calc ‖C₂.unitary (C₁.unitary ψ) - C₂.unitary φ‖
            = ‖C₂.unitary (C₁.unitary ψ - φ)‖ := by rw [map_sub]
          _ ≤ ‖C₁.unitary ψ - φ‖ := C₂.contract _
    _ ≤ ε / 2 + ε / 2 := add_le_add hd₁ hd₂
    _ = ε := by ring

/-- A transfer from a generable state produces a generable state. -/
theorem Generable.trans {φ χ : State n} (h₁ : Generable φ)
    (h₂ : TransfersState φ χ) : Generable χ :=
  TransfersState.trans h₁ h₂

/-- A transfer from a quantum-samplable state produces a quantum-samplable state. -/
theorem QSamples.trans {φ χ : State n} (h₁ : QSamples φ)
    (h₂ : TransfersState φ χ) : QSamples χ :=
  Generable.trans h₁ h₂

end Qatlib.Papers.AdiabStateGen03.MainResults.Simulation
