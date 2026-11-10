/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Tactic.NormNum

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.HHLManyBody22.FixedControl

open Matrix
open Qatlib.Foundations.PureStateMath

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def controlledGate (U : Matrix I I ℂ) : Matrix (I ⊕ I) (I ⊕ I) ℂ :=
  Matrix.fromBlocks 1 0 0 U

def embedZero (φ : I → ℂ) : QState (I ⊕ I) :=
  Sum.elim φ (fun _ => 0)

def embedOne (φ : I → ℂ) : QState (I ⊕ I) :=
  Sum.elim (fun _ => 0) φ

theorem applyGate_controlledGate_zero (U : Matrix I I ℂ) (φ : I → ℂ) :
    ApplyGate (controlledGate U) (embedZero φ) = embedZero φ := by
  rw [ApplyGate, controlledGate, Matrix.fromBlocks_mulVec]
  ext i
  cases i with
  | inl i => simp [embedZero, Matrix.one_mulVec, Matrix.zero_mulVec]
  | inr i =>
      simp only [embedZero, Sum.elim_inr, Matrix.zero_mulVec, zero_add]
      change (U *ᵥ (0 : I → ℂ)) i = 0
      simp

theorem applyGate_controlledGate_one (U : Matrix I I ℂ) (φ : I → ℂ) :
    ApplyGate (controlledGate U) (embedOne φ) = embedOne (ApplyGate U φ) := by
  rw [ApplyGate, controlledGate, Matrix.fromBlocks_mulVec]
  simp [embedOne, ApplyGate, Matrix.zero_mulVec, Matrix.one_mulVec]

theorem fixed_zero_eq_identity (U : Matrix I I ℂ) (φ : I → ℂ) :
    ApplyGate (controlledGate U) (embedZero φ) = ApplyGate 1 (embedZero φ) := by
  rw [applyGate_controlledGate_zero, applyGate_one]

theorem controlledGate_mem_unitaryGroup (U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    controlledGate U ∈ Matrix.unitaryGroup (I ⊕ I) ℂ := by
  have hU' : U * Uᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hU)
  rw [Matrix.mem_unitaryGroup_iff]
  unfold controlledGate
  rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply]
  simp [hU', Matrix.fromBlocks_one]

omit [Fintype I] in

theorem controlledGate_one : controlledGate (1 : Matrix I I ℂ) = 1 := by
  unfold controlledGate
  rw [Matrix.fromBlocks_one]

def fixedSet (probs : I → ℝ) (Pth : ℝ) : Finset I :=
  Finset.univ.filter (fun i => Pth ≤ probs i)

noncomputable def fixingCount (probs : I → ℝ) (Pth : ℝ) : ℕ :=
  (fixedSet probs Pth).card

omit [DecidableEq I] in

theorem fixingCount_mono {probs : I → ℝ} {Pth Pth' : ℝ} (h : Pth ≤ Pth') :
    fixingCount probs Pth' ≤ fixingCount probs Pth := by
  unfold fixingCount fixedSet
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, le_trans h hi.2⟩

omit [DecidableEq I] in

theorem fixingCount_le_card (probs : I → ℝ) (Pth : ℝ) :
    fixingCount probs Pth ≤ Fintype.card I := by
  unfold fixingCount fixedSet
  simpa using Finset.card_filter_le (Finset.univ : Finset I) (fun i => Pth ≤ probs i)

omit [DecidableEq I] in

theorem fixingCount_eq_card (probs : I → ℝ) (Pth : ℝ)
    (h : ∀ i, Pth ≤ probs i) : fixingCount probs Pth = Fintype.card I := by
  unfold fixingCount fixedSet
  rw [Finset.filter_true_of_mem (fun i _ => h i), Finset.card_univ]

def defaultThreshold : ℝ := 0.8

theorem defaultThreshold_mem : 0 < defaultThreshold ∧ defaultThreshold < 1 := by
  constructor <;> norm_num [defaultThreshold]

theorem defaultThreshold_eq : defaultThreshold = 4 / 5 := by
  norm_num [defaultThreshold]

end Qatlib.Papers.HHLManyBody22.FixedControl
