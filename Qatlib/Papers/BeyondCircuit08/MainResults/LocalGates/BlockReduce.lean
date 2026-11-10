/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BeyondCircuit08.MainResults.LocalGates.Basic
import Qatlib.Papers.BeyondCircuit08.MainResults.Model.ModelFacts
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped Matrix Matrix.Norms.L2Operator BigOperators
open Complex

namespace Qatlib.Papers.BeyondCircuit08.MainResults.LocalGates

open Qatlib.Papers.BeyondCircuit08.MainResults.Model

def Bn2 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![fibe, fibd; fibd, fibc]

def Bdiag2 (α : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (((α / 2 : ℝ) : ℂ) * Complex.I), 0;
     0, Complex.exp (((-(α / 2) : ℝ) : ℂ) * Complex.I)]

def gate2 : Gate5 → Matrix (Fin 2) (Fin 2) ℂ
  | .diag α => Bdiag2 α
  | .sigma => Bn2

def evalGate2 : List Gate5 → Matrix (Fin 2) (Fin 2) ℂ
  | [] => 1
  | g :: w => gate2 g * evalGate2 w

def gatePhi1 : Gate5 → ℂ
  | .diag α => Complex.exp (((α / 2 : ℝ) : ℂ) * Complex.I)
  | .sigma => fibb

def gatePhi2 : Gate5 → ℂ
  | .diag α => Complex.exp (((α / 2 : ℝ) : ℂ) * Complex.I)
  | .sigma => fiba

theorem gatePhi1_norm (g : Gate5) : ‖gatePhi1 g‖ = 1 := by
  cases g with
  | diag α => simp [gatePhi1, Complex.norm_exp]
  | sigma => exact fibb_norm

theorem gatePhi2_norm (g : Gate5) : ‖gatePhi2 g‖ = 1 := by
  cases g with
  | diag α => simp [gatePhi2, Complex.norm_exp]
  | sigma => exact fiba_norm

theorem gateMatrix_eq_block (g : Gate5) :
    gateMatrix g = lemma3Block (gatePhi1 g) (gatePhi2 g) (gate2 g) := by
  cases g with
  | diag α =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [gateMatrix, Mdiag5, lemma3Block, gate2, Bdiag2, gatePhi1, gatePhi2,
          Matrix.diagonal]
  | sigma =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [gateMatrix, Mn5, lemma3Block, gate2, Bn2, gatePhi1, gatePhi2]

theorem lemma3Block_mul (φ₁ φ₂ ψ₁ ψ₂ : ℂ)
    (V W : Matrix (Fin 2) (Fin 2) ℂ) :
    lemma3Block φ₁ φ₂ V * lemma3Block ψ₁ ψ₂ W =
      lemma3Block (φ₁ * ψ₁) (φ₂ * ψ₂) (V * W) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lemma3Block, Matrix.mul_apply, Fin.sum_univ_succ]

theorem evalGate_block (w : List Gate5) :
    ∃ φ₁ φ₂ : ℂ, ‖φ₁‖ = 1 ∧ ‖φ₂‖ = 1 ∧
      evalGate w = lemma3Block φ₁ φ₂ (evalGate2 w) := by
  induction w with
  | nil =>
      refine ⟨1, 1, by simp, by simp, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [evalGate, evalGate2, lemma3Block]
  | cons g w ih =>
      obtain ⟨φ₁, φ₂, h1, h2, heq⟩ := ih
      refine ⟨gatePhi1 g * φ₁, gatePhi2 g * φ₂,
        by rw [norm_mul, gatePhi1_norm, one_mul]; exact h1,
        by rw [norm_mul, gatePhi2_norm, one_mul]; exact h2, ?_⟩
      simp only [evalGate, evalGate2]
      rw [gateMatrix_eq_block, heq, lemma3Block_mul]

theorem lemma3_of_twoD
    (h : ∃ C : ℕ, ∀ V : Matrix (Fin 2) (Fin 2) ℂ, IsSUOn (Fin 2) V →
      ∃ w : List Gate5, w.length ≤ C ∧ evalGate2 w = V) :
    ∃ C : ℕ, ∀ V : Matrix (Fin 2) (Fin 2) ℂ, IsSUOn (Fin 2) V →
      ∃ w : List Gate5, w.length ≤ C ∧
        ∃ φ₁ φ₂ : ℂ, ‖φ₁‖ = 1 ∧ ‖φ₂‖ = 1 ∧
          evalGate w = lemma3Block φ₁ φ₂ V := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun V hV => ?_⟩
  obtain ⟨w, hlen, hw⟩ := hC V hV
  obtain ⟨φ₁, φ₂, h1, h2, heq⟩ := evalGate_block w
  exact ⟨w, hlen, φ₁, φ₂, h1, h2, by rw [heq, hw]⟩

end Qatlib.Papers.BeyondCircuit08.MainResults.LocalGates
