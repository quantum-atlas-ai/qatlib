/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators ComplexOrder Matrix
namespace Qatlib.Foundations.MatrixAlgebra.ProjectiveFix
noncomputable section
variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E]

def kraus (K : E → Matrix D D ℂ) (M : Matrix D D ℂ) : Matrix D D ℂ :=
  ∑ a, K a * M * (K a)ᴴ

omit [DecidableEq D] in

theorem kraus_pos (K : E → Matrix D D ℂ) {M : Matrix D D ℂ} (hM : M.PosSemidef) :
    (kraus K M).PosSemidef := by
  exact Matrix.posSemidef_sum _ (fun a _ => hM.mul_mul_conjTranspose_same (K a))

omit [DecidableEq D] in

theorem trace_kraus (K : E → Matrix D D ℂ) (M : Matrix D D ℂ) :
    (kraus K M).trace = ((∑ a, (K a)ᴴ * K a) * M).trace := by
  simp only [kraus, Matrix.trace_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.trace_mul_cycle]

theorem trace_kraus_of_complete (K : E → Matrix D D ℂ)
    (hK : ∑ a, (K a)ᴴ * K a = 1) (M : Matrix D D ℂ) :
    (kraus K M).trace = M.trace := by
  rw [trace_kraus, hK, one_mul]

omit [DecidableEq D] in

theorem kraus_preserves (K : E → Matrix D D ℂ) (Q M : Matrix D D ℂ)
    (hcomm : ∀ a, Q * K a = K a * Q) (hM : Q * M = 0) :
    Q * kraus K M = 0 := by
  simp only [kraus, Matrix.mul_sum]
  apply Finset.sum_eq_zero
  intro a _
  calc Q * (K a * M * (K a)ᴴ) = (Q * K a) * M * (K a)ᴴ := by noncomm_ring
       _ = (K a * Q) * M * (K a)ᴴ := by rw [hcomm a]
       _ = K a * (Q * M) * (K a)ᴴ := by noncomm_ring
       _ = 0 := by rw [hM]; simp

structure Projector (D : Type*) [Fintype D] [DecidableEq D] where

  val : Matrix D D ℂ

  hermitian : val.IsHermitian

  idem : val * val = val

theorem projector_pos (P : Projector D) : P.val.PosSemidef := by
  simpa only [P.hermitian.eq, P.idem] using Matrix.posSemidef_self_mul_conjTranspose P.val

def outcome (P : Projector D) (b : Bool) : Matrix D D ℂ :=
  if b then P.val else 1 - P.val

theorem outcome_hermitian (P : Projector D) (b : Bool) : (outcome P b).IsHermitian := by
  cases b
  · exact Matrix.isHermitian_one.sub P.hermitian
  · exact P.hermitian

theorem outcome_idem (P : Projector D) (b : Bool) : outcome P b * outcome P b = outcome P b := by
  cases b
  · change (1 - P.val) * (1 - P.val) = 1 - P.val
    noncomm_ring [P.idem]
  · exact P.idem

theorem outcome_complete (P : Projector D) :
    ∑ b : Bool, (outcome P b)ᴴ * outcome P b = 1 := by
  simp only [Fintype.sum_bool]
  rw [(outcome_hermitian P true).eq, (outcome_hermitian P false).eq,
    outcome_idem, outcome_idem]
  simp [outcome]

def branch (P : Projector D) (b : Bool) (M : Matrix D D ℂ) : Matrix D D ℂ :=
  outcome P b * M * (outcome P b)ᴴ

theorem branch_pos (P : Projector D) (b : Bool) {M : Matrix D D ℂ} (hM : M.PosSemidef) :
    (branch P b M).PosSemidef := hM.mul_mul_conjTranspose_same _

theorem branch_trace_sum (P : Projector D) (M : Matrix D D ℂ) :
    (branch P false M).trace + (branch P true M).trace = M.trace := by
  have h := trace_kraus_of_complete (outcome P) (outcome_complete P) M
  simpa [kraus, branch, Fintype.sum_bool, add_comm] using h

theorem branch_mass_nonneg (P : Projector D) (b : Bool) {M : Matrix D D ℂ}
    (hM : M.PosSemidef) : 0 ≤ (branch P b M).trace.re :=
  (Complex.nonneg_iff.mp (branch_pos P b hM).trace_nonneg).1

theorem branch_mass_le (P : Projector D) (b : Bool) {M : Matrix D D ℂ}
    (hM : M.PosSemidef) : (branch P b M).trace.re ≤ M.trace.re := by
  have h := congrArg Complex.re (branch_trace_sum P M)
  simp only [Complex.add_re] at h
  cases b <;> linarith [branch_mass_nonneg P false hM, branch_mass_nonneg P true hM]

theorem branch_zero_satisfies (P : Projector D) (M : Matrix D D ℂ) :
    P.val * branch P false M = 0 := by
  have h : P.val * (1 - P.val) = 0 := by rw [mul_sub, mul_one, P.idem, sub_self]
  simp only [branch, outcome, Bool.false_eq_true, ↓reduceIte]
  calc P.val * ((1 - P.val) * M * (1 - P.val)ᴴ)
      = (P.val * (1 - P.val)) * M * (1 - P.val)ᴴ := by noncomm_ring
       _ = 0 := by rw [h]; simp

theorem branch_preserves (P : Projector D) (b : Bool) (Q M : Matrix D D ℂ)
    (hcomm : Q * P.val = P.val * Q) (hM : Q * M = 0) :
    Q * branch P b M = 0 := by
  have hc : Q * outcome P b = outcome P b * Q := by
    cases b
    · simp only [outcome, Bool.false_eq_true, ↓reduceIte, mul_sub, sub_mul, mul_one, one_mul]
      rw [hcomm]
    · exact hcomm
  calc Q * branch P b M = (Q * outcome P b) * M * (outcome P b)ᴴ := by
         simp only [branch]; noncomm_ring
       _ = (outcome P b * Q) * M * (outcome P b)ᴴ := by rw [hc]
       _ = outcome P b * (Q * M) * (outcome P b)ᴴ := by noncomm_ring
       _ = 0 := by rw [hM]; simp

end
end Qatlib.Foundations.MatrixAlgebra.ProjectiveFix
