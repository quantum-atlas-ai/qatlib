/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Prod.Basic
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ThermalRate98.MainResults
open Matrix
open scoped BigOperators
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

section PhaseBits
variable {m : ℕ}

def bitValue (w : Fin m → ℝ) (b : Fin m → Bool) : ℝ :=
  ∑ l, if b l then w l else 0

def bitPhaseGate (w : Fin m → ℝ) : Matrix (Fin m → Bool) (Fin m → Bool) ℂ :=
  Matrix.diagonal (fun b => Complex.exp (Complex.I * (bitValue w b : ℂ)))

theorem bitPhaseGate_apply (w : Fin m → ℝ) (b : Fin m → Bool) :
    bitPhaseGate w *ᵥ (Ket b : QState (Fin m → Bool)) =
      fun b' => if b' = b then Complex.exp (Complex.I * (bitValue w b : ℂ)) else 0 := by
  funext b'
  simp only [bitPhaseGate, Matrix.mulVec, dotProduct, Matrix.diagonal, Ket]
  rw [Finset.sum_eq_single b]
  · by_cases h : b' = b <;> simp [h]
  · intro k _ hk; simp [hk]
  · intro h; exact absurd (Finset.mem_univ b) h

theorem bitPhaseGate_product (w : Fin m → ℝ) (b : Fin m → Bool) :
    Complex.exp (Complex.I * (bitValue w b : ℂ)) =
      ∏ l, (if b l then Complex.exp (Complex.I * (w l : ℂ)) else 1) := by
  unfold bitValue
  simp only [Complex.ofReal_sum]
  rw [Finset.mul_sum, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro l _
  by_cases h : b l <;> simp [h]

theorem bitPhaseGate_unitary (w : Fin m → ℝ) :
    bitPhaseGate w ∈ Matrix.unitaryGroup (Fin m → Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  unfold bitPhaseGate
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  have h1 : ∀ b : Fin m → Bool, star (Complex.exp (Complex.I * (bitValue w b : ℂ))) *
      Complex.exp (Complex.I * (bitValue w b : ℂ)) = 1 := by
    intro b
    have hc : star (Complex.exp (Complex.I * (bitValue w b : ℂ))) =
        Complex.exp (-(Complex.I * (bitValue w b : ℂ))) := by
      rw [Complex.star_def, ← Complex.exp_conj]
      congr 1
      simp
    rw [hc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  ext b j
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : b = j
  · subst h
    simpa using h1 b
  · simp [h]

def signedBinaryValue (m : ℕ) (k : ℤ) (b : Fin m → Bool) : ℝ :=
  ∑ l, if b l then (2 : ℝ) ^ ((l : ℤ) - k) else 0

theorem signedBinary_phase_law (m : ℕ) (k : ℤ) (b : Fin m → Bool) :
    Complex.exp (Complex.I * (signedBinaryValue m k b : ℂ)) =
      ∏ l : Fin m,
        (if b l then Complex.exp (Complex.I * (((2 : ℝ) ^ ((l : ℤ) - k) : ℝ) : ℂ)) else 1) := by
  simpa only [signedBinaryValue] using!
    bitPhaseGate_product (fun l : Fin m => (2 : ℝ) ^ ((l : ℤ) - k)) b

end PhaseBits

section CleanPhase
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [AddCommGroup β]

def evalMap (X : α → β) (p : α × β) : α × β := (p.1, p.2 + X p.1)

def evalMapInv (X : α → β) (p : α × β) : α × β := (p.1, p.2 - X p.1)

theorem evalMap_bijective (X : α → β) : Function.Bijective (evalMap X) := by
  constructor
  · intro p q h
    simp only [evalMap, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    exact Prod.ext h1 (by rw [h1] at h2; exact add_right_cancel h2)
  · intro q
    exact ⟨(q.1, q.2 - X q.1), by simp [evalMap]⟩

def evalPerm (X : α → β) : Matrix (α × β) (α × β) ℂ :=
  fun i j => if i = evalMap X j then 1 else 0

def evalPermInv (X : α → β) : Matrix (α × β) (α × β) ℂ :=
  fun i j => if i = evalMapInv X j then 1 else 0

theorem evalPerm_apply (X : α → β) (p : α × β) :
    evalPerm X *ᵥ (Ket p : QState (α × β)) = Ket (evalMap X p) := by
  funext i
  simp only [evalPerm, Matrix.mulVec, dotProduct, Ket, evalMap]
  rw [Finset.sum_eq_single p]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ p) h

theorem evalPermInv_apply (X : α → β) (p : α × β) :
    evalPermInv X *ᵥ (Ket p : QState (α × β)) = Ket (evalMapInv X p) := by
  funext i
  simp only [evalPermInv, Matrix.mulVec, dotProduct, Ket, evalMapInv]
  rw [Finset.sum_eq_single p]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ p) h

theorem evalPerm_unitary (X : α → β) :
    evalPerm X ∈ Matrix.unitaryGroup (α × β) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, evalPerm, Matrix.one_apply]
  obtain ⟨k0, hk0⟩ := (evalMap_bijective X).2 i
  rw [Finset.sum_eq_single k0]
  · by_cases hij : i = j <;> simp [hk0, hij, eq_comm]
  · intro k _ hk
    have hki : ¬ (i = evalMap X k) := by
      intro h
      exact hk ((evalMap_bijective X).1 (by rw [← h, hk0]))
    simp [hki]
  · intro h; exact absurd (Finset.mem_univ k0) h

theorem evalMapInv_eq (X : α → β) :
    evalMapInv X = evalMap (fun a => -X a) := by
  funext p
  simp [evalMapInv, evalMap, sub_eq_add_neg]

theorem evalPermInv_eq (X : α → β) :
    evalPermInv X = evalPerm (fun a => -X a) := by
  unfold evalPermInv evalPerm
  rw [evalMapInv_eq]

theorem evalPermInv_unitary (X : α → β) :
    evalPermInv X ∈ Matrix.unitaryGroup (α × β) ℂ := by
  rw [evalPermInv_eq]
  exact evalPerm_unitary _

def appPhase (val : β → ℝ) : Matrix (α × β) (α × β) ℂ :=
  Matrix.diagonal (fun p => Complex.exp (Complex.I * (val p.2 : ℂ)))

theorem appPhase_apply (val : β → ℝ) (p : α × β) :
    appPhase val *ᵥ (Ket p : QState (α × β)) =
      (Complex.exp (Complex.I * (val p.2 : ℂ))) • Ket p := by
  funext i
  simp only [appPhase, Matrix.mulVec, dotProduct, Matrix.diagonal, Ket,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single p]
  · by_cases h : i = p <;> simp [h]
  · intro k _ hk; simp [hk]
  · intro h; exact absurd (Finset.mem_univ p) h

theorem appPhase_unitary (val : β → ℝ) : appPhase val ∈ Matrix.unitaryGroup (α × β) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  unfold appPhase
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  have h1 : ∀ p : α × β, star (Complex.exp (Complex.I * (val p.2 : ℂ))) *
      Complex.exp (Complex.I * (val p.2 : ℂ)) = 1 := by
    intro p
    have hc : star (Complex.exp (Complex.I * (val p.2 : ℂ))) =
        Complex.exp (-(Complex.I * (val p.2 : ℂ))) := by
      rw [Complex.star_def, ← Complex.exp_conj]; congr 1; simp
    rw [hc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  ext p j
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : p = j
  · subst h
    simpa using h1 p
  · simp [h]

def cleanPhaseWord (X : α → β) (val : β → ℝ) : Circuit (α × β) :=
  [Step.gate (evalPerm X), Step.gate (appPhase val), Step.gate (evalPermInv X)]

theorem cleanPhaseWord_run (X : α → β) (val : β → ℝ) (a : α) :
    Run 1 (cleanPhaseWord X val) (Ket (a, 0)) =
      (Complex.exp (Complex.I * (val (X a) : ℂ))) • Ket (a, 0) := by
  simp only [cleanPhaseWord, Run, ApplyGate, List.cons.injEq, and_true, List.nil_eq]
  rw [evalPerm_apply, appPhase_apply, Matrix.mulVec_smul, evalPermInv_apply]
  simp [evalMap, evalMapInv, add_comm]

theorem cleanPhaseWord_resources (X : α → β) (val : β → ℝ) :
    IsUnitaryCircuit (cleanPhaseWord X val) ∧
      GateCount (cleanPhaseWord X val) = 3 ∧ QueryCount (cleanPhaseWord X val) = 0 := by
  refine ⟨?_, rfl, rfl⟩
  simp only [cleanPhaseWord, isUnitaryCircuit_gate, isUnitaryCircuit_nil, and_true]
  exact ⟨evalPerm_unitary X, appPhase_unitary val, evalPermInv_unitary X⟩

end CleanPhase

end Qatlib.Papers.ThermalRate98.MainResults
