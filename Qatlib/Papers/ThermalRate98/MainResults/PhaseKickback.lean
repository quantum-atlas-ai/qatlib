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

/-!
# Binary phases and clean phase circuits

This module implements weighted binary phases and reversible evaluation on a finite ancillary
register for the phase construction of [LidarWang1999]. `bitPhaseGate_product` factors the phase
into one contribution per bit, and `signedBinary_phase_law` specializes this identity to powers
of two with an integer scaling exponent.

The circuit `cleanPhaseWord` evaluates a function, applies an ancillary phase, and reverses the
evaluation. Its action on a zero ancillary input restores that input while applying the desired
phase.

## Main statements

* `signedBinary_phase_law`: factors the fixed precision binary phase.
* `cleanPhaseWord_run`: proves phase application with the ancillary register restored to zero.
* `cleanPhaseWord_resources`: records unitarity, three abstract gates, and zero oracle queries.

## References

* [Lidar and Wang, 1999][LidarWang1999]
-/

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

/-- The sum of the weights selected by the true bits of a Boolean register. -/
def bitValue (w : Fin m → ℝ) (b : Fin m → Bool) : ℝ :=
  ∑ l, if b l then w l else 0

/-- The diagonal gate assigning to each bit string the phase exponential of its weighted bit
value. -/
def bitPhaseGate (w : Fin m → ℝ) : Matrix (Fin m → Bool) (Fin m → Bool) ℂ :=
  Matrix.diagonal (fun b => Complex.exp (Complex.I * (bitValue w b : ℂ)))

/-- On a basis ket, the weighted bit phase gate has the phase exponential at that basis index
and zero amplitudes elsewhere. See [LidarWang1999]. -/
theorem bitPhaseGate_apply (w : Fin m → ℝ) (b : Fin m → Bool) :
    bitPhaseGate w *ᵥ (Ket b : QState (Fin m → Bool)) =
      fun b' => if b' = b then Complex.exp (Complex.I * (bitValue w b : ℂ)) else 0 := by
  funext b'
  simp only [bitPhaseGate, Matrix.mulVec, dotProduct, Matrix.diagonal, Ket]
  rw [Finset.sum_eq_single b]
  · by_cases h : b' = b <;> simp [h]
  · intro k _ hk; simp [hk]
  · intro h; exact absurd (Finset.mem_univ b) h

/-- The exponential of a weighted bit value factors into the product of the phases selected by
its true bits. See [LidarWang1999]. -/
theorem bitPhaseGate_product (w : Fin m → ℝ) (b : Fin m → Bool) :
    Complex.exp (Complex.I * (bitValue w b : ℂ)) =
      ∏ l, (if b l then Complex.exp (Complex.I * (w l : ℂ)) else 1) := by
  unfold bitValue
  simp only [Complex.ofReal_sum]
  rw [Finset.mul_sum, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro l _
  by_cases h : b l <;> simp [h]

/-- The weighted bit phase gate is unitary. See [LidarWang1999]. -/
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

/-- The sum of `2^(l - k)` over the true bits at positions `l`, with integer scaling exponent
`k`. -/
def signedBinaryValue (m : ℕ) (k : ℤ) (b : Fin m → Bool) : ℝ :=
  ∑ l, if b l then (2 : ℝ) ^ ((l : ℤ) - k) else 0

/-- The phase of the scaled binary value factors into a product of powers-of-two phases selected
by the true bits. See [LidarWang1999]. -/
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

/-- The reversible evaluation map sending `(a, b)` to `(a, b + X a)`. -/
def evalMap (X : α → β) (p : α × β) : α × β := (p.1, p.2 + X p.1)

/-- The inverse evaluation map sending `(a, b)` to `(a, b - X a)`. -/
def evalMapInv (X : α → β) (p : α × β) : α × β := (p.1, p.2 - X p.1)

/-- Adding the function value to the ancillary coordinate defines a bijection. -/
theorem evalMap_bijective (X : α → β) : Function.Bijective (evalMap X) := by
  constructor
  · intro p q h
    simp only [evalMap, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    exact Prod.ext h1 (by rw [h1] at h2; exact add_right_cancel h2)
  · intro q
    exact ⟨(q.1, q.2 - X q.1), by simp [evalMap]⟩

/-- The permutation matrix implementing addition of `X a` to the ancillary coordinate. -/
def evalPerm (X : α → β) : Matrix (α × β) (α × β) ℂ :=
  fun i j => if i = evalMap X j then 1 else 0

/-- The permutation matrix implementing subtraction of `X a` from the ancillary coordinate. -/
def evalPermInv (X : α → β) : Matrix (α × β) (α × β) ℂ :=
  fun i j => if i = evalMapInv X j then 1 else 0

/-- The evaluation permutation sends a basis ket to the ket indexed by `evalMap X`. -/
theorem evalPerm_apply (X : α → β) (p : α × β) :
    evalPerm X *ᵥ (Ket p : QState (α × β)) = Ket (evalMap X p) := by
  funext i
  simp only [evalPerm, Matrix.mulVec, dotProduct, Ket, evalMap]
  rw [Finset.sum_eq_single p]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ p) h

/-- The inverse evaluation permutation sends a basis ket to the ket indexed by `evalMapInv X`. -/
theorem evalPermInv_apply (X : α → β) (p : α × β) :
    evalPermInv X *ᵥ (Ket p : QState (α × β)) = Ket (evalMapInv X p) := by
  funext i
  simp only [evalPermInv, Matrix.mulVec, dotProduct, Ket, evalMapInv]
  rw [Finset.sum_eq_single p]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ p) h

/-- The evaluation permutation matrix is unitary. -/
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

/-- Subtracting `X` from the ancillary coordinate is the evaluation map associated with the
pointwise negative of `X`. -/
theorem evalMapInv_eq (X : α → β) :
    evalMapInv X = evalMap (fun a => -X a) := by
  funext p
  simp [evalMapInv, evalMap, sub_eq_add_neg]

/-- The inverse evaluation permutation matrix equals the evaluation permutation matrix for the
pointwise negative of `X`. -/
theorem evalPermInv_eq (X : α → β) :
    evalPermInv X = evalPerm (fun a => -X a) := by
  unfold evalPermInv evalPerm
  rw [evalMapInv_eq]

/-- The inverse evaluation permutation matrix is unitary. -/
theorem evalPermInv_unitary (X : α → β) :
    evalPermInv X ∈ Matrix.unitaryGroup (α × β) ℂ := by
  rw [evalPermInv_eq]
  exact evalPerm_unitary _

/-- The diagonal gate whose phase depends only on the ancillary coordinate through `val`. -/
def appPhase (val : β → ℝ) : Matrix (α × β) (α × β) ℂ :=
  Matrix.diagonal (fun p => Complex.exp (Complex.I * (val p.2 : ℂ)))

/-- The ancillary phase gate multiplies a basis ket by the exponential of `i` times the value of
its ancillary coordinate. -/
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

/-- The ancillary phase gate is unitary. -/
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

/-- The three-gate circuit that evaluates `X` into the ancillary register, applies `appPhase
val`, and reverses the evaluation. -/
def cleanPhaseWord (X : α → β) (val : β → ℝ) : Circuit (α × β) :=
  [Step.gate (evalPerm X), Step.gate (appPhase val), Step.gate (evalPermInv X)]

/-- On input `(a, 0)`, the clean phase circuit applies the phase `exp (i * val (X a))` and
restores the ancillary register to zero. See [LidarWang1999]. -/
theorem cleanPhaseWord_run (X : α → β) (val : β → ℝ) (a : α) :
    Run 1 (cleanPhaseWord X val) (Ket (a, 0)) =
      (Complex.exp (Complex.I * (val (X a) : ℂ))) • Ket (a, 0) := by
  simp only [cleanPhaseWord, Run, ApplyGate, List.cons.injEq, and_true, List.nil_eq]
  rw [evalPerm_apply, appPhase_apply, Matrix.mulVec_smul, evalPermInv_apply]
  simp [evalMap, evalMapInv, add_comm]

/-- The clean phase circuit is unitary and contains three abstract gates and zero oracle
queries. See [LidarWang1999]. -/
theorem cleanPhaseWord_resources (X : α → β) (val : β → ℝ) :
    IsUnitaryCircuit (cleanPhaseWord X val) ∧
      GateCount (cleanPhaseWord X val) = 3 ∧ QueryCount (cleanPhaseWord X val) = 0 := by
  refine ⟨?_, rfl, rfl⟩
  simp only [cleanPhaseWord, isUnitaryCircuit_gate, isUnitaryCircuit_nil, and_true]
  exact ⟨evalPerm_unitary X, appPhase_unitary val, evalPermInv_unitary X⟩

end CleanPhase

end Qatlib.Papers.ThermalRate98.MainResults
