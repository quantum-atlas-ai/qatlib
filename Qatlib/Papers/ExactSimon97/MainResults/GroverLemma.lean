/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Matrix

namespace Qatlib.Papers.ExactSimon97.MainResults

def psiVec (α β : ℂ) : Fin 2 → ℂ := ![α, β]

def phaseA : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, 1]

noncomputable def zeroRefl (α β : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Complex.I - 1) • Matrix.of (fun i j => psiVec α β i * psiVec α β j) + 1

noncomputable def groverOp (α β : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  zeroRefl α β * phaseA

lemma zeroRefl_mulVec (α β : ℂ) (v : Fin 2 → ℂ) :
    zeroRefl α β *ᵥ v =
      fun i => (Complex.I - 1) * (∑ j, psiVec α β j * v j) * psiVec α β i + v i := by
  funext i
  fin_cases i <;>
    simp [zeroRefl, psiVec, Matrix.mulVec, dotProduct,
      Matrix.add_apply, Matrix.one_apply, Matrix.of_apply,
      Fin.sum_univ_two] <;>
    ring

theorem lemma8_grover_output (α β : ℝ) (hαβ : α ^ 2 + β ^ 2 = 1) :
    groverOp (α : ℂ) (β : ℂ) *ᵥ psiVec (α : ℂ) (β : ℂ) =
      psiVec ((2 * Complex.I * (1 - ((α : ℂ) ^ 2)) - 1) * (α : ℂ))
        ((Complex.I * (1 - 2 * ((α : ℂ) ^ 2))) * (β : ℂ)) := by
  have hreal : ((β ^ 2 : ℝ) : ℂ) = ((1 - α ^ 2 : ℝ) : ℂ) := by
    rw [show β ^ 2 = 1 - α ^ 2 by linarith]
  have hβ2 : ((β : ℂ) ^ 2) = 1 - ((α : ℂ) ^ 2) := by
    have := hreal
    push_cast at this ⊢
    exact this

  have hphase : phaseA *ᵥ psiVec (α : ℂ) (β : ℂ) =
      ![Complex.I * (α : ℂ), (β : ℂ)] := by
    funext i
    fin_cases i <;>
      simp [phaseA, psiVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  calc groverOp (α : ℂ) (β : ℂ) *ᵥ psiVec (α : ℂ) (β : ℂ)
      = (zeroRefl (α : ℂ) (β : ℂ) * phaseA) *ᵥ psiVec (α : ℂ) (β : ℂ) := rfl
    _ = zeroRefl (α : ℂ) (β : ℂ) *ᵥ (phaseA *ᵥ psiVec (α : ℂ) (β : ℂ)) := by
          rw [← Matrix.mulVec_mulVec]
    _ = zeroRefl (α : ℂ) (β : ℂ) *ᵥ ![Complex.I * (α : ℂ), (β : ℂ)] := by rw [hphase]
    _ = (fun i => (Complex.I - 1) *
            (∑ j, psiVec (α : ℂ) (β : ℂ) j * ![Complex.I * (α : ℂ), (β : ℂ)] j) *
            psiVec (α : ℂ) (β : ℂ) i + ![Complex.I * (α : ℂ), (β : ℂ)] i) := by
          rw [zeroRefl_mulVec]
    _ = psiVec ((2 * Complex.I * (1 - ((α : ℂ) ^ 2)) - 1) * (α : ℂ))
          ((Complex.I * (1 - 2 * ((α : ℂ) ^ 2))) * (β : ℂ)) := by
          have hβ3 : ((β : ℂ) ^ 3) = (β : ℂ) * (1 - ((α : ℂ) ^ 2)) := by
            rw [show ((β : ℂ) ^ 3) = ((β : ℂ) ^ 2 * (β : ℂ)) by ring, hβ2]
            ring
          have hI2 : Complex.I ^ 2 = -1 := by
            rw [pow_two, Complex.I_mul_I]
          have hI3 : Complex.I ^ 3 = -Complex.I := by
            rw [show Complex.I ^ 3 = Complex.I ^ 2 * Complex.I by ring, hI2]
            ring
          funext i
          fin_cases i
          · simp [psiVec, Fin.sum_univ_two]
            ring_nf
            try rw [hβ2]
            try rw [hβ3]
            try rw [hI2]
            try rw [hI3]
            ring
          · simp [psiVec, Fin.sum_univ_two]
            ring_nf
            try rw [hβ2]
            try rw [hβ3]
            try rw [hI2]
            try rw [hI3]
            ring

theorem lemma8_amplitude_normalised (a : ℝ) (_ha : 0 ≤ a) (_ha1 : a ≤ 1) :
    (4 * (1 - a) ^ 2 + 1) * a + (1 - 2 * a) ^ 2 * (1 - a) = 1 := by
  ring

theorem lemma8_at_half (α β : ℝ) (_hαβ : α ^ 2 + β ^ 2 = 1) (hα : α ^ 2 = 1 / 2) :
    (2 * Complex.I * (1 - ((α : ℂ) ^ 2)) - 1) = Complex.I - 1 ∧
      (Complex.I * (1 - 2 * ((α : ℂ) ^ 2))) = 0 := by
  have hαC : ((α : ℂ) ^ 2) = ((1 / 2 : ℝ) : ℂ) := by
    exact_mod_cast hα
  rw [hαC]
  constructor <;> push_cast <;> ring

theorem lemma8_at_zero (α β : ℝ) (_hαβ : α ^ 2 + β ^ 2 = 1) (hα : α = 0) :
    (2 * Complex.I * (1 - ((α : ℂ) ^ 2)) - 1) * (α : ℂ) = 0 ∧
      (Complex.I * (1 - 2 * ((α : ℂ) ^ 2))) = Complex.I := by
  subst hα
  norm_num

end Qatlib.Papers.ExactSimon97.MainResults
