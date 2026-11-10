/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Pow
set_option autoImplicit false
open scoped BigOperators
open Matrix
namespace Qatlib.Foundations.MatrixAlgebra.PhaseUnitary

theorem diagonal_unitary {I : Type*} [Fintype I] [DecidableEq I] (d : I → ℂ) (hd : ∀ i, ‖d i‖=1) :
    diagonal d ∈ unitaryGroup I ℂ := by
  rw [mem_unitaryGroup_iff',star_eq_conjTranspose,diagonal_conjTranspose,diagonal_mul_diagonal]
  ext i j
  by_cases h:i=j
  · subst j
    simp only [diagonal_apply_eq,one_apply_eq]
    have hn : Complex.normSq (d i)=1 := by rw [Complex.normSq_eq_norm_sq,hd i];norm_num
    change star (d i) * d i = 1
    rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, hn]
    norm_num
  · simp [h]

theorem exp_phase_norm (t : ℝ) : ‖Complex.exp ((t:ℂ)*Complex.I)‖=1 := by
  simp [Complex.norm_exp]

theorem real_phase_unitary {I : Type*} [Fintype I] [DecidableEq I] (p : I → ℝ) :
    Matrix.diagonal (fun i=>Complex.exp ((p i:ℂ)*Complex.I)) ∈ Matrix.unitaryGroup I ℂ :=
  diagonal_unitary _ (fun i=>exp_phase_norm (p i))
end Qatlib.Foundations.MatrixAlgebra.PhaseUnitary
