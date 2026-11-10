/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Set.Defs
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JonesPolyShor07.MainResults.Definitions

open Matrix

def SpecialUnitary (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {U | U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ U.det = 1}

@[simp] theorem mem_specialUnitary {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ} :
    U ∈ SpecialUnitary n ↔ U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ U.det = 1 := Iff.rfl

theorem one_mem_specialUnitary (n : ℕ) :
    (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SpecialUnitary n := by
  refine ⟨?_, ?_⟩
  · exact Submonoid.one_mem _
  · simp

theorem mul_mem_specialUnitary {n : ℕ} {U V : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ SpecialUnitary n) (hV : V ∈ SpecialUnitary n) : U * V ∈ SpecialUnitary n := by
  refine ⟨Submonoid.mul_mem _ hU.1 hV.1, ?_⟩
  rw [Matrix.det_mul, hU.2, hV.2, mul_one]

theorem specialUnitary_subset_unitary (n : ℕ) :
    SpecialUnitary n ⊆ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) :=
  fun _ hU => hU.1

def PhaseDenseOn (α : Type) [Fintype α] [DecidableEq α]
    (S : Set (Matrix α α ℂ)) : Prop :=
  ∀ U ∈ Matrix.unitaryGroup α ℂ, ∀ ε : ℝ, 0 < ε →
    ∃ g ∈ (Submonoid.closure S : Set (Matrix α α ℂ)), ∃ μ : ℂ, ‖μ‖ = 1 ∧
      ∀ i j, ‖g i j - μ * U i j‖ < ε

abbrev PhaseDense (n : ℕ) (S : Set (Matrix (Fin n) (Fin n) ℂ)) : Prop :=
  PhaseDenseOn (Fin n) S

theorem phaseDenseOn_mono {α : Type} [Fintype α] [DecidableEq α]
    {S T : Set (Matrix α α ℂ)} (hST : S ⊆ T) (h : PhaseDenseOn α S) : PhaseDenseOn α T := by
  intro U hU ε hε
  obtain ⟨g, hg, μ, hμ, hclose⟩ := h U hU ε hε
  exact ⟨g, Submonoid.closure_mono hST hg, μ, hμ, hclose⟩

theorem phaseDenseOn_of_subsingleton {α : Type} [Fintype α] [DecidableEq α]
    [Subsingleton α] (S : Set (Matrix α α ℂ)) : PhaseDenseOn α S := by
  intro U hU ε hε
  by_cases hα : Nonempty α
  · obtain ⟨a⟩ := hα
    have hU' : U * Uᴴ = (1 : Matrix α α ℂ) := Matrix.mem_unitaryGroup_iff.mp hU
    have hentry : (∑ k : α, U a k * star (U a k)) = 1 := by
      have h := congrFun (congrFun hU' a) a
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using h
    have hcollapse : (∑ k : α, U a k * star (U a k)) = U a a * star (U a a) := by
      refine Finset.sum_eq_single a ?_ ?_
      · intro b _ hb
        exact absurd (Subsingleton.elim b a) hb
      · intro ha
        exact absurd (Finset.mem_univ a) ha
    have hone : star (U a a) * U a a = 1 := by
      have h := hcollapse ▸ hentry
      rw [mul_comm]
      exact h
    have hnorm : ‖U a a‖ = 1 := by
      have h := congrArg norm hone
      rw [norm_mul, norm_star, norm_one] at h
      have h2 : ‖U a a‖ ^ 2 = 1 := by rw [pow_two]; exact h
      rcases sq_eq_one_iff.mp h2 with h1 | h1
      · exact h1
      · have hnn : (0 : ℝ) ≤ ‖U a a‖ := norm_nonneg _
        rw [h1] at hnn
        linarith
    have hnorm' : ‖star (U a a)‖ = 1 := by rw [norm_star]; exact hnorm
    refine ⟨1, Submonoid.one_mem _, star (U a a), hnorm', ?_⟩
    intro i j
    have hia : i = a := Subsingleton.elim i a
    have hja : j = a := Subsingleton.elim j a
    rw [hia, hja]
    have hd : (1 : Matrix α α ℂ) a a - star (U a a) * U a a = 0 := by
      rw [hone]
      simp
    rw [hd]
    simpa using hε
  · refine ⟨1, Submonoid.one_mem _, 1, by simp, ?_⟩
    intro i j
    exact absurd ⟨i⟩ hα

end Qatlib.Papers.JonesPolyShor07.MainResults.Definitions
