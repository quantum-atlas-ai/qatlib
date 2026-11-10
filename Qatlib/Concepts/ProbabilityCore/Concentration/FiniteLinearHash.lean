/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.FiniteLinearHashData
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace Qatlib.Concepts.ProbabilityCore.Concentration

open scoped BigOperators

private theorem uniform_hom_fiber_average
    {G Y : Type} [AddGroup G] [Fintype G] [AddMonoid Y] [Fintype Y]
    [DecidableEq Y] (f : G →+ Y) (hsurj : Function.Surjective f) (y : Y) :
    finiteHashAverage (fun g : G => if f g = y then 1 else 0) =
      (Fintype.card Y : ℝ)⁻¹ := by
  classical
  let c : ℕ := (Finset.univ.filter (fun g : G => f g = y)).card
  have hcount (a : Y) :
      (Finset.univ.filter (fun g : G => f g = a)).card = c := by
    dsimp only [c]
    exact AddMonoidHom.card_fiber_eq_of_mem_range f (hsurj a) (hsurj y)
  have htotalNat : Fintype.card G = Fintype.card Y * c := by
    calc
      Fintype.card G =
          ∑ a : Y, (Finset.univ.filter (fun g : G => f g = a)).card := by
        simpa only [Finset.card_univ] using
          (Finset.card_eq_sum_card_fiberwise
            (s := (Finset.univ : Finset G)) (t := (Finset.univ : Finset Y))
            (f := fun g => f g) (by
              intro g _
              exact Finset.mem_univ (f g)))
      _ = Fintype.card Y * c := by
        simp only [hcount, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
  have htotal : (Fintype.card G : ℝ) = (Fintype.card Y : ℝ) * (c : ℝ) := by
    exact_mod_cast htotalNat
  have hG : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  have hY : (Fintype.card Y : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Y ≠ 0)
  unfold finiteHashAverage
  rw [Finset.sum_boole]
  change (Fintype.card G : ℝ)⁻¹ * (c : ℝ) = (Fintype.card Y : ℝ)⁻¹
  field_simp [hG, hY]
  nlinarith [htotal]

theorem finite_linear_matrix_hash_collision
    (K I J : Type) [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (v w : I → K) (hvw : v ≠ w) :
    finiteHashAverage (fun A : Matrix I J K =>
      if finiteLinearMatrixHash A v = finiteLinearMatrixHash A w then 1 else 0) =
        (Fintype.card (J → K) : ℝ)⁻¹ := by
  classical
  have hd : v - w ≠ 0 := sub_ne_zero.mpr hvw
  obtain ⟨i₀, hi₀⟩ : ∃ i : I, (v - w) i ≠ 0 := by
    by_contra h
    push Not at h
    exact hd (funext h)
  let F : Matrix I J K →+ (J → K) :=
    (Matrix.mulVec.addMonoidHomLeft (v - w)).comp
      (Matrix.transposeAddEquiv I J K).toAddMonoidHom
  have hsurj : Function.Surjective F := by
    intro y
    refine ⟨fun i j => if i = i₀ then y j / (v - w) i₀ else 0, ?_⟩
    change finiteLinearMatrixHash
      (fun i j => if i = i₀ then y j / (v - w) i₀ else 0) (v - w) = y
    funext j
    simp only [finiteLinearMatrixHash, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    exact div_mul_cancel₀ (y j) hi₀
  have hdiff (A : Matrix I J K) :
      finiteLinearMatrixHash A v - finiteLinearMatrixHash A w = F A := by
    change Matrix.mulVec A.transpose v - Matrix.mulVec A.transpose w =
      Matrix.mulVec A.transpose (v - w)
    exact (Matrix.mulVec_sub A.transpose v w).symm
  have hevent (A : Matrix I J K) :
      (finiteLinearMatrixHash A v = finiteLinearMatrixHash A w) ↔ F A = 0 := by
    rw [← hdiff A, sub_eq_zero]
  calc
    _ = finiteHashAverage (fun A : Matrix I J K => if F A = 0 then 1 else 0) := by
      congr 1
      funext A
      simp only [hevent A]
    _ = _ := uniform_hom_fiber_average F hsurj 0

end Qatlib.Concepts.ProbabilityCore.Concentration
