/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMetropolis11.AcceptanceCoin.CoherentInstrumentSubgoalStat
set_option warningAsError false

open Qatlib.Concepts.WalkSearch.TwoLevelLower

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.QMetropolis11.AcceptanceCoin
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GibbsMetropolis.RationalBath

theorem metropolisControlledCoin_apply {D : ℕ} (E : Fin D → ℝ) (β : ℝ)
    (ψ : QState (Fin D × Fin D × Fin D × Fin 2)) (p : Fin D × Fin D × Fin D × Fin 2) :
    ApplyGate (metropolisControlledCoin E β) ψ p =
      ∑ c : Fin 2, MetropolisCoin (thermalAcceptance E β p.2.1 p.2.2.1) p.2.2.2 c *
        ψ (p.1, p.2.1, p.2.2.1, c) := by
  classical
  rcases p with ⟨a, b, c, q⟩
  simp only [ApplyGate, Matrix.mulVec, dotProduct, metropolisControlledCoin,
    Matrix.of_apply, Fintype.sum_prod_type]
  simp_rw [ite_and, ite_mul, zero_mul]
  simp

theorem metropolisControlledCoin_unitary {D : ℕ} (E : Fin D → ℝ) (β : ℝ) :
    metropolisControlledCoin E β ∈ Matrix.unitaryGroup _ ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext p p'
  rcases p with ⟨a, b, c, q⟩
  rcases p' with ⟨a', b', c', q'⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, metropolisControlledCoin,
    Matrix.of_apply, Fintype.sum_prod_type]
  simp only [apply_ite (star : ℂ → ℂ), star_zero, ite_and, ite_mul, zero_mul]
  by_cases ha : a = a'
  · subst a'
    by_cases hb : b = b'
    · subst b'
      by_cases hc : c = c'
      · subst c'
        have hu := metropolisCoin_unitary (thermalAcceptance_pos E β b c).le
          (thermalAcceptance_le_one E β b c)
        have he := congrFun (congrFun
          ((Matrix.mem_unitaryGroup_iff').mp hu) q) q'
        simpa [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.one_apply, eq_comm] using he
      · simp [hc, eq_comm]
    · simp [hb, eq_comm]
  · simp [ha, eq_comm]

theorem metropolisControlledCoin_coherent_state {D : ℕ} (E : Fin D → ℝ) (β : ℝ)
    (i : Fin D) (x : Fin D → ℂ) :
    ApplyGate (metropolisControlledCoin E β) (coherentEnergySuperposition i x) =
      fun p : Fin D × Fin D × Fin D × Fin 2 =>
        if p.2.1 = i ∧ p.1 = p.2.2.1 then
          if p.2.2.2 = 1 then x p.1 * (Real.sqrt (thermalAcceptance E β i p.1) : ℂ)
          else x p.1 * (Real.sqrt (1 - thermalAcceptance E β i p.1) : ℂ)
        else 0 := by
  classical
  funext p
  rcases p with ⟨a, b, c, q⟩
  rw [metropolisControlledCoin_apply]
  by_cases hb : b = i
  · subst b
    by_cases hc : a = c
    · subst c
      fin_cases q <;> simp [coherentEnergySuperposition, MetropolisCoin, mul_comm]
    · simp [coherentEnergySuperposition, hc]
  · simp [coherentEnergySuperposition, hb]

theorem metropolisControlledCoin_accept_mass {D : ℕ} (E : Fin D → ℝ) (β : ℝ)
    (i : Fin D) (x : Fin D → ℂ) :
    MeasureProb (ApplyGate (metropolisControlledCoin E β) (coherentEnergySuperposition i x))
      (Finset.univ.filter (fun p : Fin D × Fin D × Fin D × Fin 2 => p.2.2.2 = 1)) =
      ∑ k, ‖x k‖ ^ 2 * thermalAcceptance E β i k := by
  classical
  rw [metropolisControlledCoin_coherent_state]
  unfold MeasureProb
  rw [Finset.sum_filter]
  simp only [BornProb, Fintype.sum_prod_type]
  simp_rw [apply_ite (fun z : ℂ => ‖z‖), norm_zero, ite_pow,
    zero_pow (by decide : 2 ≠ 0)]
  simp [ite_and]
  apply Finset.sum_congr rfl
  intro k _
  rw [abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (thermalAcceptance_pos E β i k).le]

theorem coherentInstrumentSubgoal : CoherentInstrumentSubgoal := by
  intro D E β i x _
  exact ⟨metropolisControlledCoin_unitary E β,
    metropolisControlledCoin_coherent_state E β i x,
    metropolisControlledCoin_accept_mass E β i x⟩

end Qatlib.Papers.QMetropolis11.AcceptanceCoin
