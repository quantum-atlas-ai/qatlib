/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs

set_option autoImplicit false
set_option maxHeartbeats 400000

open Matrix Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
open scoped Classical BigOperators Matrix.Norms.L2Operator

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError

open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.TrotterFormula.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open scoped ComplexOrder

theorem l2_opNorm_one_le {I : Type} [Fintype I] [DecidableEq I] :
    ‖(1 : Matrix I I ℂ)‖ ≤ 1 :=
  l2_opNorm_le_of_mulVec_le zero_le_one (1 : Matrix I I ℂ) (fun v => by
    simp [Matrix.one_mulVec])

theorem l2_opNorm_pow_le {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (n : ℕ) : ‖A ^ n‖ ≤ ‖A‖ ^ n := by
  induction n with
  | zero => simpa using! l2_opNorm_one_le
  | succ n ih =>
    calc
      ‖A ^ (n + 1)‖ = ‖A * A ^ n‖ := by rw [pow_succ']
      _ ≤ ‖A‖ * ‖A ^ n‖ := Matrix.l2_opNorm_mul A (A ^ n)
      _ ≤ ‖A‖ * ‖A‖ ^ n := mul_le_mul_of_nonneg_left ih (norm_nonneg _)
      _ = ‖A‖ ^ (n + 1) := (pow_succ' _ _).symm

theorem multiplicativeDefect_one_add {I : Type} [Fintype I]
    (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (t : ℝ) :
    1 + multiplicativeDefect xs H t =
      orderedEvolution (fun τ => -(pfWordMultiplicativeField xs H τ)) 0 t := by
  unfold multiplicativeDefect
  abel

theorem suzuki_multiplicative_representation {I : Type} [Fintype I]
    (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (t : ℝ) :
    suzukiExponentialWord xs t =
      NormedSpace.exp (t • H) * (1 + multiplicativeDefect xs H t) := by
  have h := @pf_word_multiplicative_representation I _
    (fun a b => Classical.propDecidable (a = b)) xs H t
  rw [multiplicativeDefect_one_add]
  exact h

theorem exp_mul_inverse_cancel {I : Type} [Fintype I] (H : Matrix I I ℂ) (t : ℝ) :
    NormedSpace.exp (t • H) * Ring.inverse (NormedSpace.exp (t • H)) = 1 := by
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  exact Ring.mul_inverse_cancel _ (NormedSpace.isUnit_exp (t • H))

theorem segment_multiplicative_representation {I : Type} [Fintype I]
    (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (t : ℝ) (r : ℕ) :
    (segmentWord xs t r).prod =
      NormedSpace.exp (t • H) * (1 + segmentMultiplicativeDefect xs H t r) := by
  have hcancel := exp_mul_inverse_cancel H t
  have hkey : NormedSpace.exp (t • H) *
      (1 + segmentMultiplicativeDefect xs H t r) = (segmentWord xs t r).prod := by
    unfold segmentMultiplicativeDefect
    have h1 : (1 : Matrix I I ℂ) +
        (Ring.inverse (NormedSpace.exp (t • H)) * (segmentWord xs t r).prod - 1) =
        Ring.inverse (NormedSpace.exp (t • H)) * (segmentWord xs t r).prod := by abel
    rw [h1, ← mul_assoc, hcancel, one_mul]
  exact hkey.symm

theorem inverse_stability_of_norm_le {I : Type} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (η : ℝ) (hM : ‖M‖ ≤ η) (hη : η < 1) :
    inversePropagationWindow η ∧
      ‖Ring.inverse (1 + M)‖ ≤ inverseStabilityFactor η := by
  refine ⟨hη, ?_⟩
  have hnorm : ‖M‖ < 1 := hM.trans_lt hη
  have hnm : ‖(-M : Matrix I I ℂ)‖ < 1 := by simpa using! hnorm
  have hsum : (∑' n : ℕ, (-M : Matrix I I ℂ) ^ n) = Ring.inverse (1 + M) := by
    have h := geom_series_eq_inverse (-M) hnm
    simpa using! h
  have hns : Summable fun n : ℕ => ‖((-M : Matrix I I ℂ) ^ n)‖ := by
    have hg : Summable fun n : ℕ => (‖(-M : Matrix I I ℂ)‖) ^ n :=
      summable_geometric_of_lt_one (norm_nonneg _) hnm
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hg
    calc
      ‖((-M : Matrix I I ℂ) ^ n)‖ ≤ ‖(-M : Matrix I I ℂ)‖ ^ n := l2_opNorm_pow_le _ _
      _ = (‖(-M : Matrix I I ℂ)‖) ^ n := rfl
  have hmg : Summable fun n : ℕ => (‖M‖ : ℝ) ^ n :=
    summable_geometric_of_lt_one (norm_nonneg _) hnorm
  calc
    ‖Ring.inverse (1 + M)‖ = ‖∑' n : ℕ, (-M : Matrix I I ℂ) ^ n‖ := by rw [← hsum]
    _ ≤ ∑' n : ℕ, ‖((-M : Matrix I I ℂ) ^ n)‖ := norm_tsum_le_tsum_norm hns
    _ ≤ ∑' n : ℕ, (‖M‖ : ℝ) ^ n :=
      hns.tsum_le_tsum (fun n => by
        calc
          ‖((-M : Matrix I I ℂ) ^ n)‖ ≤ ‖(-M : Matrix I I ℂ)‖ ^ n := l2_opNorm_pow_le _ _
          _ = (‖M‖ : ℝ) ^ n := by rw [norm_neg]) hmg
    _ = (1 - ‖M‖)⁻¹ := tsum_geometric_of_abs_lt_one (by simpa using! hnorm)
    _ ≤ (1 - η)⁻¹ := inv_anti₀ (by linarith) (by linarith)
    _ = inverseStabilityFactor η := rfl
open scoped ComplexOrder
open Set
set_option warningAsError false
variable {I : Type} [Fintype I] [DecidableEq I]
variable {I : Type} [Fintype I]
variable {S ι : Type} [Fintype S] [Fintype ι]

theorem segmentMultiplicativeDefect_eq_inverse_mul_sub
    (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (t : ℝ) (r : ℕ) :
    segmentMultiplicativeDefect xs H t r =
      Ring.inverse (NormedSpace.exp (t • H)) *
        ((segmentWord xs t r).prod - NormedSpace.exp (t • H)) := by
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hmul : Ring.inverse (NormedSpace.exp (t • H)) * NormedSpace.exp (t • H) = 1 :=
    Ring.inverse_mul_cancel _ (NormedSpace.isUnit_exp (t • H))
  unfold segmentMultiplicativeDefect
  rw [mul_sub, hmul]

theorem segmentMultiplicativeDefect_norm_le
    (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (p r : ℕ) (t : ℝ)
    (hp : 1 ≤ p) (hr : 0 < r)
    (hc : ∀ n ≤ p, suzukiSeries xs n = ((n.factorial : ℝ)⁻¹) • H ^ n) :
    ‖segmentMultiplicativeDefect xs H t r‖ ≤
      (p.factorial : ℝ) * pfCommAlphaSelf xs (p + 1) * |t| ^ (p + 1) /
        (((p + 1).factorial : ℝ) * (r : ℝ) ^ p) *
        Real.exp (4 * |t| * (suzukiMass xs + ‖H‖) + |t| * ‖H‖) := by
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hinv : Ring.inverse (NormedSpace.exp (t • H)) = NormedSpace.exp (-(t • H)) :=
    Ring.inverse_exp (t • H)
  have hnorm : ‖Ring.inverse (NormedSpace.exp (t • H))‖ ≤ Real.exp (|t| * ‖H‖) := by
    rw [hinv]
    simpa [neg_smul, abs_neg] using! pf_matrix_exp_norm_le H (-t)
  have hadd : ‖(segmentWord xs t r).prod - NormedSpace.exp (t • H)‖ ≤
      (p.factorial : ℝ) * pfCommAlphaSelf xs (p + 1) * |t| ^ (p + 1) /
        (((p + 1).factorial : ℝ) * (r : ℝ) ^ p) *
        Real.exp (4 * |t| * (suzukiMass xs + ‖H‖)) := by
    have hprod : (segmentWord xs t r).prod = suzukiExponentialWord xs (t / r) ^ r :=
      pf_segment_word_prod xs t r
    rw [hprod]
    exact @pf_matched_word_segmented_general I _
      (fun a b => Classical.propDecidable (a = b)) xs H p r t hp hr hc
  rw [segmentMultiplicativeDefect_eq_inverse_mul_sub]
  calc
    ‖Ring.inverse (NormedSpace.exp (t • H)) *
        ((segmentWord xs t r).prod - NormedSpace.exp (t • H))‖ ≤
        ‖Ring.inverse (NormedSpace.exp (t • H))‖ *
          ‖(segmentWord xs t r).prod - NormedSpace.exp (t • H)‖ := norm_mul_le _ _
    _ ≤ Real.exp (|t| * ‖H‖) *
          ((p.factorial : ℝ) * pfCommAlphaSelf xs (p + 1) * |t| ^ (p + 1) /
            (((p + 1).factorial : ℝ) * (r : ℝ) ^ p) *
            Real.exp (4 * |t| * (suzukiMass xs + ‖H‖))) :=
      mul_le_mul hnorm hadd (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_add]; ring

theorem clause22_leading_coeff_pair {I : Type} [Fintype I] [DecidableEq I] (X Y : Matrix I I ℂ) :
    suzukiSeries [X, Y] 2 - (((2:ℕ).factorial : ℝ)⁻¹) • (X + Y) ^ 2 =
      (1 / 2 : ℝ) • pfComm X Y := by
  have h1 : suzukiSeries ([] : List (Matrix I I ℂ)) 1 = 0 := suzukiSeries_nil_succ 0
  have h2 : suzukiSeries ([] : List (Matrix I I ℂ)) 2 = 0 := suzukiSeries_nil_succ 1
  have hs : suzukiSeries [X, Y] 2 = (1 / 2 : ℝ) • Y ^ 2 + X * Y + (1 / 2 : ℝ) • X ^ 2 := by
    rw [suzukiSeries_cons_two, suzukiSeries_cons_one, suzukiSeries_cons_two, h2, h1]
    simp only [mul_zero, add_zero, zero_add]
  rw [hs]
  have hfact : (((2:ℕ).factorial : ℝ)⁻¹) = (1 / 2 : ℝ) := by norm_num
  rw [hfact]
  simp only [pow_two, add_mul, mul_add, pfComm, smul_add, smul_sub]
  module

theorem clause22_pair_word_comm (X Y : Matrix I I ℂ) :
    pfNestedCommList (pfChosenList [X, Y] ![0, 1]) = pfComm Y X ∧
      pfNestedCommList (pfChosenList [X, Y] ![1, 0]) = pfComm X Y := ⟨rfl, rfl⟩

theorem clause22_leading_budget_pair {I : Type} [Fintype I] [DecidableEq I] (X Y : Matrix I I ℂ) :
    ‖(1 / 2 : ℝ) • pfComm X Y‖ ≤ pfCommAlphaSelf [X, Y] 2 / 2 := by
  have hne : (![0, 1] : Fin 2 → Fin 2) ≠ ![1, 0] := by
    intro h
    have := congrFun h 0
    simp at this
  have hsub : ({![0, 1], ![1, 0]} : Finset (Fin 2 → Fin 2)) ⊆ Finset.univ :=
    fun i _ => Finset.mem_univ _
  obtain ⟨hw1, hw2⟩ := clause22_pair_word_comm X Y
  have hneg : ‖pfComm Y X‖ = ‖pfComm X Y‖ := by
    have h : pfComm Y X = -pfComm X Y := by
      simp only [pfComm]
      abel
    rw [h, norm_neg]
  have h2 : 2 * ‖pfComm X Y‖ ≤ pfCommAlphaSelf [X, Y] 2 := by
    have key : ∑ i ∈ ({![0, 1], ![1, 0]} : Finset (Fin 2 → Fin 2)),
        ‖pfNestedCommList (pfChosenList [X, Y] i)‖ = 2 * ‖pfComm X Y‖ := by
      rw [Finset.sum_pair hne, hw1, hw2, hneg]
      ring
    rw [← key]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => norm_nonneg _
  have hα : (0:ℝ) ≤ pfCommAlphaSelf [X, Y] 2 := by
    simp only [pfCommAlphaSelf]
    exact Finset.sum_nonneg fun i _ => norm_nonneg _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
  linarith [h2, hα]
end Qatlib.Concepts.TrotterFormula.GeneralOrder
