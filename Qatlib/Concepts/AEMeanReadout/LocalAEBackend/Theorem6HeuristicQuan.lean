/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem6HeuristicStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchQuan

/-!
# Quantum speedup of heuristic search

`bhmt_theorem6_heuristic` bounds the distributional quantum search cost by `400` times the
square root of the classical average-time quantity. The proof combines finite-horizon search
bounds with averaging, assuming every supported input has a successful seed, as in
[BrassardEtAl2002].

## Main statements

* `bhmt_theorem6_heuristic`: the distributional square-root cost bound.
* `bhmt_theorem6_heuristic_contract`: the packaged heuristic-search specification.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Qatlib
open scoped ENNReal

set_option maxHeartbeats 800000

/-- For positive `h` and `n`, rewrites `400 / sqrt (h / n)` as `400 * sqrt (n / h)`. -/
private theorem cost_flip {h n : ℕ} (hh : 0 < h) (hn : 0 < n) :
    (400:ℝ)/Real.sqrt (((h:ℝ))/((n:ℝ))) = 400 * Real.sqrt (((n:ℝ))/((h:ℝ))) := by
  have h0 : (0:ℝ) ≤ (h:ℝ) := Nat.cast_nonneg _
  have h1 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg _
  rw [Real.sqrt_div h0, Real.sqrt_div h1]
  have hhp : (0:ℝ) < Real.sqrt ((h:ℝ)) := Real.sqrt_pos.mpr (by exact_mod_cast hh)
  have hnp : (0:ℝ) < Real.sqrt ((n:ℝ)) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  field_simp

/-- For an input with at least one successful heuristic seed, the expected second search cost is
at most `400 * sqrt (n / heuristicGoodCount n G f)`. -/
private theorem per_instance_chi_cost {n : ℕ} (hn : 0 < n)
    (G : (Fin n → Bool) → Fin n → Fin n) (T : ℕ) (f : Fin n → Bool)
    (hf : 0 < BHMTTh6.heuristicGoodCount n G f) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
        (BHMTQSearch.qSearchLoop (QFTMatrix n) (qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n)
          (Finset.univ.filter (fun r => f (G f r) = true)) T 0)
        (fun out => (out.2.2 : ℝ≥0∞))
      ≤ ENNReal.ofReal
          (400 * Real.sqrt ((n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ))) := by
  have hmass := prepared_qft_mark_mass n hn (Finset.univ.filter (fun r => f (G f r) = true))
  have hpos : 0 < MeasureProb (preparedAAState (QFTMatrix n) (⟨0, hn⟩ : Fin n))
      (Finset.univ.filter (fun r => f (G f r) = true)) := by
    rw [hmass]
    exact div_pos (by exact_mod_cast hf) (by exact_mod_cast hn)
  have hcard : (Finset.univ.filter (fun r => f (G f r) = true)).card
      = BHMTTh6.heuristicGoodCount n G f := rfl
  have hG1 := BHMTQSearch.bhmt_theorem3_qsearch (Fin n) (QFTMatrix n)
    (qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n) (Finset.univ.filter (fun r => f (G f r) = true)) T
  have hE := (hG1.2.2 hpos).2
  rw [hmass, hcard, cost_flip hf hn] at hE
  exact hE

/-- If every supported input has a successful heuristic seed, the average quantum second-counter
cost is at most `400` times the square root of the classical average-time quantity [Brassard
et al., Theorem 6][BrassardEtAl2002]. -/
theorem bhmt_theorem6_heuristic : ∀ (n : ℕ) (hn : 0 < n) (G : (Fin n → Bool) → Fin n → Fin n)
    (D : PMF (Fin n → Bool)) (T : ℕ),
    (∀ f ∈ D.support, 0 < BHMTTh6.heuristicGoodCount n G f) →
    BHMTTh6.heuristicQuantumChiCost hn G D T ≤
      ENNReal.ofReal (400 * Real.sqrt (BHMTTh6.heuristicClassicalTime n G D)) := by
  intro n hn G D T hsupp
  simp only [BHMTTh6.heuristicQuantumChiCost]
  have hxnn : ∀ f : Fin n → Bool,
      (0:ℝ) ≤ (n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ) :=
    fun f => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hCS : ∑ f : Fin n → Bool, (D f).toReal
        * Real.sqrt ((n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ))
      ≤ Real.sqrt (BHMTTh6.heuristicClassicalTime n G D) := by
    have hsq := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (Finset.univ : Finset (Fin n → Bool))
      (r := fun f => (D f).toReal
        * Real.sqrt ((n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ)))
      (f := fun f => (D f).toReal)
      (g := fun f => (D f).toReal * ((n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ)))
      (fun f _ => ENNReal.toReal_nonneg)
      (fun f _ => mul_nonneg (ENNReal.toReal_nonneg) (hxnn f))
      (fun f _ => le_of_eq (by
        rw [mul_pow, Real.sq_sqrt (hxnn f)]
        ring))
    have h1 : ∑ f : Fin n → Bool, (D f).toReal = 1 := by
      rw [← ENNReal.toReal_sum (fun a _ => ne_of_lt
        (lt_of_le_of_lt (PMF.coe_le_one D a) (by norm_num)))]
      rw [show ∑ f : Fin n → Bool, (D f : ℝ≥0∞) = 1 from
        (hasSum_fintype (fun f => (D f : ℝ≥0∞))).unique (PMF.hasSum_coe_one D)]
      exact ENNReal.toReal_one
    have hT2 : (Real.sqrt (BHMTTh6.heuristicClassicalTime n G D))^2
        = BHMTTh6.heuristicClassicalTime n G D :=
      Real.sq_sqrt (Finset.sum_nonneg (fun f _ => mul_nonneg ENNReal.toReal_nonneg
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))))
    have hT : (∑ f : Fin n → Bool, (D f).toReal)
        * ∑ f : Fin n → Bool, (D f).toReal
            * ((n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ))
        = (Real.sqrt (BHMTTh6.heuristicClassicalTime n G D))^2 := by
      rw [h1, one_mul, hT2]
      rfl
    exact le_of_sq_le_sq (hsq.trans_eq hT) (Real.sqrt_nonneg _)
  have hsum1 : ∑ f : Fin n → Bool, (D f) * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
        (BHMTQSearch.qSearchLoop (QFTMatrix n) (qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n)
          (Finset.univ.filter (fun r => f (G f r) = true)) T 0)
        (fun out => (out.2.2 : ℝ≥0∞))
      ≤ ∑ f : Fin n → Bool, ENNReal.ofReal ((D f).toReal
          * (400 * Real.sqrt ((n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ)))) := by
    refine Finset.sum_le_sum (fun f _ => ?_)
    by_cases hmem : f ∈ D.support
    · have hE := per_instance_chi_cost hn G T f (hsupp f hmem)
      refine le_trans (mul_le_mul_right hE _) ?_
      have hDne : D f ≠ ⊤ := ne_of_lt
        (lt_of_le_of_lt (PMF.coe_le_one D f) (by norm_num))
      have hDeq : (D f) * ENNReal.ofReal
            (400 * Real.sqrt ((n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ)))
          = ENNReal.ofReal ((D f).toReal
              * (400 * Real.sqrt ((n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ)))) := by
        conv_lhs => rw [← ENNReal.ofReal_toReal hDne]
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      exact hDeq.le
    · have hz : D f = 0 := by
        by_contra hcon
        exact hmem ((PMF.mem_support_iff D f).mpr hcon)
      rw [hz, zero_mul]
      exact zero_le
  refine le_trans hsum1 ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg ENNReal.toReal_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))]
  refine ENNReal.ofReal_le_ofReal ?_
  have hre : ∀ f : Fin n → Bool, (D f).toReal
      * (400 * Real.sqrt ((n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ)))
      = 400 * ((D f).toReal
          * Real.sqrt ((n : ℝ) / ((BHMTTh6.heuristicGoodCount n G f : ℕ) : ℝ))) :=
    fun f => by ring
  rw [Finset.sum_congr rfl (fun f _ => hre f), ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hCS (by norm_num)

/-- Packages the distributional heuristic-search cost bound as `Theorem6HeuristicSpec.expected`. -/
theorem bhmt_theorem6_heuristic_contract :
    Theorem6HeuristicSpec.expected :=
  bhmt_theorem6_heuristic

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
