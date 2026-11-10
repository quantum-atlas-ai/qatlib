/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GibbsMetropolis.RationalBath.RationalHeatBathChannel
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.FairRandomBits.RationalReject

open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.GibbsMetropolis.RationalBath
open Matrix
open scoped Classical BigOperators ComplexOrder ENNReal
set_option autoImplicit false
set_option linter.unusedVariables false

abbrev HeatBathSamplerRecord (N : ℕ) := ((Fin N × ℕ × ℕ) ⊕ (ℕ × ℕ)) × ℕ

def rationalHeatBathCoins {N : ℕ} (w : Fin N → ℕ) (R m : ℕ)
    (hist : Fin m → HeatBathSamplerRecord N) : ℕ := ∑ k, rejectionBits (hist k).1

def rationalHeatBathComparisons {N : ℕ} (w : Fin N → ℕ) (R m : ℕ)
    (hist : Fin m → HeatBathSamplerRecord N) : ℕ := ∑ k, rejectionComparisons (hist k).1

theorem rational_heat_bath_gibbs_integer_weight_identification :
    ∀ (N : ℕ) (hN : 0 < N) (w : Fin N → ℕ) (hW : 0 < weightTotal w),
      (∀ j, 0 < w j) → rationalHeatBathDensity w hW =
        diagonalGibbsDensity N hN (fun j => -Real.log (w j : ℝ)) 1 := by
  intro N hN w hW hw
  have hexp (j : Fin N) : Real.exp (-(1:ℝ) * -Real.log (w j : ℝ)) = (w j : ℝ) := by
    rw [neg_one_mul, neg_neg, Real.exp_log (by exact_mod_cast hw j)]
  have hpart : diagonalGibbsPartition N (fun j => -Real.log (w j : ℝ)) 1 =
      (weightTotal w : ℝ) := by
    simp only [diagonalGibbsPartition, hexp]
    simp [weightTotal]
  simp only [rationalHeatBathDensity, diagonalGibbsDensity, diagonalGibbsDist, hexp, hpart]

theorem rationalHeatBath_leaf_cost {N : ℕ} (c : Option (Fin N))
    (l : Fin (observedLeafCount (rationalHeatBathProgram c))) :
    (observedLeaf 1 (rationalHeatBathProgram c) l).queries = 0 ∧
    (observedLeaf 1 (rationalHeatBathProgram c) l).gates = 1 ∧
    (observedLeaf 1 (rationalHeatBathProgram c) l).measurements = 1 := by
  have hmem : observedLeaf 1 (rationalHeatBathProgram c) l ∈
      observedKrausLeaves 1 (rationalHeatBathProgram c) := List.get_mem _ _
  rw [rationalHeatBathLeaves] at hmem
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
  rw [← hi]
  exact ⟨rfl, rfl, rfl⟩

theorem rational_heat_bath_actual_leaf_and_classical_ledgers :
    ∀ (N R m : ℕ) (w : Fin N → ℕ) (hW : 0 < weightTotal w)
      (c : Option (Fin N)) (l : Fin (observedLeafCount (rationalHeatBathProgram c))),
      (observedLeaf 1 (rationalHeatBathProgram c) l).queries = 0 ∧
      (observedLeaf 1 (rationalHeatBathProgram c) l).gates = 1 ∧
      (observedLeaf 1 (rationalHeatBathProgram c) l).measurements = 1 ∧
      ∀ hist : Fin m → HeatBathSamplerRecord N,
        (∀ k, hist k ∈ (rationalRejectionRun w (Nat.clog 2 (weightTotal w)) R).support) →
        rationalHeatBathCoins w R m hist = (∑ k, rejectionBits (hist k).1) ∧
        rationalHeatBathComparisons w R m hist = (∑ k, rejectionComparisons (hist k).1) ∧
        rationalHeatBathCoins w R m hist ≤ m * Nat.clog 2 (weightTotal w) * R ∧
        rationalHeatBathComparisons w R m hist ≤ m * N * R := by
  intro N R m w hW c l
  have hc := rationalHeatBath_leaf_cost c l
  refine ⟨hc.1, hc.2.1, hc.2.2, ?_⟩
  intro hist hh
  have hb := (rational_effective_truncation_consumer N w R hW).2.2.2.2.2.2
  refine ⟨rfl, rfl, ?_, ?_⟩
  · calc _ ≤ ∑ _ : Fin m, Nat.clog 2 (weightTotal w) * R :=
        Finset.sum_le_sum (fun k _ => (hb (hist k) (hh k)).1)
      _ = _ := by simp [Nat.mul_assoc]
  · calc _ ≤ ∑ _ : Fin m, N * R :=
        Finset.sum_le_sum (fun k _ => (hb (hist k) (hh k)).2)
      _ = _ := by simp [Nat.mul_assoc]

theorem rationalHeatBath_expected_classical_costs {N : ℕ} (w : Fin N → ℕ)
    (hW : 0 < weightTotal w) (R : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalRejectionRun w (Nat.clog 2 (weightTotal w)) R)
      (fun z => (rejectionBits z.1 : ℝ≥0∞)) ≤ (2 * Nat.clog 2 (weightTotal w) : ℕ) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalRejectionRun w (Nat.clog 2 (weightTotal w)) R)
      (fun z => (rejectionComparisons z.1 : ℝ≥0∞)) ≤ (2*N : ℕ) := by
  have h := rational_effective_truncation_consumer N w R hW
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩

end Qatlib.Concepts.GibbsMetropolis.RationalBath
