/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GibbsMetropolis.RationalBath.CountedRationalHeatBath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution

open Qatlib.Concepts.GibbsMetropolis.RationalBath

namespace Qatlib.Concepts.SamplingBackend.GibbsBackend
open Matrix
open scoped Classical BigOperators ComplexOrder ENNReal
set_option autoImplicit false

theorem rationalGibbs123_reject : rationalHeatBathReject (![1,2,3] : Fin 3 → ℕ) = 1/4 := by
  have ht : weightTotal (![1,2,3] : Fin 3 → ℕ) = 6 := by
    norm_num [weightTotal, Fin.sum_univ_succ]
  have hb : Nat.clog 2 6 = 3 := by decide
  norm_num [rationalHeatBathReject, rationalRejectMass, coinRejectMass, ht, hb]

theorem rationalGibbs123_density (hW : 0 < weightTotal (![1,2,3] : Fin 3 → ℕ)) :
    rationalHeatBathDensity (![1,2,3] : Fin 3 → ℕ) hW =
      Matrix.diagonal (![1/6,1/3,1/2] : Fin 3 → ℂ) := by
  unfold rationalHeatBathDensity
  congr 1
  funext i
  fin_cases i <;> norm_num [weightTotal, Fin.sum_univ_succ]

theorem rational_gibbs_non_power_two_actual_consumer :
    ∀ (m r : ℕ) (X : Matrix (Fin 3 × Fin r) (Fin 3 × Fin r) ℂ),
      0 < m → X.PosSemidef → let w := (![1,2,3] : Fin 3 → ℕ);
      ∀ hW : 0 < weightTotal w,
        rationalHeatBathReject w = 1/4 ∧
        rationalHeatBathDensity w hW = Matrix.diagonal (![1/6,1/3,1/2] : Fin 3 → ℂ) ∧
        Matrix.traceNorm (tensorLeft (rationalHeatBathPower w hW 1 m).map X -
          TensorGate (rationalHeatBathDensity w hW) (Matrix.traceLeft X)) ≤
            2 * (1/4:ℝ)^m * Matrix.traceNorm X := by
  intro m r X hm hX w hW
  refine ⟨rationalGibbs123_reject, rationalGibbs123_density hW, ?_⟩
  simpa only [w, rationalGibbs123_reject, one_mul] using
    (rational_heat_bath_derived_reference_mixing_budget 3 1 m 0 r w hW X hm hX).1

theorem rationalGibbs13_reject : rationalHeatBathReject (![1,3] : Fin 2 → ℕ) = 0 := by
  have ht : weightTotal (![1,3] : Fin 2 → ℕ) = 4 := by
    norm_num [weightTotal, Fin.sum_univ_succ]
  have hb : Nat.clog 2 4 = 2 := by decide
  norm_num [rationalHeatBathReject, rationalRejectMass, coinRejectMass, ht, hb]

theorem rational_gibbs_power_two_actual_reset (r : ℕ)
    (X : Matrix (Fin 2 × Fin r) (Fin 2 × Fin r) ℂ)
    (hW : 0 < weightTotal (![1,3] : Fin 2 → ℕ)) :
    tensorLeft (rationalHeatBathPower (![1,3] : Fin 2 → ℕ) hW 1 1).map X =
      TensorGate (rationalHeatBathDensity (![1,3] : Fin 2 → ℕ) hW) (Matrix.traceLeft X) := by
  rw [rational_heat_bath_actual_reference_power_formula 2 1 1 r _ hW X (by omega),
    rationalGibbs13_reject]
  simp

theorem rational_gibbs123_actual_costs (R m : ℕ)
    (hist : Fin m → HeatBathSamplerRecord 3)
    (hh : ∀ k, hist k ∈
      (rationalRejectionRun (![1,2,3] : Fin 3 → ℕ) 3 R).support) :
    rationalHeatBathCoins (![1,2,3] : Fin 3 → ℕ) R m hist ≤ m*3*R ∧
    rationalHeatBathComparisons (![1,2,3] : Fin 3 → ℕ) R m hist ≤ m*3*R := by
  have ht : weightTotal (![1,2,3] : Fin 3 → ℕ) = 6 := by
    norm_num [weightTotal, Fin.sum_univ_succ]
  have hb : Nat.clog 2 6 = 3 := by decide
  have hW : 0 < weightTotal (![1,2,3] : Fin 3 → ℕ) := by omega
  have h := (rational_heat_bath_actual_leaf_and_classical_ledgers 3 R m _ hW none
    ⟨0, by rw [(rationalHeatBathProgram_spec (N := 3) none).2]; omega⟩).2.2.2 hist
    (by simpa only [ht, hb] using hh)
  simpa only [ht, hb] using h.2.2

end Qatlib.Concepts.SamplingBackend.GibbsBackend
