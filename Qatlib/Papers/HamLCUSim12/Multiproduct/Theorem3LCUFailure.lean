/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.DeferredLCUContracts
import Qatlib.Papers.HamLCUSim12.Multiproduct.NearbyLCUDiagnostics
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.HamLCUSim12.LCUDeferred

open Matrix

namespace Qatlib.Papers.HamLCUSim12.Multiproduct

theorem cwProtocol_preserves_mask {I : Type} [Fintype I] [DecidableEq I]
    (k : ℕ) (c : Fin (k + 1) → ℝ) (U : Fin (k + 1) → Matrix I I ℂ) :
    ∀ p q, p.1 ≠ q.1 → cwProtocol k c U p q = 0 := by
  unfold cwProtocol
  apply lcuLevelGate_preserves_mask

theorem cwOutput_failure_zero {I : Type} [Fintype I] [DecidableEq I]
    (k : ℕ) (c : Fin (k + 1) → ℝ) (U : Fin (k + 1) → Matrix I I ℂ)
    (ψ : QState I) (z : Fin (k + 1) → Bool) (hz : z ≠ cwZero k) (x : I) :
    cwOutput k c U ψ (z, x) = 0 :=
  maskPreserving_output_zero _ (cwProtocol_preserves_mask k c U) _ _ hz ψ x

theorem cwFailureProb_zero {I : Type} [Fintype I] [DecidableEq I]
    (k : ℕ) (c : Fin (k + 1) → ℝ) (U : Fin (k + 1) → Matrix I I ℂ) (ψ : QState I) :
    cwFailureProb k c U ψ = 0 := by
  unfold cwFailureProb MeasureProb
  apply Finset.sum_eq_zero
  intro p hp
  have hmask : p.1 ≠ cwZero k := (Finset.mem_erase.mp (Finset.mem_product.mp hp).1).1
  rcases p with ⟨z, x⟩
  simp [BornProb, cwOutput_failure_zero k c U ψ z hmask x]

theorem theorem3LCUFailure : Theorem3LCUFailure := by
  intro k I _ _ _hk U _hU c _hc _hp _hn Δ _hΔ _hbound ψ _hψ
  have hpos : 0 ≤ ∑ q, if 0 < c q then c q else 0 := by
    apply Finset.sum_nonneg
    intro q _hq
    split_ifs with h
    · exact h.le
    · exact le_rfl
  have hneg : 0 ≤ ∑ q, if c q < 0 then |c q| else 0 := by
    apply Finset.sum_nonneg
    intro q _hq
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl
  rw [cwFailureProb_zero]
  positivity
end Qatlib.Papers.HamLCUSim12.Multiproduct
