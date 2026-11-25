/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma2NearbyFailureCorrectedHami
public import Qatlib.Papers.HamLCUSim12.Multiproduct.Theorem3Signed.Theorem3
public import Qatlib.Papers.HamLCUSim12.Multiproduct.Corollary7Delta.Corollary7

@[expose] public section

/-!
# Finite failure budgets for the corrected signed LCU

The equal-weight addition uses Lemma 2. Theorem 3 then combines the
addition budget with the subtraction budget from Corollary 7.
-/

set_option autoImplicit false

namespace Qatlib.Papers.HamLCUSim12.Multiproduct

open Matrix
open scoped BigOperators
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.HamLCUSim12.LCUDeferred
open Qatlib.Papers.HamLCUSim12.Multiproduct
open Qatlib.Papers.HamLCUSim12.Multiproduct.Theorem3Signed
open Qatlib.Papers.HamLCUSim12.Multiproduct.Corollary7Delta

/-- Lemma 2 at unit weight ratio gives the pair-addition cost in Eq. (10). -/
theorem add_failure_le {I : Type} [Fintype I] [DecidableEq I]
    (Ua Ub : Matrix I I ℂ) (hUa : Ua ∈ Matrix.unitaryGroup I ℂ)
    (hUb : Ub ∈ Matrix.unitaryGroup I ℂ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hclose : ∀ φ : QState I, Normalized φ →
      (∑ x : I, ‖((Ua - Ub) *ᵥ φ) x‖ ^ 2) ≤ Δ ^ 2)
    (ψ : QState I) (hψ : Normalized ψ) :
    lemma2FailureProbCorrected 1 Ua Ub ψ ≤ Δ ^ 2 / 4 := by
  have h := lemma2NearbyFailureCorrected I 1 (by norm_num) Ua Ub hUa hUb Δ hΔ hclose ψ hψ
  norm_num at h
  exact h

/-- Theorem 3 and Corollary 7 give a total failure budget when each part
is allocated half of the desired tolerance. -/
theorem failure_le {I : Type} [Fintype I] [DecidableEq I]
    (k : ℕ) (hk : 1 ≤ k) (γ η δ : ℝ) (hγ : 0 < γ) (hη : 1 / 4 < η)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hEta : EtaMaxProperty η) (hFact : FactorialLowerBound)
    (hγlow : 1 + Real.log η / 2 +
      (1 / (2 * (k : ℝ))) * Real.log ((2 * (k : ℝ)) ^ ((5 : ℝ) / 2) / (δ / 2)) ≤ γ)
    (U : Fin (k + 1) → Matrix I I ℂ) (hU : ∀ q, U q ∈ Matrix.unitaryGroup I ℂ)
    (c : Fin (k + 1) → ℝ) (hc : ∀ q, c q = mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) q)
    (hc0 : ∀ q, c q ≠ 0) (hpos : ∃ q, 0 < c q) (hneg : ∃ q, c q < 0)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hclose : ∀ q q' : Fin (k + 1), ∀ φ : QState I, Normalized φ →
      (∑ x : I, ‖((U q - U q') *ᵥ φ) x‖ ^ 2) ≤ Δ ^ 2)
    (hadd : (k : ℝ) * Δ ^ 2 / 4 ≤ δ / 2)
    (ψ : QState I) (hψ : Normalized ψ) :
    cwFailureProbCorrected k c U ψ ≤ δ := by
  have hκ : paperKappa c = kappa k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) := by
    simp only [paperKappa, kappa, posMass, negMass, Finset.sum_filter, hc]
  have hsub := (corollary7_delta k hk γ η (δ / 2) hγ hη (by linarith) (by linarith)
    hEta hFact hγlow).1
  have hfail := (theorem3_signed_lcu k I hk U hU c hc0 hpos hneg Δ hΔ hclose).2 ψ hψ
  rw [hκ] at hfail
  linarith

end Qatlib.Papers.HamLCUSim12.Multiproduct
