/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NativeNumerics.EmpiricalRisk.RiskActualAccessLedgerFiniteStat
import Qatlib.Concepts.RiskEstimation.CVaREstimation.CVaRAlgorithmFiniteRestrictedQuan

/-!
# Support bound for conditional-risk call counts

This module proves a uniform support bound for the call-count component returned by `riskCVaR`.
It extracts the bisection count and includes the two additional estimation stages in the
conditional-risk construction associated with [WoernerEgger2019].

## Main statements

* `riskCVaR_support_calls`: every supported result records at most `Nat.clog 2 xs.length + 3`
  calls.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped Classical BigOperators ENNReal
set_option autoImplicit false

open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

namespace Qatlib.Concepts.NativeNumerics.EmpiricalRisk

/-- Every supported output of `riskCVaR` has recorded call count at most `Nat.clog 2 xs.length +
3`. -/
theorem riskCVaR_support_calls {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (loss : I → ℚ) (xs : List ℚ) (q eps : ℝ) (k M r : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hloss : ∀ i, 0 ≤ loss i ∧ loss i ≤ 1) (hM : 2 ≤ M) :
    ∀ z ∈ (riskCVaR A j loss xs q eps k M r hA hloss hM).support, z.2.2 ≤ Nat.clog 2 xs.length+3 := by
  intro z hz
  unfold riskCVaR at hz
  obtain ⟨w, hw, hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
  obtain ⟨phat, _, hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
  obtain ⟨muhat, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
  subst z
  have hh := riskBisect_support_calls (fun t => riskMedianPMF (riskCDFLaw A j loss t M hA hM) r)
    xs q (Nat.clog 2 xs.length+1) 0 (xs.length-1) w hw
  (try dsimp only)
  omega
end Qatlib.Concepts.NativeNumerics.EmpiricalRisk
