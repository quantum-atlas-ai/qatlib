/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Papers.HamLCUSim12.LCUDeferred.Theorem3LCUFiberCorrectedHami
import Qatlib.Papers.HamLCUSim12.LCUDeferred.Theorem3LCUFailureCorrectedHami

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 3 — signed `k+1`-term linear combination of unitaries

Fixed source: arXiv:1202.5822v1, Theorem 3, p.3, Eqs. (5)-(6):
for `V = sum_q C_q U_q` (`k >= 1`, `C_q != 0`, `||U_q|| = 1`,
`max_{q != q'} ||U_q - U_{q'}|| <= Delta`) and
`kappa = (sum_{C_q>0} C_q)/(sum_{C_q<0} |C_q|)`, there is a deferred-measurement
circuit implementing an operator proportional to `V` whose total failure probability
is `P_+ + P_-` with `P_+ <= k Delta^2/4` and `P_- <= 4 kappa/(kappa+1)^2`.

The frozen deferred protocol `Theorem3LCUFailureCorrected` proves the *total*
failure bound (its ancilla-failure mass equals `1 - ||success||^2`), so the paper
layer states `P_+ + P_- <= k Delta^2/4 + 4 kappa/(kappa+1)^2`.  The paper's split
`P_+ <= k Delta^2/4` (union bound over the `k` pair additions, each with Lemma 2 at
`kappa = 1`) is recorded separately as `theorem3_addition_failure_budget`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.HamLCUSim12.Multiproduct.Theorem3Signed

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Papers.HamLCUSim12.LCUDeferred

/-- Paper bookkeeping of Theorem 3: `kappa = Sigma_+/Sigma_-`. -/
noncomputable def paperKappa {k : ℕ} (c : Fin (k + 1) → ℝ) : ℝ :=
  (∑ q, if 0 < c q then c q else 0) / (∑ q, if c q < 0 then |c q| else 0)

/-- Fixed arXiv:1202.5822v1, Theorem 3: the deferred signed LCU outputs `V psi / sum|c|`
on the all-zero ancilla fiber and fails on all other fibers with total probability at
most `k Delta^2/4 + 4 kappa/(kappa+1)^2`. -/
theorem theorem3_signed_lcu (k : ℕ) (I : Type) [Fintype I] [DecidableEq I] (hk : 1 ≤ k)
    (U : Fin (k + 1) → Matrix I I ℂ) (hU : ∀ q, U q ∈ Matrix.unitaryGroup I ℂ)
    (c : Fin (k + 1) → ℝ) (hc : ∀ q, c q ≠ 0) (hpos : ∃ q, 0 < c q) (hneg : ∃ q, c q < 0)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hclose : ∀ q q' : Fin (k + 1), ∀ φ : QState I, Normalized φ →
      (∑ x : I, ‖((U q - U q') *ᵥ φ) x‖ ^ 2) ≤ Δ ^ 2) :
    (∀ ψ : QState I, ∀ x : I,
        cwOutputCorrected k c U ψ (cwZero k, x)
          = (((∑ q, c q • U q)) *ᵥ ψ) x / (∑ q, |c q|))
      ∧ (∀ ψ : QState I, Normalized ψ →
          cwFailureProbCorrected k c U ψ ≤
            (k : ℝ) * Δ ^ 2 / 4 + 4 * paperKappa c / (paperKappa c + 1) ^ 2) := by
  refine ⟨fun ψ x => theorem3LCUFiberCorrected k I hk U hU c hc hpos hneg ψ x, ?_⟩
  intro ψ hψ
  have hfail := theorem3LCUFailureCorrected k I hk U hU c hc hpos hneg Δ hΔ hclose ψ hψ
  simpa [paperKappa] using hfail

/-- The `P_+` part of Theorem 3, Eq. (5): a union bound over the `k` pair-addition
attempts, each failing with probability at most `Delta^2/4` (Lemma 2 with
`kappa = 1`), gives total addition failure at most `k Delta^2/4`. -/
theorem theorem3_addition_failure_budget (k : ℕ) (Δ : ℝ) (p : Fin k → ℝ)
    (hp : ∀ i, p i ≤ Δ ^ 2 / 4) :
    (∑ i, p i) ≤ (k : ℝ) * Δ ^ 2 / 4 := by
  calc (∑ i, p i) ≤ ∑ _i : Fin k, Δ ^ 2 / 4 := Finset.sum_le_sum (fun i _ => hp i)
    _ = (k : ℝ) * (Δ ^ 2 / 4) := by simp
    _ = (k : ℝ) * Δ ^ 2 / 4 := by ring

end Qatlib.Papers.HamLCUSim12.Multiproduct.Theorem3Signed
