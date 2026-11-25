/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QSDPSpeedup16.MainResults.Lemma16Gibbs.SourceLemma16
public import Qatlib.Concepts.SdpMmwSolver.OracleError.SdpSparsificationGibbsError
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# Trace-norm budget for the Gibbs sampling step

The proof of Theorem 4 in arXiv:1609.05537v5 combines the sampler's
trace-norm error with a change in the exponential's Hermitian input. Here
that second part of the error budget is expressed as an explicit bound on
the operator norm of the change, using Lemma 16.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Concepts.HspRecovery.SieveLaw
open Qatlib.Concepts.MatrixExpTrace.GibbsNorm
open Qatlib.Concepts.MatrixWeights.WeightsCore
open Qatlib.Concepts.SdpMmwSolver.OracleError
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.QSDPSpeedup16.MainResults

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

/-- The Gibbs state as written in Eq. (85), with the temperature and sign
absorbed into the Hermitian input `H`. -/
def gibbsDensity (H : Matrix I I ℂ) : Matrix I I ℂ :=
  ((Matrix.trace (NormedSpace.exp H)).re : ℂ)⁻¹ • NormedSpace.exp H

/-- A logarithmic bound on the change of input gives an additive trace-norm
budget for the change of Gibbs state. -/
theorem gibbs_traceNorm_le_budget (H K : Matrix I I ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) (η : ℝ) (hη : 0 < η)
    (hgap : ‖H - K‖ ≤ Real.log (1 + η / 2)) :
    Matrix.traceNorm (gibbsDensity H - gibbsDensity K) ≤ η := by
  simpa only [gibbsDensity, normalizedPositiveBranch,
    ite_eq_left (exp_trace_re_pos H hH), ite_eq_left (exp_trace_re_pos K hK)] using
    normalized_gibbs_branch_eps_le I H K η hH hK hη hgap

/-- The two half-budgets yield Eq. (61) once the Hermitian inputs satisfy the
stated operator-norm bound. `ρ` is the output of the sampler for `K`. -/
theorem eq61_sampler_error (H K ρ : Matrix I I ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (ε : ℝ) (hε : 0 < ε)
    (hgap : ‖H - K‖ ≤ Real.log (1 + ε / 4))
    (hsample : Matrix.traceNorm (ρ - gibbsDensity K) ≤ ε / 2) :
    Matrix.traceNorm (ρ - gibbsDensity H) ≤ ε := by
  have hbudget : Matrix.traceNorm (gibbsDensity K - gibbsDensity H) ≤ ε / 2 := by
    apply gibbs_traceNorm_le_budget K H hK hH (ε / 2) (by positivity)
    rw [norm_sub_rev, show ε / 2 / 2 = ε / 4 by ring]
    exact hgap
  calc
    Matrix.traceNorm (ρ - gibbsDensity H) =
        Matrix.traceNorm ((ρ - gibbsDensity K) + (gibbsDensity K - gibbsDensity H)) := by
          rw [sub_add_sub_cancel]
    _ ≤ Matrix.traceNorm (ρ - gibbsDensity K) + Matrix.traceNorm (gibbsDensity K - gibbsDensity H) :=
      Matrix.traceNorm_add_le _ _
    _ ≤ ε := by linarith only [hsample, hbudget]

/-- For a prefix of payoff matrices, the per-round error from Eq. (60)
controls Eq. (61) provided the accumulated learning-rate budget meets the
logarithmic threshold. The histories use zero-based indices. -/
theorem eq61_payoff_history_error (D T t : ℕ) (M N : ℕ → Operator D) (ρ : Operator D)
    (η ε : ℝ) (hD : 0 < D) (hT : 0 < T) (hη : 0 ≤ η) (hε : 0 < ε)
    (hM : (-η • (∑ s ∈ Finset.range t, M s)).IsHermitian)
    (hN : (-η • (∑ s ∈ Finset.range t, N s)).IsHermitian)
    (herr : ∀ s, ‖M s - N s‖ ≤ 1 / (4 * (T : ℝ)))
    (hbudget : η * (t : ℝ) / (4 * (T : ℝ)) ≤ Real.log (1 + ε / 4))
    (hsample : Matrix.traceNorm (ρ - mmwState D N η t) ≤ ε / 2) :
    Matrix.traceNorm (ρ - mmwState D M η t) ≤ ε := by
  let _ : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  exact eq61_sampler_error _ _ ρ hM hN ε hε
    ((sdpCumulativePayoffError D T t M N η hT hη herr).trans hbudget) hsample

end Qatlib.Papers.QSDPSpeedup16.MainResults
