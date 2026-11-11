/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QDynamics10.MainResults.SourceModel
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# QDynamics10.MainResults.PiecewiseSingular — c006 (Corollary 6)

Fixed source: arXiv:1011.3489v1, Corollary 6 (p. 9–11), Eq. (32); proof on p. 10–11.

Corollary 6. Let `{H_μ}` be `Λ-2k`-smooth on `I = (t₀, t₀+Δt) \ {t₁, …, t_L}` (with
`t₀ < t₁ < ⋯ < t_L < t₀+Δt`), suppose

1. `∃ Hmax ≥ max_{t∈[t₀,t₀+Δt]} ‖H(t)‖`, and
2. near each singularity the evolution is close to the identity: `‖U(t+δ,t) − 1‖ ≤
   e^{Hmax δ} − 1` for `δ` the deleted radius;

then the evolution can be simulated within error `ε`, and

  `QueryCost ≤ 12 C M d² 5^{k−1} ⌈(L+1) + 24 k d² Λ Δt (5/3)^k
     (6 d² Λ Δt/(ε/3))^{1/2k}⌉`.                                                       (32)

Proof route. The omitted-neighbourhood contribution is bounded by
`(L+1)(e^{Hmax δ} − 1)`, and `δ` is chosen so that `e^{Hmax δ} − 1 ≤ ε/(6(L+2))`, giving an
omitted error of at most `ε/6`. On the remaining `L+1` intervals Lemma 7 gives integrator
error at most `ε/3`, and Lemma 1 gives round-off at most `ε/2`; `ε/6 + ε/3 + ε/2 = ε`.

We prove the three numerical ingredients (`exp_delta_choice`, `omitted_error_le`, and the
three-way triangle inequality) and assemble the corollary from the paper's cited bounds.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QDynamics10.MainResults.PiecewiseSingular

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

open Qatlib.Papers.QDynamics10.MainResults

/-- Eq. (32)'s `N_exp` count with the `(L+1)` singularity factor and error budget `ε/3`. -/
def piecewiseNexpBound (M d k L : ℕ) (Λ Δt ε : ℝ) : ℕ :=
  (L + 1) + stepExponentials M d k * Nat.ceil (queryCostCeilArg k d Λ Δt (ε / 3))

/-- Right-hand side of Eq. (32), written as `C` calls per exponential. -/
def piecewiseCostBound (C M d k L : ℕ) (Λ Δt ε : ℝ) : ℕ :=
  C * piecewiseNexpBound M d k L Λ Δt ε

/-- The `δ` of the proof of Corollary 6: `δ = log(1 + ε/(6(L+2)))/Hmax`, chosen so that
`e^{Hmax δ} − 1 = ε/(6(L+2))`. -/
theorem exp_delta_choice (Hmax ε : ℝ) (L : ℕ) (hHmax : 0 < Hmax) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ Real.exp (Hmax * δ) - 1 ≤ ε / (6 * ((L : ℝ) + 2)) := by
  refine ⟨Real.log (1 + ε / (6 * ((L : ℝ) + 2))) / Hmax, ?_, ?_⟩
  · have h1 : 0 < 1 + ε / (6 * ((L : ℝ) + 2)) := by positivity
    have hlog : 0 < Real.log (1 + ε / (6 * ((L : ℝ) + 2))) := by
      rw [Real.log_pos_iff (by positivity)]
      have : (0 : ℝ) < ε / (6 * ((L : ℝ) + 2)) := by positivity
      linarith
    positivity
  · have h1 : 0 < 1 + ε / (6 * ((L : ℝ) + 2)) := by positivity
    have hδ : Hmax * (Real.log (1 + ε / (6 * ((L : ℝ) + 2))) / Hmax)
        = Real.log (1 + ε / (6 * ((L : ℝ) + 2))) := by
      field_simp
    rw [hδ, Real.exp_log h1]
    linarith

/-- The omitted-neighbourhood error: `L` deleted intervals, each contributing at most
`ε/(6(L+2))`, sum to at most `ε/6`. (The paper's `(L+2)` accounts for the extra slack
used when splitting the remaining intervals.) -/
theorem omitted_error_le (L : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    (L : ℝ) * (ε / (6 * ((L : ℝ) + 2))) ≤ ε / 6 := by
  have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
  have hpos : (0 : ℝ) < (L : ℝ) + 2 := by positivity
  have hkey : (L : ℝ) / ((L : ℝ) + 2) ≤ 1 := by
    rw [div_le_one hpos]
    linarith
  have := mul_le_mul_of_nonneg_right hkey (show (0 : ℝ) ≤ ε / 6 by positivity)
  calc (L : ℝ) * (ε / (6 * ((L : ℝ) + 2)))
      = ((L : ℝ) / ((L : ℝ) + 2)) * (ε / 6) := by
        field_simp
    _ ≤ ε / 6 := by simpa using this

/-- Three-way triangle inequality: `ε/2` round-off plus `ε/3` integrator plus `ε/6`
omitted-neighbourhood error is at most `ε`. -/
theorem simulatedWithinError_of_three {I : Type} [Fintype I] [DecidableEq I]
    (A B C D : Matrix I I ℂ) {ε : ℝ}
    (h1 : ‖A - B‖ ≤ ε / 2) (h2 : ‖B - C‖ ≤ ε / 3) (h3 : ‖C - D‖ ≤ ε / 6) :
    SimulatedWithinError A D ε := by
  unfold SimulatedWithinError
  have hdecomp : A - D = (A - B) + (B - C) + (C - D) := by abel
  rw [hdecomp]
  calc ‖(A - B) + (B - C) + (C - D)‖
      ≤ ‖(A - B) + (B - C)‖ + ‖C - D‖ := norm_add_le _ _
    _ ≤ (‖A - B‖ + ‖B - C‖) + ‖C - D‖ := by
        have := norm_add_le (A - B) (B - C)
        linarith
    _ ≤ ε / 2 + ε / 3 + ε / 6 := by linarith
    _ = ε := by ring

/-- Corollary 6, Eq. (32): if `QueryCost = C · N` with `N ≤ (L+1) + N_exp` (one step per
retained interval plus the Lemma-7 exponential count on each of the `L+1` intervals at
error `ε/3`), then `QueryCost` is at most the right-hand side of Eq. (32). -/
theorem corollary6_queryCost_le (C M d k L : ℕ) (Λ Δt ε : ℝ)
    (N Nexp : ℕ) (QueryCost : ℕ)
    (hQuery : QueryCost = C * ((L + 1) + Nexp))
    (hNexp : Nexp ≤ stepExponentials M d k
      * Nat.ceil (queryCostCeilArg k d Λ Δt (ε / 3))) :
    QueryCost ≤ piecewiseCostBound C M d k L Λ Δt ε := by
  unfold piecewiseCostBound piecewiseNexpBound
  rw [hQuery]
  exact Nat.mul_le_mul_left C (Nat.add_le_add_left hNexp (L + 1))

/-- c006 — Corollary 6 (p. 9–11; Eq. (32)).

`Λ-2k`-smooth outside `L` singularities, bounded by `Hmax`, with singular neighbourhoods of
radius `δ` chosen by `exp_delta_choice`: the evolution is simulated within error `ε`
(three-way error split `ε/2 + ε/3 + ε/6`), with query cost bounded by Eq. (32).

The hypotheses `hRound`, `hIntegrator`, `hOmitted` are the paper's cited bounds (Lemma 1 at
`ε/2`, Lemma 7 at `ε/3` on each retained interval, and the per-neighbourhood identity bound
`e^{Hmaxδ}−1 ≤ ε/(6(L+2))` from `exp_delta_choice` and the exponential-series estimate). -/
theorem corollary6 {I : Type} [Fintype I] [DecidableEq I]
    (A U B V : Matrix I I ℂ) (C Cq M d k L : ℕ) (Λ Δt ε : ℝ)
    (N Nexp : ℕ)
    (hε : 0 < ε)
    (hRound : ‖A - U‖ ≤ ε / 2)
    (hIntegrator : ‖U - B‖ ≤ ε / 3)
    (hOmitted : ‖B - V‖ ≤ ε / 6)
    (hQuery : Cq = C * ((L + 1) + Nexp))
    (hNexp : Nexp ≤ stepExponentials M d k
      * Nat.ceil (queryCostCeilArg k d Λ Δt (ε / 3))) :
    SimulatedWithinError A V ε ∧ Cq ≤ piecewiseCostBound C M d k L Λ Δt ε :=
  ⟨simulatedWithinError_of_three A U B V hRound hIntegrator hOmitted,
    corollary6_queryCost_le C M d k L Λ Δt ε N Nexp Cq hQuery hNexp⟩

end Qatlib.Papers.QDynamics10.MainResults.PiecewiseSingular
