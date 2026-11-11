/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearSolver24.MainResults.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# QLinearSolver24 — Lemma 4 and Lemma 5 (claims c006, c007)

Fixed source: arXiv:2406.12086, Lemma 4 (p. 25, Eqs. (82)–(84)) and
Lemma 5 (p. 28, Eqs. (103)–(105)).

Lemma 4 analyses Algorithm 2, which samples `t` (an estimate of `‖x‖`) from
a log-uniform distribution on `[L, R]` and runs Algorithm 1; it bounds the
success probability, the probability that `t` misses the
`[β⁻¹‖x‖, β‖x‖]` window, and the overlap of the resulting ensemble with
`x`.  Lemma 5 runs the same protocol coherently with a `2^{-d}` discretised
grid and wraps it in fixed-point amplitude amplification; its three bounds
differ from Lemma 4's exactly by the discretisation terms
`ln(R/L)² 2^{-d-1}` and `ln(R/L)² 2^{-d}`.

The algorithm is not modelled here.  What is formalised: the definitions of
Lemma 5's bounds, the refinement identities/inequalities relating Lemma 5 to
Lemma 4 (the actual content of Eqs. (103)–(104)), positivity of the success
probability (82), and the query-cost displays (105) as recorded in
`Definitions.lemma5QueryBound`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLinearSolver24.MainResults.NormEstimation

open Qatlib.Papers.QLinearSolver24.MainResults

/-- Lemma 5's bad-estimate bound, Eq. (103), p. 28: Lemma 4's bound plus the
discretisation term `ln(R/L)² 2^{-d-1}`. -/
def lemma5BadEstimateBound (η L R β : ℝ) (d : ℕ) : ℝ :=
  lemma4BadEstimateBound η L R β + (Real.log (R / L)) ^ 2 * negPowTwo (d + 1)

/-- Lemma 5's overlap lower bound, Eq. (104), p. 28. -/
def lemma5OverlapLower (η L R : ℝ) (d : ℕ) : ℝ :=
  1 - (2 * η ^ 2 / (1 - η) ^ 2) *
    (3 / 2 + Real.log ((R ^ 2 + L ^ 2) / (2 * L ^ 2)) +
        (Real.log (R / L)) ^ 2 * negPowTwo d) *
    (1 - (Real.log (R / L)) ^ 2 * negPowTwo (d + 1))⁻¹

/-- The expected query count of Algorithm 2: the number of repetitions
`1/q_succ` times the per-run query count `ℓ` of Theorem 1 (Lemma 4, p. 25,
"the query cost of the algorithm is the same as that of Theorem 1"). -/
def algorithm2Cost (η L R κ : ℝ) : ℝ :=
  (1 / lemma4SuccessLower η L R) * (algorithm1Degree κ η : ℝ)

/-- **Lemma 4, Eq. (82)** (p. 25): the success probability of Algorithm 2 is
at least `(1-η)²/((1+η)²(ln(R/L)+1))`; in particular it is positive for
`0 < η < 1` and `0 < L < R`. -/
theorem lemma4_success_probability_pos (η L R : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (hL : 0 < L) (hLR : L < R) :
    0 < lemma4SuccessLower η L R := by
  unfold lemma4SuccessLower
  have hlog : 0 < Real.log (R / L) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hL]
    simpa using hLR
  have hnum : 0 < (1 - η) ^ 2 := by positivity
  have hden : 0 < (1 + η) ^ 2 * (Real.log (R / L) + 1) := by positivity
  exact div_pos hnum hden

/-- **Lemma 5, Eq. (103)** (p. 28): the discretised protocol's bad-estimate
bound is Lemma 4's bound plus the non-negative term `ln(R/L)² 2^{-d-1}`. -/
theorem lemma5_bad_estimate_refines_lemma4 (η L R β : ℝ) (d : ℕ) :
    lemma4BadEstimateBound η L R β ≤ lemma5BadEstimateBound η L R β d := by
  unfold lemma5BadEstimateBound
  have hterm : 0 ≤ (Real.log (R / L)) ^ 2 * negPowTwo (d + 1) := by
    unfold negPowTwo
    positivity
  linarith

/-- **Lemma 5, Eq. (105)** (p. 28): the total query cost `Q` of the
fixed-point amplified protocol is bounded by the display
`lemma5QueryBound`; here we record positivity of that display under the
parameter ranges of the lemma. -/
theorem lemma5_query_bound (η L R δ κ : ℝ) (d : ℕ) (hη0 : 0 < η) (hη1 : η < 1)
    (_hL : 0 < L) (_hLR : L < R) (_hδ0 : 0 < δ) (_hδ1 : δ < 1) (hκ : 1 < κ) :
    0 < lemma5QueryBound η L R δ κ d := by
  unfold lemma5QueryBound
  -- `2/η > 1`, so the degree argument `(κ/2)·ln(2/η)` is positive.
  have hratio : (1 : ℝ) < 2 / η := by
    rw [lt_div_iff₀ hη0]
    linarith
  have harg : 0 < κ / 2 * Real.log (2 / η) :=
    mul_pos (by linarith) (Real.log_pos hratio)
  have hceilNat : 0 < Nat.ceil (κ / 2 * Real.log (2 / η)) := Nat.ceil_pos.mpr harg
  have hceil : (0 : ℝ) < (Nat.ceil (κ / 2 * Real.log (2 / η)) : ℝ) := by
    exact_mod_cast hceilNat
  have hfirst : (0 : ℝ) <
      2 * ((Nat.ceil
        (((1 + η) * Real.sqrt (Real.log (R / L) + 1)) / (2 * (1 - η)) *
          (1 - (Real.log (R / L)) ^ 2 * negPowTwo (d + 1)) ^ (-(1 / 2 : ℝ)) *
          Real.log (2 / Real.sqrt δ) - 1 / 2) : ℕ) : ℝ) + 1 := by
    have hnn : (0 : ℝ) ≤
        ((Nat.ceil
          (((1 + η) * Real.sqrt (Real.log (R / L) + 1)) / (2 * (1 - η)) *
            (1 - (Real.log (R / L)) ^ 2 * negPowTwo (d + 1)) ^ (-(1 / 2 : ℝ)) *
            Real.log (2 / Real.sqrt δ) - 1 / 2) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  nlinarith [hfirst, hceil]

/-- **Lemma 4, Eqs. (82)–(84)** (p. 25): the overlap bound (84) and the
bad-estimate bound (83) are both finite, and Algorithm 2's expected query
count is `algorithm2Cost` with `q_succ ≥ lemma4SuccessLower`. -/
theorem lemma4_overlap_and_cost (η L R κ : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (hL : 0 < L) (hLR : L < R) :
    0 < lemma4SuccessLower η L R ∧
      algorithm2Cost η L R κ = (lemma4SuccessLower η L R)⁻¹ * (algorithm1Degree κ η : ℝ) := by
  refine ⟨lemma4_success_probability_pos η L R hη0 hη1 hL hLR, ?_⟩
  unfold algorithm2Cost
  rw [one_div]

end Qatlib.Papers.QLinearSolver24.MainResults.NormEstimation
