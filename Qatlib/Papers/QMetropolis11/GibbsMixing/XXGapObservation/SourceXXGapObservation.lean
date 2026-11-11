/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Spectral gap of the XX chain and mixing time (Temme et al. 2011, Sec. 9)

Fixed source: arXiv:0911.3635v2, Section 9 and Fig. 6, printed page 27.

The paper observes numerically (Fig. 6) that the spectral gap of the XX spin
chain decays like `1/N` in the number `N` of spins, and explicitly calls the
rapid-mixing question an open problem.  It combines this observation with the
mixing-time formula (9), `m_mix ≥ O(ln(1/ε_mix)/Δ)`, to argue that a gap
`Δ = Θ(1/N)` gives a mixing time of order `N ln(1/ε)`.

This file records:
* the observation itself as the predicate `XXChainGapObservation` (a
  hypothesis, not a theorem: the paper presents no proof);
* the *conditional* arithmetic consequence, which is proved: if the gap obeys
  `Δ ≥ c/N` then `N ln(1/ε)/c` evolution steps suffice to contract the error
  below `ε` (this is the exponential-decay form of Eq. (9)).
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMetropolis11.GibbsMixing.XXGapObservation

/-- **c017, the Fig. 6 observation.**  The numerically observed gap `Δ N` of
the `N`-spin XX chain is bounded above and below by constants over `N`.  The
paper states this as a plot-based observation and an open problem, so it is
used here only as a hypothesis. -/
def XXChainGapObservation (Δ : ℕ → ℝ) : Prop :=
  ∃ C c : ℝ, 0 < c ∧ c < C ∧ ∀ N : ℕ, 0 < N →
    c / (N : ℝ) ≤ Δ N ∧ Δ N ≤ C / (N : ℝ)

/-- **c017, Eq. (9) with a `1/N` gap.**  If the gap obeys `Δ ≥ c/N`, then
`m = N ln(1/ε)/c` steps of a map whose error decays like `e^{-Δm}` bring the
error below `ε`.  Proved from `exp` monotonicity and `exp(log x) = x`; this is
the formal content of "a gap `O(1/N)` gives mixing time `O(N log(1/ε))`".

Source: arXiv:0911.3635v2, Eq. (9) (`m_mix ≥ O(ln(1/ε_mix)/Δ)`) combined
with the Fig. 6 observation `Δ = Θ(1/N)`.  The paper's `m_mix` is a lower
bound on the number of steps; the equivalent useful statement proved here is
that the displayed number of steps *suffices*. -/
theorem source_xx_gap_mixing_time (N : ℕ) (c ε Δ : ℝ)
    (hN : 0 < N) (hc : 0 < c) (hε0 : 0 < ε) (hε1 : ε < 1)
    (_hΔ0 : 0 < Δ) (hΔ : c / (N : ℝ) ≤ Δ) :
    Real.exp (-(Δ * ((N : ℝ) * Real.log (1 / ε) / c))) ≤ ε := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hLpos : 0 < Real.log (1 / ε) := by
    apply Real.log_pos
    rw [one_lt_div hε0]
    exact hε1
  have hge : (1 : ℝ) ≤ Δ * (N : ℝ) / c := by
    rw [le_div_iff₀ hc, one_mul]
    have h := mul_le_mul_of_nonneg_right hΔ (le_of_lt hNpos)
    rw [div_mul_cancel₀ _ (ne_of_gt hNpos)] at h
    linarith
  have hmul : (1 : ℝ) * Real.log (1 / ε) ≤ (Δ * (N : ℝ) / c) * Real.log (1 / ε) :=
    mul_le_mul_of_nonneg_right hge (le_of_lt hLpos)
  have hm : Real.log (1 / ε) ≤ Δ * ((N : ℝ) * Real.log (1 / ε) / c) := by
    have heq : Δ * ((N : ℝ) * Real.log (1 / ε) / c) =
        (Δ * (N : ℝ) / c) * Real.log (1 / ε) := by ring
    rw [heq]; simpa using hmul
  calc Real.exp (-(Δ * ((N : ℝ) * Real.log (1 / ε) / c)))
      ≤ Real.exp (-(Real.log (1 / ε))) := Real.exp_le_exp.mpr (by linarith)
    _ = ε := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp

end Qatlib.Papers.QMetropolis11.GibbsMixing.XXGapObservation
