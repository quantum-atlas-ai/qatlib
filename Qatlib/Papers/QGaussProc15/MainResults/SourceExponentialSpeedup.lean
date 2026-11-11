/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGaussProc15.MainResults.SourceCostModel

set_option backward.isDefEq.respectTransparency false

/-!
# QGaussProc15 c001 — exponential speed-up for sparse GP regression

Zhao--Fitzsimons--Fitzsimons, fixed arXiv:1512.03929v1 (12 Dec 2015),
claim c001 (main text, "Discussion"/abstract): in the most ideal situation,
where both `y` and `k_*` are sparse and `K + σ_n² I` is well-conditioned and
highly sparse, the QLA procedure of the paper achieves an exponential
speed-up over classical Gaussian process regression.

Formalisation.  The "ideal situation" realises the QLA run cost as
`poly(log n, 1/ε, s, κ) = C · log²(n + 1)` (`qlaRunCost`), with all the
non-`n` parameters absorbed into a finite constant `C`, while classical GPR
costs `Θ(n³)` (`classicalGPRCost`).  "Exponential speed-up" is formalised in
the standard, checkable way: the quantum cost is *subpolynomial*, i.e.
`o(n^p)` for every `p > 0` (`qlaRunCost_subpolynomial`), so eventually it is
cheaper than the classical `n³` cost (`eventually_qla_cheaper`) and the cost
ratio tends to zero (`exponential_speedup_over_classical`).
-/

set_option autoImplicit false
noncomputable section

open Filter Asymptotics

namespace Qatlib.Papers.QGaussProc15.MainResults

/-- **Fixed arXiv:1512.03929v1 (c001), subpolynomial QLA cost.**  In the
ideal sparse, well-conditioned regime the cost of one QLA run,
`C · log²(n + 1)`, is `o(n^p)` for every exponent `p > 0`: it grows slower
than any polynomial in the number of training points `n`.  This is the
formal content of "exponential speed-up" relative to the polynomial
classical cost. -/
theorem qlaRunCost_subpolynomial (C p : ℝ) (hp : 0 < p) :
    (fun n : ℕ => qlaRunCost C n) =o[atTop] fun n : ℕ => (n : ℝ) ^ p := by
  have h := (logSq_succ_isLittleO_rpow p hp).const_mul_left C
  simpa [qlaRunCost] using h

/-- **Fixed arXiv:1512.03929v1 (c001), exponential speed-up.**  The ratio of
the QLA run cost to the classical GPR cost `Θ(n³)` tends to zero: quantum
assisted GPR is asymptotically infinitely cheaper than classical GPR in the
ideal sparse, well-conditioned regime. -/
theorem exponential_speedup_over_classical (C : ℝ) :
    Tendsto (fun n : ℕ => qlaRunCost C n / classicalGPRCost n) atTop (nhds 0) := by
  have h : (fun n : ℕ => qlaRunCost C n) =o[atTop] classicalGPRCost := by
    change (fun n : ℕ => qlaRunCost C n) =o[atTop] (fun n : ℕ => (n : ℝ) ^ (3 : ℕ))
    simpa only [show (3 : ℝ) = ((3 : ℕ) : ℝ) from rfl, Real.rpow_natCast] using
      (qlaRunCost_subpolynomial C 3 (by norm_num))
  exact h.tendsto_div_nhds_zero

/-- **Fixed arXiv:1512.03929v1 (c001), eventual dominance.**  For every
positive cost constant `C` the QLA run cost is eventually at most the
classical GPR cost, which is the concrete reading of "achieves a speed-up
over classical Gaussian process regression". -/
theorem eventually_qla_cheaper {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, qlaRunCost C n ≤ classicalGPRCost n := by
  have h : (fun n : ℕ => qlaRunCost C n) =o[atTop] classicalGPRCost := by
    change (fun n : ℕ => qlaRunCost C n) =o[atTop] (fun n : ℕ => (n : ℝ) ^ (3 : ℕ))
    simpa only [show (3 : ℝ) = ((3 : ℕ) : ℝ) from rfl, Real.rpow_natCast] using
      (qlaRunCost_subpolynomial C 3 (by norm_num))
  filter_upwards [h.def (show (0 : ℝ) < 1 by norm_num)] with n hn
  have hq : (0 : ℝ) ≤ qlaRunCost C n := by unfold qlaRunCost; positivity
  have hc : (0 : ℝ) ≤ classicalGPRCost n := by unfold classicalGPRCost; positivity
  rwa [Real.norm_of_nonneg hq, Real.norm_of_nonneg hc, one_mul] at hn

end Qatlib.Papers.QGaussProc15.MainResults
