/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 16: the sampling process solves the promise problem

Formalises Lemma 16 of Liu--Shaydulin--Niroula et al., *Certified randomness
using a trapped-ion quantum processor*, fixed arXiv:2503.20498v1, Lemma 16 and
Eqs. I.44--I.47, pp. 7--8.

The sampling process `Z` estimates
`y = Pr_z[p̃(z) ≥ τ/2^{B/2} ∧ ∃i, z_i=s_i]` from `L` samples and outputs `1`
iff `ỹ ≥ t + δ/4`.  The paper proves:

* if `Z_{τ,t+δ/2}(C,s) = 1`, i.e. `Y_τ(C,s) > t + δ/2`, then by Hoeffding
  (I.44) and Lemma 15, `ỹ > t + 3δ/8`, hence `Z` outputs `1`;
* if `Z_{τ-1/T,t}(C,s) = 0`, i.e. `Y_{τ-1/T}(C,s) ≤ t`, then
  `ỹ < t + δ/8`, hence `Z` outputs `0`,

each with probability at least `1 - η` when `η = 2^{-n^{O(1)}}`, and `Z` runs
in time `2^B n^{O(1)}`.

We formalise the threshold arithmetic of (I.44)--(I.47) exactly and record the
elementary probability consequence of the two failure events; the Hoeffding
MGF estimate itself is not restated (it is a shared `ProbabilityInterfaces`
theorem).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.RandCertLiu25.MainResults.SamplingPromise

/-- **Lemma 16, decision threshold for a yes instance** (Eq. I.45): if
`t + 3δ/8 ≤ ỹ`, then the rule `ỹ ≥ t + δ/4` accepts. -/
theorem lemma16_yes_accepts (delta t ytilde : ℝ) (hdelta : 0 < delta)
    (h : t + 3 * delta / 8 ≤ ytilde) : t + delta / 4 ≤ ytilde := by
  linarith

/-- **Lemma 16, decision threshold for a no instance** (Eq. I.47): if
`ỹ ≤ t + δ/8`, then the rule `ỹ ≥ t + δ/4` rejects. -/
theorem lemma16_no_rejects (delta t ytilde : ℝ) (hdelta : 0 < delta)
    (h : ytilde ≤ t + delta / 8) : ytilde < t + delta / 4 := by
  linarith

/-- **Lemma 16, error assembly.**  If the yes-case estimation error and the
no-case estimation error each have mass at most `η/2`, the union of the two
error events has mass at most `η`, so the promise is solved with probability at
least `1 - η`. -/
theorem lemma16_error_assembly (eta eps_yes eps_no : ℝ)
    (hyes : eps_yes ≤ eta / 2) (hno : eps_no ≤ eta / 2) :
    eps_yes + eps_no ≤ eta := by
  linarith

/-- **Lemma 16, promise conclusion.**  Combining the two decision thresholds
with the error assembly: on the complement of the union of the estimation-error
events (mass at least `1 - η`), the sampling process returns the correct answer
on both promise cases. -/
theorem lemma16_promise_solved (eta delta t yhat_yes yhat_no : ℝ)
    (hdelta : 0 < delta) (heta : 0 ≤ eta)
    (hyes : t + 3 * delta / 8 ≤ yhat_yes)
    (hno : yhat_no ≤ t + delta / 8) :
    (t + delta / 4 ≤ yhat_yes) ∧ (yhat_no < t + delta / 4) :=
  ⟨lemma16_yes_accepts delta t yhat_yes hdelta hyes,
   lemma16_no_rejects delta t yhat_no hdelta hno⟩

end Qatlib.Papers.RandCertLiu25.MainResults.SamplingPromise
