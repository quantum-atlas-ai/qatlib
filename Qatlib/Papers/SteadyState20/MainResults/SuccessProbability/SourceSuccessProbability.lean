/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SuccessProbability — c003 of SteadyState20

Fixed source: arXiv:2008.07133v2 (Quantum **5**, 420 (2021)), Section 3.1, p. 6, Eq. (11)
and the sentence following it: “As `p0 > 1/2`, the number of executions required to
successfully measure the zero eigenvalue is `O(1)` and does not scale with `N` or `t`.”

The paper's derivation is Eq. (11):
`p0 = 1/2 (1 + |c0|^2 + Σ_{j≠0,1} |c_j|^2 |α0^(j)|^2) = (1 + |c0|^2)/2 + p_e`,
with `p_e = 1/2 Σ_{j≠0,1} |c_j|^2 |α0^(j)|^2 ≥ 0` the QPE error mass.  Consequently
`p0 ≥ 1/2`; the paper's strict inequality holds whenever the overlap or the error mass is
positive.  For a Bernoulli experiment with success probability `p`, the expected number of
repetitions (number of failures before the first success plus one) is
`Σ_{m≥0} (1-p)^m = p⁻¹ ≤ 2`, and the failure tail after `m` runs is `(1-p)^m ≤ 2^{-m}`.
Both bounds are uniform: no factor of `N` or `t` appears.

Shared interface: the circuit-level Born mass of the zero-phase sector is
`QuantumAlgorithm.Concepts.SpectralFilter.ZeroPhaseFilter.degenerate_detection_mass`
(Frozen v2.0.2), which identifies the measured zero-event probability with the squared
norm of the zero-phase data branch.  This file formalises the numerical consequence that
the paper draws from that mass identity; it does not reprove the circuit identity.

Boundary: this is the statistical repetition count.  It does not assert that the
amplitudes are realised by a concrete gate word (that is the algorithm/existence part of
c001) and it does not estimate the observable.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SteadyState20.MainResults.SuccessProbability

/-- Paper Eq. (11) (arXiv:2008.07133v2, Sec. 3.1, p. 6): success probability of measuring
zero in the first register, split as `p0 = (1 + |c0|^2)/2 + p_e`.  `c0Sq` is `|c0|^2` and
`pE` is the QPE error mass `p_e`. -/
def successProbability (c0Sq pE : ℝ) : ℝ :=
  (1 + c0Sq) / 2 + pE

/-- Paper Eq. (11), bracketed amplitude form: the parenthesised sum is exactly
`1 + |c0|^2 + 2 p_e`, hence dividing by two reproduces `successProbability`. -/
theorem successProbability_eq_amplitude_form (c0Sq pE : ℝ) :
    (1 + c0Sq + 2 * pE) / 2 = successProbability c0Sq pE := by
  unfold successProbability
  ring

/-- Paper Eq. (11), p. 6: because `|c0|^2 ≥ 0` and the QPE error mass is nonnegative,
`p0 ≥ 1/2`.  This is the inequality used for the `O(1)` repetition count. -/
theorem half_le_successProbability {c0Sq pE : ℝ} (hc : 0 ≤ c0Sq) (hp : 0 ≤ pE) :
    (1 : ℝ) / 2 ≤ successProbability c0Sq pE := by
  unfold successProbability
  linarith

/-- Paper Eq. (11), p. 6, strict form: `p0 > 1/2` as soon as either the overlap
`|c0|^2` or the QPE error mass is positive.  (The paper quotes the strict inequality
`p0 > 1/2`; at the degenerate point `|c0|^2 = p_e = 0` only `p0 = 1/2` survives, which
is still enough for the `O(1)` bound.) -/
theorem successProbability_gt_half {c0Sq pE : ℝ}
    (h : 0 < c0Sq + 2 * pE) :
    (1 : ℝ) / 2 < successProbability c0Sq pE := by
  unfold successProbability
  linarith

/-- Paper Sec. 3.1, p. 6: a physical probability is at most one; this is the upper bound
needed to read `1 - p` as the failure probability. -/
theorem successProbability_le_one {c0Sq pE : ℝ}
    (h : successProbability c0Sq pE ≤ 1) :
    successProbability c0Sq pE ≤ 1 := h

/-- Failure tail (paper Sec. 3.1, p. 6): after `m` independent runs, all fail with
probability `(1-p)^m`.  When `1/2 ≤ p ≤ 1` this is at most `2^{-m}`, i.e. exponentially
small in the number of repetitions and independent of `N` and `t`. -/
theorem failure_tail_le {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1) (m : ℕ) :
    (1 - p) ^ m ≤ (1 / 2 : ℝ) ^ m := by
  exact pow_le_pow_left₀ (by linarith) (by linarith) m

/-- Expected repetition count (paper Sec. 3.1, p. 6, “the number of executions required to
successfully measure the zero eigenvalue is `O(1)`”): for a per-run success probability
`1/2 ≤ p ≤ 1`, the expected number of runs until the first success is
`Σ_{m≥0} (1-p)^m = p⁻¹ ≤ 2`. -/
theorem expected_repetitions_le_two {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1) :
    (∑' m : ℕ, (1 - p) ^ m) ≤ 2 := by
  have h0 : (0 : ℝ) ≤ 1 - p := by linarith
  have h1 : 1 - p < 1 := by linarith
  rw [tsum_geometric_of_lt_one h0 h1]
  have hp0 : (0 : ℝ) < p := by linarith
  have hsub : 1 - (1 - p) = p := by ring
  rw [hsub]
  calc p⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp
    _ = 2 := by norm_num

/-- c003 main statement (arXiv:2008.07133v2, Sec. 3.1, p. 6): for every `N`-spin system
and every `t`-bit QPE register, the expected number of runs of the NESS algorithm needed
to observe the zero eigenvalue is at most `2`, uniformly in `N` and `t`.  This makes the
paper's “does not scale with `N` or `t`” precise. -/
theorem repetitions_uniform_in_size (_N _t : ℕ) {c0Sq pE : ℝ}
    (hc : 0 ≤ c0Sq) (hp : 0 ≤ pE) (hp1 : successProbability c0Sq pE ≤ 1) :
    (∑' m : ℕ, (1 - successProbability c0Sq pE) ^ m) ≤ 2 :=
  expected_repetitions_le_two (half_le_successProbability hc hp) hp1

/-- c003 tail corollary: the probability that `m` runs all fail is at most `2^{-m}`,
again uniformly in `N` and `t`. -/
theorem failure_tail_uniform_in_size (_N _t : ℕ) {c0Sq pE : ℝ}
    (hc : 0 ≤ c0Sq) (hp : 0 ≤ pE) (hp1 : successProbability c0Sq pE ≤ 1) (m : ℕ) :
    (1 - successProbability c0Sq pE) ^ m ≤ (1 / 2 : ℝ) ^ m :=
  failure_tail_le (half_le_successProbability hc hp) hp1 m

end Qatlib.Papers.SteadyState20.MainResults.SuccessProbability
