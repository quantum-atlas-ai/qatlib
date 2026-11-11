/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# PEPSPrep11.MainResults.AlternatingMeasurement

Schwarz--Temme--Verstraete, "Preparing projected entangled pair states on a
quantum computer", fixed arXiv:1104.1410v2 (21 Feb 2012).

This file formalises **Lemma 3** (p. 4 of v2, proof pp. 4, Eq. (9)--(15)).

Lemma 3 (source). Let `H_t, H_{t+1}` have unique zero-energy ground states
`|ψ_t⟩, |ψ_{t+1}⟩`. Let `s` be a positive integer. If the system starts in
`|ψ_t⟩`, the process that alternatingly measures `H_{t+1}` and `H_t`, stopping
once `|ψ_{t+1}⟩` is reached, takes the system to `|ψ_{t+1}⟩` with probability at
least `1 - 1/(2 e s)` after at most `s/p` alternations, where
`p = |⟨ψ_{t+1}|ψ_t⟩|²`.

Modelling.  The source derives, from Jordan's lemma and the amplitude relations
(9)--(12), a two-state Markov chain on {success (ground of `H_{t+1}`),
failure}.  Starting from `|ψ_t⟩`, the first measurement of `H_{t+1}` succeeds
with probability `p`; conditioned on failure, one alternating round
(measure `H_t`, then measure `H_{t+1}`) returns to a failed state with
probability `p² + (1-p)²` and succeeds with probability `2p(1-p)`
(Eq. (13)--(14); `round_fail_prob`/`round_success_prob` below).  Hence the
failure probability after `m` rounds is `(1-p)(p²+(1-p)²)^m` (Eq. (15)).

The formal content below is: the Markov recursion (Eq. (15)), the exponential
bound `(1-q)^m ≤ e^{-qm}`, and the calculus step `max_x x e^{-2sx} = 1/(2es)`
which yields the `1 - 1/(2es)` success guarantee.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PEPSPrep11.MainResults.AlternatingMeasurement

/-- One round of the alternating measurement keeps the system in the failed
subspace with probability `p² + (1-p)²` (arXiv:1104.1410v2, Eq. (13)--(14)):
from `|ψ_{t+1}^⊥⟩`, measuring `H_t` gives `|ψ_t⟩` w.p. `1-p` and `|ψ_t^⊥⟩`
w.p. `p`; the subsequent `H_{t+1}` measurement fails again from `|ψ_t⟩` with
probability `1-p` and from `|ψ_t^⊥⟩` with probability `p`. -/
def keepProb (p : ℝ) : ℝ := p ^ 2 + (1 - p) ^ 2

/-- The round-level failure probability as a sum of the two failing two-step
histories (arXiv:1104.1410v2, Eq. (13)--(15)). -/
theorem round_fail_prob (p : ℝ) : (1 - p) * (1 - p) + p * p = keepProb p := by
  unfold keepProb
  ring

/-- The round-level success probability, the complementary two-step histories
(arXiv:1104.1410v2, Eq. (13)--(14)). -/
theorem round_success_prob (p : ℝ) : (1 - p) * p + p * (1 - p) = 2 * p * (1 - p) := by
  ring

/-- Failure probability after `m` alternating rounds, Eq. (15):
`p_fail(p, m) = (1-p)(p² + (1-p)²)^m`.  The first factor `1-p` is the
probability that the initial measurement of `H_{t+1}` (performed on `|ψ_t⟩`)
fails. -/
def failProb (p : ℝ) (m : ℕ) : ℝ := (1 - p) * (keepProb p) ^ m

/-- The termination probability after `m` rounds, Eq. (15):
`p_term(p, m) = 1 - (1-p)(p² + (1-p)²)^m`. -/
def termProb (p : ℝ) (m : ℕ) : ℝ := 1 - failProb p m

/-- One-step recursion of the two-state Markov chain (Eq. (15)). -/
theorem failProb_succ (p : ℝ) (m : ℕ) :
    failProb p (m + 1) = failProb p m * keepProb p := by
  unfold failProb
  rw [pow_succ]
  ring

/-- Eq. (15) restated: `p_term(p, m) = 1 - (1-p)(p² + (1-p)²)^m`. -/
theorem termProb_eq (p : ℝ) (m : ℕ) :
    termProb p m = 1 - (1 - p) * (keepProb p) ^ m := by
  unfold termProb failProb
  rfl

/-- `keepProb p = 1 - 2p(1-p)`. -/
theorem keepProb_eq (p : ℝ) : keepProb p = 1 - 2 * p * (1 - p) := by
  unfold keepProb
  ring

/-- The elementary exponential bound `(1 - q)^m ≤ e^{-qm}` for `0 ≤ q ≤ 1`. -/
theorem one_sub_pow_le_exp (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (m : ℕ) :
    (1 - q) ^ m ≤ Real.exp (-((m : ℝ) * q)) := by
  have hbase : 1 - q ≤ Real.exp (-q) := by
    have h := Real.add_one_le_exp (-q)
    linarith
  have hb0 : 0 ≤ 1 - q := by linarith
  calc (1 - q) ^ m ≤ (Real.exp (-q)) ^ m := pow_le_pow_left₀ hb0 hbase m
    _ = Real.exp (-((m : ℝ) * q)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

/-- Exponential upper bound on the failure probability, Eq. (15) proof:
`p_fail(p, m) ≤ (1-p) e^{-2mp(1-p)}`. -/
theorem failProb_exp_bound (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) :
    failProb p m ≤ (1 - p) * Real.exp (-((m : ℝ) * (2 * p * (1 - p)))) := by
  have hq0 : 0 ≤ 2 * p * (1 - p) := by nlinarith
  have hq1 : 2 * p * (1 - p) ≤ 1 := by nlinarith
  have hpow : (keepProb p) ^ m ≤ Real.exp (-((m : ℝ) * (2 * p * (1 - p)))) := by
    rw [keepProb_eq]
    exact one_sub_pow_le_exp _ hq0 hq1 m
  have h1p : 0 ≤ 1 - p := by linarith
  unfold failProb
  exact mul_le_mul_of_nonneg_left hpow h1p

/-- Calculus step used at the end of the Lemma 3 proof: for `s > 0` and
`x ≥ 0`, `x e^{-2sx} ≤ 1/(2 e s)`, whose maximum is attained at
`x = 1/(2s)` ("straightforward calculus" in the source). -/
theorem mul_exp_neg_le (s x : ℝ) (hs : 0 < s) (hx : 0 ≤ x) :
    x * Real.exp (-(2 * s * x)) ≤ 1 / (2 * Real.exp 1 * s) := by
  have h2s : 0 < 2 * s := by positivity
  have h := Real.mul_exp_neg_le_exp_neg_one (2 * s * x)
  have hrewrite : x * Real.exp (-(2 * s * x)) =
      (1 / (2 * s)) * ((2 * s * x) * Real.exp (-(2 * s * x))) := by
    field_simp
  rw [hrewrite]
  calc (1 / (2 * s)) * ((2 * s * x) * Real.exp (-(2 * s * x)))
      ≤ (1 / (2 * s)) * Real.exp (-1) := by
        apply mul_le_mul_of_nonneg_left h
        positivity
    _ = 1 / (2 * Real.exp 1 * s) := by
        have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
        have hs' : s ≠ 0 := hs.ne'
        rw [Real.exp_neg]
        field_simp

/-- **Lemma 3** (arXiv:1104.1410v2, p. 4).  For a transition probability
`p ∈ (0, 1]` and `s > 0`, after `m ≥ s/p` alternating rounds the process has
reached `|ψ_{t+1}⟩` with probability at least `1 - 1/(2 e s)`.

The number `m` of rounds is the "number of alternations" of the source; the
source chooses `m` a multiple of `1/p` with `m ≥ s/p` and bounds
`p_fail ≤ 1/(2es)`. -/
theorem lemma3_alternating_measurement (p s : ℝ) (m : ℕ)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hs : 0 < s) (hm : s / p ≤ (m : ℝ)) :
    1 - 1 / (2 * Real.exp 1 * s) ≤ termProb p m := by
  -- `m ≥ s/p` implies `m p ≥ s`.
  have hmp : s ≤ (m : ℝ) * p := by
    have h := hm
    rw [div_le_iff₀ hp0] at h
    linarith
  have h1p : 0 ≤ 1 - p := by linarith
  -- Exponential bound with the round count replaced by `s`.
  have hmul : s * (1 - p) ≤ ((m : ℝ) * p) * (1 - p) :=
    mul_le_mul_of_nonneg_right hmp h1p
  have hexp : Real.exp (-((m : ℝ) * (2 * p * (1 - p)))) ≤
      Real.exp (-(2 * s * (1 - p))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hmul]
  have hfail_bound : failProb p m ≤ (1 - p) * Real.exp (-(2 * s * (1 - p))) := by
    have hb := failProb_exp_bound p (le_of_lt hp0) hp1 m
    have h1p' : 0 ≤ 1 - p := by linarith
    calc failProb p m ≤ (1 - p) * Real.exp (-((m : ℝ) * (2 * p * (1 - p)))) := hb
      _ ≤ (1 - p) * Real.exp (-(2 * s * (1 - p))) :=
          mul_le_mul_of_nonneg_left hexp h1p'
  have hcalc : (1 - p) * Real.exp (-(2 * s * (1 - p))) ≤ 1 / (2 * Real.exp 1 * s) :=
    mul_exp_neg_le s (1 - p) hs h1p
  have hfinal : failProb p m ≤ 1 / (2 * Real.exp 1 * s) := le_trans hfail_bound hcalc
  unfold termProb
  linarith

end Qatlib.Papers.PEPSPrep11.MainResults.AlternatingMeasurement
