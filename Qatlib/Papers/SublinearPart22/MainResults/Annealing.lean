/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# SublinearPart22 — Lemma A.6 (probabilistic annealing)

Fixed paper: arXiv:2207.08643v1, Appendix A, Algorithm 7 and Lemma A.6, p. 21.

Two states `|ψ⟩`, `|φ⟩` with squared overlap `p = |⟨ψ|φ⟩|²` are annealed by
repeated two-basis measurements (Algorithm 7).  The paper proves
`E[T] = 1 + (1-p)/f` with `f = 2p(1-p)`, hence `E[T] = 1 + 1/(2p)`, where `T`
is the number of iterations (each iteration performs one reflection round in
each basis; the paper states the same quantity as the expected number of
reflections).

`annealTerminationProb p T` below is the law of `T` used in the paper's proof:
`Pr[T = 1] = p`, and for `t ≥ 2`, `Pr[T = t] = (1-p) f (1-f)^{t-2}`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SublinearPart22.MainResults

/-- Law of the iteration count `T` in the proof of Lemma A.6: the first
iteration succeeds deterministically with probability `p`, and every later
iteration succeeds with probability `f = 2p(1-p)`. -/
noncomputable def annealTerminationProb (p : ℝ) (T : ℕ) : ℝ :=
  if T = 0 then 0
  else if T = 1 then p
  else (1 - p) * (2 * p * (1 - p)) * (1 - 2 * p * (1 - p)) ^ (T - 2)

/-- `2p(1-p) ≤ 1/2`, so the per-iteration success probability `f` is `< 1`. -/
private lemma two_mul_p_mul_one_sub_p_le (p : ℝ) : 2 * p * (1 - p) ≤ 1 / 2 := by
  nlinarith [sq_nonneg (p - 1 / 2)]

/-- Two successive `tsum_eq_zero_add` splits expose the `t ≥ 2` tail. -/
private lemma tsum_eq_prob1_add_tail (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∑' T : ℕ, (T : ℝ) * annealTerminationProb p T) =
      p + ∑' n : ℕ,
        ((n : ℝ) + 2) * ((1 - p) * (2 * p * (1 - p)) * (1 - 2 * p * (1 - p)) ^ n) := by
  set f : ℝ := 2 * p * (1 - p) with hf
  set q : ℝ := 1 - f with hq
  have hp0' : (0 : ℝ) < p := hp0
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have hfpos : 0 < f := by rw [hf]; positivity
  have hf1 : f < 1 := by
    have := two_mul_p_mul_one_sub_p_le p
    rw [hf]; linarith
  have hqpos : 0 < q := by rw [hq]; linarith
  have hq1 : q < 1 := by rw [hq]; linarith
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hqpos]; exact hq1
  -- the tail `term (n+2)`
  have hterm_two : ∀ n : ℕ,
      ((n : ℝ) + 2) * annealTerminationProb p (n + 2) =
        ((n : ℝ) + 2) * ((1 - p) * f * q ^ n) := by
    intro n
    have h0 : n + 2 ≠ 0 := by omega
    have h1 : n + 2 ≠ 1 := by omega
    rw [annealTerminationProb, if_neg h0, if_neg h1, Nat.add_sub_cancel, hf, hq]
  -- summability of the tail
  have hsum_q : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_norm_lt_one hqnorm
  have hsum_nq : Summable (fun n : ℕ => (n : ℝ) * q ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hqnorm).summable
  have hsum_n2 : Summable (fun n : ℕ => ((n : ℝ) + 2) * q ^ n) := by
    have h := hsum_nq.add (hsum_q.mul_left 2)
    simpa [add_mul] using h
  have htail : Summable (fun n : ℕ =>
      ((n : ℝ) + 2) * ((1 - p) * f * q ^ n)) := by
    have h := hsum_n2.mul_left ((1 - p) * f)
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hshift : Summable (fun n : ℕ => ((n : ℝ) + 2) * annealTerminationProb p (n + 2)) := by
    simpa [hterm_two] using htail
  have hterm : Summable (fun T : ℕ => (T : ℝ) * annealTerminationProb p T) :=
    (summable_nat_add_iff 2).mp (by simpa using hshift)
  have hshift1 : Summable (fun n : ℕ => ((n : ℝ) + 1) * annealTerminationProb p (n + 1)) := by
    have h := (summable_nat_add_iff 1).mpr hterm
    simpa using h
  -- split twice
  have h0 : ((0 : ℕ) : ℝ) * annealTerminationProb p 0 = 0 := by simp
  have h1v : ((1 : ℕ) : ℝ) * annealTerminationProb p 1 = p := by
    simp [annealTerminationProb]
  calc (∑' T : ℕ, (T : ℝ) * annealTerminationProb p T)
      = ((0 : ℕ) : ℝ) * annealTerminationProb p 0 +
          ∑' n : ℕ, ((n : ℝ) + 1) * annealTerminationProb p (n + 1) := by
        simpa only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] using hterm.tsum_eq_zero_add
    _ = p + ∑' n : ℕ, ((n : ℝ) + 2) * annealTerminationProb p (n + 2) := by
        rw [h0, zero_add]
        have hthis := hshift1.tsum_eq_zero_add
        rw [show (((0 : ℕ) : ℝ) + 1) * annealTerminationProb p (0 + 1) = p by
          simp [annealTerminationProb]] at hthis
        rw [hthis]
        congr 1
        apply tsum_congr
        intro n
        push_cast
        ring
    _ = p + ∑' n : ℕ,
          ((n : ℝ) + 2) * ((1 - p) * (2 * p * (1 - p)) * (1 - 2 * p * (1 - p)) ^ n) := by
        rfl

/-- **Lemma A.6** (arXiv:2207.08643v1, p. 21; Algorithm 7): if `p = |⟨ψ|φ⟩|²`
with `0 < p < 1`, the expected number of annealing iterations (= reflection
rounds) is `1 + 1/(2p)`. -/
theorem lemmaA6_expected_reflections (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∑' T : ℕ, (T : ℝ) * annealTerminationProb p T) = 1 + 1 / (2 * p) := by
  set f : ℝ := 2 * p * (1 - p) with hf
  set q : ℝ := 1 - f with hq
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have hfpos : 0 < f := by rw [hf]; positivity
  have hf1 : f < 1 := by
    have := two_mul_p_mul_one_sub_p_le p
    rw [hf]; linarith
  have hqpos : 0 < q := by rw [hq]; linarith
  have hq1 : q < 1 := by rw [hq]; linarith
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hqpos]; exact hq1
  have hsum_q : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_norm_lt_one hqnorm
  have hsum_nq : Summable (fun n : ℕ => (n : ℝ) * q ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hqnorm).summable
  have hsum_n2 : Summable (fun n : ℕ => ((n : ℝ) + 2) * q ^ n) := by
    have h := hsum_nq.add (hsum_q.mul_left 2)
    simpa [add_mul] using h
  have hqval : (∑' n : ℕ, q ^ n) = (1 - q)⁻¹ := tsum_geometric_of_norm_lt_one hqnorm
  have hnq : (∑' n : ℕ, (n : ℝ) * q ^ n) = q / (1 - q) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hqnorm
  have hsum_n2_val : (∑' n : ℕ, ((n : ℝ) + 2) * q ^ n) =
      q / (1 - q) ^ 2 + 2 * (1 - q)⁻¹ := by
    have hsplit : (fun n : ℕ => ((n : ℝ) + 2) * q ^ n) =
        (fun n : ℕ => (n : ℝ) * q ^ n + 2 * q ^ n) := by
      ext n; ring
    rw [hsplit, hsum_nq.tsum_add (hsum_q.mul_left 2), tsum_mul_left, hnq, hqval]
  -- the tail value
  have htail_val : (∑' n : ℕ,
        ((n : ℝ) + 2) * ((1 - p) * f * q ^ n)) =
      (1 - p) * f * (q / (1 - q) ^ 2 + 2 * (1 - q)⁻¹) := by
    rw [show (fun n : ℕ => ((n : ℝ) + 2) * ((1 - p) * f * q ^ n)) =
        (fun n : ℕ => ((1 - p) * f) * (((n : ℝ) + 2) * q ^ n)) by
      ext n; ring]
    rw [tsum_mul_left, hsum_n2_val]
  rw [tsum_eq_prob1_add_tail p hp0 hp1, htail_val]
  -- arithmetic: `p + (1-p) f (q/(1-q)^2 + 2/(1-q)) = 1 + 1/(2p)`
  have hp_ne : p ≠ 0 := ne_of_gt hp0
  have h1p_ne : (1 - p) ≠ 0 := ne_of_gt h1p
  have hq_ne : (1 - q) ≠ 0 := by rw [hq]; linarith
  have hf_ne : (2 * p * (1 - p)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hp_ne) h1p_ne
  rw [hq, hf]
  field_simp
  ring

end Qatlib.Papers.SublinearPart22.MainResults
