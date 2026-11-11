/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FiniteMaximumLikelihood
import Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.FiniteSelection

/-!
# Rational maximum likelihood with gate bounds

The rational likelihood `score` multiplies observation masses while recording arithmetic cost,
and `decode` selects a candidate by a counted scan. For normalized nonnegative tables, the
rational computation agrees with finite real-valued maximum likelihood and inherits support and
log-likelihood error bounds. Finite statistical inference provides the background; see
[Watrous2018].

## Main statements

* `decode_agrees`: the rational and real likelihood decoders return the same candidate.
* `decode_gates`: input widths bound the arithmetic gate count.
* `log_error_bound`: bounded log-likelihood ratios give an exponential error bound.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteRationalLikelihood

open Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational
open FiniteSelection
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

variable {X : Type} {m n : ℕ}

/-- The rational product likelihood of a candidate on an observation record, paired with its
counted multiplication cost. -/
def score (q : Fin (m + 1) → X → ℚ) (w : Fin n → X) (c : Fin (m + 1)) : ℚ × ℕ :=
  product (List.ofFn fun i : Fin n => q c (w i))

/-- A counted scan of all candidates using their rational product likelihoods, initialized at
candidate zero. -/
def decode (q : Fin (m + 1) → X → ℚ) (w : Fin n → X) : Selection (Fin (m + 1)) :=
  scan (score q w) 0 (List.ofFn fun c : Fin (m + 1) => c)

/-- The value component of the counted likelihood is the product of the candidate masses along
the record. -/
theorem score_value (q : Fin (m + 1) → X → ℚ) (w : Fin n → X) (c : Fin (m + 1)) :
    (score q w c).1 = ∏ i, q c (w i) := by
  simp only [score, product_value, List.prod_ofFn]

/-- Nonnegative table entries give a nonnegative rational likelihood score. -/
theorem score_nonneg (q : Fin (m + 1) → X → ℚ) (hq : ∀ c x, 0 ≤ q c x)
    (w : Fin n → X) (c : Fin (m + 1)) : 0 ≤ (score q w c).1 := by
  rw [score_value]
  exact Finset.prod_nonneg fun i _ => hq c (w i)

/-- If every table entry has width at most `B`, the likelihood width is at most 1 + nB and its
cost is bounded by `n` rational multiplication caps. -/
theorem score_bounds (q : Fin (m + 1) → X → ℚ) (w : Fin n → X) (B : ℕ)
    (hB : ∀ c x, width (q c x) ≤ B) (c : Fin (m + 1)) :
    width (score q w c).1 ≤ 1 + n * B ∧
      (score q w c).2 ≤ n * binomialRatOpGateCap (1 + n * B) := by
  have h := product_bounds (List.ofFn fun i : Fin n => q c (w i))
  have hs : ((List.ofFn fun i : Fin n => q c (w i)).map width).sum ≤ n * B := by
    rw [List.map_ofFn, List.sum_ofFn]
    calc
      _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum fun i _ => hB c (w i)
      _ = _ := by simp
  refine ⟨h.1.trans (Nat.add_le_add_left hs 1), ?_⟩
  have hg := h.2.trans (Nat.mul_le_mul_left _ (product_cap_mono (Nat.add_le_add_left hs 1)))
  simpa only [List.length_ofFn] using! hg

/-- Uniform input width bounds give the stated gate cap for scanning all `m + 1` candidate
likelihoods. -/
theorem decode_gates (q : Fin (m + 1) → X → ℚ) (w : Fin n → X) (B : ℕ)
    (hB : ∀ c x, width (q c x) ≤ B) :
    (decode q w).gates ≤ (m + 1) *
      (2 * (n * binomialRatOpGateCap (1 + n * B)) +
        24 * (1 + n * B) ^ 2 + 20 * (1 + n * B)) := by
  have h := scan_gates (score q w) (1 + n * B)
    (n * binomialRatOpGateCap (1 + n * B))
    (fun c => (score_bounds q w B hB c).1) (fun c => (score_bounds q w B hB c).2)
    0 (List.ofFn fun c : Fin (m + 1) => c)
  simpa only [decode, List.length_ofFn] using h

section Probability
variable [Fintype X]
open scoped Classical

/-- The finite real probability distribution obtained by coercing a nonnegative rational table
whose entries sum to one. -/
noncomputable def distribution (q : X → ℚ) (hq : ∀ x, 0 ≤ q x) (hsum : ∑ x, q x = 1) :
    FinDist X where
  prob x := (q x : ℝ)
  nonneg x := by exact_mod_cast hq x
  sum_one := by exact_mod_cast hsum

/-- For normalized rational tables, the real coercion of the likelihood score equals the
probability of the observation record. -/
theorem score_real (q : Fin (m + 1) → X → ℚ) (hq : ∀ c x, 0 ≤ q c x)
    (hsum : ∀ c, ∑ x, q c x = 1) (w : Fin n → X) (c : Fin (m + 1)) :
    ((score q w c).1 : ℝ) = (distribution (q c) (hq c) (hsum c)).probOf w := by
  rw [score_value]
  simp [FinDist.probOf, distribution]

/-- Scanning rational scores returns the same candidate as the real maximum-likelihood scan
after coercing the scores. -/
theorem rationalScan_real {C : Type} (s : C → ℚ) (best : C) (cs : List C) :
    rationalScan s best cs = FiniteMaximumLikelihood.scan (fun c => (s c : ℝ)) best cs := by
  induction cs generalizing best with
  | nil => rfl
  | cons c cs ih =>
    simp only [rationalScan, FiniteMaximumLikelihood.scan, Rat.cast_lt]
    exact ih _

/-- For nonnegative normalized tables, rational decoding returns the same candidate as real
finite maximum-likelihood decoding. -/
theorem decode_agrees (q : Fin (m + 1) → X → ℚ) (hq : ∀ c x, 0 ≤ q c x)
    (hsum : ∀ c, ∑ x, q c x = 1) (w : Fin n → X) :
    (decode q w).candidate = FiniteMaximumLikelihood.decode
      (fun c => distribution (q c) (hq c) (hsum c)) w := by
  rw [decode, scan_value _ (score_nonneg q hq w), rationalScan_real]
  simp only [FiniteMaximumLikelihood.decode, score_real q hq hsum w]

/-- The candidate returned by rational decoding has record likelihood at least that of every
candidate in the normalized family. -/
theorem decode_maximal (q : Fin (m + 1) → X → ℚ) (hq : ∀ c x, 0 ≤ q c x)
    (hsum : ∀ c, ∑ x, q c x = 1) (w : Fin n → X) (c : Fin (m + 1)) :
    (distribution (q c) (hq c) (hsum c)).probOf w ≤
      (distribution (q (decode q w).candidate) (hq _) (hsum _)).probOf w := by
  rw [decode_agrees q hq hsum w]
  exact FiniteMaximumLikelihood.decode_maximal (fun c => distribution (q c) (hq c) (hsum c)) w c

/-- The decoding error probability under the true table is bounded by the sum, over competing
candidates, of their support masses under the true law raised to `n`. -/
theorem support_error_bound (q : Fin (m + 1) → X → ℚ) (hq : ∀ c x, 0 ≤ q c x)
    (hsum : ∀ c, ∑ x, q c x = 1) (truth : Fin (m + 1)) :
    (distribution (q truth) (hq truth) (hsum truth)).probEvent
      (fun w : Fin n → X => (decode q w).candidate ≠ truth) ≤
      ∑ c with c ≠ truth,
        (∑ x with (distribution (q c) (hq c) (hsum c)).prob x ≠ 0,
          (distribution (q truth) (hq truth) (hsum truth)).prob x) ^ n := by
  simpa only [decode_agrees q hq hsum] using
    (FiniteMaximumLikelihood.support_error_bound
      (fun c => distribution (q c) (hq c) (hsum c)) (n := n) truth)

/-- Positive normalized tables with bounded log-likelihood ratios and negative mean gaps have
decoding error bounded by the sum of exp(-2n d²/(b - a)²) over competing candidates. -/
theorem log_error_bound (q : Fin (m + 1) → X → ℚ) (hq : ∀ c x, 0 ≤ q c x)
    (hsum : ∀ c, ∑ x, q c x = 1) (truth : Fin (m + 1))
    (a b d : Fin (m + 1) → ℝ) (hpos : ∀ c x, 0 < (q c x : ℝ)) (hn : 0 < n)
    (hab : ∀ c, c ≠ truth → a c < b c) (hd : ∀ c, c ≠ truth → 0 < d c)
    (hrange : ∀ c, c ≠ truth → ∀ x,
      Real.log (q c x : ℝ) - Real.log (q truth x : ℝ) ∈ Set.Icc (a c) (b c))
    (hmean : ∀ c, c ≠ truth → (distribution (q truth) (hq truth) (hsum truth)).expect
      (fun x => Real.log (q c x : ℝ) - Real.log (q truth x : ℝ)) = -d c) :
    (distribution (q truth) (hq truth) (hsum truth)).probEvent
      (fun w : Fin n → X => (decode q w).candidate ≠ truth) ≤
      ∑ c with c ≠ truth, Real.exp (-2 * (n : ℝ) * (d c) ^ 2 / (b c - a c) ^ 2) := by
  simpa only [decode_agrees q hq hsum] using
    (FiniteMaximumLikelihood.log_error_bound (fun c => distribution (q c) (hq c) (hsum c))
      truth a b d hpos hn hab hd hrange hmean)

end Probability
end Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteRationalLikelihood
