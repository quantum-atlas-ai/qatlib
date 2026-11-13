/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# RobustQLearn14.MainResults.DepolarizingNoise — majority-vote error bound and query threshold

Fixed source: Cross--Smith--Smolin, *Quantum learning robust to noise*,
arXiv:1407.5088v1 (18 Jul 2014).

Claim `c006` (Sec. IV C, Eqs. (11), (17)--(19), p. 4).  The quantum learner keeps
`k'` measured strings and takes a bit-wise majority vote.  With `X` the sum of `k`
independent Bernoulli(`η`) variables, Eq. (11) is the loose Chernoff bound

  `Pr[|X - ηk| < δηk] > 1 - B_k(η,δ)`,  `B_k(η,δ) = 2 e^{-δ²ηk/3}`.

Eq. (17) bounds the per-bit error probability by `2 B_{k'}(η̃,δ')`, the union
bound over the `n` bits (Eq. (18)) gives `Pr[â ≠ a] < 2nB_{k'}(η̃,δ')`, and the
choice

  `k' > 3/((δ')² η̃) log(4n/δ)`                                    (19)

ensures `Pr[â ≠ a] < δ`.  Since the right-hand side is `C · log(4n/δ)` with
`C = 3/((δ')²η̃)` independent of `n`, the number of queries is logarithmic in
`n`; for large `η` the paper remarks that `(δ')²η̃` is polynomial in
`1/(1/2-η)` (an asymptotic statement that is not separately formalized here).

The finite-cube probability space used below is the counting measure on
`Fin k → Bool`.  This uniform model matches Eq. (11) only at `η = 1/2`: the
source sums `k` independent Bernoulli(`η`) variables, whereas the uniform cube
gives Binomial(`k, 1/2`).  The registered statement below is therefore not
asserted in this model; a faithful formalisation first needs the Bernoulli-weighted
measure on the cube (or the paper's amplitude encoding).
-/

open scoped BigOperators

namespace Qatlib.Papers.RobustQLearn14.MainResults

noncomputable section

/-! ## Bernoulli sums on the Boolean cube -/

/-- Number of `1` bits of a Boolean string.
Source: arXiv:1407.5088v1, Sec. IV C, Eq. (11), p. 4 (`X` is a sum of Bernoulli
variables). -/
def majorityOneCount {k : ℕ} (s : Fin k → Bool) : ℕ :=
  (Finset.univ.filter (fun i => s i = true)).card

/-- The uniform-cube ratio
`|{s : Fin k → Bool | |count s - ηk| < δηk}| / 2^k`.
This equals the paper's `Pr[|X - ηk| < δηk]` only at `η = 1/2`; for `η ≠ 1/2`
the Bernoulli(`η`) product measure is not represented here.
Source: arXiv:1407.5088v1, Sec. IV C, Eq. (11), p. 4. -/
def majoritySuccessProb (k : ℕ) (η δ : ℝ) : ℝ :=
  ((Finset.univ.filter (fun s : Fin k → Bool =>
      |(majorityOneCount s : ℝ) - η * (k : ℝ)| < δ * η * (k : ℝ))).card : ℝ) /
    (2 : ℝ) ^ k

/-- The loose Chernoff deviation bound `B_k(η,δ) = 2 exp(-δ²ηk/3)` of Eq. (11).
Source: arXiv:1407.5088v1, Sec. IV C, Eq. (11), p. 4. -/
def majorityChernoffBound (k : ℕ) (η δ : ℝ) : ℝ :=
  2 * Real.exp (-(δ ^ 2 * η * (k : ℝ)) / 3)

/-- The effective error rate `η̃ = η(1 - (1+δ')(1-η))` used in Eq. (16).
Source: arXiv:1407.5088v1, Sec. IV C, p. 4 (definition of `η̃`). -/
def tildeEta (η δ' : ℝ) : ℝ := η * (1 - (1 + δ') * (1 - η))

/-! ## The Chernoff bound of Eq. (11) -/

/-- `c006` / Eq. (11): a loose Chernoff bound.  For `k` independent Bernoulli(`η`)
variables with `0 < η < 1` and `0 < δ < 1`,
`Pr[|X - ηk| < δηk] > 1 - B_k(η,δ)`.

Source: Cross--Smith--Smolin, *Quantum learning robust to noise*,
arXiv:1407.5088v1, Sec. IV C, Eq. (11), p. 4.

Scope note: `majority_chernoff` is a `Prop`-valued definition whose proof is
outside the scope of this file. The uniform-cube model above does not establish
the Bernoulli(`η`) bound for `η ≠ 1/2`.

The paper writes `X = Σ_{i<k} X_i` with `X_i` i.i.d. Bernoulli(`η`) and applies
the multiplicative Chernoff/mgf bound
`Pr[|X-ηk| ≥ δηk] ≤ 2 e^{-δ²ηk/3}`, using the exponential expression
`t ↦ e^{-tδηk} (1-η+ηe^{t})^{k}`, the choice `t = log(1+δ) > 0`, and
bounds of the form `log(1+δ) ≥ δ - δ²/2 ≥ δ/2`.

The corresponding probability model is the Bernoulli product measure on
`Fin k → Bool`, expressible with `MeasureTheory.Measure.pi`; independence gives
`mgf X μ t = (1 - η + η * exp t) ^ k`. Mathlib's generic Chernoff inequalities
`ProbabilityTheory.measure_ge_le_exp_mul_mgf` and
`ProbabilityTheory.measure_le_le_exp_mul_mgf`
(`Mathlib.Probability.Moments.Basic`) provide the exponential tail bounds.
The product-measure construction, independence argument and Bernoulli-sum mgf
computation are outside the scope of this file. -/
def majority_chernoff (k : ℕ) (η δ : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) : Prop :=
  1 - majorityChernoffBound k η δ < majoritySuccessProb k η δ

/-! ## Union bound over the `n` bits -/

/-- The union-bound quantity `2nB_k(η,δ)` of Eq. (18).
Source: arXiv:1407.5088v1, Sec. IV C, Eq. (18), p. 4. -/
def unionErrorBound (n : ℕ) (k : ℕ) (η δ : ℝ) : ℝ :=
  (n : ℝ) * (2 * majorityChernoffBound k η δ)

/-- `c006` / Eq. (18): if each of the `n` bits is wrong with probability at most
`2 B_k(η̃,δ')` (Eq. (17)), then by the union bound the probability that any bit
is wrong is at most `2nB_k(η̃,δ')`.
Source: arXiv:1407.5088v1, Sec. IV C, Eq. (18), p. 4. -/
theorem majority_union_bound (n : ℕ) (p B : ℝ) (hp : p ≤ 2 * B) :
    (∑ _j : Fin n, p) ≤ (n : ℝ) * (2 * B) := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg n)

/-- `c006` / Eq. (19): the sample count `k` satisfying
`k > 3/((δ')² η̃) log(4n/δ)` makes the union-bound error estimate smaller than
`δ`, for `n ≥ 1` and positive `η, δ, δ'`.
Source: arXiv:1407.5088v1, Sec. IV C, Eq. (19), p. 4. -/
theorem majority_eq19_threshold (n k : ℕ) (η δ δ' : ℝ) (hn : 1 ≤ n)
    (hη : 0 < η) (hδ : 0 < δ) (hδ' : 0 < δ')
    (hk : 3 / (δ' ^ 2 * η) * Real.log (4 * (n : ℝ) / δ) < (k : ℝ)) :
    unionErrorBound n k η δ' < δ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have h4n : (0 : ℝ) < 4 * (n : ℝ) / δ := div_pos (by linarith) hδ
  have hpos : (0 : ℝ) < δ' ^ 2 * η := mul_pos (pow_pos hδ' 2) hη
  have hlog : Real.log (4 * (n : ℝ) / δ) < δ' ^ 2 * η * (k : ℝ) / 3 := by
    have h0 : 3 / (δ' ^ 2 * η) * Real.log (4 * (n : ℝ) / δ)
        = 3 * Real.log (4 * (n : ℝ) / δ) / (δ' ^ 2 * η) := by ring
    rw [h0] at hk
    rw [div_lt_iff₀ hpos] at hk
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    linarith [hk]
  have hexp : 4 * (n : ℝ) / δ < Real.exp (δ' ^ 2 * η * (k : ℝ) / 3) := by
    have h := Real.exp_lt_exp.mpr hlog
    rwa [Real.exp_log h4n] at h
  have hEneg : (0 : ℝ) < Real.exp (-(δ' ^ 2 * η * (k : ℝ)) / 3) := Real.exp_pos _
  have hprod : Real.exp (δ' ^ 2 * η * (k : ℝ) / 3) *
      Real.exp (-(δ' ^ 2 * η * (k : ℝ)) / 3) = 1 := by
    rw [← Real.exp_add,
      show δ' ^ 2 * η * (k : ℝ) / 3 + -(δ' ^ 2 * η * (k : ℝ)) / 3 = 0 by ring,
      Real.exp_zero]
  have hE1 : 4 * (n : ℝ) < δ * Real.exp (δ' ^ 2 * η * (k : ℝ) / 3) := by
    have h := mul_lt_mul_of_pos_right hexp hδ
    rw [div_mul_cancel₀ (4 * (n : ℝ)) (ne_of_gt hδ)] at h
    linarith [h]
  have hR : (δ * Real.exp (δ' ^ 2 * η * (k : ℝ) / 3)) *
      Real.exp (-(δ' ^ 2 * η * (k : ℝ)) / 3) = δ := by
    rw [mul_assoc, hprod, mul_one]
  unfold unionErrorBound majorityChernoffBound
  have h := mul_lt_mul_of_pos_right hE1 hEneg
  rw [hR] at h
  linarith [h]

/-- `c006`, composed form of Eqs. (17)--(19): if every bit is wrong with
probability at most `2 B_k(η̃,δ')` (Eq. (17)) and the number of retained samples
satisfies Eq. (19), then the probability that the majority-vote estimate differs
from `a` in any bit is below `δ`.
Source: arXiv:1407.5088v1, Sec. IV C, Eqs. (17)--(19), p. 4. -/
theorem majority_eq19_ensures_error_below_delta (n k : ℕ) (η δ δ' p : ℝ)
    (hn : 1 ≤ n) (hη : 0 < η) (hδ : 0 < δ) (hδ' : 0 < δ')
    (hp : p ≤ 2 * majorityChernoffBound k η δ')
    (hk : 3 / (δ' ^ 2 * η) * Real.log (4 * (n : ℝ) / δ) < (k : ℝ)) :
    (∑ _j : Fin n, p) < δ := by
  have h1 : (∑ _j : Fin n, p) ≤ unionErrorBound n k η δ' := by
    unfold unionErrorBound
    exact majority_union_bound n p (majorityChernoffBound k η δ') hp
  have h2 : unionErrorBound n k η δ' < δ :=
    majority_eq19_threshold n k η δ δ' hn hη hδ hδ' hk
  linarith

end

end Qatlib.Papers.RobustQLearn14.MainResults
