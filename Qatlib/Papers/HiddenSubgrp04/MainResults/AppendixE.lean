/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Appendix E, GCD probabilities: Lemmas E.2 and E.3

Fixed source version: Lomont, *The Hidden Subgroup Problem -- Review and Open
Problems*, arXiv `quant-ph/0411037` (2004), Appendix E, pp. 77--78.

The paper samples integers `{0,…,d-1}` uniformly; in Lean that is `Fin d` with
the counting measure `Finset.univ`.  `gcdAll t` is the `gcd` of all sampled
values.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.HiddenSubgrp04.MainResults

noncomputable section

/-- `gcd(t_1,…,t_k)` for `k` samples `t : Fin k → Fin d`, using `Finset.gcd`
(with value `0` only if all samples are `0`). -/
def gcdAll {k d : ℕ} (t : Fin k → Fin d) : ℕ :=
  (Finset.univ : Finset (Fin k)).gcd (fun j => (t j).val)

/-- The probability that two independent uniform samples from `{0,…,n}` are
coprime, computed as a counting fraction over `Fin (n+1) × Fin (n+1)`. -/
def coprimePairProb (n : ℕ) : ℝ :=
  ((Finset.univ.filter
      (fun p : Fin (n + 1) × Fin (n + 1) => Nat.Coprime p.1.val p.2.val)).card : ℝ) /
    ((Fintype.card (Fin (n + 1) × Fin (n + 1)) : ℕ) : ℝ)

/-- The probability that `k` independent uniform samples from `{0,…,d-1}` have
`gcd` equal to `1`, computed as a counting fraction over `Fin k → Fin d`. -/
def gcdAllProb (k d : ℕ) : ℝ :=
  ((Finset.univ.filter (fun t : Fin k → Fin d => gcdAll t = 1)).card : ℝ) /
    ((Fintype.card (Fin k → Fin d) : ℕ) : ℝ)

/-! ## Lemma E.2: two samples are coprime with probability at least `1/2` -/

/-- **Lemma E.2** (Lomont, arXiv `quant-ph/0411037`, p. 78).  For `n > 0`, two
independently and uniformly chosen integers `a, b ∈ {0,…,n}` satisfy
`gcd(a,b) = 1` with probability at least `1/2`.

The paper's proof: `Pr[max{a,b} = c] = (2c+1)/(n+1)²`; conditioning on the
larger value being `c > 0`, the second is coprime to it with probability
`φ(c)/c`; hence `p_n = Σ_c (2c+1)φ(c)/((n+1)² c)`, which the paper rearranges
to (233), lower-bounds by (234), and then uses Lemma E.1
(`Σ_{c≤n} φ(c) − 3n²/π² < n ln n`) together with monotonicity of
`f(n) = ((2n²+4n)/(n+1)⁴)(3n²−π²n ln n)/π²` for `n ≥ 4` and `f(94) > 1/2`;
the finitely many cases `n ≤ 93` are checked directly from (233).

Gap: neither Lemma E.1 (the totient summatory estimate) nor the finite
verification `f(94) > 1/2` / `n ≤ 93` is available in this paper-layer
development.  Candidate dependencies: `Nat.totient`, `Nat.totient_spec`,
`Finset.sum_filter`, `Nat.card_coprime`, `Real.log_le_sub_one_of_pos`,
`Nat.div`, and `norm_num` for the finite range.  Suggested handoff: prove the
counting identity for `Pr[max = c]` by summing `2c+1` over the matrix entries,
then replicate (233)--(235); the `n ≤ 93` range can be discharged by `decide`
or `norm_num` on rational arithmetic.  Note `Nat.Coprime 0 0` is false, as in
the paper (`gcd(0,0) = 0 ≠ 1`). -/
def lemma_E2Statement (n : ℕ) (hn : 0 < n) : Prop :=
    (1 : ℝ) / 2 ≤ coprimePairProb n

/-! ## Lemma E.3: `k` samples are coprime with exponentially high probability -/

/-- **Lemma E.3** (Lomont, arXiv `quant-ph/0411037`, p. 78).  For `k ≥ 2` and
`d ≥ 2`, `k` independent uniform samples from `{0,…,d-1}` have `gcd` equal to
`1` with probability at least `1 − (1/2)^{k/2}`.

The paper pairs the samples: if any pair `(t_{2j-1}, t_{2j})` is coprime then
the full gcd is `1`; by Lemma E.2 each pair fails to be coprime with
probability at most `1/2`, so with `⌊k/2⌋` independent pairs the failure
probability is at most `(1/2)^{⌊k/2⌋} ≤ (1/2)^{k/2}`.  (Samples are drawn with
replacement, so the pairs are independent.)

Gap: the pair-decomposition argument and the union bound over `⌊k/2⌋` pairs
require a product-space counting lemma and the monotonicity of `x ↦ (1/2)^x`.
Candidate dependencies: `lemma_E2`, `Finset.univ_product_univ`,
`Fintype.card_pi`, `Real.rpow_le_rpow_of_exponent_le` (base `< 1` reverses the
inequality), and `Nat.floor_le`.  Suggested handoff: identify
`Fin k → Fin d` with `(Fin 2 → Fin d)^{k/2}` on the paired coordinates and
apply Lemma E.2 to each pair; then bound `(1/2)^{⌊k/2⌋}` by
`(1/2)^{k/2}` using `Real.rpow_le_rpow_of_exponent_le` with `1/2 ≤ 1`. -/
def lemma_E3Statement (k d : ℕ) (hk : 2 ≤ k) (hd : 2 ≤ d) : Prop :=
    1 - Real.rpow (1 / 2 : ℝ) ((k : ℝ) / 2) ≤ gcdAllProb k d

end

end Qatlib.Papers.HiddenSubgrp04.MainResults
