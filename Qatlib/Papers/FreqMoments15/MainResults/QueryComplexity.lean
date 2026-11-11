/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FreqMoments15.MainResults.FrequencyMomentModel
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# Query-complexity results for the frequency moments

Paper: Ashley Montanaro, *The quantum complexity of approximating the frequency moments*
(arXiv:1505.00113v3, 4 Aug 2016).  This file states the paper's query-model upper and lower
bounds: Theorem 2 (§2.1 p. 6), Theorem 5 (§2.2 pp. 7–8), Theorem 6 (§2.4 pp. 9–10) and
Theorem 7 (§2.4 p. 10).

The query model is the one fixed in `FrequencyMomentModel`: a `QueryProgram` is a fixed
unitary circuit on a query/value register with arbitrary fixed workspace and output
register, using the unitary value oracle `|i,x⟩ ↦ |i, x + a_i⟩`; its query cost is
`QueryCount` of the circuit and its success probability is the honest Born probability
`relSuccess` that the decoded output is within relative error `ε`.

Model boundary (recorded for each statement): the paper's algorithms also use a
pairwise-independent hash family and the subroutines of Theorems 1/3; those are not
separately modelled, the theorems below state the *existence* of a query program with the
paper's query cost and success guarantee, which is exactly the paper's conclusion.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FreqMoments15.MainResults

open Qatlib.Foundations.QueryWordCore.Circuit
open scoped BigOperators

/-! ## Theorem 2: `F_0` query upper bound (§2.1 p. 6) -/

/-
Gap record for `theorem2_F0_query_upper`.

* Paper version: arXiv:1505.00113v3 (4 Aug 2016), Theorem 2, §2.1 p. 6 (Algorithm 1 p. 6).
* Original proof route: Algorithm 1 picks a hash family `h : [m] → [n/ε²]`, reads the stream,
  keeps the `d` smallest distinct hash values, lets `v` be the `d`-th smallest, and outputs
  `dM/v`; the multiplicative guarantee follows from the proof of Theorem 1 of Bar-Yossef et
  al. [8] (`dM/v` is within `1+ε` with probability `2/3−1/m`), and the query bound is the one
  from Theorem 1.
* Lean gap: the repo has the circuit/query-count machinery but no formal quantum approximate
  counting (Theorem 1 of [8]), no hash-family sampling model, and no formal `dM/v`
  estimator.  Only the existential `QueryProgram` interface is available, so the algorithmic
  construction cannot be instantiated.
* Candidate reusable dependencies: `QuantumAlgorithm.Foundations.ReferenceError.MixturePaths.Circuit`
  (`Circuit`, `QueryCount`, `Run`, `IsUnitaryCircuit`); `QueryProgram`, `QueryProgram.successF0`
  and `streamOracle_unitary` in `FrequencyMomentModel` (the value oracle and its unitarity are
  fully formalised there).
* Suggested takeover: state a `CountingLemma` interface (amplitude-estimation query bound) as a
  hypothesis record, prove the `dM/v` estimator's relative-error lemma separately, and instantiate
  `QueryProgram` by `circuit := counting-circuit` using `streamOracle`; the missing mathematics
  is then isolated to that interface.
-/
/-- **Theorem 2 — statement registration** (paper §2.1 p. 6).  Algorithm 1 makes
`O(√n/ε)` queries and outputs an estimate of `F_0` accurate up to relative error `ε` with
probability at least `3/5 − 1/m`.

Formalised as: there is a constant `C > 0` such that for every `n, m` (`m ≥ 2`) and every
`ε > 0` there is a query program with at most `C·√n/ε` queries whose relative-error success
probability is at least `3/5 − 1/m` on every stream.

**Status.** The statement is registered as a `Prop`-valued definition; the counting
subroutine of Theorem 1 of [8] and the hash-based `dM/v` estimator are not formalised. -/
def theorem2_F0_query_upper_statement : Prop :=
    ∃ C : ℝ, 0 < C ∧
      ∀ (n m : ℕ) [NeZero m], 1 < m → 0 < n → ∀ ε : ℝ, 0 < ε →
        ∃ P : QueryProgram n m 1,
          (QueryCount P.circuit : ℝ) ≤ C * Real.sqrt (n : ℝ) / ε ∧
          ∀ a : Stream n m, (3 : ℝ) / 5 - 1 / (m : ℝ) ≤ P.successF0 a ε

/-! ## Theorem 5: `F_k` query upper bound (§2.2 pp. 7–8) -/

/-
Gap record for `theorem5_Fk_query_upper`.

* Paper version: arXiv:1505.00113v3 (4 Aug 2016), Theorem 5, §2.2 pp. 7–8 (Algorithm 2 p. 8).
* Original proof route: Algorithm 2 counts `k`-wise collisions among a random sample of `ℓ`
  positions; Lemma 4 gives `E[C_k] = C(ℓ,k)F_k/n^k` and the variance bound; Markov's inequality
  and the variance bound determine a sample size `ℓ` within a constant factor of `n/F_k^{1/k}`;
  the sample is then processed with Belovs' `k`-distinctness algorithm (Theorem 3, query cost
  `o(n^{3/4} log(1/δ))`), a union bound giving total failure `1/4`.
* Lean gap: Theorem 3 (Belovs `k`-distinctness) is not formalised, and the expected-query and
  sampling analyses are not present.  Lemma 4's expectation is proved here; its variance part is
  `lemma4_variance_statement` (see `Lemma4CollisionMoments.lean`).
* Candidate reusable dependencies: `lemma4_expectation`, `lemma4_variance`,
  `collCount`, `sampleExp`, `sampleVar` (this development); `QueryProgram`/`QueryCount`
  (model); no `k`-distinctness counterpart in Frozen v2.0.2.
* Suggested takeover: introduce a hypothesis record `DistinctnessAlgorithm` carrying the query
  bound of Theorem 3, prove the Markov/variance sample-size lemma (`ℓ = Θ(n/F_k^{1/k})` gives
  `C_k ≥ 1` with high probability), then instantiate `QueryProgram` with that record; the
  remaining gap is the Belovs algorithm itself.
-/
/-- **Theorem 5 — statement registration** (paper §2.2 pp. 7–8).  Algorithm 2 outputs an
approximation of `F_k` accurate up to relative error `ε` with probability at least `3/4`,
using an expected number of queries
`O((n^{(1−1/k)(1−2^{k−2}/(2^k−1))}/ε²) log(n/ε))`.

Formalised as: there is a constant `C > 0` such that for every `k ≥ 2`, every stream length
`n`, universe size `m` and `ε > 0`, there is a query program with at most the stated number
of queries whose relative-error success probability is at least `3/4` on every stream.

**Status.** The statement is registered as a `Prop`-valued definition; the sampler analysis
(with the registered variance bound) and Belovs' `k`-distinctness subroutine are not
formalised. -/
def theorem5_Fk_query_upper_statement : Prop :=
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ), 2 ≤ k →
      ∀ (n m : ℕ) [NeZero m], 0 < n → ∀ ε : ℝ, 0 < ε →
        ∃ P : QueryProgram n m 1,
          (QueryCount P.circuit : ℝ) ≤
            C * Real.rpow (n : ℝ)
                ((1 - 1 / (k : ℝ)) *
                  (1 - Real.rpow 2 ((k : ℝ) - 2) / (Real.rpow 2 (k : ℝ) - 1)))
              / ε ^ 2 * Real.log ((n : ℝ) / ε) ∧
          ∀ a : Stream n m, (3 : ℝ) / 4 ≤ P.successFk a k ε

/-! ## Theorem 6: query lower bounds (§2.4 pp. 9–10) -/

/-
Gap record for `theorem6_query_lower` (five conjuncts).

* Paper version: arXiv:1505.00113v3 (4 Aug 2016), Theorem 6, §2.4 pp. 9–10.
* Original proof route: (i) `F_0`: reduction from the threshold function `Th_d` on `n` bits,
  using `F_0` relative error `1/(4d)` to decide `Th_d`, with the `Ω(√(dn))` threshold lower
  bound [9] and `d = ⌈1/ε⌉`; (ii) `k > 1`: reduction from quantum counting [39], splicing a
  sequence with `F_k = 2n − n^{1/k}` and one with `F_k = 2n + 8εn − (n(1+8ε))^{1/k}`;
  (iii) `k > 1`: reduction from the collision problem with small range (`F_k = n` versus
  `n^{2k−1}`), lower bound `Ω(n^{1/3})` [35,5]; (iv) `k = ∞`: reduction from element
  distinctness (`Ω(n^{2/3})`) [5]; (v) `k = ∞`: reduction from the counting problem
  `n/2` versus `(1+ε)n/2`, giving `Ω(1/ε)` [39].
* Lean gap: none of the five oracle lower-bound techniques (threshold-function bound, quantum
  counting, collision problem, element distinctness, polynomial method of [39]) is formalised
  in the repo, and no reduction framework from a query problem to `QueryProgram` exists.
* Candidate reusable dependencies: `QueryProgram`, `Fk`, `F0`, `Finf`, `Stream` (model);
  `QuantumAlgorithm.Foundations.ReferenceError.MixturePaths.Circuit.QueryCount`.
  A search of Frozen v2.0.2 for `elementDistinctness`/`collisionProblem`/`threshold` lower
  bounds returns no counterpart (searched for the mathematical content, not only names).
* Suggested takeover: define a `QueryProblem` record with a `queryComplexity` lower-bound
  field, formalise the five reductions as maps of problem instances, and discharge the five
  base lower bounds as imported hypotheses; the reductions themselves are elementary.
-/
/-- **Theorem 6 — statement registration** (paper §2.4 pp. 9–10).  Assume `m ≥ n + 1` and
`ε < 1/4`.  The quantum query complexity of estimating `F_0` up to relative error `ε` with
failure probability at most `1/3` is `Ω(√(n/ε))`.  For any `k > 1` it is
`Ω(n^{1/2−1/(2k)}/ε)` and also `Ω(n^{1/3})`.  For `k = ∞` it is `Ω(n^{2/3})`, and also
`Ω(1/ε)` for any `m ≥ 2`.

Each lower bound is stated as: there is an absolute constant `c > 0` such that every query
program achieving relative-error `ε` success probability `≥ 2/3` on all streams uses at
least `c` times the stated quantity of queries.

**Status.** The statement is registered as a `Prop`-valued definition; the five oracle
lower-bound techniques (threshold function, quantum counting, collision problem, element
distinctness, polynomial method) and the reductions to them are not formalised. -/
def theorem6_query_lower_statement : Prop :=
    -- `F_0`: `Ω(√(n/ε))`
    (∃ c : ℝ, 0 < c ∧
      ∀ (n m : ℕ) [NeZero m], n + 1 ≤ m → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
        ∀ (P : QueryProgram n m 1),
          (∀ a : Stream n m, (2 : ℝ) / 3 ≤ P.successF0 a ε) →
            c * Real.sqrt ((n : ℝ) / ε) ≤ (QueryCount P.circuit : ℝ)) ∧
    -- `k > 1`: `Ω(n^{1/2−1/(2k)}/ε)`
    (∃ c : ℝ, 0 < c ∧
      ∀ (k : ℕ), 2 ≤ k →
      ∀ (n m : ℕ) [NeZero m], n + 1 ≤ m → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
        ∀ (P : QueryProgram n m 1),
          (∀ a : Stream n m, (2 : ℝ) / 3 ≤ P.successFk a k ε) →
            c * Real.rpow (n : ℝ) (1 / 2 - 1 / (2 * (k : ℝ))) / ε
              ≤ (QueryCount P.circuit : ℝ)) ∧
    -- `k > 1`: `Ω(n^{1/3})` (collision problem reduction)
    (∃ c : ℝ, 0 < c ∧
      ∀ (k : ℕ), 2 ≤ k →
      ∀ (n m : ℕ) [NeZero m], n + 1 ≤ m → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
        ∀ (P : QueryProgram n m 1),
          (∀ a : Stream n m, (2 : ℝ) / 3 ≤ P.successFk a k ε) →
            c * Real.rpow (n : ℝ) (1 / 3) ≤ (QueryCount P.circuit : ℝ)) ∧
    -- `k = ∞`: `Ω(n^{2/3})` (element distinctness reduction)
    (∃ c : ℝ, 0 < c ∧
      ∀ (n m : ℕ) [NeZero m], n + 1 ≤ m → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
        ∀ (P : QueryProgram n m 1),
          (∀ a : Stream n m, (2 : ℝ) / 3 ≤ P.successFinf a ε) →
            c * Real.rpow (n : ℝ) (2 / 3) ≤ (QueryCount P.circuit : ℝ)) ∧
    -- `k = ∞`: `Ω(1/ε)` for `m ≥ 2`
    (∃ c : ℝ, 0 < c ∧
      ∀ (n m : ℕ) [NeZero m], 2 ≤ m → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
        ∀ (P : QueryProgram n m 1),
          (∀ a : Stream n m, (2 : ℝ) / 3 ≤ P.successFinf a ε) →
            c / ε ≤ (QueryCount P.circuit : ℝ))

/-! ## Theorem 7: `Θ(n)` query complexity at `O(1/n)` error (§2.4 p. 10) -/

/-
Gap record for `theorem7_query_theta`.

* Paper version: arXiv:1505.00113v3 (4 Aug 2016), Theorem 7, §2.4 p. 10.
* Original proof route: the lower bound is a reduction from the Beame--Machmouchi problem
  [11] on a sequence with `m ≥ n/2+1` (all values paired except possibly two), for which
  `F_k(S_1) = 2^{k−1}n` and `F_k(S_2) = 2^{k−1}n + 2` (and `n/2` versus `n/2−1` for `k=0`),
  so `O(1/n)` relative error distinguishes the two cases; the `k = ∞` case reuses the `Ω(1/ε)`
  bound of Theorem 6.  The upper bound is the trivial `O(n)`-query classical algorithm
  (read the whole stream).
* Lean gap: the Beame--Machmouchi `Θ(n)` problem is not formalised, and the `O(n)` upper
  half needs a `QueryProgram` that performs `n` classical reads, i.e. circuit synthesis for a
  classical scan from `streamOracle` queries; neither is available.
* Candidate reusable dependencies: `Lemma4CollisionMoments` (for `F_k` arithmetic),
  `QueryProgram`/`QueryCount`, `streamOracle_unitary`; the `F_k` values on the two Beame--
  Machmouchi instances can be computed from `freq`/`Fk` directly.
* Suggested takeover: prove the `F_k` evaluations on the two instances by `Finset.card`/
  `Finset.sum` computation on `ZMod m` (`m ≥ n/2+1`), then add the `Θ(n)` base lower bound as
  a hypothesis; for the upper bound, build a `Circuit` of `n` `Step.query` steps and show
  `QueryCount = n` by `queryCount_append`/`queryCount_cons`.
-/
/-- **Theorem 7 — statement registration** (paper §2.4 p. 10).  For any `k ≠ 1` and
`m ≥ n/2 + 1`, the quantum query complexity of computing `F_k` up to `O(1/n)` relative
error with failure probability at most `1/3` is `Θ(n)`.  For `k = ∞` the bound still holds
for any `m ≥ 2`.

We instantiate the `O(1/n)` error by the fixed accuracy `1/n`, and state both the lower and
the upper half of `Θ(n)` as existence of positive constants.

**Status.** The statement is registered as a `Prop`-valued definition; the
Beame--Machmouchi lower bound and the `O(n)` classical-scan circuit are not formalised. -/
def theorem7_query_theta_statement : Prop :=
    (∀ (k : ℕ), k ≠ 1 →
      ∀ (n m : ℕ) [NeZero m], n / 2 + 1 ≤ m →
        (∃ c : ℝ, 0 < c ∧
          ∀ (P : QueryProgram n m 1),
            (∀ a : Stream n m, (2 : ℝ) / 3 ≤ P.successFk a k (1 / (n : ℝ))) →
              c * (n : ℝ) ≤ (QueryCount P.circuit : ℝ)) ∧
        (∃ C : ℝ, 0 < C ∧
          ∃ P : QueryProgram n m 1,
            (QueryCount P.circuit : ℝ) ≤ C * (n : ℝ) ∧
            ∀ a : Stream n m, (2 : ℝ) / 3 ≤ P.successFk a k (1 / (n : ℝ)))) ∧
    (∀ (n m : ℕ) [NeZero m], 2 ≤ m →
        (∃ c : ℝ, 0 < c ∧
          ∀ (P : QueryProgram n m 1),
            (∀ a : Stream n m, (2 : ℝ) / 3 ≤ P.successFinf a (1 / (n : ℝ))) →
              c * (n : ℝ) ≤ (QueryCount P.circuit : ℝ)) ∧
        (∃ C : ℝ, 0 < C ∧
          ∃ P : QueryProgram n m 1,
            (QueryCount P.circuit : ℝ) ≤ C * (n : ℝ) ∧
            ∀ a : Stream n m, (2 : ℝ) / 3 ≤ P.successFinf a (1 / (n : ℝ))))

end Qatlib.Papers.FreqMoments15.MainResults
