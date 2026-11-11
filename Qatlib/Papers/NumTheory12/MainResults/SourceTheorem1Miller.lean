/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FourierRecovery.ModularFourier.ShorOrder

set_option backward.isDefEq.respectTransparency false

/-!
# NumTheory12.MainResults — Theorem 1 (Miller's factoring reduction)

Source: Wim van Dam and Yoshitaka Sasaki, *Quantum algorithms for problems in
number theory, algebraic geometry, and group theory*, fixed arXiv:1206.6126
(2012). Theorem 1 (Miller, 1976), §3.1, page 5 (lines 117–124 of the pinned
text).

Paper statement. For a given odd integer `N` with at least two distinct prime
factors:

1. pick a random `a ∈ {2, 3, …, N−1}`;
2. compute `gcd(a, N)`: a value different from `1` is a nontrivial factor;
3. find the multiplicative order `r` of `a` modulo `N`; odd `r` is discarded;
4. compute `gcd(a^{r/2} − 1, N)`: a value different from `1` is a nontrivial
   factor; otherwise retry.

Repeating the routine finds all factors of `N`.

Lean decomposition (one theorem per step, all about *actual* programs):

* step 2 — `theorem1_classical_gcd_yields_factor`: proved directly in `ℕ`;
  from `2 ≤ a < N` and `gcd(a,N) ≠ 1` the gcd is a nontrivial divisor;
* steps 3–4 — `theorem1_half_power_gcd_yields_factor`: the Frozen v2.0.2
  checked program `orderFactor N a r` returns only `1 < d < N` with `d ∣ N`
  (`QuantumAlgorithm.Papers.ShorFactoring97.OrderRecovery.orderFactor_sound`);
* steps 2–4 jointly — `theorem1_attempt_yields_nontrivial_factor`: every
  branch of one attempt (`attemptOutcomeFactor`, covering the classical gcd
  branch and the quantum order branch) returns a nontrivial divisor or nothing
  (`attemptOutcomeFactor_sound`);
* last sentence — `theorem1_finds_all_factors`: with a split program that never
  refuses on a composite modulus, the recursion `factorTreeOf` has leaves
  multiplying back to the modulus and all prime (`factorTreeOf_complete`).

The randomness of step 1 and the probability that step 3/4 succeeds are the
content of Lemma 1, formalized in `SourceLemma1Probability.lean`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NumTheory12.MainResults

open Qatlib.Concepts.FourierRecovery.ModularFourier.ShorOrder
open Qatlib.Concepts.PeriodSampling.OrderRecovery

/-- **Theorem 1 (Miller, 1976), step 2** (arXiv:1206.6126, p. 5): for `2 ≤ a < N`,
if `gcd(a, N) ≠ 1` then `gcd(a, N)` is a nontrivial factor of `N`, i.e.
`1 < gcd(a,N) < N` and `gcd(a,N) ∣ N`.

Here `a < N` encodes the paper's range `a ∈ {2, …, N−1}`; without it the gcd
could equal `N`. -/
theorem theorem1_classical_gcd_yields_factor (N a : ℕ) (hN : 1 < N)
    (ha2 : 2 ≤ a) (haN : a < N) (hgcd : Nat.gcd a N ≠ 1) :
    1 < Nat.gcd a N ∧ Nat.gcd a N < N ∧ Nat.gcd a N ∣ N := by
  have hpos : 0 < Nat.gcd a N := Nat.gcd_pos_of_pos_left N (by omega)
  have hle : Nat.gcd a N ≤ a := Nat.gcd_le_left N (by omega)
  refine ⟨?_, lt_of_le_of_lt hle haN, Nat.gcd_dvd_right a N⟩
  omega

/-- **Theorem 1 (Miller, 1976), steps 3–4** (arXiv:1206.6126, p. 5): the checked
half-order/gcd program `orderFactor N a r` — which computes
`gcd(a^{r/2} − 1, N)` for even `r` and validates the result — returns only
nontrivial factors.

Bridges the Frozen v2.0.2 theorem
`QuantumAlgorithm.Papers.ShorFactoring97.OrderRecovery.orderFactor_sound`. -/
theorem theorem1_half_power_gcd_yields_factor (N : ℕ) [NeZero N]
    (a : (ZMod N)ˣ) (r d : ℕ) (h : orderFactor N a r = some d) :
    1 < d ∧ d < N ∧ d ∣ N :=
  orderFactor_sound N a r d h

/-- **Theorem 1 (Miller, 1976), steps 2–4** (arXiv:1206.6126, p. 5): whatever
nontrivial factor a single attempt returns, it is a proper divisor of `N`.
The attempt outcome covers both the classical gcd branch (step 2) and the
quantum order branch (steps 3–4).

Bridges the Frozen v2.0.2 theorem
`QuantumAlgorithm.Concepts.FourierRecovery.ModularFourier.ShorOrderCompletion.attemptOutcomeFactor_sound`. -/
theorem theorem1_attempt_yields_nontrivial_factor (N M : ℕ) [NeZero N]
    (t : AttemptOutcome N M) (d : ℕ)
    (h : attemptOutcomeFactor N M t = some d) :
    1 < d ∧ d < N ∧ d ∣ N :=
  attemptOutcomeFactor_sound N M t d h

/-- **Theorem 1 (Miller, 1976), repeated routine** (arXiv:1206.6126, p. 5, last
sentence: "By repeating this routine we can find all factors of `N`").

Given a split program `split` that, on every composite modulus in range, answers
a certified proper divisor, the factor tree `factorTreeOf split n` has leaves
whose product is `n` and all of whose leaves are prime (up to the trivial
leaves `p ≤ 1`).

Bridges the Frozen v2.0.2 theorem
`QuantumAlgorithm.Concepts.FourierRecovery.ModularFourier.ShorOrderCompletion.factorTreeOf_complete`. -/
theorem theorem1_finds_all_factors (split : ∀ n, Option (ProperDivisor n)) :
    ∀ n, (∀ m, 2 ≤ m → m ≤ n → ∀ h : ¬Nat.Prime m, split m ≠ none) →
      (factorTreeOf split n).complete :=
  factorTreeOf_complete split

/-- **Theorem 1 (Miller, 1976)** (arXiv:1206.6126, p. 5), headline form: under the
paper's standing hypotheses (`N` odd, `1 < N`, at least two distinct prime
factors), any nontrivial factor returned by one attempt is a proper divisor of
`N`.

The hypotheses are the paper's setting rather than soundness conditions: the
divisor property itself holds unconditionally (see
`theorem1_attempt_yields_nontrivial_factor`); the hypotheses are what makes the
retry loop of Lemma 1 terminate with probability at least `1/2`. -/
theorem theorem1_miller (N M : ℕ) [NeZero N] (hN : 1 < N) (hodd : Odd N)
    (hk : 2 ≤ N.primeFactors.card) (t : AttemptOutcome N M) (d : ℕ)
    (h : attemptOutcomeFactor N M t = some d) :
    1 < d ∧ d < N ∧ d ∣ N :=
  attemptOutcomeFactor_sound N M t d h

end Qatlib.Papers.NumTheory12.MainResults
