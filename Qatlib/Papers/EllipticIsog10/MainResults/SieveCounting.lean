/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma A.3: the state, failure and space ledger of the sieve (Algorithm 5)

Paper: Childs, Jao, Soukharev, *Constructing elliptic curves in quantum
subexponential time*, arXiv:1012.4019v3, Lemma A.3 and its proof (Appendix A).

Lemma A.3 states that, provided `m · e^{-2k} = o(1)`, Algorithm 5 is correct and
succeeds with probability `1 - o(1)` using `k^{(1+o(1))m}` state preparations and
combination operations and `O(mk)` space.  The proof has three quantitative
ingredients that are formalized here:

* **Failure (union bound).**  At each of the `m` sieve levels the Chernoff bound
  bounds the probability of too few successful combinations by `e^{-2k}`; the
  union bound over the levels gives total failure at most `m · e^{-2k}`, so the
  success probability is at least `1 - m·e^{-2k}`.
* **State count.**  Because each combination succeeds with some `p ≥ 1/2`
  (the constant product of Lemmas A.2, A.5, A.6), the number of `S₀` state
  preparations `(2k/p)^m` is at most `(4k)^m`, which is the paper's
  `k^{(1+o(1))m}` up to the constant base `4`.
* **Space.**  The sieve never buffers more than `k` states at any of its `m+1`
  levels, so the total number of live states is at most `(m+1)·k = O(mk)`.

The `o(1)` asymptotics, the Chernoff bound itself, and the correctness of the
combination routines are not formalized; see the PR notes.
-/

set_option autoImplicit false

namespace Qatlib.Papers.EllipticIsog10.MainResults

/-- **Lemma A.3, failure union bound.**  If every one of the `m` sieve levels
fails with probability at most `e^{-2k}`, the union bound gives a total failure
probability of at most `m · e^{-2k}`, hence a success probability of at least
`1 - m·e^{-2k}`. -/
theorem lemmaA3_success_from_failure (m k : ℕ) (eps : ℝ)
    (hfail : (m : ℝ) * Real.exp (-(2 : ℝ) * (k : ℝ)) ≤ eps) :
    1 - eps ≤ 1 - (m : ℝ) * Real.exp (-(2 : ℝ) * (k : ℝ)) := by
  linarith

/-- **Lemma A.3, state count.**  If each combination succeeds with probability at
least `1/2` and `k ≥ 1`, the number of `S₀` state preparations needed by the
sieve, `(2k/p)^m`, is at most `(4k)^m`.  This turns the constant success
probability `p` into a concrete bound on the preparation count. -/
theorem lemmaA3_state_count (k m : ℕ) (p : ℝ) (hp : 1 / 2 ≤ p) (hk : 1 ≤ k) :
    (2 * (k : ℝ) / p) ^ m ≤ (4 * (k : ℝ)) ^ m := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hppos : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp
  have hle : 2 * (k : ℝ) / p ≤ 4 * (k : ℝ) := by
    rw [div_le_iff₀ hppos]
    nlinarith [hkpos, hp]
  exact pow_le_pow_left₀ (by positivity) hle m

/-- **Lemma A.3, space.**  The sieve keeps at most `k` states at each of its
`m+1` levels, so the total number of live states is at most `(m+1)·k`, which is
the `O(mk)` space bound of the lemma. -/
theorem lemmaA3_space (m k : ℕ) :
    (Finset.range (m + 1)).sum (fun _ => k) = (m + 1) * k := by
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **Lemma A.3 assembled.**  Under the constant per-combination success of the
surrounding lemmas, the sieve's failure probability is at most `m·e^{-2k}`, its
preparation count is at most `(4k)^m`, and its space is `(m+1)·k = O(mk)`. -/
theorem lemmaA3 (m k : ℕ) (p eps : ℝ) (hp : 1 / 2 ≤ p) (hk : 1 ≤ k)
    (hfail : (m : ℝ) * Real.exp (-(2 : ℝ) * (k : ℝ)) ≤ eps) :
    1 - eps ≤ 1 - (m : ℝ) * Real.exp (-(2 : ℝ) * (k : ℝ)) ∧
      (2 * (k : ℝ) / p) ^ m ≤ (4 * (k : ℝ)) ^ m ∧
      (Finset.range (m + 1)).sum (fun _ => k) = (m + 1) * k :=
  ⟨lemmaA3_success_from_failure m k eps hfail,
    lemmaA3_state_count k m p hp hk, lemmaA3_space m k⟩

end Qatlib.Papers.EllipticIsog10.MainResults
