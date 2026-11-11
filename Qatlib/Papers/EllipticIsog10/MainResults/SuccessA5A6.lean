/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false

/-!
# Lemmas A.5 and A.6: constant success probability of Algorithms 6 and 7

Paper: Childs, Jao, Soukharev, *Constructing elliptic curve isogenies in quantum
subexponential time*, arXiv:1012.4019v3, Appendix A.

**Lemma A.5** (Algorithm 6, cancelling low-order bits): the routine succeeds with
probability `Ω(1)` provided `k ≥ ℓ' - ℓ + 1`.  In the proof there are at most
`2^{ℓ'-ℓ}` "bad" remainders `r`, each occurring with probability `2^{-k}`, so the
probability of the abort `ν = 1` is at most `2^{ℓ'-ℓ-k} ≤ 1/2`; the projection of
Step 7 fails with probability at most `1/3 + o(1)`.

**Lemma A.6** (Algorithm 7, zeroing undesired components): the routine succeeds
with probability `Ω(1)` provided `B/B' ≤ 2^k/(2k)`.  There are at most `kB/B'`
bad measurement outcomes `q`, each with probability `2^{-k}`, so the abort
probability is at most `kB/(B' 2^k) ≤ 1/2`; again the projection fails with
probability at most `1/3 + o(1)`.

This module formalizes the two bad-outcome unions (`lemmaA5_bad_bound`,
`lemmaA6_bad_bound`) and the constant-success composition
(`lemmaA5_success`, `lemmaA6_success`).  The distribution of the projection
failure probability, the "correctness" of the routines and the exact constant
`1/3` of the projection step are taken from the source's analysis; see the PR
notes.
-/

set_option autoImplicit false

namespace Qatlib.Papers.EllipticIsog10.MainResults

/-- **Lemma A.5, bad-remainder union bound.**  If `ℓ ≤ ℓ'` and
`k ≥ ℓ' - ℓ + 1`, the probability that the measured remainder is bad,
`2^{ℓ'-ℓ} / 2^k`, is at most `1/2`. -/
theorem lemmaA5_bad_bound (l l' k : ℕ) (_hll : l ≤ l')
    (hk : l' - l + 1 ≤ k) :
    (2 : ℝ) ^ (l' - l) / (2 : ℝ) ^ k ≤ 1 / 2 := by
  have hbase : (2 : ℝ) ^ (l' - l + 1) ≤ (2 : ℝ) ^ k :=
    pow_le_pow_right₀ (by norm_num) hk
  have hexp : (2 : ℝ) ^ (l' - l + 1) = 2 * (2 : ℝ) ^ (l' - l) := by
    rw [pow_succ]
    ring
  have hden : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) k
  rw [div_le_iff₀ hden]
  nlinarith [hbase, hexp]

/-- **Lemma A.5, constant success.**  If the bad-outcome stage survives with
probability at least `1/2` and the projection survives with probability at least
`1/2` (the source's `1 - 1/3 - o(1)`), the combined success probability is at
least `1/4`, a positive constant, i.e. `Ω(1)`. -/
theorem lemmaA5_success {pbad pproj : ℝ} (hbad : pbad ≤ 1 / 2)
    (hproj : 1 / 2 ≤ pproj) :
    1 / 4 ≤ (1 - pbad) * pproj := by
  have h1 : (1 : ℝ) / 2 ≤ 1 - pbad := by linarith
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hm := mul_le_mul h1 hproj hhalf (by linarith : (0 : ℝ) ≤ 1 - pbad)
  have hc : (1 / 2 : ℝ) * (1 / 2) = 1 / 4 := by norm_num
  linarith [hm, hc]

/-- **Lemma A.5 assembled.**  The bad-remainder probability is at most `1/2` and
the projection keeps at least `1/2`, so the routine reaches a correct output with
constant probability. -/
theorem lemmaA5 (l l' k : ℕ) (hll : l ≤ l') (hk : l' - l + 1 ≤ k)
    {pproj : ℝ} (hproj : 1 / 2 ≤ pproj) :
    (2 : ℝ) ^ (l' - l) / (2 : ℝ) ^ k ≤ 1 / 2 ∧
      1 / 4 ≤ (1 - (2 : ℝ) ^ (l' - l) / (2 : ℝ) ^ k) * pproj :=
  ⟨lemmaA5_bad_bound l l' k hll hk,
    lemmaA5_success (lemmaA5_bad_bound l l' k hll hk) hproj⟩

/-- **Lemma A.6, bad-outcome union bound.**  If `k, B' > 0` and
`B/B' ≤ 2^k/(2k)`, the probability of a bad measurement outcome `q`,
`kB/(B' 2^k)`, is at most `1/2`. -/
theorem lemmaA6_bad_bound (k B B' : ℕ) (hk : 0 < k) (hB' : 0 < B')
    (hratio : (B : ℝ) / (B' : ℝ) ≤ (2 : ℝ) ^ k / (2 * (k : ℝ))) :
    (k : ℝ) * (B : ℝ) / ((B' : ℝ) * 2 ^ k) ≤ 1 / 2 := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hB'pos : (0 : ℝ) < (B' : ℝ) := by exact_mod_cast hB'
  have hbb : (B : ℝ) ≤ ((2 : ℝ) ^ k / (2 * (k : ℝ))) * (B' : ℝ) := by
    have := mul_le_mul_of_nonneg_right hratio (le_of_lt hB'pos)
    rwa [div_mul_cancel₀ _ (ne_of_gt hB'pos)] at this
  have hmain : (k : ℝ) * (B : ℝ) ≤ (2 : ℝ) ^ k * (B' : ℝ) / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hbb (le_of_lt hkpos)
    have heq : (k : ℝ) * (((2 : ℝ) ^ k / (2 * (k : ℝ))) * (B' : ℝ))
        = (2 : ℝ) ^ k * (B' : ℝ) / 2 := by
      field_simp
    linarith [hmul, heq]
  have hden : (0 : ℝ) < (B' : ℝ) * 2 ^ k := by positivity
  rw [div_le_iff₀ hden]
  nlinarith [hmain]

/-- **Lemma A.6, constant success.**  If the bad-outcome stage survives with
probability at least `1/2` and the projection survives with probability at least
`1/2`, the combined success probability is at least `1/4`. -/
theorem lemmaA6_success {pbad pproj : ℝ} (hbad : pbad ≤ 1 / 2)
    (hproj : 1 / 2 ≤ pproj) :
    1 / 4 ≤ (1 - pbad) * pproj :=
  lemmaA5_success hbad hproj

/-- **Lemma A.6 assembled.**  The bad-outcome probability is at most `1/2` and the
projection keeps at least `1/2`, so Algorithm 7 succeeds with constant
probability. -/
theorem lemmaA6 (k B B' : ℕ) (hk : 0 < k) (hB' : 0 < B')
    (hratio : (B : ℝ) / (B' : ℝ) ≤ (2 : ℝ) ^ k / (2 * (k : ℝ)))
    {pproj : ℝ} (hproj : 1 / 2 ≤ pproj) :
    (k : ℝ) * (B : ℝ) / ((B' : ℝ) * 2 ^ k) ≤ 1 / 2 ∧
      1 / 4 ≤ (1 - (k : ℝ) * (B : ℝ) / ((B' : ℝ) * 2 ^ k)) * pproj :=
  ⟨lemmaA6_bad_bound k B B' hk hB' hratio,
    lemmaA6_success (lemmaA6_bad_bound k B B' hk hB' hratio) hproj⟩

end Qatlib.Papers.EllipticIsog10.MainResults
