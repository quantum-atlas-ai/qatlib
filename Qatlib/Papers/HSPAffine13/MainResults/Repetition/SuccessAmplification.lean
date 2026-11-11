/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 6: repetition amplification

The last step of the paper computes `T_k` with per-run success probability at
least `φ(q - 1) / (q - 1)`, and cites the Hardy--Wright estimate

```
φ(n) / n ≥ e^{-γ} / (log log n + 3 / log log n) > 1 / (2 log log n).
```

Running `-2 log log(q - 1) log ε` times then raises the success probability to
`1 - ε`.

We isolate the elementary probability step, taking the Hardy--Wright bound as
an explicit hypothesis `hphi` (the cited number-theory input), and prove the
failure bound.  This is the algorithmic content of Lemma 6; the totient
estimate itself is a separate number-theory theorem and is not reproved here.
-/

set_option autoImplicit false

namespace Qatlib.Papers.HSPAffine13.MainResults

/-- **Repetition amplification.**  If a single run succeeds with probability at
least `1 / (2 L)` with `L = log log n ≥ 1`, then after `k ≥ -2 L log ε`
independent runs the failure probability is at most `ε`. -/
theorem failure_pow_le_of_per_run (p ε L : ℝ) (k : ℕ) (hL : 1 ≤ L)
    (hp1 : p ≤ 1) (hp : 1 / (2 * L) ≤ p) (hε0 : 0 < ε)
    (hk : -2 * L * Real.log ε ≤ (k : ℝ)) :
    (1 - p) ^ k ≤ ε := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have h2L : 0 < 2 * L := by positivity
  have hfrac_nonneg : 0 ≤ 1 / (2 * L) := le_of_lt (by positivity)
  have hfrac_le_one : 1 / (2 * L) ≤ 1 := by
    have : 1 ≤ 2 * L := by nlinarith
    exact div_le_one_of_le₀ this (by positivity)
  have hbase_nonneg : 0 ≤ 1 - p := by linarith
  have hbase_le : 1 - p ≤ 1 - 1 / (2 * L) := by linarith
  have hbase_nonneg' : 0 ≤ 1 - 1 / (2 * L) := by linarith
  have hbase_pos : 0 < 1 - 1 / (2 * L) := by
    have : 1 / (2 * L) < 1 := by
      rw [div_lt_one h2L]
      nlinarith
    linarith
  have hpow_le : (1 - p) ^ k ≤ (1 - 1 / (2 * L)) ^ k :=
    pow_le_pow_left₀ hbase_nonneg hbase_le k
  have hlogbase : Real.log (1 - 1 / (2 * L)) ≤ -(1 / (2 * L)) := by
    have h := Real.log_le_sub_one_of_pos hbase_pos
    linarith
  have hlogpow : Real.log ((1 - 1 / (2 * L)) ^ k) ≤ Real.log ε := by
    rw [Real.log_pow]
    have hmul : (k : ℝ) * Real.log (1 - 1 / (2 * L)) ≤
        (k : ℝ) * (-(1 / (2 * L))) :=
      mul_le_mul_of_nonneg_left hlogbase (Nat.cast_nonneg k)
    have hkdiv : -Real.log ε ≤ (k : ℝ) / (2 * L) := by
      have hdiv : (-2 * L * Real.log ε) / (2 * L) ≤ (k : ℝ) / (2 * L) :=
        div_le_div_of_nonneg_right hk (le_of_lt h2L)
      have hleft : (-2 * L * Real.log ε) / (2 * L) = -Real.log ε := by
        field_simp [h2L.ne']
      calc
        -Real.log ε = (-2 * L * Real.log ε) / (2 * L) := hleft.symm
        _ ≤ (k : ℝ) / (2 * L) := hdiv
    have hneg : -((k : ℝ) / (2 * L)) ≤ Real.log ε := by
      have := neg_le_neg hkdiv
      simpa using this
    have hright : (k : ℝ) * (-(1 / (2 * L))) = -((k : ℝ) / (2 * L)) := by ring
    calc
      (k : ℝ) * Real.log (1 - 1 / (2 * L)) ≤ (k : ℝ) * (-(1 / (2 * L))) := hmul
      _ = -((k : ℝ) / (2 * L)) := hright
      _ ≤ Real.log ε := hneg
  have hpos : 0 < (1 - 1 / (2 * L)) ^ k := pow_pos hbase_pos k
  exact hpow_le.trans ((Real.log_le_log_iff hpos hε0).mp hlogpow)

/-- **Lemma 6 (HSPAffine13), with the cited totient estimate.**  Let `n = q - 1`
and suppose a single run of the `T_k` subroutine succeeds with probability at
least `φ(n) / n`, and the Hardy--Wright bound
`φ(n) / n ≥ 1 / (2 log log n)` holds.  Then `k = ⌈-2 log log n log ε⌉` runs
fail with probability at most `ε`. -/
theorem lemma6_failure_bound (n : ℕ) (hn : 1 < n) (hL : 1 ≤ Real.log (Real.log n))
    (hphi : 1 / (2 * Real.log (Real.log n)) ≤ (Nat.totient n : ℝ) / (n : ℝ))
    {ε : ℝ} (hε0 : 0 < ε) :
    (1 - (Nat.totient n : ℝ) / (n : ℝ)) ^
        (Nat.ceil (-2 * Real.log (Real.log n) * Real.log ε)) ≤ ε := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hn)
  have htot_le : (Nat.totient n : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.totient_le n
  have hp1 : (Nat.totient n : ℝ) / (n : ℝ) ≤ 1 := by
    exact (div_le_one hn0).mpr htot_le
  have hk : -2 * Real.log (Real.log n) * Real.log ε ≤
      (Nat.ceil (-2 * Real.log (Real.log n) * Real.log ε) : ℝ) :=
    Nat.le_ceil _
  exact failure_pow_le_of_per_run ((Nat.totient n : ℝ) / (n : ℝ)) ε
    (Real.log (Real.log n)) _ hL hp1 hphi hε0 (by simpa using hk)

end Qatlib.Papers.HSPAffine13.MainResults
