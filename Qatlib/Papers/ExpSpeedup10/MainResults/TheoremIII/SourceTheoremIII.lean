/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExpSpeedup10.MainResults.Model.SourceComplexity

set_option backward.isDefEq.respectTransparency false

/-!
# ExpSpeedup10 — Theorem III (local random circuits are 3-designs)

Brandão–Horodecki, *Exponential Quantum Speed-ups are Generic*,
fixed arXiv:1010.3654**v2** (16 Apr 2013).
Theorem III, Section I p. 5 (line 239); proof Section VI pp. 16–17.

Statement: local random circuits with `5n log(1/ε)` gates approximate a
unitary 3-design to error `ε`.

Route of the paper: Lemma VI.1 gives `λ₂(M_{t,n}) ≤ 1 − 1/(5n)` and Lemma VI.4
gives `λ₂(M_{t,3}) = 7/10`; together with Eq. (59) the `k`-step twirl difference
obeys `‖G_{μ^{*k},t} − G_{H,t}‖ ≤ (1 − 1/(5n))^k`.  Choosing
`k ≥ 5n log(1/ε)` makes this at most `ε`.

This file proves the final real-analytic inequality that is the quantitative
content of Theorem III (the circuit-to-design reduction is `sourceLocalCircuitResidual`).
-/

set_option autoImplicit false
noncomputable section

open Matrix BigOperators
open scoped Classical

namespace Qatlib.Papers.ExpSpeedup10.MainResults
namespace TheoremIII

open Model

/-- Theorem III (Section I p. 5, proof Section VI pp. 16–17): `k` gates of a
local random circuit give a twirl residual `(1 − 1/(5n))^k`, which is at most
`ε` once `5n log(1/ε) ≤ k`. -/
theorem theorem_III_local_random_circuits
    (n k : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hk : 5 * (n : ℝ) * Real.log (1 / ε) ≤ (k : ℝ)) :
    sourceLocalCircuitResidual n k ≤ ε := by
  unfold sourceLocalCircuitResidual
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set x : ℝ := 1 / (5 * (n : ℝ)) with hxdef
  have h5n : (0 : ℝ) < 5 * (n : ℝ) := by positivity
  have hxpos : 0 < x := by rw [hxdef]; positivity
  have hxle : x ≤ 1 := by
    rw [hxdef, div_le_one h5n]
    nlinarith
  have hbase_nonneg : (0 : ℝ) ≤ 1 - x := by linarith
  have hbase_le : (1 - x) ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  have hlog_nonneg : 0 ≤ Real.log (1 / ε) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hε0]
    simpa using hε1
  calc (1 - x) ^ k
      ≤ (Real.exp (-x)) ^ k := pow_le_pow_left₀ hbase_nonneg hbase_le k
    _ = Real.exp ((k : ℝ) * (-x)) := (Real.exp_nat_mul (-x) k).symm
    _ = Real.exp (-((k : ℝ) / (5 * (n : ℝ)))) := by
        congr 1
        rw [hxdef]
        ring
    _ ≤ Real.exp (-(Real.log (1 / ε))) := by
        apply Real.exp_le_exp.mpr
        have hk' : Real.log (1 / ε) ≤ (k : ℝ) / (5 * (n : ℝ)) := by
          rw [le_div_iff₀ h5n]
          linarith
        linarith
    _ = ε := by
        rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 1 / ε), one_div, inv_inv]

end TheoremIII
end Qatlib.Papers.ExpSpeedup10.MainResults
