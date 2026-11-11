/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExpSpeedup10.MainResults.Model.SourceComplexity

set_option backward.isDefEq.respectTransparency false

/-!
# ExpSpeedup10 — Proposition VI.5 (uniform random circuits are 3-designs)

Brandão–Horodecki, *Exponential Quantum Speed-ups are Generic*,
fixed arXiv:1010.3654**v2** (16 Apr 2013).
Proposition VI.5, Section VI p. 21 (line 1250); proof pp. 21–22.

Statement: uniform random circuits on `n` qubits with `5n² log(1/ε)` gates
approximate a unitary 3-design to error `ε`.

Route of the paper: Eq. (89)–(93) compares the local gap with the uniform gap
via the `ℓ∞ → ℓ1` mixing estimate, giving the residual `(1 − 1/(5n²))^k`.
Choosing `k ≥ 5n² log(1/ε)` makes it at most `ε`.

This file proves the final real-analytic inequality.
-/

set_option autoImplicit false
noncomputable section

open Matrix BigOperators
open scoped Classical

namespace Qatlib.Papers.ExpSpeedup10.MainResults
namespace PropVI5

open Model

/-- Proposition VI.5 (Section VI p. 21, proof pp. 21–22): `k` gates of a
uniform random circuit give a twirl residual `(1 − 1/(5n²))^k`, which is at
most `ε` once `5n² log(1/ε) ≤ k`. -/
theorem proposition_VI_5_uniform_random_circuits
    (n k : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hk : 5 * (n : ℝ) ^ 2 * Real.log (1 / ε) ≤ (k : ℝ)) :
    sourceUniformCircuitResidual n k ≤ ε := by
  unfold sourceUniformCircuitResidual
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set x : ℝ := 1 / (5 * (n : ℝ) ^ 2) with hxdef
  have h5n : (0 : ℝ) < 5 * (n : ℝ) ^ 2 := by positivity
  have hxpos : 0 < x := by rw [hxdef]; positivity
  have hxle : x ≤ 1 := by
    rw [hxdef, div_le_one h5n]
    nlinarith
  have hbase_nonneg : (0 : ℝ) ≤ 1 - x := by linarith
  have hbase_le : (1 - x) ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  calc (1 - x) ^ k
      ≤ (Real.exp (-x)) ^ k := pow_le_pow_left₀ hbase_nonneg hbase_le k
    _ = Real.exp ((k : ℝ) * (-x)) := (Real.exp_nat_mul (-x) k).symm
    _ = Real.exp (-((k : ℝ) / (5 * (n : ℝ) ^ 2))) := by
        congr 1
        rw [hxdef]
        ring
    _ ≤ Real.exp (-(Real.log (1 / ε))) := by
        apply Real.exp_le_exp.mpr
        have hk' : Real.log (1 / ε) ≤ (k : ℝ) / (5 * (n : ℝ) ^ 2) := by
          rw [le_div_iff₀ h5n]
          linarith
        linarith
    _ = ε := by
        rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 1 / ε), one_div, inv_inv]

end PropVI5
end Qatlib.Papers.ExpSpeedup10.MainResults
