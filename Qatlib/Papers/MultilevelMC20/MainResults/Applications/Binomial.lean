/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultilevelMC20.MainResults.CostModel.CostAsymptotics

set_option backward.isDefEq.respectTransparency false

/-!
# Propositions 4 and Theorem 4: the binomial option pricing model

An, Linden, Liu, Montanaro, Shao, Wang,
*Quantum-accelerated multilevel Monte Carlo methods for stochastic differential equations
in mathematical finance*, fixed arXiv:2012.06283v2 (accepted in Quantum 2021-06-16).

For a piecewise constant payoff (8.9) the zeroth-order oracle (8.10) evaluated on the
binomial tree (8.1) costs `O(1)` per node, independently of the number of steps `n`,
because one only compares the binomial draw with the thresholds `k*_j` of (8.11).  The
BOPM estimator runs `n = O(1/ε²)` steps, so one sample costs `O(log n) = O(log 1/ε)`
(a binomial `B(n,p)` draw can be sampled in `O(log n)` expected time).  Proposition 4
repeats this `O(ε^{-2})` times classically, giving `Õ(ε^{-2})` (8.12); Theorem 4 applies
quantum amplitude estimation to the same sampler, giving `Õ(ε^{-1})` (8.14).

The formal statements below isolate exactly these two composition steps:

* `proposition4`: `N ε = O(ε^{-2})` repetitions of a per-sample cost `per ε = O(log 1/ε)`
  give `Õ(ε^{-2})`;
* `theorem4`: a quantum estimator at accuracy `ε` costing `Õ(ε^{-1})` per call, applied to
  a sampler of polylogarithmic cost, gives `Õ(ε^{-1})`.
-/

set_option autoImplicit false
noncomputable section

open Filter Asymptotics
open scoped Topology BigOperators

namespace Qatlib.Papers.MultilevelMC20.MainResults

/-- The distinguished bound `costBound 2 1 0` is `ε^{-2} log (1/ε)` for `ε > 0`. -/
theorem costBound_two_one_zero {ε : ℝ} (hε : 0 < ε) :
    costBound 2 1 0 ε = ε ^ (-2 : ℝ) * Real.log ε⁻¹ := by
  unfold costBound
  rw [Real.rpow_one, Real.rpow_zero, mul_one]

/-- Proposition 4 (p. 24, (8.12)): `O(ε^{-2})` classical repetitions of a BOPM sample of
cost `O(log 1/ε)` yield total cost `Õ(ε^{-2})`.

`N` is the number of Monte Carlo repetitions (bounded by `C ε^{-2}`) and `per` the cost of
one binomial sample (bounded by `C log 1/ε`), matching the proof of Proposition 4: "the
cost of each iteration is `O(log n)`" with `n = O(1/ε²)`, repeated `O(ε^{-2})` times. -/
theorem proposition4 {C : ℝ} (hC : 0 < C) {N per : ℝ → ℝ}
    (hN : ∀ᶠ ε : ℝ in epsZero, 0 ≤ N ε ∧ N ε ≤ C * ε ^ (-2 : ℝ))
    (hper : ∀ᶠ ε : ℝ in epsZero, 0 ≤ per ε ∧ per ε ≤ C * Real.log ε⁻¹) :
    CostTildeClass 2 (fun ε => N ε * per ε) := by
  apply costClass_toTilde
  refine costClass_of_bound (p := 2) (q := 1) (s := 0) (M := C * C) ?_
  filter_upwards [hN, hper, eventually_pos_epsZero, eventually_small]
    with ε hNε hperε hε0 hsmall
  have hε1 : ε ≤ 1 := by
    have hexp_lt : Real.exp (-(Real.exp 1)) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith [Real.exp_pos 1]
    exact le_trans (le_of_lt hsmall.2) (le_of_lt hexp_lt)
  have hlog : 0 ≤ Real.log ε⁻¹ := by
    apply Real.log_nonneg
    rw [one_le_inv₀ hε0]
    exact hε1
  have hrpow : 0 ≤ ε ^ (-2 : ℝ) := Real.rpow_nonneg hε0.le _
  have hnorm : ‖costBound 2 1 0 ε‖ = ε ^ (-2 : ℝ) * Real.log ε⁻¹ := by
    rw [costBound_two_one_zero hε0, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hrpow hlog)]
  rw [hnorm, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hNε.1 hperε.1)]
  calc N ε * per ε ≤ (C * ε ^ (-2 : ℝ)) * (C * Real.log ε⁻¹) :=
        mul_le_mul hNε.2 hperε.2 hperε.1 (mul_nonneg hC.le hrpow)
    _ = C * C * (ε ^ (-2 : ℝ) * Real.log ε⁻¹) := by ring

/-- Theorem 4 (p. 24, (8.14)): quantum amplitude estimation (cost `Õ(ε^{-1})` for
accuracy `ε`) applied to a BOPM sampler of `Õ(1)` cost per call gives `Õ(ε^{-1})`. -/
theorem theorem4 {qcost per : ℝ → ℝ} (hq : CostTildeClass 1 qcost)
    (hper : CostTildeClass 0 per) :
    CostTildeClass 1 (fun ε => qcost ε * per ε) := by
  convert! costTildeClass_mul hq hper using 1 <;> first | rfl | simp

end Qatlib.Papers.MultilevelMC20.MainResults
