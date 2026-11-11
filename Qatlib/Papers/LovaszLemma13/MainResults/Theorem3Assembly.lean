/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Qatlib.Papers.LovaszLemma13.MainResults.Lemma9ParameterBound

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 3 of arXiv:1311.6474v1: assembly layer

Source: Martin Schwarz, Toby S. Cubitt, Frank Verstraete,
*An Information-Theoretic Proof of the Constructive Commutative Quantum Lovász Local Lemma*,
arXiv:1311.6474v1, Theorem 3 (Section 1, p. 2) and its proof in Appendix A.1 (pp. 11–13).

Theorem 3 says that for commuting `k`-local projectors of rank at most `r` with interaction degree
`d ≤ 2 ^ k / (r e)` there is a quantum algorithm with run time `O(m + log(1/ε))` that returns a
state `σ` with `tr(Π_i σ) = 0` for all `i` with probability `1 - ε`.

This file formalises the two concluding ingredients of the proof:

* `theorem3_parameter_bound`: the run-time parameter `N` of Algorithm 2, defined implicitly by
  `N = a log₂ N + b`, is bounded by `b + 3 a (log₂ b + 1)` (Eq. (46)–(47) together with Lemma 9).
  The run-time is `T = m + N d`.
* `theorem3_energy_zero_of_mix`: zero energy is a *linear* condition, so the state returned by the
  algorithm — the mixture `ρ_P = (1 - P_N) ρ_C (1 - P_N) / (1 - tr(P_N ρ_C))` of the histories that
  terminated (Appendix A.1, after Eq. (49)) — has zero energy once every history in the mixture
  does: `tr(Π_i ρ_P) = 0` for all `i`.

The remaining ingredients of Theorem 3 — the explicit unitary Algorithm 2 with its coherent
measurements, the structure theorem for the run-time state (Lemma 6), the compression/trace bound
(Lemma 5 with Lemma 7) and the success probability `≥ 1 - ε` — are *not* formalised here; the file
therefore does not prove Theorem 3 as a whole.
-/

namespace Qatlib.Papers.LovaszLemma13.MainResults

open Matrix

open scoped BigOperators

set_option autoImplicit false

/-! ## The run-time parameter

Algorithm 2 sets `N = b + 3 a (log₂ b + 1)` with `a = (k - log(der))⁻¹` and
`b = (m + log(1/ε)) / (k - log(der))` and runs for `T = m + N d` steps.  The next theorem shows that
the implicitly defined `N = a log₂ N + b` of Eq. (45) is no larger than this explicit choice, which
is the content of Eq. (46)–(47) and Lemma 9. -/

/-- **Theorem 3, run-time parameter (Eq. (46)–(47), (60)).**  For parameters `1 ≤ a ≤ b` in the
regime of the paper, the implicitly defined `N = a log₂ N + b`, written as `N = t + a log₂ t` with
`t > 0`, is at most `b + 3 a (log₂ b + 1)`. -/
theorem theorem3_parameter_bound (a b t N : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) (ht : 0 < t)
    (hNpos : 0 < N) (hN₁ : N = t + a * Real.logb 2 t) (hN₂ : N = a * Real.logb 2 N + b) :
    N ≤ b + 3 * a * (Real.logb 2 b + 1) := by
  have ha0 : 0 ≤ a := by linarith
  exact (lemma9_implicit_bound a b t N ha0 ht hNpos hN₁ hN₂).trans
    (lemma9_explicit_bound a b ha hab)

/-- **Theorem 3, run time.**  With the explicit parameter `N` of the previous theorem, Algorithm 2
runs for `T = m + N d` steps, hence `T ≤ m + d (b + 3 a (log₂ b + 1))`.  For constant `d` and
`k - log(der)` this is the paper's `O(m + log(1/ε))` bound. -/
theorem theorem3_runtime (m d N b a T : ℝ) (hd : 0 ≤ d)
    (hN : N ≤ b + 3 * a * (Real.logb 2 b + 1)) (hT : T = m + d * N) :
    T ≤ m + d * (b + 3 * a * (Real.logb 2 b + 1)) := by
  rw [hT]
  have h := mul_le_mul_of_nonneg_left hN hd
  linarith

/-! ## Zero energy is preserved by mixtures -/

/-- **Theorem 3, energy conclusion (Appendix A.1, after Eq. (49)).**  Energy zero is a linear
condition: if every component `σ j` of a mixture satisfies `tr(Π_i σ j) = 0` for all `i`, then the
mixture `∑ j, c j • σ j` does too.  Applied to the returned state `ρ_P`, which is a mixture of the
terminated histories, this is the paper's final step "the `W` subsystem of the returned state is a
mixture of zero energy states and has thus energy zero itself". -/
theorem theorem3_energy_zero_of_mix {ν κ : Type*} [Fintype ν] [DecidableEq ν] [Fintype κ]
    (Proj : κ → Matrix ν ν ℂ) (σ : ν → Matrix ν ν ℂ) (c : ν → ℂ)
    (hσ : ∀ j i, (Proj i * σ j).trace = 0) :
    ∀ i, (Proj i * (∑ j, c j • σ j)).trace = 0 := by
  intro i
  rw [Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_eq_zero ?_
  intro j _
  rw [Matrix.mul_smul, Matrix.trace_smul, hσ j i, smul_zero]

/-- **Theorem 3, energy conclusion for a normalised mixture.**  The same statement for a state
written as a convex combination with real weights, the form in which the returned state
`ρ_P = (1 - P_N) ρ_C (1 - P_N) / (1 - tr(P_N ρ_C))` appears. -/
theorem theorem3_energy_zero_of_weighted_mix {ν κ : Type*} [Fintype ν] [DecidableEq ν]
    [Fintype κ] (Proj : κ → Matrix ν ν ℂ) (σ : ν → Matrix ν ν ℂ) (w : ν → ℝ)
    (hσ : ∀ j i, (Proj i * σ j).trace = 0) :
    ∀ i, (Proj i * (∑ j, ((w j : ℂ)) • σ j)).trace = 0 :=
  theorem3_energy_zero_of_mix Proj σ (fun j => (w j : ℂ)) hσ

end Qatlib.Papers.LovaszLemma13.MainResults
