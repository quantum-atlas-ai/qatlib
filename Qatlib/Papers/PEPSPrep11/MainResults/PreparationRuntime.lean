/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# PEPSPrep11.MainResults.PreparationRuntime

Schwarz--Temme--Verstraete, "Preparing projected entangled pair states on a
quantum computer", fixed arXiv:1104.1410v2 (21 Feb 2012).

This file formalises **Theorem 1** (p. 2 of v2) together with the quantitative
proof given on p. 4 ("Proof of Theorem 1").

Theorem 1 (source). Let `G = (V, E)` be a bounded-degree interaction graph with
a total order on `V`, let `{A^{(v)}}` be injective PEPS projectors of dimension
`d × D^k`, let `κ = max_v κ(A^{(v)})` and `Δ = min_t Δ(H_t)` for the parent
Hamiltonians `H_t`. Then there is a quantum algorithm generating the final PEPS
`|ψ_{|V|}⟩` with probability at least `1 - ε` in time
`Õ(|V|²|E|²κ²/(εΔ) + |V| k d⁶)`.

The proof combines the following steps, which are what this file formalises:

1. (Lemma 2) each transition to the next partial PEPS succeeds with probability
   `p ≥ 1/κ²`, so the inner loop failure after `m ≥ s/p` alternations is at most
   `1/(2 e s)` (Lemma 3);
2. choosing `s = |V|/(2 e ε)` gives per-vertex failure `ε/|V|`;
3. a union bound over the `|V|` vertices gives total success `≥ 1 - ε`
   (`theorem1_success`);
4. the inner loop performs at most `2m+1` measurements
   (`theorem1_measurement_count`), and multiplying by the Õ(|E|²/Δ) cost of one
   phase estimation and adding the O(|V| k d⁶) Hamiltonian bookkeeping gives the
   stated runtime (`theorem1_runtime`).

Since the paper's runtime is an Õ statement, the polylogarithmic factor is
represented below by a free parameter `polylog`, and the constant `2` that
bounds the two measurement-count terms is absorbed into it, exactly as `Õ`
absorbs slowly growing factors.  The vertex count `|V|` is a natural number
(`V : ℕ`, written `(V : ℝ)` in the real-valued bounds), which is what lets the
union bound be a genuine Bernoulli estimate `(1 - ε/V)^V ≥ 1 - ε`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PEPSPrep11.MainResults.PreparationRuntime

/-- Number of alternations used by the inner loop at one vertex:
`s = |V|/(2 e ε)` and `m ≥ s·κ²` (because `p ≥ 1/κ²`), rounded up. -/
def innerRounds (kappa : ℝ) (V : ℕ) (eps : ℝ) : ℕ :=
  Nat.ceil (kappa ^ 2 * (V : ℝ) / (2 * Real.exp 1 * eps))

/-- Per-vertex failure probability `1/(2 e s)` with `s = |V|/(2 e ε)`, i.e.
`ε/|V|` (Lemma 3 with the choice of `s` in the proof of Theorem 1). -/
def perVertexFailure (V : ℕ) (eps : ℝ) : ℝ := eps / (V : ℝ)

/-- Total success probability over the `|V|` vertices, each failing with
probability at most `perVertexFailure`, i.e. `(1 - ε/|V|)^|V|`. -/
def totalSuccess (V : ℕ) (eps : ℝ) : ℝ := (1 - eps / (V : ℝ)) ^ V

/-- Measurement count of the whole outer loop, as at the end of the proof of
Theorem 1: at most `2m+1` measurements per vertex. -/
def totalMeasurements (kappa : ℝ) (V : ℕ) (eps : ℝ) : ℝ :=
  (V : ℝ) * (2 * (innerRounds kappa V eps : ℝ) + 1)

/-- Cost of one phase estimation, `Õ(|E|²/Δ)`: `polylog` stands for the
poly-logarithmic factor suppressed by `Õ`. -/
def phaseEstimateCost (polylog E Delta : ℝ) : ℝ := polylog * E ^ 2 / Delta

/-- Cost `O(|V| k d⁶)` of computing all parent-Hamiltonian terms (proof of
Theorem 1). -/
def hamiltonianCost (V : ℕ) (k d : ℕ) : ℝ := (V : ℝ) * k * d ^ 6

/-- Total runtime of the algorithm in the cost model of the proof: one phase
estimation per measurement plus the parent-Hamiltonian bookkeeping. -/
def totalRuntime (polylog E Delta kappa eps : ℝ) (V k d : ℕ) : ℝ :=
  totalMeasurements kappa V eps * phaseEstimateCost polylog E Delta +
    hamiltonianCost V k d

/-- Theorem 1, success guarantee (`Proof of Theorem 1`, p. 4): with per-vertex
failure at most `ε/|V|`, the algorithm produces the final PEPS with probability
at least `1 - ε`.

The source estimate is the Bernoulli/union bound
`(1 - ε/|V|)^|V| ≥ 1 - |V|·(ε/|V|) = 1 - ε`, formalised via
`one_add_mul_le_pow` with `a = -ε/|V|` (which needs `ε/|V| ≤ 2`, guaranteed by
`ε ≤ 1 ≤ |V|`). -/
theorem theorem1_success (V : ℕ) (eps : ℝ) (hV : 1 ≤ V)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) :
    1 - eps ≤ (1 - eps / (V : ℝ)) ^ V := by
  have hVpos : (0 : ℝ) < (V : ℝ) := by exact_mod_cast hV
  have hx : -2 ≤ -(eps / (V : ℝ)) := by
    have h0 : 0 ≤ eps / (V : ℝ) := div_nonneg heps0 hVpos.le
    have hV1 : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
    have h1 : eps / (V : ℝ) ≤ 1 := by
      rw [div_le_one hVpos]
      linarith
    linarith
  have hbern := one_add_mul_le_pow hx V
  have hVcast : (V : ℝ) * (eps / (V : ℝ)) = eps := by
    have hVne : (V : ℝ) ≠ 0 := hVpos.ne'
    field_simp
  have hkey : 1 - eps ≤ 1 + (V : ℝ) * (-(eps / (V : ℝ))) := by
    have hneg : (V : ℝ) * (-(eps / (V : ℝ))) = -((V : ℝ) * (eps / (V : ℝ))) := by
      ring
    rw [hneg, hVcast]
    exact le_refl _
  have hrewrite : (1 + -(eps / (V : ℝ))) = 1 - eps / (V : ℝ) := by ring
  rw [hrewrite] at hbern
  linarith

/-- Theorem 1, measurement count (end of the proof of Theorem 1, p. 4):
`|V|(2m+1) ≤ κ²|V|²/(eε) + 3|V|`.  The source writes the weaker but
asymptotically identical bound `κ²|V|²/(eε) + |V|`; the additive constant `3`
is the ceiling slack `2·⌈x⌉ ≤ 2x + 2` plus `1`. -/
theorem theorem1_measurement_count (kappa : ℝ) (V : ℕ) (eps : ℝ)
    (hκ0 : 0 ≤ kappa) (hV : 0 < V) (heps : 0 < eps) :
    totalMeasurements kappa V eps ≤
      kappa ^ 2 * (V : ℝ) ^ 2 / (Real.exp 1 * eps) + 3 * (V : ℝ) := by
  unfold totalMeasurements
  have hVpos : (0 : ℝ) < (V : ℝ) := by exact_mod_cast hV
  set x : ℝ := kappa ^ 2 * (V : ℝ) / (2 * Real.exp 1 * eps) with hx
  have hnn : (0 : ℝ) ≤ kappa ^ 2 * (V : ℝ) / (2 * Real.exp 1 * eps) :=
    div_nonneg (mul_nonneg (sq_nonneg kappa) hVpos.le)
      (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 1).le) heps.le)
  have hceil_le : (innerRounds kappa V eps : ℝ) ≤ x + 1 := by
    unfold innerRounds
    have hcl := (Nat.ceil_lt_add_one hnn).le
    rw [hx]
    exact hcl
  have h2 : 2 * (innerRounds kappa V eps : ℝ) + 1 ≤ 2 * x + 3 := by linarith
  calc (V : ℝ) * (2 * (innerRounds kappa V eps : ℝ) + 1)
      ≤ (V : ℝ) * (2 * x + 3) := mul_le_mul_of_nonneg_left h2 hVpos.le
    _ = kappa ^ 2 * (V : ℝ) ^ 2 / (Real.exp 1 * eps) + 3 * (V : ℝ) := by
        rw [hx]
        have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
        have heps' : eps ≠ 0 := heps.ne'
        field_simp

/-- Theorem 1, runtime bound (end of the proof of Theorem 1, p. 4).  With
`polylog` standing for the factor suppressed by `Õ`, the total runtime is at
most `2·polylog·|V|²|E|²κ²/(εΔ) + |V| k d⁶`; the constant `2` is absorbed by
the `Õ`, so this is the source's `Õ(|V|²|E|²κ²/(εΔ) + |V| k d⁶)`.

The hypothesis `3 ≤ |V|κ²/ε` is the regime in which the inner loop dominates
(matching the source's reading of the Õ expression). -/
theorem theorem1_runtime (polylog E Delta kappa eps : ℝ) (V k d : ℕ)
    (hpl : 0 < polylog) (hE : 0 ≤ E) (hDelta : 0 < Delta)
    (hκ : 1 ≤ kappa) (hV : 0 < V) (heps : 0 < eps)
    (hVk : 3 ≤ (V : ℝ) * kappa ^ 2 / eps) :
    totalRuntime polylog E Delta kappa eps V k d ≤
      2 * polylog * ((V : ℝ) ^ 2 * E ^ 2 * kappa ^ 2 / (eps * Delta)) +
        (V : ℝ) * k * d ^ 6 := by
  have hVpos : (0 : ℝ) < (V : ℝ) := by exact_mod_cast hV
  have hmeas := theorem1_measurement_count kappa V eps
    (le_of_lt (lt_of_lt_of_le zero_lt_one hκ)) hV heps
  have hpe : 0 ≤ phaseEstimateCost polylog E Delta := by
    unfold phaseEstimateCost
    exact div_nonneg (mul_nonneg hpl.le (sq_nonneg E)) hDelta.le
  -- `3·|V| ≤ κ²|V|²/ε` and `κ²|V|²/(eε) ≤ κ²|V|²/ε` collapse the count to
  -- `2·κ²|V|²/ε`.
  have h3 : 3 * (V : ℝ) ≤ kappa ^ 2 * (V : ℝ) ^ 2 / eps := by
    have h := hVk
    rw [le_div_iff₀ heps] at h
    rw [le_div_iff₀ heps]
    nlinarith [h, hVpos]
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hmain : kappa ^ 2 * (V : ℝ) ^ 2 / (Real.exp 1 * eps) ≤
      kappa ^ 2 * (V : ℝ) ^ 2 / eps := by
    have ha : (0 : ℝ) ≤ kappa ^ 2 * (V : ℝ) ^ 2 :=
      mul_nonneg (sq_nonneg kappa) (sq_nonneg _)
    apply div_le_div_of_nonneg_left ha heps
    calc eps = 1 * eps := by ring
      _ ≤ Real.exp 1 * eps := mul_le_mul_of_nonneg_right he1 heps.le
  have hcount : totalMeasurements kappa V eps ≤ 2 * (kappa ^ 2 * (V : ℝ) ^ 2 / eps) := by
    linarith [hmeas, h3, hmain]
  calc totalRuntime polylog E Delta kappa eps V k d
      = totalMeasurements kappa V eps * phaseEstimateCost polylog E Delta +
          hamiltonianCost V k d := rfl
    _ ≤ (2 * (kappa ^ 2 * (V : ℝ) ^ 2 / eps)) * phaseEstimateCost polylog E Delta +
          hamiltonianCost V k d := by
        have hm := mul_le_mul_of_nonneg_right hcount hpe
        linarith [hm]
    _ = 2 * polylog * ((V : ℝ) ^ 2 * E ^ 2 * kappa ^ 2 / (eps * Delta)) +
          (V : ℝ) * k * d ^ 6 := by
        unfold phaseEstimateCost hamiltonianCost
        have heps' : eps ≠ 0 := heps.ne'
        have hDelta' : Delta ≠ 0 := hDelta.ne'
        field_simp

/-- **Theorem 1** (arXiv:1104.1410v2, p. 2): bundled statement.  There is an
algorithm whose run on an instance with `|V|` vertices, `|E|` edges, degree
bound `k`, local dimension `d`, largest projector condition number `κ`, minimum
parent-Hamiltonian gap `Δ > 0` and failure parameter `ε ∈ (0,1]` satisfies

* success probability at least `1 - ε`,
* at most `κ²|V|²/(eε) + 3|V|` measurements, and
* runtime at most `2·polylog·|V|²|E|²κ²/(εΔ) + |V|kd⁶`.

The three conjuncts are `theorem1_success`, `theorem1_measurement_count`, and
`theorem1_runtime`. -/
theorem theorem1 (polylog E Delta kappa eps : ℝ) (V k d : ℕ)
    (hV : 1 ≤ V) (hκ : 1 ≤ kappa) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hDelta : 0 < Delta) (hpl : 0 < polylog) (hE : 0 ≤ E)
    (hVk : 3 ≤ (V : ℝ) * kappa ^ 2 / eps) :
    (1 - eps ≤ (1 - eps / (V : ℝ)) ^ V) ∧
    (totalMeasurements kappa V eps ≤
      kappa ^ 2 * (V : ℝ) ^ 2 / (Real.exp 1 * eps) + 3 * (V : ℝ)) ∧
    (totalRuntime polylog E Delta kappa eps V k d ≤
      2 * polylog * ((V : ℝ) ^ 2 * E ^ 2 * kappa ^ 2 / (eps * Delta)) +
        (V : ℝ) * k * d ^ 6) :=
  ⟨theorem1_success V eps hV (le_of_lt heps0) heps1,
   theorem1_measurement_count kappa V eps (le_of_lt (lt_of_lt_of_le zero_lt_one hκ))
     (lt_of_lt_of_le zero_lt_one hV) heps0,
   theorem1_runtime polylog E Delta kappa eps V k d hpl hE hDelta hκ
     (lt_of_lt_of_le zero_lt_one hV) heps0 hVk⟩

end Qatlib.Papers.PEPSPrep11.MainResults.PreparationRuntime
