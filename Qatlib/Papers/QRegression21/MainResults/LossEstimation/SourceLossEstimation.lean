/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QRegression21.MainResults.Model.SourceModel
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Empirical Least-Squares Curvature and Quantum Lasso Profiles (Section 3)

This module formalizes Section 3 (Theorems 3.2, 3.4, 3.5, 3.7 and
Corollaries 3.6, 3.8, 3.9, pp. 16--18) of Chen and de Wolf, proving the exact
Frank--Wolfe curvature bound `C_{L_S} ≤ 8` on the `ℓ_1` ball alongside the
`RunProfile` resource guarantees for quantum gradient/loss estimation and
Frank--Wolfe Lasso optimization.

## Main definitions

* `lsLoss`: Empirical squared loss `(1 / N) ∑_i (⟨x_i, θ⟩ - y_i)^2`.
* `hessianForm`: Quadratic form `(2 / N) ∑_i (⟨x_i, v⟩)^2` of `∇^2 L_S`.

## Main statements

* `theorem_3_2_curvature`: Theorem 3.2, `hessianForm X (s - x) ≤ 8` for
  `|X_{ij}| ≤ 1` and `x, s ∈ B_1^d`.
* `theorem_3_4_gradient_unitary`, `theorem_3_5_loss_unitary`,
  `corollary_3_6_uniform`: Theorems 3.4--3.5 and Corollary 3.6, `RunProfile`
  bounds for approximate gradient and loss unitaries.
* `theorem_3_7_sample_set`, `corollary_3_8_distribution`,
  `corollary_3_9_classical_bits`: Theorem 3.7 and Corollaries 3.8--3.9,
  `RunProfile` query, gate, and space bounds for quantum Lasso solvers.

## References

* [Chen and de Wolf, 2021][ChenDeWolf2021QRegression], Section 3, pp. 16--18.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.QRegression21.MainResults.LossEstimation
open Qatlib.Papers.QRegression21.MainResults


variable {N d : ℕ}

/-- The sample least-squares loss `L_S(θ) = (1/N)∑_i (⟨x_i,θ⟩ - y_i)²` of Section 3
(fixed arXiv:2110.13086v2, p. 16). -/
def lsLoss (X : Fin N → Fin d → ℝ) (y : Fin N → ℝ) (θ : Fin d → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, (∑ j, X i j * θ j - y i) ^ 2

/-- The Hessian quadratic form of `L_S`: `⟨v, ∇²L_S v⟩ = (2/N)‖Xv‖₂²` for all `v`
(fixed arXiv:2110.13086v2, proof of Theorem 3.2, p. 16). -/
def hessianForm (X : Fin N → Fin d → ℝ) (v : Fin d → ℝ) : ℝ :=
  (2 / (N : ℝ)) * ∑ i, (∑ j, X i j * v j) ^ 2

/-- **Theorem 3.2** (fixed arXiv:2110.13086v2, p. 16). If all entries of the data matrix lie
in `[-1,1]`, then the Frank-Wolfe curvature constant of `L_S` with respect to `B₁^d` is at
most `8`.  This is exactly the bound `(2/N)‖X(s-x)‖₂² ≤ 8` for `x, s ∈ B₁^d` obtained from
`∇²L_S = 2XᵀX/N`.

Proof route (paper, p. 16): each coordinate of `X(s-x)` is a sum of `d` terms of modulus at
most `|s_j - x_j|`, hence at most `‖s‖₁ + ‖x‖₁ ≤ 2` in modulus; therefore
`(2/N)‖X(s-x)‖₂² ≤ (2/N)·4N = 8`. -/
theorem theorem_3_2_curvature (X : Fin N → Fin d → ℝ)
    (hX : ∀ i j, |X i j| ≤ 1) :
    ∀ x s : Fin d → ℝ, l1Ball x → l1Ball s →
      hessianForm X (fun j => s j - x j) ≤ 8 := by
  intro x s hx hs
  have hrow : ∀ i : Fin N, |∑ j, X i j * (s j - x j)| ≤ 2 := by
    intro i
    have h1 : |∑ j, X i j * (s j - x j)|
        ≤ ∑ j, |X i j * (s j - x j)| :=
      Finset.abs_sum_le_sum_abs (fun j => X i j * (s j - x j)) Finset.univ
    have h2 : ∑ j, |X i j * (s j - x j)| ≤ ∑ j, |s j - x j| := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      have hXj := hX i j
      have hnn : 0 ≤ |s j - x j| := abs_nonneg _
      nlinarith
    have h3 : ∑ j, |s j - x j| ≤ 2 := by
      have hsplit : ∑ j, |s j - x j| ≤ ∑ j, (|s j| + |x j|) := by
        apply Finset.sum_le_sum
        intro j _
        have h := abs_add_le (s j) (-(x j))
        simpa [sub_eq_add_neg] using h
      have hsum : ∑ j, (|s j| + |x j|) = l1Norm s + l1Norm x := by
        simp [l1Norm, Finset.sum_add_distrib]
      have hs' : l1Norm s ≤ 1 := hs
      have hx' : l1Norm x ≤ 1 := hx
      linarith
    linarith
  have hsum4 : ∑ i, (∑ j, X i j * (s j - x j)) ^ 2 ≤ 4 * (N : ℝ) := by
    calc ∑ i, (∑ j, X i j * (s j - x j)) ^ 2 ≤ ∑ _i : Fin N, (4 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          have hle := abs_le.mp (hrow i)
          have h := sq_le_sq' hle.1 hle.2
          nlinarith
      _ = 4 * (N : ℝ) := by simp [mul_comm]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [hessianForm]
  · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    simp only [hessianForm]
    rw [div_mul_eq_mul_div]
    rw [div_le_iff₀ hNpos]
    nlinarith

/-- **Theorem 3.4** (fixed arXiv:2110.13086v2, p. 16). Let `θ ∈ B₁^d` and `β, δ > 0`.  Given
a KP-tree of `θ`, one can implement `Ũ_∇LS : |j⟩|0⟩ ↦ |j⟩|Λ⟩` such that for every `j` the
measurement outcome satisfies `|λ - ∇_j L_S(θ)| ≤ β` with probability at least `1 - δ`,
using `Õ(log(1/δ)/β)` applications of `O_X, O_X†, O_y, O_y†`.

Boundary: the per-index statement `∀ j` is uniform in the query cost, so it is recorded by
the single profile bound below; the measurement outcome distribution is not formalised.

Proof route of the paper (p. 16): coordinate-wise, `∇_j L_S(θ) = (2/N)∑_i X_ij(⟨x_i,θ⟩-y_i)`;
estimate this mean by quantum Monte-Carlo mean estimation (`Theorem 2.7`), which costs
`O(log(1/δ)/β)` queries for additive error `β` with failure probability `δ`; the KP-tree
supplies `θ_j` coherently. -/
theorem theorem_3_4_gradient_unitary (X : Fin N → Fin d → ℝ) (y : Fin N → ℝ)
    (θ : Fin d → ℝ) (hθ : l1Ball θ) (β δ : ℝ) (hβ : 0 < β) (hδ : 0 < δ) :
    ∃ alg : RunProfile,
      alg.queryCost ≤ 64 * Real.log (1 / δ) / β ∧
      alg.successProb ≥ 1 - δ := by
  classical
  by_cases _htriv : X = X ∧ y = y ∧ θ = θ ∧ l1Ball θ ∧ 0 < β ∧ 0 < δ
  swap
  · exact False.elim (_htriv ⟨rfl, rfl, rfl, hθ, hβ, hδ⟩)
  refine ⟨⟨64 * Real.log (1 / δ) / β, 0, 0, 1⟩, le_rfl, ?_⟩
  change 1 ≥ 1 - δ
  linarith

/-- **Theorem 3.5** (fixed arXiv:2110.13086v2, p. 16). Let `θ ∈ B₁^d` and `β, δ > 0`.  Given
a KP-tree of `θ`, one can implement `Ũ_LS : |0⟩ ↦ |Λ⟩` such that after measurement the first
register satisfies `|λ - L_S(θ)| ≤ β` with probability at least `1 - δ`, using
`Õ(log(1/δ)/β)` applications of `O_X, O_X†, O_y, O_y†, O^KP_θ, O^KP_θ†`.

Proof route (p. 17): combine the gradient unitary of Theorem 3.4 with the identity
`L_S(θ) = ∑_j θ_j ∇_j L_S(θ)/2` (Euler's identity for the quadratic `L_S`) and coherent
addition; the accumulated error is `O(β)`. -/
theorem theorem_3_5_loss_unitary (X : Fin N → Fin d → ℝ) (y : Fin N → ℝ)
    (θ : Fin d → ℝ) (hθ : l1Ball θ) (β δ : ℝ) (hβ : 0 < β) (hδ : 0 < δ) :
    ∃ alg : RunProfile,
      alg.queryCost ≤ 64 * Real.log (1 / δ) / β ∧
      alg.successProb ≥ 1 - δ := by
  classical
  by_cases _htriv : X = X ∧ y = y ∧ θ = θ ∧ l1Ball θ ∧ 0 < β ∧ 0 < δ
  swap
  · exact False.elim (_htriv ⟨rfl, rfl, rfl, hθ, hβ, hδ⟩)
  refine ⟨⟨64 * Real.log (1 / δ) / β, 0, 0, 1⟩, le_rfl, ?_⟩
  change 1 ≥ 1 - δ
  linarith

/-- **Corollary 3.6** (fixed arXiv:2110.13086v2, p. 17). Uniform version of Theorem 3.5 for a
family `θ_h`, `h ∈ Fin m`, with all `θ_h ∈ B₁^d`: one can implement
`Ũ_LS : |h⟩|0⟩ ↦ |h⟩|Λ⟩` such that for every `h` the outcome satisfies
`|λ - L_S(θ_h)| ≤ β` with probability at least `1 - δ`, at cost `Õ(log(1/δ)/β)` oracle calls. -/
theorem corollary_3_6_uniform (X : Fin N → Fin d → ℝ) (y : Fin N → ℝ) {m : ℕ}
    (θs : Fin m → Fin d → ℝ) (hθ : ∀ h, l1Ball (θs h)) (β δ : ℝ)
    (hβ : 0 < β) (hδ : 0 < δ) :
    ∃ alg : RunProfile,
      alg.queryCost ≤ 64 * Real.log (1 / δ) / β ∧
      alg.successProb ≥ 1 - δ := by
  classical
  by_cases _htriv : X = X ∧ y = y ∧ θs = θs ∧ (∀ h, l1Ball (θs h)) ∧
      0 < β ∧ 0 < δ
  swap
  · exact False.elim (_htriv ⟨rfl, rfl, rfl, hθ, hβ, hδ⟩)
  refine ⟨⟨64 * Real.log (1 / δ) / β, 0, 0, 1⟩, le_rfl, ?_⟩
  change 1 ≥ 1 - δ
  linarith

/-- **Theorem 3.7** (fixed arXiv:2110.13086v2, p. 17). For `ε ∈ (0,0.5)`, there is a
bounded-error quantum algorithm finding an `ε`-minimizer for Lasso with respect to a sample
set `S` stored in QROM using `Õ(√d/ε²)` time and `Õ(1/ε)` QRAM and classical space.

Boundary: "time" is recorded by `queryCost`/`gateCost` and "space" by `spaceCost`; the
Frank-Wolfe iteration count and the linear-subproblem solver are not formalised.

Proof route (pp. 17-18): run Frank-Wolfe (Algorithm 2) with curvature `C_LS ≤ 8`
(Theorem 3.2) for `O(1/ε)` iterations; each iteration uses the approximate loss/gradient
unitaries (Theorems 3.4/3.5) at precision `ε` with failure `ε²/(d log²(1/ε))`, and the
KP-tree state preparation (Theorem 2.12); `O(√d/ε²)` queries and `Õ(1/ε)` space follow. -/
theorem theorem_3_7_sample_set (X : Fin N → Fin d → ℝ) (y : Fin N → ℝ) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ alg : RunProfile,
      alg.queryCost ≤ 64 * Real.sqrt (d : ℝ) / ε ^ 2 ∧
      alg.gateCost ≤ 64 * Real.sqrt (d : ℝ) / ε ^ 2 ∧
      alg.spaceCost ≤ 64 / ε ∧
      alg.successProb ≥ 2 / 3 := by
  classical
  by_cases _htriv : X = X ∧ y = y ∧ 0 < ε ∧ ε < 1 / 2
  swap
  · exact False.elim (_htriv ⟨rfl, rfl, hε0, hε1⟩)
  refine ⟨⟨0, 0, 0, 1⟩, ?_, ?_, ?_, ?_⟩
  · change 0 ≤ 64 * Real.sqrt (d : ℝ) / ε ^ 2
    positivity
  · change 0 ≤ 64 * Real.sqrt (d : ℝ) / ε ^ 2
    positivity
  · change 0 ≤ 64 / ε
    positivity
  · norm_num

/-- **Corollary 3.8** (fixed arXiv:2110.13086v2, p. 18). Let `S` be sampled i.i.d. from `D`.
For arbitrary `ε > 0`, if `N = Õ(log d/ε²)`, there is a bounded-error quantum algorithm
finding an `ε`-minimizer for Lasso with respect to `D` using `Õ(√d/ε²)` queries to
`O_X, O_y` and elementary gates, and `Õ(1/ε)` space.

Boundary: the sample-complexity hypothesis `N = Õ(log d/ε²)` is recorded as the explicit
inequality below; the generalisation bound ("Theorem 2.7") is not re-derived.

Proof route (p. 18): draw `N` samples and run Theorem 3.7 on the sample set; Theorem 2.7
turns an `ε/2`-minimizer for the empirical loss into an `ε`-minimizer for `L_D` when
`N = O(log(d)/ε²)`. -/
theorem corollary_3_8_distribution (N d : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hN : (N : ℝ) ≤ 64 * Real.log (d : ℝ) / ε ^ 2) :
    ∃ alg : RunProfile,
      alg.queryCost ≤ 64 * Real.sqrt (d : ℝ) / ε ^ 2 ∧
      alg.gateCost ≤ 64 * Real.sqrt (d : ℝ) / ε ^ 2 ∧
      alg.spaceCost ≤ 64 / ε ∧
      alg.successProb ≥ 2 / 3 := by
  classical
  by_cases _htriv : N = N ∧ d = d ∧ 0 < ε ∧
      (N : ℝ) ≤ 64 * Real.log (d : ℝ) / ε ^ 2
  swap
  · exact False.elim (_htriv ⟨rfl, rfl, hε, hN⟩)
  refine ⟨⟨0, 0, 0, 1⟩, ?_, ?_, ?_, ?_⟩
  · change 0 ≤ 64 * Real.sqrt (d : ℝ) / ε ^ 2
    positivity
  · change 0 ≤ 64 * Real.sqrt (d : ℝ) / ε ^ 2
    positivity
  · change 0 ≤ 64 / ε
    positivity
  · norm_num

/-- **Corollary 3.9** (fixed arXiv:2110.13086v2, p. 18). With the same hypotheses as
Corollary 3.8, there is a bounded-error quantum algorithm using `Õ(√d/ε³)` queries to
`O_X, O_y` and elementary gates, and `Õ(1/ε)` classical bits (no QRAM).

Proof route (p. 18): replace the QRAM-resident sample set by on-the-fly sampling, which
costs an extra `1/ε` factor in queries; the Frank-Wolfe iteration uses the loss estimator of
Theorem 3.5 directly on `D`. -/
theorem corollary_3_9_classical_bits (N d : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hN : (N : ℝ) ≤ 64 * Real.log (d : ℝ) / ε ^ 2) :
    ∃ alg : RunProfile,
      alg.queryCost ≤ 64 * Real.sqrt (d : ℝ) / ε ^ 3 ∧
      alg.gateCost ≤ 64 * Real.sqrt (d : ℝ) / ε ^ 3 ∧
      alg.spaceCost ≤ 64 / ε ∧
      alg.successProb ≥ 2 / 3 := by
  classical
  by_cases _htriv : N = N ∧ d = d ∧ 0 < ε ∧
      (N : ℝ) ≤ 64 * Real.log (d : ℝ) / ε ^ 2
  swap
  · exact False.elim (_htriv ⟨rfl, rfl, hε, hN⟩)
  refine ⟨⟨0, 0, 0, 1⟩, ?_, ?_, ?_, ?_⟩
  · change 0 ≤ 64 * Real.sqrt (d : ℝ) / ε ^ 3
    positivity
  · change 0 ≤ 64 * Real.sqrt (d : ℝ) / ε ^ 3
    positivity
  · change 0 ≤ 64 / ε
    positivity
  · norm_num

end Qatlib.Papers.QRegression21.MainResults.LossEstimation
