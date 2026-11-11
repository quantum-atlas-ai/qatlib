/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Preparation of the right-hand-side state `|B⟩`

Fixed source: arXiv:1901.00961, *Quantum spectral methods for differential
equations*, Lemma 6 (§7, p. 17, eqs. (7.1)–(7.5)).

The right-hand side of the collocation system (3.14)–(3.15) is

  `|B⟩ ∝ |0⟩|γ⟩|0⟩ + Σ_{h<m} Σ_{1≤l≤n} |h⟩|f_h(cos(lπ/n))⟩|l⟩`   (7.1).

The paper normalizes it with the amplitudes (7.2)

  `b₀₀ = ‖γ‖/D`,  `b_{hl} = ‖f_h(cos(lπ/n))‖/D`,
  `D = sqrt(‖γ‖² + Σ_{h<m} Σ_{1≤l≤n} ‖f_h(cos(lπ/n))‖²)`,

so that `Σ b² = 1` (7.3).  The preparation is: one uniform superposition over
the `(m+1)(n+1)` labels (7.4), one application of `O_x`, and `mn` applications
of `O_f(h,l)` (7.5).

This file proves (i) the normalization identity (7.3) for the amplitudes (7.2),
and (ii) the query count: `1 + mn ≤ 2(m+1)(n+1)`, i.e. `O(mn)` oracle queries.
The gate synthesis of the uniform superposition (7.4), which the paper cites as
a standard `O(mn)` construction, is not re-proved here.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpectralDE19.MainResults

open scoped BigOperators

/-- The normalizing denominator `D` of eq. (7.2). -/
noncomputable def stateNormalizer (γnorm : ℝ) (fnorm : ℕ → ℕ → ℝ) (m n : ℕ) : ℝ :=
  Real.sqrt (γnorm ^ 2 + ∑ h ∈ Finset.range m, ∑ l ∈ Finset.Icc 1 n, (fnorm h l) ^ 2)

/-- The number of oracle calls of the preparation (7.4)–(7.5): one `O_x` call
plus one `O_f(h,l)` call for each of the `m·n` pairs `(h,l)`, `1 ≤ l ≤ n`. -/
def statePreparationQueries (m n : ℕ) : ℕ := 1 + m * n

/-- **SpectralDE19, Lemma 6, eq. (7.3).**  The amplitudes (7.2) are normalized:
their squares sum to `1`. -/
theorem lemma6_amplitudes_normalized
    (m n : ℕ) (γnorm : ℝ) (fnorm : ℕ → ℕ → ℝ)
    (hγ : 0 < γnorm) (hD : 0 < stateNormalizer γnorm fnorm m n) :
    (γnorm / stateNormalizer γnorm fnorm m n) ^ 2
        + ∑ h ∈ Finset.range m, ∑ l ∈ Finset.Icc 1 n,
            (fnorm h l / stateNormalizer γnorm fnorm m n) ^ 2 = 1 := by
  set D : ℝ := stateNormalizer γnorm fnorm m n with hDdef
  set S : ℝ := γnorm ^ 2
      + ∑ h ∈ Finset.range m, ∑ l ∈ Finset.Icc 1 n, (fnorm h l) ^ 2 with hS
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hDsq : D ^ 2 = S := by
    rw [hDdef, stateNormalizer, hS]
    exact Real.sq_sqrt hS0
  have hinner : ∀ h : ℕ,
      (∑ l ∈ Finset.Icc 1 n, (fnorm h l / D) ^ 2)
        = (∑ l ∈ Finset.Icc 1 n, (fnorm h l) ^ 2) / D ^ 2 := by
    intro h
    simp_rw [div_pow]
    exact (Finset.sum_div _ _ _).symm
  have hsum : (∑ h ∈ Finset.range m, ∑ l ∈ Finset.Icc 1 n, (fnorm h l / D) ^ 2)
      = (∑ h ∈ Finset.range m, ∑ l ∈ Finset.Icc 1 n, (fnorm h l) ^ 2) / D ^ 2 := by
    calc (∑ h ∈ Finset.range m, ∑ l ∈ Finset.Icc 1 n, (fnorm h l / D) ^ 2)
        = ∑ h ∈ Finset.range m,
            ((∑ l ∈ Finset.Icc 1 n, (fnorm h l) ^ 2) / D ^ 2) := by
              apply Finset.sum_congr rfl
              intro h _
              exact hinner h
      _ = (∑ h ∈ Finset.range m, ∑ l ∈ Finset.Icc 1 n, (fnorm h l) ^ 2) / D ^ 2 :=
            (Finset.sum_div _ _ _).symm
  have hDne : D ≠ 0 := ne_of_gt hD
  rw [div_pow, hsum, ← add_div, ← hS, ← hDsq]
  field_simp

/-- **SpectralDE19, Lemma 6, eq. (7.4)–(7.5), query count.**  The preparation
makes `1 + mn` oracle calls, which is at most `2(m+1)(n+1) = O(mn)`. -/
theorem lemma6_query_complexity (m n : ℕ) :
    (statePreparationQueries m n : ℝ) ≤ 2 * ((m : ℝ) + 1) * ((n : ℝ) + 1) := by
  unfold statePreparationQueries
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  push_cast
  nlinarith

/-- **SpectralDE19, Lemma 6.**  The state `|B⟩` of (7.1) is prepared from the
oracles `O_x`, `O_f(h,l)` with normalized amplitudes (7.2)/(7.3) and `O(mn)`
query complexity (7.4)–(7.5). -/
theorem lemma6_state_preparation
    (m n : ℕ) (γnorm : ℝ) (fnorm : ℕ → ℕ → ℝ)
    (hγ : 0 < γnorm) (hD : 0 < stateNormalizer γnorm fnorm m n) :
    ((γnorm / stateNormalizer γnorm fnorm m n) ^ 2
        + ∑ h ∈ Finset.range m, ∑ l ∈ Finset.Icc 1 n,
            (fnorm h l / stateNormalizer γnorm fnorm m n) ^ 2 = 1) ∧
    (statePreparationQueries m n : ℝ) ≤ 2 * ((m : ℝ) + 1) * ((n : ℝ) + 1) :=
  ⟨lemma6_amplitudes_normalized m n γnorm fnorm hγ hD, lemma6_query_complexity m n⟩

end Qatlib.Papers.SpectralDE19.MainResults
