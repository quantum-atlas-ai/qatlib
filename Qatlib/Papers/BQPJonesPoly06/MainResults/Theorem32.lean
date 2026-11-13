/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Theorem31

/-!
# Polynomial bounds from logarithmic braid synthesis

The estimates `word_count_le` and `log_to_poly` provide elementary counting and precision bounds
for braid synthesis. Assuming a synthesis bound polynomial in `log (1 / δ) + 1`,
`theorem32_density_efficiency` obtains a bound polynomial in `δ⁻¹ + 1` without changing the
approximation guarantee, as used for Theorem 3.2 of [AharonovArad2011].

## Main statements

* `word_count_le`: bounds the number of words of length at most `N` over `g` symbols.
* `theorem32_density_efficiency`: converts the assumed logarithmic crossing bound to a
  polynomial inverse-precision bound.
* `theorem32_synthesis`: the same implication with the paper's parameter and norm-preservation
  hypotheses.

## References

* [Aharonov and Arad, 2011][AharonovArad2011]
-/

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults

open Model

/-- The sum of `g ^ i` over lengths from zero to `N` is at most `(g + 1) ^ N`
[AharonovArad2011]. -/
theorem word_count_le (g N : ℕ) :
    (Finset.range (N + 1)).sum (fun i => g ^ i) ≤ (g + 1) ^ N := by
  rw [add_pow g 1 N]
  apply Finset.sum_le_sum
  intro i hi
  have hiN : i ≤ N := by
    have : i < N + 1 := Finset.mem_range.mp hi
    omega
  have hc : 1 ≤ N.choose i := Nat.choose_pos hiN
  calc g ^ i = g ^ i * (1 : ℕ) := by ring
    _ ≤ g ^ i * (N.choose i) := Nat.mul_le_mul_left _ hc
    _ = g ^ i * 1 ^ (N - i) * N.choose i := by simp

/-- For positive `δ`, the logarithm of `1 / δ` is at most `δ⁻¹ - 1`. -/
theorem log_one_div_le_inv {δ : ℝ} (hδ : 0 < δ) :
    Real.log (1 / δ) ≤ δ⁻¹ - 1 := by
  have hpos : (0 : ℝ) < 1 / δ := by positivity
  have := Real.log_le_sub_one_of_pos hpos
  simpa [one_div] using this

/-- For `0 < δ ≤ 1`, the quantity `log (1 / δ) + 1` is nonnegative. -/
theorem log_one_div_add_one_nonneg {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ Real.log (1 / δ) + 1 := by
  have hge1 : (1 : ℝ) ≤ 1 / δ := by
    rw [one_le_div hδ]
    simpa using hδ1
  have := Real.log_nonneg hge1
  linarith

/-- For `0 < δ ≤ 1`, a natural-coefficient power of `log (1 / δ) + 1` is bounded by the
corresponding power of `δ⁻¹ + 1` [AharonovArad2011]. -/
theorem log_to_poly (C d : ℕ) :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      (C : ℝ) * (Real.log (1 / δ) + 1) ^ d ≤ (C : ℝ) * (δ⁻¹ + 1) ^ d := by
  intro δ hδ hδ1
  have hbase : Real.log (1 / δ) + 1 ≤ δ⁻¹ + 1 := by
    have hlog := log_one_div_le_inv hδ
    linarith
  have hnn : (0 : ℝ) ≤ Real.log (1 / δ) + 1 :=
    log_one_div_add_one_nonneg hδ hδ1
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn hbase d) (by positivity)

/-- An assumed eight-strand braid synthesis bound polynomial in `log (1 / δ) + 1` gives a bound
polynomial in `δ⁻¹ + 1` with the same error on unit vectors [AharonovArad2011, Theorem
3.2][AharonovArad2011]. -/
theorem theorem32_density_efficiency {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ρ : BraidWord 8 → H →L[ℂ] H) (Ũ : H →L[ℂ] H)
    (C d : ℕ)
    (hsynth : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ b : BraidWord 8,
      ((b.numCrossings : ℝ) ≤ C * (Real.log (1 / δ) + 1) ^ d) ∧
      (∀ p : H, ‖p‖ = 1 → ‖(ρ b - Ũ) p‖ ≤ δ)) :
    ∃ C' d' : ℕ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ b : BraidWord 8,
      ((b.numCrossings : ℝ) ≤ C' * (δ⁻¹ + 1) ^ d') ∧
      (∀ p : H, ‖p‖ = 1 → ‖(ρ b - Ũ) p‖ ≤ δ) := by
  refine ⟨C, d, fun δ hδ hδ1 => ?_⟩
  obtain ⟨b, hb, happrox⟩ := hsynth δ hδ hδ1
  exact ⟨b, le_trans hb (log_to_poly C d δ hδ hδ1), happrox⟩

/-- With the stated parameter and norm-preservation hypotheses, the supplied logarithmic
synthesis bound yields polynomial crossing bounds in inverse precision while preserving the
unit-vector error guarantee [AharonovArad2011, Theorem 3.2][AharonovArad2011]. -/
theorem theorem32_synthesis {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (k : ℕ) (_hk : 4 < k) (_hk6 : k ≠ 6)
    (ρ : BraidWord 8 → H →L[ℂ] H) (Ũ : H →L[ℂ] H)
    (_hρ : ∀ (b : BraidWord 8) (p : H), ‖p‖ = 1 → ‖ρ b p‖ = 1)
    (C d : ℕ)
    (hsynth : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ b : BraidWord 8,
      ((b.numCrossings : ℝ) ≤ C * (Real.log (1 / δ) + 1) ^ d) ∧
      (∀ p : H, ‖p‖ = 1 → ‖(ρ b - Ũ) p‖ ≤ δ)) :
    ∃ C' d' : ℕ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ b : BraidWord 8,
      ((b.numCrossings : ℝ) ≤ C' * (δ⁻¹ + 1) ^ d') ∧
      (∀ p : H, ‖p‖ = 1 → ‖(ρ b - Ũ) p‖ ≤ δ) :=
  theorem32_density_efficiency ρ Ũ C d hsynth

end Qatlib.Papers.BQPJonesPoly06.MainResults
