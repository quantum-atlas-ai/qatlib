/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DiscreteSim08.MainResults.FractionalQuery
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Binomial truncation estimates for controlled simulation

The unnormalized terms `poissonTerm` bound binomial weights and, when the mean is at most one
eighth, yield a geometric estimate for `binomTail`. The module also bounds the Hamming-weight
parameter and the scalar segment-success expression used in controlled simulation.

This development follows [CleveEtAl2009].

## Main statements

* `binomTail_le_poisson`: the binomial tail is at most twice its first Poisson comparison term.
* `binomTail_le_eps`: an explicit comparison-term bound controls the truncation error.
* `controlledSimulation_segment_success`: the segment-success expression is at least three
  quarters.

## References

* [Cleve et al., 2009][CleveEtAl2009]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.DiscreteSim08.MainResults

/-- The unnormalized Poisson comparison term `μ ^ j / j!`. -/
noncomputable def poissonTerm (μ : ℝ) (j : ℕ) : ℝ := μ ^ j / (Nat.factorial j : ℝ)

/-- The Poisson comparison term is nonnegative when its parameter is nonnegative. -/
theorem poissonTerm_nonneg (μ : ℝ) (hμ : 0 ≤ μ) (j : ℕ) : 0 ≤ poissonTerm μ j := by
  unfold poissonTerm
  exact div_nonneg (pow_nonneg hμ j) (Nat.cast_nonneg _)

/-- The next Poisson comparison term is the current term times `μ / (j + 1)`. -/
theorem poissonTerm_succ (μ : ℝ) (j : ℕ) :
    poissonTerm μ (j + 1) = poissonTerm μ j * (μ / ((j : ℝ) + 1)) := by
  unfold poissonTerm
  rw [pow_succ, Nat.factorial_succ]
  push_cast
  have hf : (Nat.factorial j : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- Every finite geometric sum with ratio one eighth is at most `8 / 7`. -/
theorem geom_eighth_sum_le (N : ℕ) :
    (∑ i ∈ Finset.range N, ((1 : ℝ) / 8) ^ i) ≤ 8 / 7 := by
  have hmul : (∑ i ∈ Finset.range N, ((1 : ℝ) / 8) ^ i) * (1 - 1 / 8)
      = 1 - ((1 : ℝ) / 8) ^ N := by
    simpa using! geom_sum_mul_neg ((1 : ℝ) / 8) N
  have hpow : 0 ≤ ((1 : ℝ) / 8) ^ N := pow_nonneg (by norm_num) N
  have hpos : (0 : ℝ) < 1 - 1 / 8 := by norm_num
  have hle : (∑ i ∈ Finset.range N, ((1 : ℝ) / 8) ^ i) * (1 - 1 / 8) ≤ 1 := by
    rw [hmul]; linarith
  calc (∑ i ∈ Finset.range N, ((1 : ℝ) / 8) ^ i)
      ≤ 1 / (1 - 1 / 8) := (le_div_iff₀ hpos).mpr hle
    _ = 8 / 7 := by norm_num

/-- The finite binomial tail summing weights of indices strictly greater than `k` and at most
`m`. -/
noncomputable def binomTail (m k : ℕ) (B : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (m - k),
    (m.choose (k + 1 + i) : ℝ) * B ^ (k + 1 + i) * (1 - B) ^ (m - (k + 1 + i))

/-- For `0 ≤ B ≤ 1`, the binomial weight at index `j` is at most `poissonTerm (m * B) j`. -/
theorem binomTail_term_le_poisson (m j : ℕ) (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) :
    (m.choose j : ℝ) * B ^ j * (1 - B) ^ (m - j)
      ≤ poissonTerm ((m : ℝ) * B) j := by
  have hpowB : 0 ≤ B ^ j := pow_nonneg hB0 j
  have h1B0 : 0 ≤ 1 - B := by linarith
  have h1B1 : 1 - B ≤ 1 := by linarith
  have hpow1 : (1 - B) ^ (m - j) ≤ 1 := pow_le_one₀ h1B0 h1B1
  have hchoose : (m.choose j : ℝ) ≤ (m : ℝ) ^ j / (Nat.factorial j : ℝ) :=
    Nat.choose_le_pow_div (α := ℝ) j m
  have hstep : (m.choose j : ℝ) * B ^ j * (1 - B) ^ (m - j)
      ≤ ((m : ℝ) ^ j / (Nat.factorial j : ℝ)) * B ^ j := by
    calc (m.choose j : ℝ) * B ^ j * (1 - B) ^ (m - j)
        ≤ (m.choose j : ℝ) * B ^ j * 1 := by
          exact mul_le_mul_of_nonneg_left hpow1 (mul_nonneg (Nat.cast_nonneg _) hpowB)
      _ = (m.choose j : ℝ) * B ^ j := by ring
      _ ≤ ((m : ℝ) ^ j / (Nat.factorial j : ℝ)) * B ^ j :=
          mul_le_mul_of_nonneg_right hchoose hpowB
  calc (m.choose j : ℝ) * B ^ j * (1 - B) ^ (m - j)
      ≤ ((m : ℝ) ^ j / (Nat.factorial j : ℝ)) * B ^ j := hstep
    _ = poissonTerm ((m : ℝ) * B) j := by
        unfold poissonTerm
        rw [mul_pow]
        ring

/-- For `0 ≤ μ ≤ 1 / 8`, the term at `k + 1 + i` is at most the term at `k + 1` times `(1 / 8) ^
i`. -/
theorem poissonTerm_shift_le (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ : μ ≤ 1 / 8) (k i : ℕ) :
    poissonTerm μ (k + 1 + i) ≤ poissonTerm μ (k + 1) * ((1 : ℝ) / 8) ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hstep : poissonTerm μ (k + 1 + i + 1)
          = poissonTerm μ (k + 1 + i) * (μ / (((k + 1 + i : ℕ) : ℝ) + 1)) := by
        have h := poissonTerm_succ μ (k + 1 + i)
        rw [h]
      have hratio : μ / (((k + 1 + i : ℕ) : ℝ) + 1) ≤ 1 / 8 := by
        have hden : (1 : ℝ) ≤ ((k + 1 + i : ℕ) : ℝ) + 1 := by
          have hnn : (0 : ℝ) ≤ ((k + 1 + i : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
        have hstep1 : μ / (((k + 1 + i : ℕ) : ℝ) + 1) ≤ (1 / 8) / (((k + 1 + i : ℕ) : ℝ) + 1) :=
          div_le_div_of_nonneg_right hμ (by linarith)
        have hstep2 : (1 / 8) / (((k + 1 + i : ℕ) : ℝ) + 1) ≤ (1 / 8) / 1 :=
          div_le_div_of_nonneg_left (by norm_num) one_pos hden
        linarith
      have hnonneg : 0 ≤ poissonTerm μ (k + 1 + i) := poissonTerm_nonneg μ hμ0 _
      calc poissonTerm μ (k + 1 + i + 1)
          = poissonTerm μ (k + 1 + i) * (μ / (((k + 1 + i : ℕ) : ℝ) + 1)) := hstep
        _ ≤ (poissonTerm μ (k + 1) * ((1 : ℝ) / 8) ^ i) * (1 / 8) := by
            have hrn : 0 ≤ μ / (((k + 1 + i : ℕ) : ℝ) + 1) := div_nonneg hμ0 (by positivity)
            have htn : 0 ≤ poissonTerm μ (k + 1) * ((1 : ℝ) / 8) ^ i :=
              mul_nonneg (poissonTerm_nonneg μ hμ0 _) (pow_nonneg (by norm_num) _)
            exact mul_le_mul ih hratio hrn htn
        _ = poissonTerm μ (k + 1) * ((1 : ℝ) / 8) ^ (i + 1) := by ring

/-- For `0 ≤ B ≤ 1` and `m * B ≤ 1 / 8`, the binomial tail above `k` is at most `2 * poissonTerm
(m * B) (k + 1)`. -/
theorem binomTail_le_poisson (m k : ℕ) (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (hμ : (m : ℝ) * B ≤ 1 / 8) :
    binomTail m k B ≤ 2 * poissonTerm ((m : ℝ) * B) (k + 1) := by
  have hμ0 : 0 ≤ (m : ℝ) * B := mul_nonneg (Nat.cast_nonneg _) hB0
  have hterm : ∀ i ∈ Finset.range (m - k),
      (m.choose (k + 1 + i) : ℝ) * B ^ (k + 1 + i) * (1 - B) ^ (m - (k + 1 + i))
        ≤ poissonTerm ((m : ℝ) * B) (k + 1) * ((1 : ℝ) / 8) ^ i := by
    intro i _
    exact le_trans (binomTail_term_le_poisson m (k + 1 + i) B hB0 hB1)
      (poissonTerm_shift_le ((m : ℝ) * B) hμ0 hμ k i)
  calc binomTail m k B
      = ∑ i ∈ Finset.range (m - k),
          (m.choose (k + 1 + i) : ℝ) * B ^ (k + 1 + i) * (1 - B) ^ (m - (k + 1 + i)) := rfl
    _ ≤ ∑ i ∈ Finset.range (m - k),
          poissonTerm ((m : ℝ) * B) (k + 1) * ((1 : ℝ) / 8) ^ i :=
        Finset.sum_le_sum hterm
    _ = poissonTerm ((m : ℝ) * B) (k + 1) *
          ∑ i ∈ Finset.range (m - k), ((1 : ℝ) / 8) ^ i := by
        rw [Finset.mul_sum]
    _ ≤ poissonTerm ((m : ℝ) * B) (k + 1) * (8 / 7) := by
        exact mul_le_mul_of_nonneg_left (geom_eighth_sum_le (m - k))
          (poissonTerm_nonneg _ hμ0 _)
    _ ≤ 2 * poissonTerm ((m : ℝ) * B) (k + 1) := by
        have h := poissonTerm_nonneg ((m : ℝ) * B) hμ0 (k + 1)
        nlinarith

/-- If `0 ≤ B ≤ 1`, `m * B ≤ 1 / 8`, and `2 * poissonTerm (1 / 8) (k + 1) ≤ ε`, then the
binomial tail above `k` is at most `ε`. See [CleveEtAl2009]. -/
theorem binomTail_le_eps (m k : ℕ) (B ε : ℝ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (hμ : (m : ℝ) * B ≤ 1 / 8)
    (hk : 2 * poissonTerm ((1 : ℝ) / 8) (k + 1) ≤ ε) :
    binomTail m k B ≤ ε := by
  have hmain := binomTail_le_poisson m k B hB0 hB1 hμ
  have hle : poissonTerm ((m : ℝ) * B) (k + 1) ≤ poissonTerm ((1 : ℝ) / 8) (k + 1) := by
    unfold poissonTerm
    have hden : (0 : ℝ) < (Nat.factorial (k + 1) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (k + 1)
    have hpow : ((m : ℝ) * B) ^ (k + 1) ≤ ((1 : ℝ) / 8) ^ (k + 1) :=
      pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hB0) hμ (k + 1)
    exact div_le_div_of_nonneg_right hpow hden.le
  linarith

/-- For `0 ≤ θ ≤ π` and `m * θ = 1 / 4`, the ratio `sin (θ / 2) / controlledSimulationNorm θ` is
at most `1 / (8 * m)`. -/
theorem hammingParam_le (θ m : ℝ) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi)
    (hm : m * θ = 1 / 4) :
    Real.sin (θ / 2) / controlledSimulationNorm θ ≤ 1 / (8 * m) := by
  have hθpos : 0 < θ := by
    rcases eq_or_lt_of_le h0 with h | h
    · rw [← h] at hm; norm_num at hm
    · exact h
  have hmpos : 0 < m := by nlinarith
  have hhalf0 : 0 ≤ θ / 2 := by linarith
  have hhalfπ : θ / 2 ≤ Real.pi / 2 := by linarith
  have hv1 : 1 ≤ controlledSimulationNorm θ := by
    have hcos0 : 0 ≤ Real.cos (θ / 2) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hhalfπ⟩
    have hsin0 : 0 ≤ Real.sin (θ / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hhalf0 (by linarith [Real.pi_pos])
    unfold controlledSimulationNorm
    have h2 : (Real.cos (θ / 2) + Real.sin (θ / 2)) ^ 2
        = 1 + 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
      nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
    have hnonneg : 0 ≤ Real.cos (θ / 2) + Real.sin (θ / 2) := by linarith
    nlinarith [mul_nonneg hsin0 hcos0]
  have hsin0 : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hhalf0 (by linarith [Real.pi_pos])
  have hsinle : Real.sin (θ / 2) ≤ θ / 2 := Real.sin_le hhalf0
  have hdiv : Real.sin (θ / 2) / controlledSimulationNorm θ ≤ Real.sin (θ / 2) / 1 :=
    div_le_div_of_nonneg_left hsin0 one_pos hv1
  have hθ : θ / 2 = 1 / (8 * m) := by
    rw [eq_div_iff (by positivity : (8 : ℝ) * m ≠ 0)]
    nlinarith [hm]
  calc Real.sin (θ / 2) / controlledSimulationNorm θ ≤ Real.sin (θ / 2) / 1 := hdiv
    _ = Real.sin (θ / 2) := by ring
    _ ≤ θ / 2 := hsinle
    _ = 1 / (8 * m) := hθ

/-- For `0 ≤ θ ≤ 1 / 8` and natural `m` with `m * θ = 1 / 4`, the segment expression `(1 - θ) ^
m` is at least three quarters. -/
theorem controlledSimulation_segment_success (θ : ℝ) (m : ℕ)
    (hm : (m : ℝ) * θ = 1 / 4) (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 8) :
    (3 : ℝ) / 4 ≤ (1 - θ) ^ m := by
  have hθpos : 0 < θ := by
    rcases eq_or_lt_of_le h0 with h | h
    · rw [← h] at hm; norm_num at hm
    · exact h
  have hbern := one_add_mul_le_pow (a := -θ) (by linarith) m
  have hbern' : 1 - (m : ℝ) * θ ≤ (1 - θ) ^ m := by
    simpa [mul_neg, sub_eq_add_neg] using! hbern
  rw [hm] at hbern'
  norm_num at hbern'
  linarith

end Qatlib.Papers.DiscreteSim08.MainResults
