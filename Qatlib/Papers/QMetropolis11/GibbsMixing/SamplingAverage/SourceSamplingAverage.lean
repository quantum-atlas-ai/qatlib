/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Statistical averages from the sample sequence (Temme et al. 2011, Eq. (1))

Fixed source: arXiv:0911.3635v2, Section 1, printed page 3, Eq. (1):

`(1/m) Σ_{j=1}^m ⟨φ_j|X|φ_j⟩ = Tr X ρ + O(1/√m)`.

The Metropolis sampler produces `m` states `|φ_j⟩` whose empirical average of
the observable `X` estimates `Tr X ρ_G` with error `O(1/√m)`.

This file formalises the statistical core in a finite outcome space `Ω` with
a sampling measure `P` (nonnegative, total mass 1) and the observed value
`g j ω` of the `j`-th sample.

* `source_sample_average_unbiased` (proved): if every individual sample has
  mean `μ` under `P`, then the sample average is unbiased, i.e. has mean `μ`.
  This is the `Tr X ρ` half of Eq. (1) and uses only linearity of expectation,
  no independence.
* `source_sample_average_concentration` (proved): if the second moment of the
  sample average about `μ` is at most `B²/m` (the bound that independence of
  the `m` samples yields), then the probability that the average deviates by
  more than `ε` is at most `B²/(m ε²)`.  This is the `O(1/√m)` half, in the
  Chebyshev/Markov form.

The derivation of the `B²/m` second-moment bound from i.i.d. sampling is not
formalised; it is the hypothesis `hsecond` below.  The paper's `O(1/√m)`
statement is the regime `ε = B/√(m δ)`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMetropolis11.GibbsMixing.SamplingAverage

variable {Ω : Type*} [Fintype Ω]

/-- The empirical average of the `m` sample values `g j`, Eq. (1). -/
noncomputable def EnsembleMean {m : ℕ} (g : Fin m → Ω → ℝ) (ω : Ω) : ℝ :=
  (m : ℝ)⁻¹ * ∑ j, g j ω

/-- **c003, Eq. (1), unbiasedness.**  If each of the `m` samples has mean `μ`
under the sampling measure `P`, then the empirical average `EnsembleMean` has
mean `μ`.  This is the `Tr X ρ` part of Eq. (1), proved by exchanging the two
finite sums; no independence is needed.

Source: arXiv:0911.3635v2, Eq. (1) (first equality), printed p. 3. -/
theorem source_sample_average_unbiased (P : Ω → ℝ) (_hP : ∑ ω, P ω = 1)
    {m : ℕ} (hm : 0 < m) (g : Fin m → Ω → ℝ) (μ : ℝ)
    (hμ : ∀ j, ∑ ω, P ω * g j ω = μ) :
    ∑ ω, P ω * EnsembleMean g ω = μ := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm)
  simp only [EnsembleMean]
  calc ∑ ω, P ω * ((m : ℝ)⁻¹ * ∑ j, g j ω)
      = (m : ℝ)⁻¹ * ∑ ω, P ω * ∑ j, g j ω := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun ω _ => by ring)
    _ = (m : ℝ)⁻¹ * ∑ ω, ∑ j, P ω * g j ω := by
        congr 1
        exact Finset.sum_congr rfl (fun ω _ => by rw [Finset.mul_sum])
    _ = (m : ℝ)⁻¹ * ∑ j, ∑ ω, P ω * g j ω := by
        congr 1
        rw [Finset.sum_comm]
    _ = (m : ℝ)⁻¹ * ∑ j, μ := by
        congr 1
        exact Finset.sum_congr rfl (fun j _ => hμ j)
    _ = μ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- **c003, Eq. (1), `O(1/√m)` concentration.**  If the second moment of the
empirical average about `μ` is at most `B²/m`, then the probability mass of
the event `|EnsembleMean - μ| ≥ ε` is at most `B²/(m ε²)`.  Choosing
`ε = B/√(m δ)` gives deviation `O(1/√m)` with confidence `1-δ`, i.e. the
`O(1/√m)` of Eq. (1).

The second-moment hypothesis `hsecond` is what the independence of the `m`
samples supplies; deriving it from a product measure is not formalised here.

Source: arXiv:0911.3635v2, Eq. (1), printed p. 3; Chebyshev/Markov step. -/
theorem source_sample_average_concentration (P : Ω → ℝ) (hP0 : ∀ ω, 0 ≤ P ω)
    {m : ℕ} (hm : 0 < m) (g : Fin m → Ω → ℝ) (μ ε B : ℝ)
    (hε : 0 < ε) (_hB : 0 ≤ B)
    (hsecond : ∑ ω, P ω * (EnsembleMean g ω - μ) ^ 2 ≤ B ^ 2 / (m : ℝ)) :
    ∑ ω, P ω * (if ε ≤ |EnsembleMean g ω - μ| then 1 else 0) ≤
      B ^ 2 / ((m : ℝ) * ε ^ 2) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm)
  have hterm : ∀ ω, P ω * (if ε ≤ |EnsembleMean g ω - μ| then 1 else 0)
      ≤ P ω * ((EnsembleMean g ω - μ) / ε) ^ 2 := by
    intro ω
    refine mul_le_mul_of_nonneg_left ?_ (hP0 ω)
    by_cases h : ε ≤ |EnsembleMean g ω - μ|
    · rw [if_pos h]
      have hsq : ε ^ 2 ≤ (EnsembleMean g ω - μ) ^ 2 := by
        have hs : ε ^ 2 ≤ |EnsembleMean g ω - μ| ^ 2 :=
          pow_le_pow_left₀ (le_of_lt hε) h 2
        rwa [sq_abs] at hs
      have hone : (1 : ℝ) ≤ ((EnsembleMean g ω - μ) / ε) ^ 2 := by
        rw [div_pow, one_le_div (by positivity)]
        exact hsq
      simpa using hone
    · rw [if_neg h]
      simpa using (sq_nonneg ((EnsembleMean g ω - μ) / ε) :
        (0 : ℝ) ≤ ((EnsembleMean g ω - μ) / ε) ^ 2)
  calc ∑ ω, P ω * (if ε ≤ |EnsembleMean g ω - μ| then 1 else 0)
      ≤ ∑ ω, P ω * ((EnsembleMean g ω - μ) / ε) ^ 2 :=
        Finset.sum_le_sum (fun ω _ => hterm ω)
    _ = (∑ ω, P ω * (EnsembleMean g ω - μ) ^ 2) / ε ^ 2 := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun ω _ => by rw [div_pow]; ring)
    _ ≤ (B ^ 2 / (m : ℝ)) / ε ^ 2 := by
        exact div_le_div_of_nonneg_right hsecond (by positivity)
    _ = B ^ 2 / ((m : ℝ) * ε ^ 2) := by
        field_simp

end Qatlib.Papers.QMetropolis11.GibbsMixing.SamplingAverage
