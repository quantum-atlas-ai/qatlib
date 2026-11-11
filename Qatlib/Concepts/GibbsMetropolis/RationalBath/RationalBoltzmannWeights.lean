/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Rat.Cast.Order
import Qatlib.Concepts.FairRandomBits.RationalReject.CountedWeightedDecoder

/-!
# Rational Boltzmann weights from Taylor polynomials

`rationalBoltzmannTaylor` approximates `exp (1 - E)` using rational arithmetic. On energies in
`[0, 1]`, its value is at least one and its nonnegative approximation error decays geometrically
with the truncation degree.

`boltzmannIntegerWeights` clears all denominators, and the final normalization theorem
identifies the resulting integer-weight probabilities with the normalized Taylor values. See
[TemmeEtAl2011] for background.

## Main statements

* `rational_boltzmann_computed_positive_tail`: For energies in `[0, 1]`, the Taylor weight is at
  least one and underestimates `exp (1 - E)` by at most `2 * (1 / 2) ^ K`.
* `rational_boltzmann_exact_integer_normalization`: For a nonempty system with energies in `[0,
  1]`, the integer weights have positive total and normalize exactly to the normalized Taylor
  weights.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

set_option warningAsError false
open Qatlib.Concepts.FairRandomBits.RationalReject

namespace Qatlib.Concepts.GibbsMetropolis.RationalBath
open scoped BigOperators Classical
set_option autoImplicit false
set_option linter.unusedVariables false

/-- The degree-`K` rational Taylor sum for `exp (1 - E)`. -/
def rationalBoltzmannTaylor (K : ℕ) (E : ℚ) : ℚ :=
  ∑ j ∈ Finset.range (K+1), (1-E)^j / (j.factorial : ℚ)

/-- Casting the rational Boltzmann Taylor sum to the reals gives the corresponding real Taylor
sum. -/
theorem rationalBoltzmannTaylor_cast (K : ℕ) (E : ℚ) :
    (rationalBoltzmannTaylor K E : ℝ) =
      ∑ j ∈ Finset.range (K+1), (1-(E:ℝ))^j / (j.factorial : ℝ) := by
  simp [rationalBoltzmannTaylor]

/-- For `E ≤ 1`, the rational Boltzmann Taylor sum is at least one. -/
theorem rationalBoltzmannTaylor_one_le (K : ℕ) (E : ℚ) (hE : E ≤ 1) :
    1 ≤ rationalBoltzmannTaylor K E := by
  have ht (j : ℕ) : 0 ≤ (1-E)^j / (j.factorial : ℚ) := by positivity
  simpa using! (Finset.single_le_sum (fun j _ => ht j)
    (Finset.mem_range.mpr (Nat.zero_lt_succ K)))

/-- The factorial of `K + 1` is at least `2 ^ K`. -/
private theorem two_pow_le_factorial (K : ℕ) : 2^K ≤ (K+1).factorial := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [pow_succ, Nat.factorial_succ]
    nlinarith

/-- For energies in `[0, 1]`, the Taylor weight is at least one and underestimates `exp (1 - E)`
by at most `2 * (1 / 2) ^ K`. -/
theorem rational_boltzmann_computed_positive_tail :
    ∀ (K : ℕ) (E : ℚ), 0 ≤ E → E ≤ 1 →
      1 ≤ rationalBoltzmannTaylor K E ∧
      0 ≤ Real.exp (1-(E:ℝ)) - (rationalBoltzmannTaylor K E : ℝ) ∧
      Real.exp (1-(E:ℝ)) - (rationalBoltzmannTaylor K E : ℝ) ≤ 2*(1/2:ℝ)^K := by
  intro K E h0 h1
  have hx0 : 0 ≤ 1-(E:ℝ) := by exact_mod_cast sub_nonneg.mpr h1
  have hx1 : 1-(E:ℝ) ≤ 1 := by exact_mod_cast sub_le_self 1 h0
  refine ⟨rationalBoltzmannTaylor_one_le K E h1, ?_, ?_⟩
  · rw [rationalBoltzmannTaylor_cast]
    exact sub_nonneg.mpr (Real.sum_le_exp_of_nonneg hx0 (K+1))
  · have h := Real.exp_bound' hx0 hx1 (n := K+1) (by omega)
    rw [← rationalBoltzmannTaylor_cast] at h
    have hp : (1-(E:ℝ))^(K+1) ≤ 1 := pow_le_one₀ hx0 hx1
    have hf : (2:ℝ)^K ≤ ((K+1).factorial : ℝ) := by exact_mod_cast two_pow_le_factorial K
    have hfp : (0:ℝ) < ((K+1).factorial : ℝ) := by positivity
    have hkp : (0:ℝ) < (K+1:ℕ) := by positivity
    have hb : (1-(E:ℝ))^(K+1) * ((K+1:ℕ)+1:ℝ) /
        (((K+1).factorial:ℝ) * (K+1:ℕ)) ≤ 2 / (2:ℝ)^K := by
      calc
        _ ≤ 2 / ((K+1).factorial:ℝ) := by
          apply (div_le_div_iff₀ (mul_pos hfp hkp) hfp).2
          have hp' := mul_le_mul_of_nonneg_right hp
            (by positivity : (0:ℝ) ≤ (K+1:ℕ)+1)
          have hkk : (1:ℝ) ≤ (K+1:ℕ) := by exact_mod_cast Nat.succ_pos K
          nlinarith
        _ ≤ 2 / (2:ℝ)^K := div_le_div_of_nonneg_left (by norm_num) (by positivity) hf
    have heq : 2 / (2:ℝ)^K = 2*(1/2:ℝ)^K := by rw [div_pow]; ring
    linarith

/-- The product of the denominators of all rational Boltzmann Taylor weights. -/
def boltzmannCommonDenominator {N : ℕ} (K : ℕ) (E : Fin N → ℚ) : ℕ :=
  ∏ i, (rationalBoltzmannTaylor K (E i)).den

/-- The natural-number weights obtained by scaling the Taylor numerators to their common
denominator. -/
def boltzmannIntegerWeights {N : ℕ} (K : ℕ) (E : Fin N → ℚ) (i : Fin N) : ℕ :=
  (rationalBoltzmannTaylor K (E i)).num.toNat *
    (boltzmannCommonDenominator K E / (rationalBoltzmannTaylor K (E i)).den)

/-- The common denominator of the rational Taylor weights is strictly positive. -/
theorem boltzmannCommonDenominator_pos {N : ℕ} (K : ℕ) (E : Fin N → ℚ) :
    0 < boltzmannCommonDenominator K E :=
  Finset.prod_pos fun i _ => Rat.den_pos _

/-- For energies at most one, each integer weight equals the common denominator times its
rational Taylor weight after casting to the reals. -/
theorem boltzmannIntegerWeights_cast {N : ℕ} (K : ℕ) (E : Fin N → ℚ)
    (hE : ∀ i, E i ≤ 1) (i : Fin N) :
    (boltzmannIntegerWeights K E i : ℝ) =
      (boltzmannCommonDenominator K E : ℝ) * (rationalBoltzmannTaylor K (E i) : ℝ) := by
  let q := rationalBoltzmannTaylor K (E i)
  have hq : 0 ≤ q := (rationalBoltzmannTaylor_one_le K (E i) (hE i)).trans' (by norm_num)
  have hn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  have hd : q.den ∣ boltzmannCommonDenominator K E :=
    Finset.dvd_prod_of_mem (fun j => (rationalBoltzmannTaylor K (E j)).den) (Finset.mem_univ i)
  have hm : (boltzmannCommonDenominator K E / q.den : ℕ) * q.den =
      boltzmannCommonDenominator K E := Nat.div_mul_cancel hd
  have hmr : (boltzmannCommonDenominator K E / q.den : ℕ) =
      (boltzmannCommonDenominator K E : ℝ) / (q.den : ℝ) := by
    apply (eq_div_iff (by positivity : (q.den:ℝ) ≠ 0)).2
    exact_mod_cast hm
  simp only [boltzmannIntegerWeights, Nat.cast_mul]
  change (q.num.toNat:ℝ) * (boltzmannCommonDenominator K E / q.den : ℕ) = _
  rw [hmr, show (q.num.toNat:ℝ) = (q.num:ℝ) by exact_mod_cast Int.toNat_of_nonneg hn]
  rw [Rat.cast_def]
  ring

/-- For a nonempty system with energies in `[0, 1]`, the integer weights have positive total and
normalize exactly to the normalized Taylor weights. -/
theorem rational_boltzmann_exact_integer_normalization :
    ∀ (N K : ℕ) (E : Fin N → ℚ), 0 < N → (∀ i, 0 ≤ E i ∧ E i ≤ 1) →
      0 < weightTotal (boltzmannIntegerWeights K E) ∧
      ∀ i, (boltzmannIntegerWeights K E i : ℝ) / (weightTotal (boltzmannIntegerWeights K E):ℝ) =
        (rationalBoltzmannTaylor K (E i):ℝ) / (∑ j, (rationalBoltzmannTaylor K (E j):ℝ)) := by
  intro N K E hN hE
  have hd := boltzmannCommonDenominator_pos K E
  have hc := boltzmannIntegerWeights_cast K E (fun i => (hE i).2)
  have hs : (0:ℝ) < ∑ j, (rationalBoltzmannTaylor K (E j):ℝ) := by
    have hpos (j : Fin N) : (0:ℝ) < (rationalBoltzmannTaylor K (E j):ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℚ) < 1)
        (rationalBoltzmannTaylor_one_le K (E j) (hE j).2))
    exact Finset.sum_pos' (fun j _ => (hpos j).le)
      ⟨⟨0,hN⟩, Finset.mem_univ _, hpos _⟩
  have ht : (weightTotal (boltzmannIntegerWeights K E):ℝ) =
      (boltzmannCommonDenominator K E:ℝ) * ∑ j, (rationalBoltzmannTaylor K (E j):ℝ) := by
    simp only [weightTotal, Nat.cast_sum, hc, Finset.mul_sum]
  constructor
  · have : (0:ℝ) < (weightTotal (boltzmannIntegerWeights K E):ℝ) := by rw [ht]; positivity
    exact_mod_cast this
  · intro i
    rw [hc i, ht, mul_div_mul_left _ _ (by positivity : (boltzmannCommonDenominator K E:ℝ) ≠ 0)]
end Qatlib.Concepts.GibbsMetropolis.RationalBath
