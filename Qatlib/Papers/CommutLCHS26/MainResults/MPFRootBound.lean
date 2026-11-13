/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.MPFGeometric
import Qatlib.Papers.CommutLCHS26.MainResults.MPFCommutatorBound

/-!
# Root-profile bounds for multi-product errors

This module converts products of commutator profiles into estimates controlled by the root scale
`mu`. When μ|t| ≤ 1/2, the scalar `errorProfile` is bounded by (8/3)(μ|t|)^(2m + 1), yielding an
explicit local multi-product error for the analysis of [AftabAnTrivisa2026].

Chebyshev weights replace the general coefficient mass by a harmonic-number bound and give a
time-power estimate with an explicit coefficient.

## Main statements

* `errorProfile_le`: bounds the scalar error profile by the root scale.
* `actualMPF_root_error`: gives the general local multi-product error.
* `chebyshev_time_power`: isolates the time power for Chebyshev formulas.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MPFRootBound

open Matrix
open scoped BigOperators Classical Matrix.Norms.L2Operator NNReal
open CommutatorProducts MPFRootProfile MPFGeometric BCHCommMass BCHMassProducts
open BCHControlled BCHPerturbation DysonExpansion MPFMomentSeries MPFCommutatorBound

variable {I : Type} [Fintype I]

/-- The mass profile is bounded by |t|^(2n + 3l) times the raw commutator product. -/
theorem massProfile_le_raw (xs : List (Matrix I I ℂ)) (t : ℝ) (l n : ℕ) :
    massProfile xs t l n ≤ |t| ^ (2 * n + 3 * l) * rawProduct xs l n := by
  unfold massProfile rawProduct
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  rw [tuple_mass_degree xs t l n v hv]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (abs_nonneg t) _)
  apply Finset.prod_le_prod₀
  · intro i _
    exact div_nonneg (profile_nonneg xs _) (sq_nonneg _)
  · intro i _
    exact div_le_self (profile_nonneg xs _)
      (one_le_pow₀ (by exact_mod_cast (show 1 ≤ 2 * v i + 3 by omega)))

variable [DecidableEq I]

/-- For 1 ≤ l ≤ m and n + l ≥ m, the mass profile is at most (μ|t|)^(2n + 3l). -/
theorem massProfile_le_mu (xs : List (Matrix I I ℂ)) (m l n : ℕ)
    (hl : 1 ≤ l) (hlm : l ≤ m) (hn : m ≤ n + l) (t : ℝ) :
    massProfile xs t l n ≤ (mu xs m * |t|) ^ (2 * n + 3 * l) := by
  calc
    _ ≤ |t| ^ (2 * n + 3 * l) * rawProduct xs l n := massProfile_le_raw xs t l n
    _ ≤ |t| ^ (2 * n + 3 * l) * mu xs m ^ (2 * n + 3 * l) :=
      mul_le_mul_of_nonneg_left (rawProduct_le_mu xs m l n hl hlm hn) (pow_nonneg (abs_nonneg t) _)
    _ = _ := by rw [← mul_pow, mul_comm]

/-- For positive m and μ|t| ≤ 1/2, the odd-coefficient control condition holds at radius |t| and
cutoff 2m + 1. -/
theorem actual_control (xs : List (Matrix I I ℂ)) (m : ℕ) (hm : 0 < m) (t : ℝ)
    (ht : mu xs m * |t| ≤ 1 / 2) :
    OddControl xs (⟨|t|, abs_nonneg t⟩ : ℝ≥0) (2 * m + 1) := by
  apply MPFRootProfile.oddControl xs m hm
  change |t| * mu xs m ≤ 1
  rw [mul_comm]
  linarith

/-- When μ|t| ≤ 1/2, the order-profile tail coefficient at k + m is bounded by (μ|t|)^(2m +
1)(1/4)^k times the factorial mass. -/
theorem orderProfile_le (xs : List (Matrix I I ℂ)) (m : ℕ) (hm : 0 < m)
    (t : ℝ) (ht : mu xs m * |t| ≤ 1 / 2) (k : ℕ) :
    orderProfile xs t m (k + m) ≤
      ((mu xs m * |t|) ^ (2 * m + 1) * (1 / 4 : ℝ) ^ k) * factorialMass (m - 1) := by
  unfold orderProfile factorialMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjm : j + 1 ≤ m := by have := Finset.mem_range.mp hj; omega
  have hjk : j + 1 ≤ k + m := by omega
  rw [if_pos hjk]
  have h := massProfile_le_mu xs m (j + 1) ((k + m) - (j + 1))
    (by omega) hjm (by omega) t
  have he : 2 * ((k + m) - (j + 1)) + 3 * (j + 1) = 2 * (k + m) + (j + 1) := by omega
  rw [he] at h
  calc
    _ ≤ ((mu xs m * |t|) ^ (2 * m + 1) * (1 / 4 : ℝ) ^ k) /
        ((j + 1).factorial : ℝ) := div_le_div_of_nonneg_right
      (h.trans (power_tail_le _ (mul_nonneg (mu_nonneg xs m hm) (abs_nonneg t)) ht m k (j + 1) (by omega)))
        (Nat.cast_nonneg _)
    _ = _ := by ring

/-- For positive m and μ|t| ≤ 1/2, the error profile is at most (8/3)(μ|t|)^(2m + 1). -/
theorem errorProfile_le (xs : List (Matrix I I ℂ)) (m : ℕ) (hm : 0 < m)
    (t : ℝ) (ht : mu xs m * |t| ≤ 1 / 2) :
    errorProfile xs t m ≤ (8 / 3 : ℝ) * (mu xs m * |t|) ^ (2 * m + 1) := by
  let b := mu xs m * |t|
  have hb : 0 ≤ b := mul_nonneg (mu_nonneg xs m hm) (abs_nonneg t)
  let r : ℝ≥0 := ⟨|t|, abs_nonneg t⟩
  have hc := actual_control xs m hm t ht
  have hsp := (summable_nat_add_iff m).mpr
    (orderProfile_hasSum xs r (2 * m + 1) hc t (le_refl _) m).summable
  have hsl := massProfile_hasSum xs r (2 * m + 1) hc t (le_refl _) m
  have hg := summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)
  have hgs : (∑' k : ℕ, (1 / 4 : ℝ) ^ k) = 4 / 3 := by
    rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)]
    norm_num
  have hp : (∑' k, orderProfile xs t m (k + m)) ≤
      b ^ (2 * m + 1) * (4 / 3) * factorialMass (m - 1) := by
    calc
      _ ≤ ∑' k, (b ^ (2 * m + 1) * (1 / 4 : ℝ) ^ k) * factorialMass (m - 1) :=
        Summable.tsum_le_tsum (orderProfile_le xs m hm t ht) hsp
          ((hg.mul_left (b ^ (2 * m + 1))).mul_right _)
      _ = _ := by rw [tsum_mul_right, tsum_mul_left, hgs]
  have hl (k : ℕ) : massProfile xs t m k ≤ b ^ (2 * m + 1) * (1 / 4 : ℝ) ^ k := by
    have h := massProfile_le_mu xs m m k (by omega) (le_refl _) (by omega) t
    have he : 2 * k + 3 * m = 2 * (k + m) + m := by omega
    rw [he] at h
    exact h.trans (power_tail_le b hb ht m k m (by omega))
  have hlast : commutatorMass xs t ^ m ≤ b ^ (2 * m + 1) * (4 / 3) := by
    rw [← hsl.tsum_eq]
    calc
      _ ≤ ∑' k, b ^ (2 * m + 1) * (1 / 4 : ℝ) ^ k :=
        Summable.tsum_le_tsum hl hsl.summable (hg.mul_left _)
      _ = _ := by rw [tsum_mul_left, hgs]
  have hfac : factorialMass (m - 1) + 1 / (m.factorial : ℝ) = factorialMass m := by
    have h := factorialMass_succ (m - 1)
    simpa only [Nat.sub_add_cancel (show 1 ≤ m by omega)] using! h.symm
  calc
    _ ≤ b ^ (2 * m + 1) * (4 / 3) * factorialMass (m - 1) +
        (b ^ (2 * m + 1) * (4 / 3)) / (m.factorial : ℝ) :=
      add_le_add hp (div_le_div_of_nonneg_right hlast (Nat.cast_nonneg _))
    _ = (b ^ (2 * m + 1) * (4 / 3)) * factorialMass m := by rw [← hfac]; ring
    _ ≤ (b ^ (2 * m + 1) * (4 / 3)) * 2 :=
      mul_le_mul_of_nonneg_left (factorialMass_le m) (by positivity)
    _ = _ := by ring

variable {K : Type} [Fintype K]

/-- For Hermitian generators with normalized cancellation weights and μ|t| ≤ 1/2, the
multi-product error is at most 8/3 times the absolute weight mass times (μ|t|)^(2m + 1). -/
theorem actualMPF_root_error (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (q : K → ℕ) (hq : ∀ j, 0 < q j) (a : K → ℝ) (ha : ∑ j, a j = 1)
    (m : ℕ) (hm : 0 < m) (hmom : ∀ k, 0 < k → k < m → coefficientWeight q a k = 0)
    (t : ℝ) (ht : mu xs m * |t| ≤ 1 / 2) :
    ‖actualMPF xs q a t - NormedSpace.exp (t • ((-Complex.I) • xs.sum))‖ ≤
      (8 / 3 : ℝ) * (∑ j, |a j|) * (mu xs m * |t|) ^ (2 * m + 1) := by
  have h := actualMPF_error xs hxs (⟨|t|, abs_nonneg t⟩ : ℝ≥0) (2 * m + 1)
    (actual_control xs m hm t ht) q hq a ha m hm hmom t (le_refl _)
  exact h.trans ((mul_le_mul_of_nonneg_left (errorProfile_le xs m hm t ht)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)).trans_eq (by ring))

omit [Fintype K] in

/-- For Hermitian generators and μ|t| ≤ 1/2, the Chebyshev multi-product error is at most (16/3)
times the m-th harmonic number times (μ|t|)^(2m + 1). -/
theorem chebyshev_root_error (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (m : ℕ) (hm : 0 < m) (t : ℝ) (ht : mu xs m * |t| ≤ 1 / 2) :
    ‖actualMPF xs (ChebyshevNodes.node m) (ChebyshevNodes.weight m) t -
      NormedSpace.exp (t • ((-Complex.I) • xs.sum))‖ ≤
        (16 / 3 : ℝ) * (harmonic m : ℝ) * (mu xs m * |t|) ^ (2 * m + 1) := by
  have h := chebyshev_error_harmonic xs hxs (⟨|t|, abs_nonneg t⟩ : ℝ≥0)
    (2 * m + 1) (actual_control xs m hm t ht) t (le_refl _) m hm
  have hfac : 0 ≤ 2 * (harmonic m : ℝ) :=
    (Finset.sum_nonneg fun j _ => abs_nonneg (ChebyshevNodes.weight m j)).trans
      (ChebyshevCondition.weight_mass_harmonic m hm)
  exact h.trans ((mul_le_mul_of_nonneg_left (errorProfile_le xs m hm t ht) hfac).trans_eq (by ring))

omit [Fintype K] in

/-- Under the root-scale step condition, the Chebyshev error is bounded by (16/3)Hₘ μ^(2m + 1)
times |t|^(2m + 1). -/
theorem chebyshev_time_power (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (m : ℕ) (hm : 0 < m) (t : ℝ) (ht : mu xs m * |t| ≤ 1 / 2) :
    ‖actualMPF xs (ChebyshevNodes.node m) (ChebyshevNodes.weight m) t -
      NormedSpace.exp (t • ((-Complex.I) • xs.sum))‖ ≤
        ((16 / 3 : ℝ) * (harmonic m : ℝ) * mu xs m ^ (2 * m + 1)) * |t| ^ (2 * m + 1) := by
  have h := chebyshev_root_error xs hxs m hm t ht
  simpa only [mul_pow, mul_assoc] using! h

end Qatlib.Papers.CommutLCHS26.MainResults.MPFRootBound
