/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.DysonExpansion
import Qatlib.Papers.CommutLCHS26.MainResults.ChebyshevNodes

/-!
# Moment cancellation in actual multi-product series

This module defines `actualMPF` as a weighted sum of repeated product formulas and
`coefficientWeight` as its inverse-even-power moments. Under the odd-coefficient control and
cancellation hypotheses, the Dyson expansion reduces to a tail beginning at the chosen moment
order plus `weightedRemainder`, supplying an exact identity for the analysis in
[AftabAnTrivisa2026].

## Main statements

* `tail_hasSum`: removes the canceled moment coefficients.
* `actualMPF_series`: expresses the actual approximation as target plus tail and remainder.
* `chebyshev_series`: specializes this identity to Chebyshev interpolation.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MPFMomentSeries

open Matrix
open scoped BigOperators Classical Matrix.Norms.L2Operator NNReal ENNReal
open BCHControlled BCHPerturbation DysonExpansion
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K]

/-- The finite weighted sum of repeated level-zero recursive Suzuki words for the generators
-iX. -/
def actualMPF (xs : List (Matrix I I ℂ)) (q : K → ℕ) (a : K → ℝ) (t : ℝ) : Matrix I I ℂ :=
  ∑ j, a j • (suzukiExponentialWord
    (recursiveSuzukiGenerators (xs.map (fun X => (-Complex.I) • X)) 0) (t / q j)) ^ q j

/-- The weighted inverse-even-power moment ∑ⱼ aⱼ/qⱼ^(2k). -/
def coefficientWeight (q : K → ℕ) (a : K → ℝ) (k : ℕ) : ℝ :=
  ∑ j, a j / (q j : ℝ) ^ (2 * k)

/-- The coefficient-weighted sum of the depth-p Dyson remainders for the repeated formulas. -/
def weightedRemainder (xs : List (Matrix I I ℂ)) (q : K → ℕ) (a : K → ℝ) (t : ℝ) (p : ℕ) :
    Matrix I I ℂ := ∑ j, a j • PerturbationDyson.remainder
      (t • ((-Complex.I) • xs.sum)) (perturbation xs (q j) t) p 1

/-- Under odd-coefficient control, weighting the collected coefficient series by the
inverse-power moments gives the weighted positive-depth Dyson prefix. -/
theorem weighted_prefix_hasSum (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (r : ℝ≥0) (J : ℕ) (hc : OddControl xs r J) (q : K → ℕ) (hq : ∀ j, 0 < q j)
    (a : K → ℝ) (t : ℝ) (ht : |t| ≤ r) (p : ℕ) :
    HasSum (fun k => coefficientWeight q a k • orderCoefficient xs t p k)
      (∑ j, a j • (∑ l ∈ Finset.range (p - 1),
        PerturbationDyson.term (t • ((-Complex.I) • xs.sum)) (perturbation xs (q j) t) (l + 1) 1)) := by
  have h := hasSum_sum (s := (Finset.univ : Finset K))
    (fun j _ => (prefix_hasSum xs hxs r J hc (q j) (hq j) t ht p).const_smul (a j))
  convert! h using 1
  funext k
  rw [coefficientWeight, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul]
  congr 1
  ring

/-- When positive moments below m vanish, the coefficient series starting at index m sums to the
weighted positive-depth Dyson prefix. -/
theorem tail_hasSum (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (r : ℝ≥0) (J : ℕ) (hc : OddControl xs r J) (q : K → ℕ) (hq : ∀ j, 0 < q j)
    (a : K → ℝ) (m : ℕ) (hmom : ∀ k, 0 < k → k < m → coefficientWeight q a k = 0)
    (t : ℝ) (ht : |t| ≤ r) (p : ℕ) :
    HasSum (fun k => coefficientWeight q a (k + m) • orderCoefficient xs t p (k + m))
      (∑ j, a j • (∑ l ∈ Finset.range (p - 1),
        PerturbationDyson.term (t • ((-Complex.I) • xs.sum)) (perturbation xs (q j) t) (l + 1) 1)) := by
  have hz : ∑ k ∈ Finset.range m, coefficientWeight q a k • orderCoefficient xs t p k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hk0 : k = 0
    · rw [hk0, orderCoefficient_zero, smul_zero]
    · rw [hmom k (by omega) (Finset.mem_range.mp hk), zero_smul]
  apply (hasSum_nat_add_iff
    (f := fun k => coefficientWeight q a k • orderCoefficient xs t p k) m).mpr
  simpa only [hz, add_zero] using! weighted_prefix_hasSum xs hxs r J hc q hq a t ht p

/-- For normalized weights satisfying the cancellation moments, the actual multi-product formula
equals the target exponential plus its coefficient tail from index m and weighted Dyson
remainder. -/
theorem actualMPF_series (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (r : ℝ≥0) (J : ℕ) (hc : OddControl xs r J) (q : K → ℕ) (hq : ∀ j, 0 < q j)
    (a : K → ℝ) (ha : ∑ j, a j = 1) (m : ℕ)
    (hmom : ∀ k, 0 < k → k < m → coefficientWeight q a k = 0)
    (t : ℝ) (ht : |t| ≤ r) (p : ℕ) (hp : 0 < p) :
    actualMPF xs q a t = NormedSpace.exp (t • ((-Complex.I) • xs.sum)) +
      (∑' k, coefficientWeight q a (k + m) • orderCoefficient xs t p (k + m)) +
        weightedRemainder xs q a t p := by
  have htail := (tail_hasSum xs hxs r J hc q hq a m hmom t ht p).tsum_eq
  calc
    _ = ∑ j, a j • (NormedSpace.exp (t • ((-Complex.I) • xs.sum)) +
        (∑ l ∈ Finset.range (p - 1), PerturbationDyson.term
          (t • ((-Complex.I) • xs.sum)) (perturbation xs (q j) t) (l + 1) 1) +
        PerturbationDyson.remainder (t • ((-Complex.I) • xs.sum)) (perturbation xs (q j) t) p 1) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [(BCHPerturbation.repetition_expansion xs hxs r J hc (q j) (hq j) t ht p hp).1]
    _ = _ := by
      simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, ha, one_smul,
        weightedRemainder]
      rw [htail]

/-- The Chebyshev multi-product formula equals the target exponential plus its moment-weighted
coefficient tail from index m and depth-m weighted remainder. -/
theorem chebyshev_series (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (r : ℝ≥0) (J : ℕ) (hc : OddControl xs r J) (t : ℝ) (ht : |t| ≤ r)
    (m : ℕ) (hm : 0 < m) :
    actualMPF xs (ChebyshevNodes.node m) (ChebyshevNodes.weight m) t =
      NormedSpace.exp (t • ((-Complex.I) • xs.sum)) +
        (∑' k, coefficientWeight (ChebyshevNodes.node m) (ChebyshevNodes.weight m) (k + m) •
          orderCoefficient xs t m (k + m)) +
        weightedRemainder xs (ChebyshevNodes.node m) (ChebyshevNodes.weight m) t m := by
  apply actualMPF_series xs hxs r J hc _ (ChebyshevNodes.node_pos m hm) _ _ m _ t ht m hm
  · have h := ChebyshevNodes.weight_moments m hm 0 hm
    simpa only [mul_zero, pow_zero, div_one] using! h
  · intro k hk hkm
    exact (ChebyshevNodes.weight_moments m hm k hkm).trans (zero_pow (by omega))

end Qatlib.Papers.CommutLCHS26.MainResults.MPFMomentSeries
