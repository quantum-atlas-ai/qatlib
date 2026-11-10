/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.DysonExpansion
import Qatlib.Papers.CommutLCHS26.MainResults.ChebyshevNodes
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MPFMomentSeries

open Matrix
open scoped BigOperators Classical Matrix.Norms.L2Operator NNReal ENNReal
open BCHControlled BCHPerturbation DysonExpansion
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
set_option warningAsError false

variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K]

def actualMPF (xs : List (Matrix I I ℂ)) (q : K → ℕ) (a : K → ℝ) (t : ℝ) : Matrix I I ℂ :=
  ∑ j, a j • (suzukiExponentialWord
    (recursiveSuzukiGenerators (xs.map (fun X => (-Complex.I) • X)) 0) (t / q j)) ^ q j

def coefficientWeight (q : K → ℕ) (a : K → ℝ) (k : ℕ) : ℝ :=
  ∑ j, a j / (q j : ℝ) ^ (2 * k)

def weightedRemainder (xs : List (Matrix I I ℂ)) (q : K → ℕ) (a : K → ℝ) (t : ℝ) (p : ℕ) :
    Matrix I I ℂ := ∑ j, a j • PerturbationDyson.remainder
      (t • ((-Complex.I) • xs.sum)) (perturbation xs (q j) t) p 1

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
