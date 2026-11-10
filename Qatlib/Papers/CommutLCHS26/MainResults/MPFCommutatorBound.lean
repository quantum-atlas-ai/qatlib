/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.MPFMomentSeries
import Qatlib.Papers.CommutLCHS26.MainResults.ChebyshevCondition
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MPFCommutatorBound

open Matrix
open scoped BigOperators Classical Matrix.Norms.L2Operator NNReal ENNReal
open BCHControlled BCHCommMass BCHMassProducts BCHPerturbation DysonExpansion MPFMomentSeries
set_option warningAsError false

variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K]

omit [DecidableEq I] [Fintype K] in

theorem massProfile_nonneg (xs : List (Matrix I I ℂ)) (t : ℝ) (p k : ℕ) :
    0 ≤ massProfile xs t p k :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => massTerm_nonneg xs t _

omit [DecidableEq I] [Fintype K] in

theorem orderProfile_nonneg (xs : List (Matrix I I ℂ)) (t : ℝ) (p k : ℕ) :
    0 ≤ orderProfile xs t p k := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact div_nonneg (massProfile_nonneg xs t _ _) (Nat.cast_nonneg _)
  · exact le_refl _

omit [Fintype K] in

theorem orderProfile_hasSum (xs : List (Matrix I I ℂ)) (r : ℝ≥0) (J : ℕ)
    (hc : OddControl xs r J) (t : ℝ) (ht : |t| ≤ r) (p : ℕ) :
    HasSum (orderProfile xs t p)
      (∑ j ∈ Finset.range (p - 1), commutatorMass xs t ^ (j + 1) / ((j + 1).factorial : ℝ)) := by
  have h := hasSum_sum (s := Finset.range (p - 1)) (fun j _ =>
    shift_hasSum _ _ ((massProfile_hasSum xs r J hc t ht (j + 1)).div_const
      ((j + 1).factorial : ℝ)) (j + 1))
  exact h

omit [Fintype I] [DecidableEq I] in

theorem coefficientWeight_abs_le (q : K → ℕ) (hq : ∀ j, 0 < q j) (a : K → ℝ) (k : ℕ) :
    |coefficientWeight q a k| ≤ ∑ j, |a j| := by
  unfold coefficientWeight
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  have hden : |(q j : ℝ) ^ (2 * k)| = (q j : ℝ) ^ (2 * k) :=
    abs_of_nonneg (pow_nonneg (Nat.cast_nonneg (q j)) _)
  rw [abs_div, hden]
  exact div_le_self (abs_nonneg _) (one_le_pow₀ (by exact_mod_cast hq j))

theorem tail_norm_le (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (r : ℝ≥0) (J : ℕ) (hc : OddControl xs r J) (q : K → ℕ) (hq : ∀ j, 0 < q j)
    (a : K → ℝ) (t : ℝ) (ht : |t| ≤ r) (p m : ℕ) :
    ‖∑' k, coefficientWeight q a (k + m) • orderCoefficient xs t p (k + m)‖ ≤
      (∑ j, |a j|) * ∑' k, orderProfile xs t p (k + m) := by
  have hs := (summable_nat_add_iff m).mpr (orderProfile_hasSum xs r J hc t ht p).summable
  have hm := hs.mul_left (∑ j, |a j|)
  have hb (k : ℕ) : ‖coefficientWeight q a (k + m) • orderCoefficient xs t p (k + m)‖ ≤
      (∑ j, |a j|) * orderProfile xs t p (k + m) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (coefficientWeight_abs_le q hq a _) (orderCoefficient_norm xs hxs t p _)
      (norm_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hn := hm.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  apply (norm_tsum_le_tsum_norm hn).trans
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum hb hn hm

theorem weightedRemainder_norm (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (r : ℝ≥0) (J : ℕ) (hc : OddControl xs r J) (q : K → ℕ) (hq : ∀ j, 0 < q j)
    (a : K → ℝ) (t : ℝ) (ht : |t| ≤ r) (p : ℕ) (hp : 0 < p) :
    ‖weightedRemainder xs q a t p‖ ≤
      (∑ j, |a j|) * (commutatorMass xs t ^ p / (p.factorial : ℝ)) := by
  have hb (j : K) : ‖PerturbationDyson.remainder (t • ((-Complex.I) • xs.sum))
      (perturbation xs (q j) t) p 1‖ ≤ commutatorMass xs t ^ p / (p.factorial : ℝ) := by
    have h := (BCHPerturbation.repetition_expansion xs hxs r J hc (q j) (hq j) t ht p hp).2
    apply h.trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact pow_le_pow_left₀ (div_nonneg (commutatorMass_nonneg xs t)
      (pow_nonneg (Nat.cast_nonneg (q j)) _))
      (div_le_self (commutatorMass_nonneg xs t) (one_le_pow₀ (by exact_mod_cast hq j))) p
  unfold weightedRemainder
  calc
    _ ≤ ∑ j, ‖a j • PerturbationDyson.remainder
        (t • ((-Complex.I) • xs.sum)) (perturbation xs (q j) t) p 1‖ := norm_sum_le _ _
    _ ≤ ∑ j, |a j| * (commutatorMass xs t ^ p / (p.factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hb j) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

omit [Fintype K] in

def errorProfile (xs : List (Matrix I I ℂ)) (t : ℝ) (m : ℕ) : ℝ :=
  (∑' k, orderProfile xs t m (k + m)) + commutatorMass xs t ^ m / (m.factorial : ℝ)

omit [DecidableEq I] [Fintype K] in

theorem errorProfile_nonneg (xs : List (Matrix I I ℂ)) (t : ℝ) (m : ℕ) :
    0 ≤ errorProfile xs t m :=
  add_nonneg (tsum_nonneg fun _ => orderProfile_nonneg xs t m _)
    (div_nonneg (pow_nonneg (commutatorMass_nonneg xs t) _) (Nat.cast_nonneg _))

theorem actualMPF_error (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (r : ℝ≥0) (J : ℕ) (hc : OddControl xs r J) (q : K → ℕ) (hq : ∀ j, 0 < q j)
    (a : K → ℝ) (ha : ∑ j, a j = 1) (m : ℕ) (hm : 0 < m)
    (hmom : ∀ k, 0 < k → k < m → coefficientWeight q a k = 0)
    (t : ℝ) (ht : |t| ≤ r) :
    ‖actualMPF xs q a t - NormedSpace.exp (t • ((-Complex.I) • xs.sum))‖ ≤
      (∑ j, |a j|) * errorProfile xs t m := by
  have he := actualMPF_series xs hxs r J hc q hq a ha m hmom t ht m hm
  rw [he]
  have hsplit (A T R : Matrix I I ℂ) : A + T + R - A = T + R := by abel
  rw [hsplit]
  exact (norm_add_le _ _).trans ((add_le_add
    (tail_norm_le xs hxs r J hc q hq a t ht m m)
    (weightedRemainder_norm xs hxs r J hc q hq a t ht m hm)).trans_eq (by unfold errorProfile; ring))

theorem chebyshev_error (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (r : ℝ≥0) (J : ℕ) (hc : OddControl xs r J) (t : ℝ) (ht : |t| ≤ r)
    (m : ℕ) (hm : 0 < m) :
    ‖actualMPF xs (ChebyshevNodes.node m) (ChebyshevNodes.weight m) t -
      NormedSpace.exp (t • ((-Complex.I) • xs.sum))‖ ≤
        (∑ j : Fin m, |ChebyshevNodes.weight m j|) * errorProfile xs t m := by
  apply actualMPF_error xs hxs r J hc _ (ChebyshevNodes.node_pos m hm) _ _ m hm _ t ht
  · simpa only [mul_zero, pow_zero, div_one] using! ChebyshevNodes.weight_moments m hm 0 hm
  · intro k hk hkm
    exact (ChebyshevNodes.weight_moments m hm k hkm).trans (zero_pow (by omega))

theorem chebyshev_error_harmonic (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (r : ℝ≥0) (J : ℕ) (hc : OddControl xs r J) (t : ℝ) (ht : |t| ≤ r)
    (m : ℕ) (hm : 0 < m) :
    ‖actualMPF xs (ChebyshevNodes.node m) (ChebyshevNodes.weight m) t -
      NormedSpace.exp (t • ((-Complex.I) • xs.sum))‖ ≤
        (2 * (harmonic m : ℝ)) * errorProfile xs t m :=
  (chebyshev_error xs hxs r J hc t ht m hm).trans
    (mul_le_mul_of_nonneg_right (ChebyshevCondition.weight_mass_harmonic m hm)
      (errorProfile_nonneg xs t m))

end Qatlib.Papers.CommutLCHS26.MainResults.MPFCommutatorBound
