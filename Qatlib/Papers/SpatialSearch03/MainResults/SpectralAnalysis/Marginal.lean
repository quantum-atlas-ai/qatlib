/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums.LatticeSum2Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Low-dimensional secular rescaling

This module expands the secular function at negative energies and introduces the dimension-two
and dimension-three energy rescalings used in [ChildsGoldstone2004]. It proves existence and
uniqueness of the corresponding negative rescaled roots.

The remaining results evaluate rescaled amplitude expressions and derive repetition-time lower
bounds from explicit amplitude and time hypotheses.

## Main statements

* `secular_taylor2`: expansion through the second lattice sum with an exact remainder.
* `existsUnique_rescaled_root_d3` and `existsUnique_rescaled_root_d2`: unique negative rescaled
  roots.
* `repetition_time_ge_d3` and `repetition_time_ge_d2`: conditional lower bounds on repetition
  time.

## References

* [Childs and Goldstone, 2004][ChildsGoldstone2004]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpatialSearch03.MainResults

open Finset
open ThetaSums

variable {d : ℕ}

/-- For positive coupling and side length and negative energy, split the secular function into
its zero-mode pole, nonzero-mode inverse-energy sum, and exact linear-in-energy correction
[ChildsGoldstone2004]. -/
theorem secular_expansion {γ : ℝ} {n : ℕ} [NeZero n] (hγ : 0 < γ) (hn : 0 < n)
    {E : ℝ} (hE : E < 0) :
    secular γ n d E
      = - 1 / ((n : ℝ) ^ d * E)
        + ((n : ℝ) ^ d)⁻¹ *
            (∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
              (γ * dispersion (waveVector n m))⁻¹)
        + ((n : ℝ) ^ d)⁻¹ *
            (∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
              E / (γ * dispersion (waveVector n m) *
                (γ * dispersion (waveVector n m) - E))) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hNpos : (0:ℝ) < (n:ℝ) ^ d := by positivity
  have hE0 : E ≠ 0 := ne_of_lt hE
  have hsplit : ∑ m : Fin d → ZMod n, (γ * dispersion (waveVector n m) - E)⁻¹
      = (∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
            (γ * dispersion (waveVector n m) - E)⁻¹)
        + (γ * dispersion (waveVector n (0 : Fin d → ZMod n)) - E)⁻¹ :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ _)).symm
  have hzero : (γ * dispersion (waveVector n (0 : Fin d → ZMod n)) - E)⁻¹ = -(E⁻¹) := by
    have h0 : γ * dispersion (waveVector n (0 : Fin d → ZMod n)) = 0 := by
      rw [waveVector_zero, dispersion_zero, mul_zero]
    rw [h0, zero_sub, inv_neg]
  have hpt : ∀ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
      (γ * dispersion (waveVector n m) - E)⁻¹
        = (γ * dispersion (waveVector n m))⁻¹
          + E / (γ * dispersion (waveVector n m) *
              (γ * dispersion (waveVector n m) - E)) := by
    intro m hm
    have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm).1
    have hd : 0 < dispersion (waveVector n m) := dispersion_waveVector_pos (d := d) hn hm0
    have ha : (0:ℝ) < γ * dispersion (waveVector n m) := mul_pos hγ hd
    have ha0 : γ * dispersion (waveVector n m) ≠ 0 := ne_of_gt ha
    have hb : γ * dispersion (waveVector n m) - E ≠ 0 := by linarith
    have hmain : (γ * dispersion (waveVector n m))⁻¹
        + E / (γ * dispersion (waveVector n m) *
            (γ * dispersion (waveVector n m) - E))
        = (γ * dispersion (waveVector n m) - E)⁻¹ := by
      rw [div_eq_mul_inv]
      field_simp [ha0, hb]
      ring
    exact hmain.symm
  have hsum : ∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
        (γ * dispersion (waveVector n m) - E)⁻¹
      = ∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
          (γ * dispersion (waveVector n m))⁻¹
        + ∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
          E / (γ * dispersion (waveVector n m) *
            (γ * dispersion (waveVector n m) - E)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hpt
  unfold secular
  rw [hsplit, hzero, hsum]
  field_simp [hNpos.ne', hE0]
  ring

/-- For negative energy, expand the secular function as the zero-mode pole plus `latSum1 n d /
γ`, `E * latSum2 n d / γ ^ 2`, and an explicit quadratic remainder, assuming positive
coupling and side length [ChildsGoldstone2004]. -/
theorem secular_taylor2 {γ : ℝ} {n : ℕ} [NeZero n] (hγ : 0 < γ) (hn : 0 < n)
    {E : ℝ} (hE : E < 0) :
    secular γ n d E
      = - 1 / ((n : ℝ) ^ d * E)
        + latSum1 n d / γ
        + E * latSum2 n d / γ ^ 2
        + (E ^ 2 / (n : ℝ) ^ d) *
            (∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
              (γ * dispersion (waveVector n m))⁻¹ ^ 2 *
                (γ * dispersion (waveVector n m) - E)⁻¹) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hNpos : (0:ℝ) < (n:ℝ) ^ d := by positivity
  have hE0 : E ≠ 0 := ne_of_lt hE
  have hsplit : ∑ m : Fin d → ZMod n, (γ * dispersion (waveVector n m) - E)⁻¹
      = (∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
            (γ * dispersion (waveVector n m) - E)⁻¹)
        + (γ * dispersion (waveVector n (0 : Fin d → ZMod n)) - E)⁻¹ :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ _)).symm
  have hzero : (γ * dispersion (waveVector n (0 : Fin d → ZMod n)) - E)⁻¹ = -(E⁻¹) := by
    have h0 : γ * dispersion (waveVector n (0 : Fin d → ZMod n)) = 0 := by
      rw [waveVector_zero, dispersion_zero, mul_zero]
    rw [h0, zero_sub, inv_neg]
  have hpt : ∀ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
      (γ * dispersion (waveVector n m) - E)⁻¹
        = (γ * dispersion (waveVector n m))⁻¹
          + E * ((γ * dispersion (waveVector n m))⁻¹ ^ 2)
          + E ^ 2 * ((γ * dispersion (waveVector n m))⁻¹ ^ 2 *
              (γ * dispersion (waveVector n m) - E)⁻¹) := by
    intro m hm
    have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm).1
    have hd : 0 < dispersion (waveVector n m) := dispersion_waveVector_pos (d := d) hn hm0
    have ha : (0:ℝ) < γ * dispersion (waveVector n m) := mul_pos hγ hd
    have ha0 : γ * dispersion (waveVector n m) ≠ 0 := ne_of_gt ha
    have hb : γ * dispersion (waveVector n m) - E ≠ 0 := by linarith
    have hmain : (γ * dispersion (waveVector n m))⁻¹
        + E * ((γ * dispersion (waveVector n m))⁻¹ ^ 2)
        + E ^ 2 * ((γ * dispersion (waveVector n m))⁻¹ ^ 2 *
            (γ * dispersion (waveVector n m) - E)⁻¹)
        = (γ * dispersion (waveVector n m) - E)⁻¹ := by
      field_simp [ha0, hb]
      ring
    exact hmain.symm
  have hsum : ∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
        (γ * dispersion (waveVector n m) - E)⁻¹
      = ∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
          (γ * dispersion (waveVector n m))⁻¹
        + E * (∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
            (γ * dispersion (waveVector n m))⁻¹ ^ 2)
        + E ^ 2 * (∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
            (γ * dispersion (waveVector n m))⁻¹ ^ 2 *
              (γ * dispersion (waveVector n m) - E)⁻¹) := by
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
  have ha1 : ∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
        (γ * dispersion (waveVector n m))⁻¹
      = γ⁻¹ * ∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
          (dispersion (waveVector n m))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m _
    rw [mul_inv]
  have ha2 : ∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
        (γ * dispersion (waveVector n m))⁻¹ ^ 2
      = γ⁻¹ ^ 2 * ∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
          (dispersion (waveVector n m))⁻¹ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m _
    rw [mul_inv, mul_pow]
  unfold secular latSum1 latSum2
  rw [hsplit, hzero, hsum, ha1, ha2]
  field_simp [hNpos.ne', hE0]
  ring

/-- The dimension-three rescaled energy `4 * Real.pi ^ 2 * I * x / n ^ (2 / 3 : ℝ)`. -/
def rescaledEnergy3 (I x : ℝ) (n : ℕ) : ℝ :=
  4 * Real.pi ^ 2 * I * x / ((n : ℝ) ^ (2 / 3 : ℝ))

/-- The dimension-two rescaled energy `2 * Real.pi * Real.log n / n * x`. -/
def rescaledEnergy2 (x : ℝ) (n : ℕ) : ℝ :=
  2 * Real.pi * Real.log (n : ℝ) / (n : ℝ) * x

/-- For positive `I` and side length, the dimension-three rescaled energy is strictly increasing
in `x`. -/
theorem rescaledEnergy3_strictMono {I : ℝ} {n : ℕ} (hI : 0 < I) (hn : 0 < n) :
    StrictMono (fun x : ℝ => rescaledEnergy3 I x n) := by
  intro x y hxy
  simp only [rescaledEnergy3]
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hbase : (0:ℝ) < (n:ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hnpos _
  have hc : (0:ℝ) < 4 * Real.pi ^ 2 * I / ((n : ℝ) ^ (2 / 3 : ℝ)) := by positivity
  have e1 : 4 * Real.pi ^ 2 * I * x / ((n : ℝ) ^ (2 / 3 : ℝ))
      = (4 * Real.pi ^ 2 * I / ((n : ℝ) ^ (2 / 3 : ℝ))) * x := by ring
  have e2 : 4 * Real.pi ^ 2 * I * y / ((n : ℝ) ^ (2 / 3 : ℝ))
      = (4 * Real.pi ^ 2 * I / ((n : ℝ) ^ (2 / 3 : ℝ))) * y := by ring
  rw [e1, e2]
  exact mul_lt_mul_of_pos_left hxy hc

/-- For positive coupling, side length, and `I`, there is a negative rescaled parameter solving
the dimension-three secular equation. -/
theorem exists_rescaled_root_d3 {γ I : ℝ} {n : ℕ} [NeZero n] (hγ : 0 < γ) (hn : 0 < n)
    (hI : 0 < I) :
    ∃ x : ℝ, x < 0 ∧ secular γ n 3 (rescaledEnergy3 I x n) = 1 := by
  obtain ⟨E, hEneg, hFE⟩ := exists_secular_eq_one (d := 3) hγ hn
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hbase : (0:ℝ) < (n:ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hnpos _
  refine ⟨E * (n : ℝ) ^ (2 / 3 : ℝ) / (4 * Real.pi ^ 2 * I), ?_, ?_⟩
  · have hden : (0:ℝ) < 4 * Real.pi ^ 2 * I := by positivity
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hEneg hbase) hden
  · have hI0 : (4 * Real.pi ^ 2 * I) ≠ 0 := by positivity
    have hbase0 : (n : ℝ) ^ (2 / 3 : ℝ) ≠ 0 := ne_of_gt hbase
    have hEq : rescaledEnergy3 I (E * (n : ℝ) ^ (2 / 3 : ℝ) /
        (4 * Real.pi ^ 2 * I)) n = E := by
      unfold rescaledEnergy3
      field_simp [hI0, hbase0]
    rw [hEq]
    exact hFE

/-- For positive coupling, side length, and `I`, there is exactly one negative rescaled
parameter solving the dimension-three secular equation [ChildsGoldstone2004]. -/
theorem existsUnique_rescaled_root_d3 {γ I : ℝ} {n : ℕ} [NeZero n] (hγ : 0 < γ)
    (hn : 0 < n) (hI : 0 < I) :
    ∃! x : ℝ, x < 0 ∧ secular γ n 3 (rescaledEnergy3 I x n) = 1 := by
  obtain ⟨x0, hx0neg, hx0F⟩ := exists_rescaled_root_d3 hγ hn hI
  refine ⟨x0, ⟨hx0neg, hx0F⟩, ?_⟩
  intro y hy
  obtain ⟨hyneg, hyF⟩ := hy
  have hmono := rescaledEnergy3_strictMono (n := n) hI hn
  have hEy : rescaledEnergy3 I y n < 0 := by
    have h := hmono hyneg
    simpa [rescaledEnergy3] using h
  have hEx0 : rescaledEnergy3 I x0 n < 0 := by
    have h := hmono hx0neg
    simpa [rescaledEnergy3] using h
  by_contra hne
  have hEne : rescaledEnergy3 I y n ≠ rescaledEnergy3 I x0 n := by
    intro h
    exact hne (hmono.injective h)
  rcases lt_or_gt_of_ne hEne with hlt | hlt
  · have hs := secular_strictMonoOn (d := 3) hγ hn hEy hEx0 hlt
    rw [hyF, hx0F] at hs
    exact lt_irrefl _ hs
  · have hs := secular_strictMonoOn (d := 3) hγ hn hEx0 hEy hlt
    rw [hyF, hx0F] at hs
    exact lt_irrefl _ hs

/-- For side length greater than one, the dimension-two rescaled energy is strictly increasing
in `x`. -/
theorem rescaledEnergy2_strictMono {n : ℕ} (hn : 1 < n) :
    StrictMono (fun x : ℝ => rescaledEnergy2 x n) := by
  intro x y hxy
  simp only [rescaledEnergy2]
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.lt_trans Nat.zero_lt_one hn
  have hlog : (0:ℝ) < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hc : (0:ℝ) < 2 * Real.pi * Real.log (n : ℝ) / (n : ℝ) := by positivity
  have e1 : 2 * Real.pi * Real.log (n : ℝ) / (n : ℝ) * x
      = (2 * Real.pi * Real.log (n : ℝ) / (n : ℝ)) * x := rfl
  have e2 : 2 * Real.pi * Real.log (n : ℝ) / (n : ℝ) * y
      = (2 * Real.pi * Real.log (n : ℝ) / (n : ℝ)) * y := rfl
  exact mul_lt_mul_of_pos_left hxy hc

/-- For positive coupling and side length greater than one, there is a negative rescaled
parameter solving the dimension-two secular equation. -/
theorem exists_rescaled_root_d2 {γ : ℝ} {n : ℕ} [NeZero n] (hγ : 0 < γ) (hn : 1 < n) :
    ∃ x : ℝ, x < 0 ∧ secular γ n 2 (rescaledEnergy2 x n) = 1 := by
  obtain ⟨E, hEneg, hFE⟩ := exists_secular_eq_one (d := 2) hγ (Nat.lt_trans Nat.zero_lt_one hn)
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.lt_trans Nat.zero_lt_one hn
  have hlog : (0:ℝ) < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  refine ⟨E * (n : ℝ) / (2 * Real.pi * Real.log (n : ℝ)), ?_, ?_⟩
  · have hden : (0:ℝ) < 2 * Real.pi * Real.log (n : ℝ) := by positivity
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hEneg hnpos) hden
  · have hc0 : (2 * Real.pi * Real.log (n : ℝ)) ≠ 0 := by positivity
    have hEq : rescaledEnergy2 (E * (n : ℝ) / (2 * Real.pi * Real.log (n : ℝ))) n = E := by
      unfold rescaledEnergy2
      field_simp [hc0]
    rw [hEq]
    exact hFE

/-- For positive coupling and side length greater than one, there is exactly one negative
rescaled parameter solving the dimension-two secular equation [ChildsGoldstone2004]. -/
theorem existsUnique_rescaled_root_d2 {γ : ℝ} {n : ℕ} [NeZero n] (hγ : 0 < γ) (hn : 1 < n) :
    ∃! x : ℝ, x < 0 ∧ secular γ n 2 (rescaledEnergy2 x n) = 1 := by
  obtain ⟨x0, hx0neg, hx0F⟩ := exists_rescaled_root_d2 hγ hn
  refine ⟨x0, ⟨hx0neg, hx0F⟩, ?_⟩
  intro y hy
  obtain ⟨hyneg, hyF⟩ := hy
  have hmono := rescaledEnergy2_strictMono (n := n) hn
  have hEy : rescaledEnergy2 y n < 0 := by
    have h := hmono hyneg
    simpa [rescaledEnergy2] using h
  have hEx0 : rescaledEnergy2 x0 n < 0 := by
    have h := hmono hx0neg
    simpa [rescaledEnergy2] using h
  by_contra hne
  have hEne : rescaledEnergy2 y n ≠ rescaledEnergy2 x0 n := by
    intro h
    exact hne (hmono.injective h)
  rcases lt_or_gt_of_ne hEne with hlt | hlt
  · have hs := secular_strictMonoOn (d := 2) hγ (Nat.lt_trans Nat.zero_lt_one hn)
      hEy hEx0 hlt
    rw [hyF, hx0F] at hs
    exact lt_irrefl _ hs
  · have hs := secular_strictMonoOn (d := 2) hγ (Nat.lt_trans Nat.zero_lt_one hn)
      hEx0 hEy hlt
    rw [hyF, hx0F] at hs
    exact lt_irrefl _ hs

/-- For positive natural `n`, dividing `Real.sqrt n` by `n ^ (2 / 3 : ℝ)` gives the reciprocal
of `n ^ (1 / 6 : ℝ)`. -/
theorem sqrt_div_rpow_two_thirds {n : ℕ} (hn : 0 < n) :
    Real.sqrt (n : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) = ((n : ℝ) ^ (1 / 6 : ℝ))⁻¹ := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hnpos]
  have hexp : (1 / 2 : ℝ) - 2 / 3 = -(1 / 6 : ℝ) := by norm_num
  rw [hexp, Real.rpow_neg hnpos.le (1 / 6)]

/-- For positive natural `n`, the product of `Real.sqrt n` and `n ^ (1 / 6 : ℝ)` is `n ^ (2 / 3
: ℝ)`. -/
theorem sqrt_mul_rpow_one_sixth {n : ℕ} (hn : 0 < n) :
    Real.sqrt (n : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) = (n : ℝ) ^ (2 / 3 : ℝ) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnpos]
  norm_num

/-- For positive `n` and nonnegative `I`, the expression `2 * Real.sqrt n * |rescaledEnergy3 I x
n|` equals `8 * Real.pi ^ 2 * I * |x| / n ^ (1 / 6 : ℝ)`, the rescaled amplitude expression
in [ChildsGoldstone2004]. -/
theorem amplitude_bound_d3 {I x : ℝ} {n : ℕ} (hn : 0 < n) (hI : 0 ≤ I) :
    2 * Real.sqrt (n : ℝ) * |rescaledEnergy3 I x n|
      = 8 * Real.pi ^ 2 * I * |x| / ((n : ℝ) ^ (1 / 6 : ℝ)) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hbase : (0:ℝ) < (n:ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hnpos _
  simp only [rescaledEnergy3]
  have hcoef : (0:ℝ) ≤ 4 * Real.pi ^ 2 * I / ((n : ℝ) ^ (2 / 3 : ℝ)) := by positivity
  have h1 : |4 * Real.pi ^ 2 * I * x / ((n : ℝ) ^ (2 / 3 : ℝ))|
      = (4 * Real.pi ^ 2 * I / ((n : ℝ) ^ (2 / 3 : ℝ))) * |x| := by
    rw [show 4 * Real.pi ^ 2 * I * x / ((n : ℝ) ^ (2 / 3 : ℝ))
        = (4 * Real.pi ^ 2 * I / ((n : ℝ) ^ (2 / 3 : ℝ))) * x by ring]
    rw [abs_mul, abs_of_nonneg hcoef]
  rw [h1]
  have h2 : 2 * Real.sqrt (n : ℝ) *
      ((4 * Real.pi ^ 2 * I / ((n : ℝ) ^ (2 / 3 : ℝ))) * |x|)
      = 8 * Real.pi ^ 2 * I * |x| *
          (Real.sqrt (n : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ))) := by ring
  have hub : ((n : ℝ) ^ (1 / 6 : ℝ)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hnpos _)
  rw [h2, sqrt_div_rpow_two_thirds hn]
  field_simp [hub]

/-- For positive `n`, the expression `2 * Real.sqrt n * |rescaledEnergy2 x n|` equals `4 *
Real.pi * |x| * Real.log n / Real.sqrt n`, the dimension-two rescaled expression in
[ChildsGoldstone2004]. -/
theorem amplitude_bound_d2 {x : ℝ} {n : ℕ} (hn : 0 < n) :
    2 * Real.sqrt (n : ℝ) * |rescaledEnergy2 x n|
      = 4 * Real.pi * |x| * Real.log (n : ℝ) / Real.sqrt (n : ℝ) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnpos)
  simp only [rescaledEnergy2]
  have hcoef : (0:ℝ) ≤ 2 * Real.pi * Real.log (n : ℝ) / (n : ℝ) := by
    have hlog : (0:ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    positivity
  have h1 : |2 * Real.pi * Real.log (n : ℝ) / (n : ℝ) * x|
      = (2 * Real.pi * Real.log (n : ℝ) / (n : ℝ)) * |x| := by
    rw [show 2 * Real.pi * Real.log (n : ℝ) / (n : ℝ) * x
        = (2 * Real.pi * Real.log (n : ℝ) / (n : ℝ)) * x by rfl]
    rw [abs_mul, abs_of_nonneg hcoef]
  rw [h1]
  field_simp [hsqrt]
  rw [Real.sq_sqrt hnpos.le]
  ring

/-- For positive `N`, `I`, and `A` and nonzero `x`, the stated lower bound on `t` and
dimension-three upper bound on `A` imply `N ^ (2 / 3 : ℝ) / (8 * Real.pi ^ 2 * I * |x|) ≤ t
/ A ^ 2` [ChildsGoldstone2004]. -/
theorem repetition_time_ge_d3 {N I x A t : ℝ} (hN : 0 < N) (hI : 0 < I) (hx : x ≠ 0)
    (hA : 0 < A) (htA : Real.sqrt N * A ≤ t)
    (hAupper : A ≤ 8 * Real.pi ^ 2 * I * |x| / N ^ (1 / 6 : ℝ)) :
    N ^ (2 / 3 : ℝ) / (8 * Real.pi ^ 2 * I * |x|) ≤ t / A ^ 2 := by
  have hc : (0:ℝ) < 8 * Real.pi ^ 2 * I * |x| := by
    have habs : (0:ℝ) < |x| := abs_pos.mpr hx
    positivity
  have hsqrt : (0:ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hA2 : (0:ℝ) < A ^ 2 := by positivity
  have h1 : Real.sqrt N * A / A ^ 2 ≤ t / A ^ 2 :=
    div_le_div_of_nonneg_right htA (le_of_lt hA2)
  have h2 : Real.sqrt N * A / A ^ 2 = Real.sqrt N / A := by
    field_simp [ne_of_gt hA]
  have h3 : Real.sqrt N / (8 * Real.pi ^ 2 * I * |x| / N ^ (1 / 6 : ℝ))
      ≤ Real.sqrt N / A :=
    div_le_div_of_nonneg_left hsqrt.le hA hAupper
  have h4 : Real.sqrt N / (8 * Real.pi ^ 2 * I * |x| / N ^ (1 / 6 : ℝ))
      = Real.sqrt N * N ^ (1 / 6 : ℝ) / (8 * Real.pi ^ 2 * I * |x|) := by
    field_simp [ne_of_gt hc, ne_of_gt (Real.rpow_pos_of_pos hN _)]
  have h5 : Real.sqrt N * N ^ (1 / 6 : ℝ) / (8 * Real.pi ^ 2 * I * |x|)
      = N ^ (2 / 3 : ℝ) / (8 * Real.pi ^ 2 * I * |x|) := by
    rw [show Real.sqrt N * N ^ (1 / 6 : ℝ) = N ^ (2 / 3 : ℝ) by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN]
      norm_num]
  calc N ^ (2 / 3 : ℝ) / (8 * Real.pi ^ 2 * I * |x|)
      = Real.sqrt N * N ^ (1 / 6 : ℝ) / (8 * Real.pi ^ 2 * I * |x|) := h5.symm
    _ = Real.sqrt N / (8 * Real.pi ^ 2 * I * |x| / N ^ (1 / 6 : ℝ)) := h4.symm
    _ ≤ Real.sqrt N / A := h3
    _ = Real.sqrt N * A / A ^ 2 := h2.symm
    _ ≤ t / A ^ 2 := h1

/-- For positive `N`, `Real.log N`, and `A` and nonzero `x`, the stated lower bound on `t` and
dimension-two upper bound on `A` imply `N / (4 * Real.pi * |x| * Real.log N) ≤ t / A ^ 2`
[ChildsGoldstone2004]. -/
theorem repetition_time_ge_d2 {N x A t : ℝ} (hN : 0 < N) (hx : x ≠ 0)
    (hlog : 0 < Real.log N) (hA : 0 < A) (htA : Real.sqrt N * A ≤ t)
    (hAupper : A ≤ 4 * Real.pi * |x| * Real.log N / Real.sqrt N) :
    N / (4 * Real.pi * |x| * Real.log N) ≤ t / A ^ 2 := by
  have habs : (0:ℝ) < |x| := abs_pos.mpr hx
  have hc : (0:ℝ) < 4 * Real.pi * |x| * Real.log N := by positivity
  have hsqrt : (0:ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hA2 : (0:ℝ) < A ^ 2 := by positivity
  have h1 : Real.sqrt N * A / A ^ 2 ≤ t / A ^ 2 :=
    div_le_div_of_nonneg_right htA (le_of_lt hA2)
  have h2 : Real.sqrt N * A / A ^ 2 = Real.sqrt N / A := by
    field_simp [ne_of_gt hA]
  have h3 : Real.sqrt N / (4 * Real.pi * |x| * Real.log N / Real.sqrt N)
      ≤ Real.sqrt N / A :=
    div_le_div_of_nonneg_left hsqrt.le hA hAupper
  have h4 : Real.sqrt N / (4 * Real.pi * |x| * Real.log N / Real.sqrt N)
      = N / (4 * Real.pi * |x| * Real.log N) := by
    field_simp [ne_of_gt hc, ne_of_gt hsqrt, ne_of_gt hlog]
    rw [Real.sq_sqrt hN.le]
  calc N / (4 * Real.pi * |x| * Real.log N)
      = Real.sqrt N / (4 * Real.pi * |x| * Real.log N / Real.sqrt N) := h4.symm
    _ ≤ Real.sqrt N / A := h3
    _ = Real.sqrt N * A / A ^ 2 := h2.symm
    _ ≤ t / A ^ 2 := h1

end Qatlib.Papers.SpatialSearch03.MainResults
