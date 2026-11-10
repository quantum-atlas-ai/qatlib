/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GibbsMetropolis.RationalBath.RationalBoltzmannWeights
set_option warningAsError false

open Qatlib.Concepts.FairRandomBits.RationalReject

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer

open Qatlib
open scoped BigOperators

def commonDen {N : ℕ} (q : Fin N → ℚ) : ℕ := ∏ i, (q i).den

def intWeights {N : ℕ} (q : Fin N → ℚ) (i : Fin N) : ℕ :=
  (q i).num.toNat * (commonDen q / (q i).den)

theorem commonDen_pos {N : ℕ} (q : Fin N → ℚ) : 0 < commonDen q :=
  Finset.prod_pos fun i _ => Rat.den_pos (q i)

theorem intWeights_cast {N : ℕ} (q : Fin N → ℚ)
    (hq : ∀ i, 0 ≤ q i) (i : Fin N) :
    (intWeights q i : ℝ) = (commonDen q : ℝ) * (q i : ℝ) := by
  have hn : 0 ≤ (q i).num := Rat.num_nonneg.mpr (hq i)
  have hd : (q i).den ∣ commonDen q :=
    Finset.dvd_prod_of_mem (fun j => (q j).den) (Finset.mem_univ i)
  have hm : (commonDen q / (q i).den) * (q i).den = commonDen q :=
    Nat.div_mul_cancel hd
  have hmr : (commonDen q / (q i).den : ℕ) =
      (commonDen q : ℝ) / ((q i).den : ℝ) := by
    apply (eq_div_iff (by positivity : ((q i).den : ℝ) ≠ 0)).2
    exact_mod_cast hm
  simp only [intWeights, Nat.cast_mul]
  rw [hmr, show ((q i).num.toNat : ℝ) = ((q i).num : ℝ) by
    exact_mod_cast Int.toNat_of_nonneg hn]
  rw [Rat.cast_def]
  ring

theorem intWeights_normalization {N : ℕ} (q : Fin N → ℚ)
    (hq : ∀ i, 0 ≤ q i) (hSum : 0 < ∑ i, (q i : ℝ)) :
    0 < weightTotal (intWeights q) ∧
    ∀ i, (intWeights q i : ℝ) / (weightTotal (intWeights q) : ℝ) =
      (q i : ℝ) / (∑ j, (q j : ℝ)) := by
  have hc := intWeights_cast q hq
  have hD : (0 : ℝ) < commonDen q := by exact_mod_cast commonDen_pos q
  have ht : (weightTotal (intWeights q) : ℝ) =
      (commonDen q : ℝ) * (∑ j, (q j : ℝ)) := by
    simp only [weightTotal, Nat.cast_sum, hc, Finset.mul_sum]
  constructor
  · have : (0 : ℝ) < weightTotal (intWeights q) := by
      rw [ht]; exact mul_pos hD hSum
    exact_mod_cast this
  · intro i
    rw [hc i, ht, mul_div_mul_left _ _ (ne_of_gt hD)]

def blockWidth {N : ℕ} (w : Fin N → ℕ) : ℕ := Nat.log 2 (weightTotal w) + 1

theorem blockWidth_capacity {N : ℕ} (w : Fin N → ℕ) :
    weightTotal w ≤ 2 ^ blockWidth w := by
  exact (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (weightTotal w)).le

theorem normalized_l1_bound {N : ℕ} (u v : Fin N → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hU : 0 < ∑ i, u i) (hV : 0 < ∑ i, v i) :
    (∑ i, |u i / (∑ j, u j) - v i / (∑ j, v j)|) ≤
      2 * (∑ i, |u i - v i|) / (∑ j, v j) := by
  let U := ∑ i, u i
  let V := ∑ i, v i
  let E := ∑ i, |u i - v i|
  have hUp : 0 < U := hU
  have hVp : 0 < V := hV
  have hdiff : |V - U| ≤ E := by
    change |(∑ i, v i) - (∑ i, u i)| ≤ ∑ i, |u i - v i|
    rw [← Finset.sum_sub_distrib]
    simpa only [abs_sub_comm] using
      (Finset.abs_sum_le_sum_abs (fun i : Fin N => v i - u i) Finset.univ)
  have hcoord (i : Fin N) : |u i / U - v i / V| ≤
      |u i - v i| / V + (u i / U) * (|V - U| / V) := by
    have heq : u i / U - v i / V =
        (u i - v i) / V + (u i / U) * ((V - U) / V) := by
      field_simp [ne_of_gt hUp, ne_of_gt hVp]
      ring
    rw [heq]
    calc
      _ ≤ |(u i - v i) / V| + |(u i / U) * ((V - U) / V)| := abs_add_le _ _
      _ = _ := by
        rw [abs_mul, abs_div, abs_div, abs_div,
          abs_of_pos hUp, abs_of_pos hVp, abs_of_nonneg (hu i)]
  calc
    _ ≤ ∑ i, (|u i - v i| / V + (u i / U) * (|V - U| / V)) :=
      Finset.sum_le_sum fun i _ => hcoord i
    _ = E / V + |V - U| / V := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul, ← Finset.sum_div]
      change E / V + (U / U) * (|V - U| / V) = _
      rw [div_self (ne_of_gt hUp), one_mul]
    _ ≤ E / V + E / V := add_le_add_right
      (div_le_div_of_nonneg_right hdiff hVp.le) _
    _ = 2 * E / V := by ring

theorem mixture_weight_l1 {N M : ℕ} (u v : Fin N → ℝ)
    (q : Fin N → Fin M → ℝ) (hq : ∀ t i, 0 ≤ q t i)
    (hs : ∀ t, ∑ i, q t i = 1) :
    (∑ i, |(∑ t, u t * q t i) - (∑ t, v t * q t i)|) ≤
      ∑ t, |u t - v t| := by
  calc
    _ = ∑ i, |∑ t, (u t - v t) * q t i| := by
      congr 1; funext i
      rw [← Finset.sum_sub_distrib]
      simp only [sub_mul]
    _ ≤ ∑ i, ∑ t, |u t - v t| * q t i := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [abs_mul, abs_of_nonneg (hq _ _)] using
        (Finset.abs_sum_le_sum_abs (fun t => (u t - v t) * q t i) Finset.univ)
    _ = ∑ t, |u t - v t| := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hs, mul_one]

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
