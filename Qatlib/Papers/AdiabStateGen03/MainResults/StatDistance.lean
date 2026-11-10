/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
noncomputable section

open Finset
open scoped BigOperators

namespace Qatlib.Papers.AdiabStateGen03.MainResults.StatDistance

variable {ι : Type*} [Fintype ι]

lemma min_le_sqrt_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min a b ≤ Real.sqrt (a * b) := by
  have h0 : 0 ≤ min a b := le_min ha hb
  have h1 : min a b ≤ a := min_le_left _ _
  have h2 : min a b ≤ b := min_le_right _ _
  have hs : (min a b) ^ 2 ≤ a * b := by nlinarith
  exact Real.le_sqrt_of_sq_le hs

lemma min_eq_half (a b : ℝ) : min a b = (a + b - |b - a|) / 2 := by
  have h := inf_eq_half_smul_add_sub_abs_sub' ℝ (M := ℝ) a b
  rw [div_eq_inv_mul]
  simpa [min_def, smul_eq_mul] using h

theorem one_sub_tv_le_overlap (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    1 - (1 / 2) * ∑ i, |p i - q i| ≤ ∑ i, Real.sqrt (p i * q i) := by
  have hmin : ∀ i, min (p i) (q i) ≤ Real.sqrt (p i * q i) :=
    fun i => min_le_sqrt_mul (hp i) (hq i)
  have hsum_min : ∑ i, min (p i) (q i)
      = (1 / 2) * ((∑ i, p i) + (∑ i, q i) - ∑ i, |p i - q i|) := by
    have hterm : ∀ i, min (p i) (q i) = (p i + q i - |p i - q i|) / 2 := by
      intro i
      have := min_eq_half (p i) (q i)
      rw [this, abs_sub_comm]
    calc ∑ i, min (p i) (q i)
        = ∑ i, (p i + q i - |p i - q i|) / 2 :=
          Finset.sum_congr rfl fun i _ => hterm i
      _ = (1 / 2) * ∑ i, (p i + q i - |p i - q i|) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = (1 / 2) * ((∑ i, p i) + (∑ i, q i) - ∑ i, |p i - q i|) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hstep : ∑ i, min (p i) (q i) ≤ ∑ i, Real.sqrt (p i * q i) :=
    Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hmin i
  rw [hsum_min, hp1, hq1] at hstep
  linarith

theorem overlap_le_one (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    ∑ i, Real.sqrt (p i * q i) ≤ 1 := by
  have hptw : ∀ i, Real.sqrt (p i * q i) ^ 2 = p i * q i := by
    intro i
    rw [Real.sq_sqrt (mul_nonneg (hp i) (hq i))]
  have hcs : (∑ i, Real.sqrt (p i * q i)) ^ 2 ≤ (∑ i, p i) * (∑ i, q i) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
      (f := fun i => Real.sqrt (p i)) (g := fun i => Real.sqrt (q i))
    calc (∑ i, Real.sqrt (p i * q i)) ^ 2
        = (∑ i, Real.sqrt (p i) * Real.sqrt (q i)) ^ 2 := by
          congr 1
          exact Finset.sum_congr rfl fun i _ => (Real.sqrt_mul (hp i) (q i))
      _ ≤ (∑ i, Real.sqrt (p i) ^ 2) * (∑ i, Real.sqrt (q i) ^ 2) := this
      _ = (∑ i, p i) * (∑ i, q i) := by
          rw [Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hp i)),
              Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hq i))]
  have hnn : 0 ≤ ∑ i, Real.sqrt (p i * q i) :=
    Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  nlinarith [hp1, hq1, hcs, hnn]

theorem sum_sq_sub_sqrt (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    ∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2
      = 2 * (1 - ∑ i, Real.sqrt (p i * q i)) := by
  have hterm : ∀ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2
      = p i + q i - 2 * Real.sqrt (p i * q i) := by
    intro i
    have hs : Real.sqrt (p i) * Real.sqrt (q i) = Real.sqrt (p i * q i) :=
      (Real.sqrt_mul (hp i) (q i)).symm
    calc (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2
        = Real.sqrt (p i) ^ 2 - 2 * (Real.sqrt (p i) * Real.sqrt (q i))
            + Real.sqrt (q i) ^ 2 := by ring
      _ = p i + q i - 2 * Real.sqrt (p i * q i) := by
          rw [hs, Real.sq_sqrt (hp i), Real.sq_sqrt (hq i)]
          ring
  calc ∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2
      = ∑ i, (p i + q i - 2 * Real.sqrt (p i * q i)) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = 2 * (1 - ∑ i, Real.sqrt (p i * q i)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
            hp1, hq1]
        ring

theorem sum_sq_add_sqrt (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    ∑ i, (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2
      = 2 + 2 * ∑ i, Real.sqrt (p i * q i) := by
  have hterm : ∀ i, (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2
      = p i + q i + 2 * Real.sqrt (p i * q i) := by
    intro i
    have hs : Real.sqrt (p i) * Real.sqrt (q i) = Real.sqrt (p i * q i) :=
      (Real.sqrt_mul (hp i) (q i)).symm
    calc (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2
        = Real.sqrt (p i) ^ 2 + 2 * (Real.sqrt (p i) * Real.sqrt (q i))
            + Real.sqrt (q i) ^ 2 := by ring
      _ = p i + q i + 2 * Real.sqrt (p i * q i) := by
          rw [hs, Real.sq_sqrt (hp i), Real.sq_sqrt (hq i)]
          ring
  calc ∑ i, (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2
      = ∑ i, (p i + q i + 2 * Real.sqrt (p i * q i)) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = 2 + 2 * ∑ i, Real.sqrt (p i * q i) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hp1, hq1]
        ring

theorem tv_le_sqrt_sum_sq_sub_sqrt (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    (1 / 2) * ∑ i, |p i - q i|
      ≤ Real.sqrt (∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2) := by

  have hterm : ∀ i, |p i - q i|
      = |Real.sqrt (p i) - Real.sqrt (q i)| * (Real.sqrt (p i) + Real.sqrt (q i)) := by
    intro i
    have hpq : p i - q i
        = (Real.sqrt (p i) - Real.sqrt (q i)) * (Real.sqrt (p i) + Real.sqrt (q i)) := by
      have hp' : Real.sqrt (p i) ^ 2 = p i := Real.sq_sqrt (hp i)
      have hq' : Real.sqrt (q i) ^ 2 = q i := Real.sq_sqrt (hq i)
      nlinarith [hp', hq']
    rw [hpq, abs_mul]
    have hnn : 0 ≤ Real.sqrt (p i) + Real.sqrt (q i) := by positivity
    rw [abs_of_nonneg hnn]

  have hcs : (∑ i, |p i - q i|) ^ 2
      ≤ (∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2)
        * (∑ i, (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
      (f := fun i => |Real.sqrt (p i) - Real.sqrt (q i)|)
      (g := fun i => Real.sqrt (p i) + Real.sqrt (q i))
    calc (∑ i, |p i - q i|) ^ 2
        = (∑ i, |Real.sqrt (p i) - Real.sqrt (q i)|
            * (Real.sqrt (p i) + Real.sqrt (q i))) ^ 2 := by
          congr 1
          exact Finset.sum_congr rfl fun i _ => hterm i
      _ ≤ (∑ i, |Real.sqrt (p i) - Real.sqrt (q i)| ^ 2)
            * (∑ i, (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2) := this
      _ = (∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2)
            * (∑ i, (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2) := by
          rw [Finset.sum_congr rfl (fun i _ => sq_abs (Real.sqrt (p i) - Real.sqrt (q i)))]

  have hsum2 : ∑ i, (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2 ≤ 4 := by
    rw [sum_sq_add_sqrt p q hp hq hp1 hq1]
    have hov := overlap_le_one p q hp hq hp1 hq1
    nlinarith
  have hnn1 : 0 ≤ ∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have htv : 0 ≤ ∑ i, |p i - q i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hsq : (∑ i, |p i - q i|) ^ 2
      ≤ 4 * (∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2) := by
    have := hcs
    nlinarith
  have hmain : ∑ i, |p i - q i|
      ≤ 2 * Real.sqrt (∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2) := by
    have h2 : Real.sqrt ((∑ i, |p i - q i|) ^ 2)
        ≤ Real.sqrt (4 * (∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2)) :=
      Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq htv, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)] at h2
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h4] at h2
    exact h2
  linarith

end Qatlib.Papers.AdiabStateGen03.MainResults.StatDistance
