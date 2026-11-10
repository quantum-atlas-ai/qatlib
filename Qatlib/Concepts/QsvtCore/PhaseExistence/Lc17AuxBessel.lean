/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17Support
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.CauSeqFilter
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

open NormedSpace

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

private noncomputable def lcW (k : ℕ) : ℝ :=
  ∫ x in 0..Real.pi, Real.sin x ^ (2 * k)

private lemma lcW_pos (k : ℕ) : 0 < lcW k :=
  integral_sin_pow_pos (2 * k)

private noncomputable def lcWMix (k m : ℕ) : ℝ :=
  ∫ x in 0..Real.pi, Real.sin x ^ (2 * k) * Real.cos x ^ (2 * m)

private theorem div_pow_real (a b : ℝ) (n : ℕ) : (a / b) ^ n = a ^ n / b ^ n := by
  rw [div_eq_mul_inv, mul_pow, inv_pow, div_eq_mul_inv]

private theorem lcWMix_rec (k m : ℕ) :
    lcWMix k (m + 1) = (2 * m + 1) / (2 * (m + k + 1)) * lcWMix k m := by
  classical
  have hmix : ∀ x : ℝ, Real.cos x ^ (2 * m) * Real.sin x ^ (2 * k + 2)
      = Real.sin x ^ (2 * k) * Real.cos x ^ (2 * m)
        - Real.sin x ^ (2 * k) * Real.cos x ^ (2 * m + 2) := by
    intro x
    have h2 : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
      have h := Real.sin_sq_add_cos_sq x
      linarith
    rw [pow_add (Real.sin x) (2 * k) 2, pow_add (Real.cos x) (2 * m) 2, h2]
    ring
  have hcu : Continuous fun x : ℝ => Real.cos x ^ (2 * m + 1) := by fun_prop
  have hcv : Continuous fun x : ℝ => Real.sin x ^ (2 * k + 1)
      * (((2 * k + 1 : ℕ) : ℝ)⁻¹) := by fun_prop
  have hcu' : Continuous fun x : ℝ => ((2 * m + 1 : ℕ) : ℝ)
      * Real.cos x ^ (2 * m) * (-(Real.sin x)) := by fun_prop
  have hcv' : Continuous fun x : ℝ =>
      ((2 * k + 1 : ℕ) : ℝ) * Real.sin x ^ (2 * k) * Real.cos x
        * (((2 * k + 1 : ℕ) : ℝ)⁻¹) := by fun_prop
  have hu : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Real.cos x ^ (2 * m + 1))
      (((2 * m + 1 : ℕ) : ℝ) * Real.cos x ^ (2 * m) * (-(Real.sin x))) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => Real.cos x) (-(Real.sin x)) x := Real.hasDerivAt_cos x
    have h2 := (h1.pow (2 * m + 1))
    simpa [Nat.succ_sub_one] using! h2
  have hv : ∀ x : ℝ, HasDerivAt
      (fun x : ℝ => Real.sin x ^ (2 * k + 1) * (((2 * k + 1 : ℕ) : ℝ)⁻¹))
      (((2 * k + 1 : ℕ) : ℝ) * Real.sin x ^ (2 * k) * Real.cos x
        * (((2 * k + 1 : ℕ) : ℝ)⁻¹)) x := fun x =>
    (((Real.hasDerivAt_sin x).pow (2 * k + 1)).mul_const
      (((2 * k + 1 : ℕ) : ℝ)⁻¹)).congr_deriv
      (by rw [Nat.succ_sub_one])
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    (u := fun x => Real.cos x ^ (2 * m + 1))
    (v := fun x => Real.sin x ^ (2 * k + 1) * (((2 * k + 1 : ℕ) : ℝ)⁻¹))
    (u' := fun x => ((2 * m + 1 : ℕ) : ℝ) * Real.cos x ^ (2 * m) * (-(Real.sin x)))
    (v' := fun x => ((2 * k + 1 : ℕ) : ℝ) * Real.sin x ^ (2 * k) * Real.cos x
      * (((2 * k + 1 : ℕ) : ℝ)⁻¹))
    (a := 0) (b := Real.pi)
    hcu.continuousOn hcv.continuousOn
    (fun x _ => hu x) (fun x _ => hv x)
    (hcu'.intervalIntegrable 0 Real.pi) (hcv'.intervalIntegrable 0 Real.pi)
  have hb : Real.cos Real.pi ^ (2 * m + 1)
      * (Real.sin Real.pi ^ (2 * k + 1) * (((2 * k + 1 : ℕ) : ℝ)⁻¹))
      - Real.cos 0 ^ (2 * m + 1)
      * (Real.sin 0 ^ (2 * k + 1) * (((2 * k + 1 : ℕ) : ℝ)⁻¹)) = 0 := by
    simp
  (try simp only [] at hibp)
  have hcc1 : Continuous (fun x : ℝ => (((2 * m + 1 : ℕ) : ℝ) * Real.cos x ^ (2 * m)
      * (-(Real.sin x))) * (Real.sin x ^ (2 * k + 1) * (((2 * k + 1 : ℕ) : ℝ)⁻¹))) := by fun_prop
  have hcc2 : Continuous (fun x : ℝ => (Real.cos x ^ (2 * m + 1))
      * (((2 * k + 1 : ℕ) : ℝ) * Real.sin x ^ (2 * k) * Real.cos x
      * (((2 * k + 1 : ℕ) : ℝ)⁻¹))) := by fun_prop
  have hii1 : IntervalIntegrable (fun x : ℝ => (((2 * m + 1 : ℕ) : ℝ) * Real.cos x ^ (2 * m)
      * (-(Real.sin x))) * (Real.sin x ^ (2 * k + 1) * (((2 * k + 1 : ℕ) : ℝ)⁻¹)))
      MeasureTheory.volume 0 Real.pi := hcc1.intervalIntegrable 0 Real.pi
  have hii2 : IntervalIntegrable (fun x : ℝ => (Real.cos x ^ (2 * m + 1))
      * (((2 * k + 1 : ℕ) : ℝ) * Real.sin x ^ (2 * k) * Real.cos x
      * (((2 * k + 1 : ℕ) : ℝ)⁻¹))) MeasureTheory.volume 0 Real.pi :=
    hcc2.intervalIntegrable 0 Real.pi
  rw [intervalIntegral.integral_add hii1 hii2, hb] at hibp
  have hsecond : ∫ x in 0..Real.pi, Real.cos x ^ (2 * m + 1)
      * (((2 * k + 1 : ℕ) : ℝ) * Real.sin x ^ (2 * k) * Real.cos x
        * (((2 * k + 1 : ℕ) : ℝ)⁻¹)) = lcWMix k (m + 1) := by
    rw [lcWMix]
    refine intervalIntegral.integral_congr fun x _ => ?_
    have hkk : ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [pow_add (Real.cos x) (2 * m) 1,
      show (2 * (m + 1)) = 2 * m + 2 from by ring, pow_add (Real.cos x) (2 * m) 2]
    field_simp
  rw [hsecond] at hibp
  have hfirst : ∫ x in 0..Real.pi, (((2 * m + 1 : ℕ) : ℝ) * Real.cos x ^ (2 * m) * (-(Real.sin x)))
      * (Real.sin x ^ (2 * k + 1) * (((2 * k + 1 : ℕ) : ℝ)⁻¹))
      = -(((2 * m + 1 : ℕ) : ℝ) / ((2 * k + 1 : ℕ) : ℝ)) * (lcWMix k m - lcWMix k (m + 1)) := by
    have hEq : ∫ x in 0..Real.pi, (((2 * m + 1 : ℕ) : ℝ) * Real.cos x ^ (2 * m) * (-(Real.sin x)))
        * (Real.sin x ^ (2 * k + 1) * (((2 * k + 1 : ℕ) : ℝ)⁻¹))
        = ∫ x in 0..Real.pi, (-(((2 * m + 1 : ℕ) : ℝ) / ((2 * k + 1 : ℕ) : ℝ))
          * (Real.cos x ^ (2 * m) * Real.sin x ^ (2 * k + 2))) :=
      intervalIntegral.integral_congr fun x _ => by
        have hkk : ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := by
          positivity
        rw [pow_add (Real.sin x) (2 * k) 1, pow_one,
          pow_add (Real.sin x) (2 * k) 2]
        field_simp
        try ring
    rw [hEq, intervalIntegral.integral_const_mul]
    have hEq2 : ∫ x in 0..Real.pi, Real.cos x ^ (2 * m) * Real.sin x ^ (2 * k + 2)
        = lcWMix k m - lcWMix k (m + 1) := by
      have hci1 : Continuous fun x : ℝ => Real.sin x ^ (2 * k) * Real.cos x ^ (2 * m) := by
        fun_prop
      have hci2 : Continuous fun x : ℝ =>
          Real.sin x ^ (2 * k) * Real.cos x ^ (2 * (m + 1)) := by fun_prop
      have ii1 : IntervalIntegrable
          (fun x : ℝ => Real.sin x ^ (2 * k) * Real.cos x ^ (2 * m))
          MeasureTheory.volume 0 Real.pi := hci1.intervalIntegrable _ _
      have ii2 : IntervalIntegrable
          (fun x : ℝ => Real.sin x ^ (2 * k) * Real.cos x ^ (2 * (m + 1)))
          MeasureTheory.volume 0 Real.pi := hci2.intervalIntegrable _ _
      simp only [lcWMix]
      have hsub : ∫ x in 0..Real.pi,
          (Real.sin x ^ (2 * k) * Real.cos x ^ (2 * m))
            - (Real.sin x ^ (2 * k) * Real.cos x ^ (2 * (m + 1)))
          = (∫ x in 0..Real.pi, Real.sin x ^ (2 * k) * Real.cos x ^ (2 * m))
            - (∫ x in 0..Real.pi, Real.sin x ^ (2 * k) * Real.cos x ^ (2 * (m + 1))) :=
        intervalIntegral.integral_sub ii1 ii2
      rw [← hsub]
      refine intervalIntegral.integral_congr fun x _ => ?_
      exact hmix x
    rw [hEq2, lcWMix, lcWMix]
  rw [hfirst] at hibp
  have hden : ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hden' : ((2 : ℝ) * (m + k + 1)) ≠ 0 := by positivity
  field_simp at hibp ⊢
  push_cast at hibp ⊢
  linarith

private theorem lcWMix_eq (k m : ℕ) :
    lcWMix k m = lcW k * (2 * m).factorial * k.factorial
      / (4 ^ m * m.factorial * (k + m).factorial) := by
  induction m with
  | zero =>
      have h0 : lcWMix k 0 = lcW k := by
        rw [lcWMix, lcW]
        refine intervalIntegral.integral_congr fun x _ => ?_
        simp
      rw [h0, Nat.add_zero]
      have hk : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
  | succ m ih =>
      have hfact1 : (((2 * (m + 1)).factorial : ℕ) : ℝ)
          = (2 * m + 2) * ((2 * m + 1) * (((2 * m).factorial : ℕ) : ℝ)) := by
        have e1 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
        rw [e1, Nat.factorial_succ, Nat.factorial_succ]
        push_cast
        ring
      have hfact2 : (((m + 1).factorial : ℕ) : ℝ)
          = (m + 1) * (((m.factorial : ℕ) : ℝ)) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hfact3 : (((k + (m + 1)).factorial : ℕ) : ℝ)
          = (k + m + 1) * (((k + m).factorial : ℕ) : ℝ) := by
        rw [show k + (m + 1) = (k + m) + 1 from by ring, Nat.factorial_succ]
        push_cast
        ring
      have hpos : (0 : ℝ) < 4 ^ m * ((m.factorial : ℕ) : ℝ) * ((k + m).factorial : ℕ) := by
        positivity
      have hpos' : (0 : ℝ) < 2 * ((m + k + 1 : ℕ) : ℝ) := by positivity
      have hpos'' : (0 : ℝ) < ((k + m + 1 : ℕ) : ℝ) := by positivity
      rw [lcWMix_rec, ih]
      rw [hfact1, hfact2, hfact3, pow_succ (4 : ℝ) m]
      have h4 : (0 : ℝ) < 4 * (4 ^ m * ((m.factorial : ℕ) : ℝ) * ((k + m).factorial : ℕ)) := by
        positivity
      have h2 : ((m + 1) * ((m.factorial : ℕ) : ℝ)) ≠ 0 := by positivity
      have h3 : ((k + m + 1) * (((k + m).factorial : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp
      ring

private noncomputable def lcSseries (k : ℕ) (τ : ℝ) : ℕ → ℝ :=
  fun j => (-1 : ℝ) ^ j * (τ ^ 2 / 4) ^ j / (((j.factorial : ℕ) : ℝ) * ((k + j).factorial : ℕ))

private theorem lcSseries_summable (k : ℕ) (τ : ℝ) : Summable (lcSseries k τ) := by
  have hle : ∀ j, |lcSseries k τ j| ≤ (τ ^ 2 / 4) ^ j / ((j.factorial : ℕ) : ℝ) := by
    intro j
    have h1 : ((k + j).factorial : ℕ) ≥ (j.factorial : ℕ) := Nat.factorial_le (by omega)
    have h1' : (((k + j).factorial : ℕ) : ℝ) ≥ ((j.factorial : ℕ) : ℝ) := by
      exact_mod_cast h1
    have h2 : (0 : ℝ) < ((j.factorial : ℕ) : ℝ) * ((k + j).factorial : ℕ) := by
      have e1 : (0 : ℝ) < ((j.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos j
      have e2 : (0 : ℝ) < (((k + j).factorial : ℕ) : ℝ) := by
        exact_mod_cast Nat.factorial_pos (k + j)
      positivity
    have h3 : |lcSseries k τ j|
        = (τ ^ 2 / 4) ^ j / (((j.factorial : ℕ) : ℝ) * ((k + j).factorial : ℕ)) := by
      rw [lcSseries, abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        abs_of_nonneg (show (0 : ℝ) ≤ (τ ^ 2 / 4) ^ j by positivity),
        abs_of_nonneg (show (0 : ℝ) ≤ ((j.factorial : ℕ) : ℝ) by positivity),
        abs_of_nonneg (show (0 : ℝ) ≤ (((k + j).factorial : ℕ) : ℝ) by positivity),
        one_mul]
    rw [h3, div_le_div_iff₀ h2 (show (0 : ℝ) < ((j.factorial : ℕ) : ℝ) by positivity)]
    have hc0 : (0 : ℝ) ≤ (τ ^ 2 / 4) ^ j := by positivity
    have hj1 : (1 : ℝ) ≤ ((j.factorial : ℕ) : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero j))
    have h4 : ((τ : ℝ) ^ 2 / 4) ^ j * ((j.factorial : ℕ) : ℝ)
        ≤ ((τ : ℝ) ^ 2 / 4) ^ j * ((k + j).factorial : ℕ) :=
      mul_le_mul_of_nonneg_left h1' hc0
    have h5 : ((j.factorial : ℕ) : ℝ) * ((k + j).factorial : ℕ)
        ≥ ((k + j).factorial : ℕ) := by
      nlinarith [hj1]
    have h6 : ((τ : ℝ) ^ 2 / 4) ^ j * (((j.factorial : ℕ) : ℝ) * ((k + j).factorial : ℕ))
        ≥ ((τ : ℝ) ^ 2 / 4) ^ j * ((k + j).factorial : ℕ) :=
      mul_le_mul_of_nonneg_left h5 hc0
    linarith
  refine Summable.of_norm_bounded
    (g := fun j => (τ ^ 2 / 4) ^ j / ((j.factorial : ℕ) : ℝ))
    (Real.summable_pow_div_factorial (τ ^ 2 / 4)) hle

private theorem lcBesselJ_eq_tsum (k : ℕ) (τ : ℝ) :
    lcBesselJ k τ = (τ / 2) ^ k * ∑' j, lcSseries k τ j := by
  have hs : HasSum (lcSseries k τ) (∑' j, lcSseries k τ j) :=
    (lcSseries_summable k τ).hasSum
  have hfun : (fun j => (τ / 2) ^ k * lcSseries k τ j)
      = fun j => (-1 : ℝ) ^ j * (τ / 2) ^ (2 * j + k)
          / (((j.factorial : ℕ) : ℝ) * ((j + k).factorial : ℝ)) := by
    funext j
    have e0 : (τ / 2) ^ 2 = τ ^ 2 / 4 := by
      field_simp
      ring
    have e1 : (τ / 2) ^ (2 * j + k) = (τ / 2) ^ k * (τ ^ 2 / 4) ^ j := by
      rw [pow_add, pow_mul, e0]
      ring
    rw [lcSseries, e1, Nat.add_comm k j]
    field_simp
  have h2 := hs.mul_left ((τ / 2) ^ k)
  rw [lcBesselJ, ← h2.tsum_eq, ← hfun]

private theorem lcSinPowCosEq (k : ℕ) (τ : ℝ) :
    ∫ x in 0..Real.pi, Real.sin x ^ (2 * k) * Real.cos (τ * Real.cos x)
      = lcW k * ((k.factorial : ℕ) : ℝ) * ∑' m, lcSseries k τ m := by
  classical

  have hint : ∀ n : ℕ, ∫ x in 0..Real.pi, (Real.sin x ^ (2 * k)
      * ∑ m ∈ Finset.range n, (-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m)
          / (((2 * m).factorial : ℕ) : ℝ))
      = lcW k * ((k.factorial : ℕ) : ℝ) * (∑ m ∈ Finset.range n, lcSseries k τ m) := by
    intro n
    have hE : ∀ x : ℝ, (Real.sin x ^ (2 * k)
        * ∑ m ∈ Finset.range n, (-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m)
          / (((2 * m).factorial : ℕ) : ℝ))
        = ∑ m ∈ Finset.range n, (Real.sin x ^ (2 * k)
          * ((-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m)
            / (((2 * m).factorial : ℕ) : ℝ))) :=
      fun x => Finset.mul_sum _ _ _
    have hcongE : ∫ x in 0..Real.pi, (Real.sin x ^ (2 * k)
        * ∑ m ∈ Finset.range n, (-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m)
          / (((2 * m).factorial : ℕ) : ℝ))
        = ∫ x in 0..Real.pi, ∑ m ∈ Finset.range n, (Real.sin x ^ (2 * k)
          * ((-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m)
            / (((2 * m).factorial : ℕ) : ℝ))) :=
      intervalIntegral.integral_congr (a := 0) (b := Real.pi) (f := fun x => Real.sin x ^ (2 * k)
        * ∑ m ∈ Finset.range n, (-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m)
          / (((2 * m).factorial : ℕ) : ℝ))
        (g := fun x => ∑ m ∈ Finset.range n, (Real.sin x ^ (2 * k)
          * ((-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m)
            / (((2 * m).factorial : ℕ) : ℝ))))
        (fun x _ => hE x)
    have hfin : ∀ m ∈ Finset.range n, IntervalIntegrable
        (fun x : ℝ => Real.sin x ^ (2 * k) * ((-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m)
          / (((2 * m).factorial : ℕ) : ℝ))) MeasureTheory.volume 0 Real.pi := by
      intro m _
      have hc' : Continuous fun x : ℝ => Real.sin x ^ (2 * k)
          * ((-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m)
          / (((2 * m).factorial : ℕ) : ℝ)) := by fun_prop
      exact hc'.intervalIntegrable 0 Real.pi
    have hswapn : ∫ x in 0..Real.pi, ∑ m ∈ Finset.range n, (Real.sin x ^ (2 * k)
        * ((-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m)
          / (((2 * m).factorial : ℕ) : ℝ)))
        = ∑ m ∈ Finset.range n, ∫ x in 0..Real.pi, (Real.sin x ^ (2 * k)
          * ((-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m)
          / (((2 * m).factorial : ℕ) : ℝ))) :=
      intervalIntegral.integral_finsetSum hfin
    rw [hcongE, hswapn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hEqI : ∫ x in 0..Real.pi, (Real.sin x ^ (2 * k)
        * ((-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m)
          / (((2 * m).factorial : ℕ) : ℝ)))
        = ∫ x in 0..Real.pi, ((-1 : ℝ) ^ m * τ ^ (2 * m)
          / (((2 * m).factorial : ℕ) : ℝ))
          * (Real.sin x ^ (2 * k) * Real.cos x ^ (2 * m)) :=
      intervalIntegral.integral_congr (a := 0) (b := Real.pi)
        (f := fun x : ℝ => Real.sin x ^ (2 * k)
          * ((-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m)
            / (((2 * m).factorial : ℕ) : ℝ)))
        (g := fun x : ℝ => ((-1 : ℝ) ^ m * τ ^ (2 * m)
          / (((2 * m).factorial : ℕ) : ℝ))
          * (Real.sin x ^ (2 * k) * Real.cos x ^ (2 * m)))
        (fun x _ => by
          show Real.sin x ^ (2 * k) * ((-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m)
              / (((2 * m).factorial : ℕ) : ℝ))
            = ((-1 : ℝ) ^ m * τ ^ (2 * m) / (((2 * m).factorial : ℕ) : ℝ))
              * (Real.sin x ^ (2 * k) * Real.cos x ^ (2 * m))
          have e0 : (τ * Real.cos x) ^ (2 * m)
              = τ ^ (2 * m) * Real.cos x ^ (2 * m) := by
            rw [mul_pow]
          rw [e0]
          ring)
    have hI : ∫ x in 0..Real.pi, Real.sin x ^ (2 * k) * Real.cos x ^ (2 * m)
        = lcWMix k m := rfl
    rw [hEqI, intervalIntegral.integral_const_mul, hI, lcWMix_eq, lcSseries]
    have hsq : (τ : ℝ) ^ (2 * m) = (τ * τ) ^ m := by
      rw [pow_mul, pow_two]
    have hq : (τ ^ 2 / 4) ^ m = (τ * τ) ^ m / (4 : ℝ) ^ m := by
      rw [pow_two, div_pow_real]
    rw [hsq, hq]
    field_simp

  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc 0 Real.pi)
    with hμdef
  have hconv : ∀ f : ℝ → ℝ, ∫ x in 0..Real.pi, f x = ∫ x, f x ∂μ := by
    intro f
    rw [intervalIntegral.integral_of_le Real.pi_pos.le]
    try rfl
  have hinteg : MeasureTheory.Integrable (fun x => Real.sin x ^ (2 * k)) μ := by
    have hcont2 : Continuous fun x : ℝ => Real.sin x ^ (2 * k) := by fun_prop
    have hII : IntervalIntegrable (fun x : ℝ => Real.sin x ^ (2 * k))
        MeasureTheory.volume 0 Real.pi := hcont2.intervalIntegrable 0 Real.pi
    have hIO : MeasureTheory.IntegrableOn (fun x : ℝ => Real.sin x ^ (2 * k))
        (Set.uIoc 0 Real.pi) MeasureTheory.volume := intervalIntegrable_iff.mp hII
    rw [Set.uIoc_of_le Real.pi_pos.le] at hIO
    exact hIO.integrable
  have hintegB : MeasureTheory.Integrable (fun x => Real.sin x ^ (2 * k)
      * Real.exp (τ * τ)) μ := hinteg.mul_const _
  have hbound : ∀ (n : ℕ) (x : ℝ),
      |Real.sin x ^ (2 * k)
        * ∑ m ∈ Finset.range n, (-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m)
          / (((2 * m).factorial : ℕ) : ℝ)|
      ≤ Real.sin x ^ (2 * k) * Real.exp (τ * τ) := by
    intro n x
    have hsin : (0 : ℝ) ≤ Real.sin x ^ (2 * k) := by
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg (Real.sin x)) k
    have hstep1 := Finset.abs_sum_le_sum_abs
      (fun m => (-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m) / (((2 * m).factorial : ℕ) : ℝ))
      (Finset.range n)
    have hstep2 : (∑ m ∈ Finset.range n, |(-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m)
        / (((2 * m).factorial : ℕ) : ℝ)|)
        ≤ ∑ m ∈ Finset.range n, (τ * τ) ^ m / ((m.factorial : ℕ) : ℝ) := by
      refine Finset.sum_le_sum fun m _ => ?_
      have ha : |(-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m) / (((2 * m).factorial : ℕ) : ℝ)|
          = (τ * Real.cos x) ^ (2 * m) / (((2 * m).factorial : ℕ) : ℝ) := by
        have hpn : (0 : ℝ) ≤ (τ * Real.cos x) ^ (2 * m) := by
          rw [pow_mul]
          exact pow_nonneg (sq_nonneg (τ * Real.cos x)) m
        rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
          abs_of_nonneg hpn,
          abs_of_nonneg (Nat.cast_nonneg ((2 * m).factorial)), one_mul]
      rw [ha]
      have hcos : (τ * Real.cos x) ^ (2 * m) ≤ (τ * τ) ^ m := by
        have e0 : (τ * Real.cos x) ^ (2 * m) = (τ * τ) ^ m * Real.cos x ^ (2 * m) := by
          rw [pow_mul (τ * Real.cos x) 2 m, mul_pow, pow_mul]
          ring
        have hnn : (0 : ℝ) ≤ Real.cos x ^ (2 * m) := by
          rw [pow_mul]
          exact pow_nonneg (sq_nonneg _) m
        have habs : Real.cos x ^ (2 * m) = |Real.cos x| ^ (2 * m) := by
          rw [← abs_pow, abs_of_nonneg hnn]
        have e1 : Real.cos x ^ (2 * m) ≤ 1 := by
          rw [habs]
          exact (pow_le_pow_left₀ (abs_nonneg (Real.cos x))
            (Real.abs_cos_le_one x) (2 * m)).trans_eq (one_pow (2 * m))
        rw [e0]
        exact (mul_le_mul_of_nonneg_left e1
          (pow_nonneg (mul_self_nonneg τ) m)).trans_eq (mul_one _)
      have hfact : ((m.factorial : ℕ) : ℝ) ≤ (((2 * m).factorial : ℕ) : ℝ) := by
        exact_mod_cast Nat.factorial_le (by omega)
      have h1 : (0 : ℝ) < (((2 * m).factorial : ℕ) : ℝ) := by
        exact_mod_cast Nat.factorial_pos _
      have h2 : (0 : ℝ) < ((m.factorial : ℕ) : ℝ) := by
        exact_mod_cast Nat.factorial_pos _
      rw [div_le_div_iff₀ h1 h2]
      exact mul_le_mul hcos hfact h2.le (pow_nonneg (mul_self_nonneg τ) m)
    have hstep3 : (∑ m ∈ Finset.range n, (τ * τ) ^ m / ((m.factorial : ℕ) : ℝ))
        ≤ Real.exp (τ * τ) := by
      have hle := Summable.sum_le_tsum (Finset.range n)
        (fun j _ => div_nonneg (pow_nonneg (mul_self_nonneg τ) j)
          (Nat.cast_nonneg _)) (Real.summable_pow_div_factorial (τ * τ))
      have hsum : (∑' j : ℕ, (τ * τ) ^ j / ((j.factorial : ℕ) : ℝ))
          = Real.exp (τ * τ) := by
        rw [Real.exp_eq_exp_ℝ]
        exact (NormedSpace.expSeries_div_hasSum_exp (τ * τ) (𝔸 := ℝ)).tsum_eq
      rw [hsum] at hle
      exact hle
    rw [abs_mul, abs_of_nonneg hsin]
    calc Real.sin x ^ (2 * k)
        * |∑ m ∈ Finset.range n, (-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m)
          / (((2 * m).factorial : ℕ) : ℝ)|
        ≤ Real.sin x ^ (2 * k)
          * ∑ m ∈ Finset.range n, |(-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m)
            / (((2 * m).factorial : ℕ) : ℝ)| :=
          mul_le_mul_of_nonneg_left hstep1 hsin
      _ ≤ Real.sin x ^ (2 * k) * Real.exp (τ * τ) :=
          mul_le_mul_of_nonneg_left (le_trans hstep2 hstep3) hsin

  have hFcont : ∀ (n : ℕ), Continuous fun x : ℝ => Real.sin x ^ (2 * k)
      * ∑ m ∈ Finset.range n, (-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m)
        / (((2 * m).factorial : ℕ) : ℝ) := by
    intro n
    fun_prop
  have hlim : ∀ (x : ℝ), Filter.Tendsto (fun n : ℕ => Real.sin x ^ (2 * k)
      * ∑ m ∈ Finset.range n, (-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m)
        / (((2 * m).factorial : ℕ) : ℝ)) Filter.atTop
      (nhds (Real.sin x ^ (2 * k) * Real.cos (τ * Real.cos x))) :=
    fun x => Filter.Tendsto.mul tendsto_const_nhds
      ((Real.hasSum_cos (τ * Real.cos x)).tendsto_sum_nat)
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    (F := fun n x => Real.sin x ^ (2 * k)
      * ∑ m ∈ Finset.range n, (-1 : ℝ) ^ m * (τ * Real.cos x) ^ (2 * m)
        / (((2 * m).factorial : ℕ) : ℝ))
    (f := fun x => Real.sin x ^ (2 * k) * Real.cos (τ * Real.cos x))
    (bound := fun x => Real.sin x ^ (2 * k) * Real.exp (τ * τ))
    (fun n => (hFcont n).aestronglyMeasurable)
    hintegB
    (fun n => Filter.Eventually.of_forall (hbound n))
    (Filter.Eventually.of_forall hlim)
  simp only [← hconv] at hdct
  have hL : Filter.Tendsto (fun n : ℕ => lcW k * ((k.factorial : ℕ) : ℝ)
      * ∑ m ∈ Finset.range n, lcSseries k τ m) Filter.atTop
      (nhds (∫ x in 0..Real.pi,
        Real.sin x ^ (2 * k) * Real.cos (τ * Real.cos x))) := by
    refine Filter.Tendsto.congr (fun n => hint n) hdct
  have hR : Filter.Tendsto (fun n : ℕ => lcW k * ((k.factorial : ℕ) : ℝ)
      * ∑ m ∈ Finset.range n, lcSseries k τ m) Filter.atTop
      (nhds (lcW k * ((k.factorial : ℕ) : ℝ) * ∑' m, lcSseries k τ m)) :=
    Filter.Tendsto.const_mul _
      ((lcSseries_summable k τ).hasSum.tendsto_sum_nat)
  exact tendsto_nhds_unique hL hR

theorem lcBesselJ_repr (k : ℕ) (τ : ℝ) :
    lcBesselJ k τ * ((k.factorial : ℕ) : ℝ) * lcW k
      = (τ / 2) ^ k * ∫ x in 0..Real.pi,
          Real.sin x ^ (2 * k) * Real.cos (τ * Real.cos x) := by
  rw [lcBesselJ_eq_tsum, lcSinPowCosEq]
  ring

theorem abs_lcBesselJ_le (k : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) :
    |lcBesselJ k τ| ≤ (τ / 2) ^ k / ((k.factorial : ℕ) : ℝ) := by
  have hW := lcW_pos k
  have hrepr := lcBesselJ_repr k τ
  have habs1 : |∫ x in 0..Real.pi,
      Real.sin x ^ (2 * k) * Real.cos (τ * Real.cos x)| ≤ lcW k := by
    have hEq : ∫ x in 0..Real.pi, |Real.sin x ^ (2 * k) * Real.cos (τ * Real.cos x)|
        = ∫ x in 0..Real.pi, Real.sin x ^ (2 * k) * |Real.cos (τ * Real.cos x)| :=
      intervalIntegral.integral_congr (a := 0) (b := Real.pi)
        (f := fun x : ℝ => |Real.sin x ^ (2 * k) * Real.cos (τ * Real.cos x)|)
        (g := fun x : ℝ => Real.sin x ^ (2 * k) * |Real.cos (τ * Real.cos x)|)
        (fun x _ => by
          show |Real.sin x ^ (2 * k) * Real.cos (τ * Real.cos x)|
              = Real.sin x ^ (2 * k) * |Real.cos (τ * Real.cos x)|
          rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ Real.sin x ^ (2 * k) by
            rw [pow_mul]; exact pow_nonneg (sq_nonneg _) k)])
    have h1 : |∫ x in 0..Real.pi,
        Real.sin x ^ (2 * k) * Real.cos (τ * Real.cos x)|
        ≤ ∫ x in 0..Real.pi, |Real.sin x ^ (2 * k) * Real.cos (τ * Real.cos x)| :=
      intervalIntegral.abs_integral_le_integral_abs Real.pi_pos.le
    rw [hEq] at h1
    have hc1 : Continuous fun x : ℝ => Real.sin x ^ (2 * k)
        * |Real.cos (τ * Real.cos x)| := by fun_prop
    have hc2 : Continuous fun x : ℝ => Real.sin x ^ (2 * k) := by fun_prop
    have him1 : IntervalIntegrable (fun x : ℝ => Real.sin x ^ (2 * k)
        * |Real.cos (τ * Real.cos x)|) MeasureTheory.volume 0 Real.pi :=
      hc1.intervalIntegrable 0 Real.pi
    have him2 : IntervalIntegrable (fun x : ℝ => Real.sin x ^ (2 * k))
        MeasureTheory.volume 0 Real.pi := hc2.intervalIntegrable 0 Real.pi
    exact le_trans h1 (intervalIntegral.integral_mono_on Real.pi_pos.le him1 him2
      (fun x _ => by
        have hsn : (0 : ℝ) ≤ Real.sin x ^ (2 * k) := by
          rw [pow_mul]; exact pow_nonneg (sq_nonneg _) k
        have hcn : (0 : ℝ) ≤ |Real.cos (τ * Real.cos x)| := abs_nonneg _
        nlinarith [Real.abs_cos_le_one (τ * Real.cos x)]))
  have hk : (0 : ℝ) < ((k.factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  have hkey : |lcBesselJ k τ * ((k.factorial : ℕ) : ℝ) * lcW k|
      = |lcBesselJ k τ| * ((k.factorial : ℕ) : ℝ) * lcW k := by
    rw [abs_mul, abs_mul, abs_of_nonneg hk.le, abs_of_nonneg hW.le]
  have h2 : |lcBesselJ k τ * ((k.factorial : ℕ) : ℝ) * lcW k|
      ≤ (τ / 2) ^ k * lcW k := by
    rw [hrepr, abs_mul, abs_of_nonneg (pow_nonneg (div_nonneg hτ (by norm_num)) k)]
    exact mul_le_mul_of_nonneg_left habs1 (by positivity)
  rw [hkey] at h2
  have hdiv : |lcBesselJ k τ| * ((k.factorial : ℕ) : ℝ) ≤ (τ / 2) ^ k :=
    le_of_mul_le_mul_right h2 hW
  rw [le_div_iff₀ hk]
  exact hdiv

private theorem lcNormExpIm {z : ℂ} (hz : z.im = 0) :
    ‖Complex.exp (Complex.I * z)‖ = 1 := by
  have hre : (Complex.I * z).re = 0 := by
    rw [Complex.I_mul_re, hz, neg_zero]
  have hn : (Complex.normSq (Complex.exp (Complex.I * z)) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self, ← Complex.exp_conj, ← Complex.exp_add,
      add_comm, Complex.add_conj, hre, mul_zero, Complex.ofReal_zero, Complex.exp_zero]
  have h2 : ‖Complex.exp (Complex.I * z)‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact_mod_cast hn
  have hnn : 0 ≤ ‖Complex.exp (Complex.I * z)‖ := norm_nonneg _
  have hle : ‖Complex.exp (Complex.I * z)‖ ≤ 1 := by
    rcases lt_trichotomy (‖Complex.exp (Complex.I * z)‖) 1 with h | h | h
    · exact le_of_lt h
    · exact h.le
    · exfalso
      have hgt : 1 < ‖Complex.exp (Complex.I * z)‖ ^ 2 := by nlinarith
      rw [h2] at hgt
      exact absurd hgt (by norm_num)
  have hge : 1 ≤ ‖Complex.exp (Complex.I * z)‖ := by
    rcases lt_trichotomy (‖Complex.exp (Complex.I * z)‖) 1 with h | h | h
    · exfalso
      rcases eq_or_lt_of_le hnn with h0 | h0
      · rw [← h0] at h2
        norm_num at h2
      · have hlt : ‖Complex.exp (Complex.I * z)‖ ^ 2 < 1 := by nlinarith
        rw [h2] at hlt
        exact absurd hlt (by norm_num)
    · exact le_of_eq h.symm
    · exact h.le
  exact le_antisymm hle hge

private theorem lcNormExpImNeg {z : ℂ} (hz : z.im = 0) :
    ‖Complex.exp (-(Complex.I * z))‖ = 1 := by
  rw [Complex.exp_neg, norm_inv, lcNormExpIm hz, inv_one]

noncomputable def lcJAp (τ : ℝ) (θ : ℝ) (k : ℕ) : ℂ :=
  ((lcBesselJ k τ : ℝ) : ℂ) * Complex.exp (-(Complex.I * (((k : ℕ) : ℂ) * ((θ : ℝ) : ℂ))))

noncomputable def lcJAn (τ : ℝ) (θ : ℝ) (k : ℕ) : ℂ :=
  (-1 : ℂ) ^ k * ((lcBesselJ k τ : ℝ) : ℂ)
    * Complex.exp (Complex.I * (((k : ℕ) : ℂ) * ((θ : ℝ) : ℂ)))

private noncomputable def lcJAc (τ : ℝ) (θ : ℝ) : ℂ :=
  (((τ / 2 : ℝ) : ℂ)) * Complex.exp (-(Complex.I * ((θ : ℝ) : ℂ)))

private noncomputable def lcJAd (τ : ℝ) (θ : ℝ) : ℂ :=
  (-(((τ / 2 : ℝ) : ℂ))) * Complex.exp (Complex.I * ((θ : ℝ) : ℂ))

private theorem lcJApSummable (τ : ℝ) (θ : ℝ) (hτ : 0 ≤ τ) : Summable (lcJAp τ θ) := by
  have hle : ∀ k : ℕ, ‖lcJAp τ θ k‖ ≤ (τ / 2) ^ k / ((k.factorial : ℕ) : ℝ) := by
    intro k
    have hz : (((k : ℕ) : ℂ) * ((θ : ℝ) : ℂ)).im = 0 := by simp
    rw [lcJAp, norm_mul, lcNormExpImNeg hz, Complex.norm_real, Real.norm_eq_abs, mul_one]
    exact abs_lcBesselJ_le k τ hτ
  have hn := Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle
    (Real.summable_pow_div_factorial (τ / 2))
  exact hn.of_norm

private theorem lcJAnSummable (τ : ℝ) (θ : ℝ) (hτ : 0 ≤ τ) : Summable (lcJAn τ θ) := by
  have hle : ∀ k : ℕ, ‖lcJAn τ θ k‖ ≤ (τ / 2) ^ k / ((k.factorial : ℕ) : ℝ) := by
    intro k
    have hz : (((k : ℕ) : ℂ) * ((θ : ℝ) : ℂ)).im = 0 := by simp
    have hno : ‖((-1 : ℂ) ^ k)‖ = 1 := by
      rw [norm_pow]; norm_num
    rw [lcJAn, norm_mul, norm_mul, hno, lcNormExpIm hz, Complex.norm_real, Real.norm_eq_abs,
      one_mul, mul_one]
    exact abs_lcBesselJ_le k τ hτ
  have hn := Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle
    (Real.summable_pow_div_factorial (τ / 2))
  exact hn.of_norm

private theorem lcHasSumOfTendstoNat {f : ℕ → ℂ} {m : ℂ} (hsum : Summable f)
    (h : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, f i) Filter.atTop (nhds m)) :
    HasSum f m := by
  have h1 := hsum.hasSum.tendsto_sum_nat
  have h2 := tendsto_nhds_unique h h1
  rw [h2]
  exact hsum.hasSum

private theorem lcCexpHasSum (z : ℂ) :
    HasSum (fun n => z ^ n / (((n.factorial : ℕ) : ℂ))) (Complex.exp z) := by
  have hsum : Summable (fun n => z ^ n / (((n.factorial : ℕ) : ℂ))) :=
    NormedSpace.expSeries_div_summable z (𝔸 := ℂ)
  have h1 : Filter.Tendsto (fun n : ℕ => ∑ m ∈ Finset.range n, z ^ m / (((m.factorial : ℕ) : ℂ)))
      Filter.atTop (nhds ((Complex.exp' z).lim)) :=
    (Complex.exp' z).tendsto_limit
  rw [Complex.exp_def]
  exact lcHasSumOfTendstoNat hsum h1

theorem lcBesselJacobiAnger (τ : ℝ) (θ : ℝ) (hτ : 0 ≤ τ) :
    HasSum (fun k => lcJAp τ θ k + (if k = 0 then 0 else lcJAn τ θ k))
      (Complex.exp (Complex.I * (-(τ : ℂ) * ((Real.sin θ : ℝ) : ℂ)))) := by
  classical
  set θc : ℂ := ((θ : ℝ) : ℂ) with hθc
  set fC : ℕ → ℂ := fun p => lcJAc τ θ ^ p / (((p.factorial : ℕ) : ℂ)) with hfC
  set fD : ℕ → ℂ := fun p => lcJAd τ θ ^ p / (((p.factorial : ℕ) : ℂ)) with hfD
  set famF : ℕ × ℕ → ℂ := fun p => fC p.1 * fD p.2 with hfamF
  have hnc : Summable (fun p => ‖fC p‖) := NormedSpace.norm_expSeries_div_summable (lcJAc τ θ)
  have hnd : Summable (fun p => ‖fD p‖) := NormedSpace.norm_expSeries_div_summable (lcJAd τ θ)
  have hfamSum : Summable famF := by
    rw [hfamF]
    exact summable_mul_of_summable_norm hnc hnd
  have h2d : HasSum famF (Complex.exp (lcJAc τ θ) * Complex.exp (lcJAd τ θ)) := by
    rw [hfamF]
    exact HasSum.mul (lcCexpHasSum (lcJAc τ θ)) (lcCexpHasSum (lcJAd τ θ))
      (summable_mul_of_summable_norm hnc hnd)

  have hcd : lcJAc τ θ + lcJAd τ θ
      = Complex.I * (-(τ : ℂ) * ((Real.sin θ : ℝ) : ℂ)) := by
    have hE1 := Complex.exp_mul_I θc
    have hE2 := Complex.exp_mul_I (-θc)
    have hnegI : -(Complex.I * θc) = (-θc) * Complex.I := by
      rw [mul_comm, neg_mul]
    have hposI : Complex.I * θc = θc * Complex.I := mul_comm _ _
    rw [lcJAc, lcJAd, hnegI, hposI, hE1, hE2, Complex.cos_neg, Complex.sin_neg,
      ← Complex.ofReal_sin]
    push_cast
    field_simp
    ring

  have hF₁ : ∀ (k j : ℕ), famF (j + k, j)
      = Complex.exp (-(Complex.I * (((k : ℕ) : ℂ) * θc)))
        * (((τ / 2) ^ k * lcSseries k τ j : ℝ) : ℂ) := by
    intro k j
    have e1 : lcJAc τ θ ^ (j + k)
        = (((τ / 2 : ℝ) : ℂ)) ^ (j + k)
          * Complex.exp (-(Complex.I * ((((j + k : ℕ) : ℂ)) * θc))) := by
      have hex : (((j + k : ℕ) : ℂ)) * (-(Complex.I * θc))
          = -(Complex.I * ((((j + k : ℕ) : ℂ)) * θc)) := by
        push_cast
        ring
      rw [lcJAc, mul_pow, ← Complex.exp_nat_mul, hex]
    have e2 : lcJAd τ θ ^ j
        = (-1 : ℂ) ^ j * (((τ / 2 : ℝ) : ℂ)) ^ j
          * Complex.exp (Complex.I * ((((j : ℕ) : ℂ)) * θc)) := by
      have hex : (((j : ℕ) : ℂ)) * (Complex.I * θc)
          = Complex.I * ((((j : ℕ) : ℂ)) * θc) := by
        ring
      rw [lcJAd, mul_pow, neg_pow, ← Complex.exp_nat_mul, hex]
    have e3 : Complex.exp (-(Complex.I * ((((j + k : ℕ) : ℂ)) * θc)))
        * Complex.exp (Complex.I * ((((j : ℕ) : ℂ)) * θc))
        = Complex.exp (-(Complex.I * (((k : ℕ) : ℂ) * θc))) := by
      have hex : -(Complex.I * ((((j + k : ℕ) : ℂ)) * θc)) + Complex.I * ((((j : ℕ) : ℂ)) * θc)
          = -(Complex.I * (((k : ℕ) : ℂ) * θc)) := by
        push_cast
        ring
      rw [← Complex.exp_add, hex]
    simp only [hfamF, hfC, hfD]
    rw [e1, e2]
    have hjf : (((j.factorial : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hkjf : ((((k + j).factorial : ℕ) : ℂ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hc2 : (((2 : ℝ) : ℂ)) ≠ 0 := by norm_num
    have hrw : (((τ / 2 : ℝ) : ℂ)) ^ (j + k)
          * Complex.exp (-(Complex.I * ((((j + k : ℕ) : ℂ)) * θc)))
          / (((j + k).factorial : ℕ) : ℂ)
          * ((-1 : ℂ) ^ j * (((τ / 2 : ℝ) : ℂ)) ^ j
            * Complex.exp (Complex.I * ((((j : ℕ) : ℂ)) * θc)) / (((j.factorial : ℕ) : ℂ)))
        = Complex.exp (-(Complex.I * ((((j + k : ℕ) : ℂ)) * θc)))
          * Complex.exp (Complex.I * ((((j : ℕ) : ℂ)) * θc))
          * (((((τ / 2 : ℝ) : ℂ)) ^ (j + k) * (-1 : ℂ) ^ j * (((τ / 2 : ℝ) : ℂ)) ^ j)
            / ((((j + k).factorial : ℕ) : ℂ) * (((j.factorial : ℕ) : ℂ)))) := by
      field_simp
    rw [hrw, e3]
    have hrest : ((((τ / 2 : ℝ) : ℂ)) ^ (j + k) * (-1 : ℂ) ^ j * (((τ / 2 : ℝ) : ℂ)) ^ j)
          / ((((j + k).factorial : ℕ) : ℂ) * (((j.factorial : ℕ) : ℂ)))
        = (((τ / 2) ^ k * lcSseries k τ j : ℝ) : ℂ) := by
      rw [show ((j + k).factorial) = (k + j).factorial from
        congrArg Nat.factorial (Nat.add_comm j k), lcSseries]
      push_cast
      field_simp
      have hq4 : ((τ : ℂ) ^ 2 / 4) ^ j = ((τ : ℂ) / 2) ^ (j * 2) := by
        have e : ((τ : ℂ) ^ 2 / 4) = ((τ : ℂ) / 2) ^ 2 := by
          field_simp
          ring
        rw [e, ← pow_mul]
        congr 1
        omega
      rw [hq4]
      ring
    rw [hrest]
  have hF₂ : ∀ (k j : ℕ), famF (j, k + j + 1)
      = Complex.exp (Complex.I * ((((k + 1 : ℕ) : ℂ)) * θc)) * (-1 : ℂ) ^ (k + 1)
        * (((τ / 2) ^ (k + 1) * lcSseries (k + 1) τ j : ℝ) : ℂ) := by
    intro k j
    have e1 : lcJAc τ θ ^ j
        = (((τ / 2 : ℝ) : ℂ)) ^ j
          * Complex.exp (-(Complex.I * ((((j : ℕ) : ℂ)) * θc))) := by
      have hex : (((j : ℕ) : ℂ)) * (-(Complex.I * θc))
          = -(Complex.I * ((((j : ℕ) : ℂ)) * θc)) := by
        ring
      rw [lcJAc, mul_pow, ← Complex.exp_nat_mul, hex]
    have e2 : lcJAd τ θ ^ (k + j + 1)
        = (-1 : ℂ) ^ (k + j + 1) * (((τ / 2 : ℝ) : ℂ)) ^ (k + j + 1)
          * Complex.exp (Complex.I * ((((k + j + 1 : ℕ) : ℂ)) * θc)) := by
      have hex : (((k + j + 1 : ℕ) : ℂ)) * (Complex.I * θc)
          = Complex.I * ((((k + j + 1 : ℕ) : ℂ)) * θc) := by
        push_cast
        ring
      rw [lcJAd, mul_pow, neg_pow, ← Complex.exp_nat_mul, hex]
    have e3 : Complex.exp (-(Complex.I * ((((j : ℕ) : ℂ)) * θc)))
        * Complex.exp (Complex.I * ((((k + j + 1 : ℕ) : ℂ)) * θc))
        = Complex.exp (Complex.I * ((((k + 1 : ℕ) : ℂ)) * θc)) := by
      have hex : -(Complex.I * ((((j : ℕ) : ℂ)) * θc))
          + Complex.I * ((((k + j + 1 : ℕ) : ℂ)) * θc)
          = Complex.I * ((((k + 1 : ℕ) : ℂ)) * θc) := by
        push_cast
        ring
      rw [← Complex.exp_add, hex]
    have ep : (-1 : ℂ) ^ (k + j + 1) = (-1 : ℂ) ^ (k + 1) * (-1 : ℂ) ^ j := by
      rw [← pow_add]
      congr 1
      omega
    simp only [hfamF, hfC, hfD]
    rw [e1, e2, ep]
    have hjf : (((j.factorial : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hkf : ((((k + j + 1).factorial : ℕ) : ℂ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hc2 : (((2 : ℝ) : ℂ)) ≠ 0 := by norm_num
    have hrw : (((τ / 2 : ℝ) : ℂ)) ^ j
          * Complex.exp (-(Complex.I * ((((j : ℕ) : ℂ)) * θc))) / (((j.factorial : ℕ) : ℂ))
          * ((-1 : ℂ) ^ (k + 1) * (-1 : ℂ) ^ j * (((τ / 2 : ℝ) : ℂ)) ^ (k + j + 1)
            * Complex.exp (Complex.I * ((((k + j + 1 : ℕ) : ℂ)) * θc))
            / (((k + j + 1).factorial : ℕ) : ℂ))
        = Complex.exp (-(Complex.I * ((((j : ℕ) : ℂ)) * θc)))
          * Complex.exp (Complex.I * ((((k + j + 1 : ℕ) : ℂ)) * θc))
          * ((-1 : ℂ) ^ (k + 1) * (((τ / 2 : ℝ) : ℂ)) ^ j * (-1 : ℂ) ^ j
            * (((τ / 2 : ℝ) : ℂ)) ^ (k + j + 1)
            / (((j.factorial : ℕ) : ℂ) * (((k + j + 1).factorial : ℕ) : ℂ))) := by
      field_simp
    rw [hrw, e3]
    have hrest : ((-1 : ℂ) ^ (k + 1) * (((τ / 2 : ℝ) : ℂ)) ^ j * (-1 : ℂ) ^ j
          * (((τ / 2 : ℝ) : ℂ)) ^ (k + j + 1)
          / (((j.factorial : ℕ) : ℂ) * (((k + j + 1).factorial : ℕ) : ℂ)))
        = (-1 : ℂ) ^ (k + 1)
          * (((τ / 2) ^ (k + 1) * lcSseries (k + 1) τ j : ℝ) : ℂ) := by
      rw [lcSseries, show ((k + j + 1).factorial) = ((k + 1 + j).factorial) from
        congrArg Nat.factorial (by omega)]
      push_cast
      field_simp
      have hq4 : ((τ : ℂ) ^ 2 / 4) ^ j = ((τ : ℂ) / 2) ^ (j * 2) := by
        have e : ((τ : ℂ) ^ 2 / 4) = ((τ : ℂ) / 2) ^ 2 := by
          field_simp
          ring
        rw [e, ← pow_mul]
        congr 1
        omega
      rw [hq4]
      ring
    rw [hrest]
    ring

  have hfib₁ : ∀ k : ℕ, HasSum (fun j : ℕ => famF (j + k, j)) (lcJAp τ θ k) := by
    intro k
    have hs : HasSum (fun j : ℕ => ((τ / 2) ^ k * lcSseries k τ j : ℝ))
        ((τ / 2) ^ k * ∑' m, lcSseries k τ m) :=
      HasSum.mul_left _ (lcSseries_summable k τ).hasSum
    have hs2 := hs.map (Complex.ofRealCLM) (by continuity)
    rw [funext (hF₁ k), lcJAp]
    have hgoal : (((lcBesselJ k τ : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * (((k : ℕ) : ℂ) * ((θ : ℝ) : ℂ)))))
        = (Complex.exp (-(Complex.I * (((k : ℕ) : ℂ) * θc)))
          * (((τ / 2) ^ k * ∑' m, lcSseries k τ m : ℝ) : ℂ)) := by
      rw [lcBesselJ_eq_tsum, hθc]
      ring
    rw [hgoal]
    exact hs2.mul_left _
  have hfib₂ : ∀ k : ℕ,
      HasSum (fun j : ℕ => famF (j, k + j + 1)) (lcJAn τ θ (k + 1)) := by
    intro k
    have hs : HasSum (fun j : ℕ => ((τ / 2) ^ (k + 1) * lcSseries (k + 1) τ j : ℝ))
        ((τ / 2) ^ (k + 1) * ∑' m, lcSseries (k + 1) τ m) :=
      HasSum.mul_left _ (lcSseries_summable (k + 1) τ).hasSum
    have hs2 := hs.map (Complex.ofRealCLM) (by continuity)
    rw [funext (hF₂ k), lcJAn]
    have hgoal : ((-1 : ℂ) ^ (k + 1) * (((lcBesselJ (k + 1) τ : ℝ) : ℂ))
          * Complex.exp (Complex.I * ((((k + 1 : ℕ) : ℂ) * ((θ : ℝ) : ℂ)))))
        = (Complex.exp (Complex.I * ((((k + 1 : ℕ) : ℂ)) * θc)) * (-1 : ℂ) ^ (k + 1)
          * (((τ / 2) ^ (k + 1) * ∑' m, lcSseries (k + 1) τ m : ℝ) : ℂ)) := by
      rw [lcBesselJ_eq_tsum, hθc]
      ring
    rw [hgoal]
    exact hs2.mul_left _

  have hinj₁ : Function.Injective (fun sp : Σ k : ℕ, ℕ => (sp.2 + sp.1, sp.2)) := by
    rintro ⟨k, j⟩ ⟨k', j'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h2, h1⟩ := h
    simp [h1, show k = k' by omega]
  have hinj₂ : Function.Injective
      (fun sp : Σ k : ℕ, ℕ => (sp.2, sp.1 + sp.2 + 1)) := by
    rintro ⟨k, j⟩ ⟨k', j'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hk : k = k' := by omega
    simp [h1, hk]

  have hA : HasSum (fun p : ℕ × ℕ => famF (p.2 + p.1, p.2)) (∑' k, lcJAp τ θ k) := by
    rw [← Equiv.hasSum_iff (Equiv.sigmaEquivProd ℕ ℕ)
      (f := fun p : ℕ × ℕ => famF (p.2 + p.1, p.2))]
    refine HasSum.sigma_of_hasSum (lcJApSummable τ θ hτ).hasSum hfib₁ ?_
    exact hfamSum.comp_injective hinj₁
  have hB : HasSum (fun p : ℕ × ℕ => famF (p.2, p.1 + p.2 + 1))
      (∑' k, lcJAn τ θ (k + 1)) := by
    rw [← Equiv.hasSum_iff (Equiv.sigmaEquivProd ℕ ℕ)
      (f := fun p : ℕ × ℕ => famF (p.2, p.1 + p.2 + 1))]
    refine HasSum.sigma_of_hasSum
      ((lcJAnSummable τ θ hτ).comp_injective Nat.succ_injective).hasSum hfib₂ ?_
    exact hfamSum.comp_injective hinj₂

  have hcomb : HasSum (Sum.elim (fun p : ℕ × ℕ => famF (p.2 + p.1, p.2))
        (fun p : ℕ × ℕ => famF (p.2, p.1 + p.2 + 1)))
      ((∑' k, lcJAp τ θ k) + ∑' k, lcJAn τ θ (k + 1)) :=
    HasSum.sum hA hB
  have hsplit : Function.Bijective
      (Sum.elim (fun p : ℕ × ℕ => (p.2 + p.1, p.2))
        (fun p : ℕ × ℕ => (p.2, p.1 + p.2 + 1))) := by
    constructor
    · rintro (⟨k, j⟩ | ⟨k, j⟩) (⟨k', j'⟩ | ⟨k', j'⟩) h <;>
        simp only [Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq,
          Prod.mk.injEq] at h ⊢ <;> omega
    · rintro ⟨a, b⟩
      rcases le_or_gt b a with hle | hlt
      · refine ⟨Sum.inl ⟨a - b, b⟩, ?_⟩
        simp only [Sum.elim_inl]
        rw [show b + (a - b) = a from by omega]
      · refine ⟨Sum.inr ⟨b - a - 1, a⟩, ?_⟩
        simp only [Sum.elim_inr]
        rw [show (b - a - 1) + a + 1 = b from by omega]
  set e := Equiv.ofBijective
    (Sum.elim (fun p : ℕ × ℕ => (p.2 + p.1, p.2))
      (fun p : ℕ × ℕ => (p.2, p.1 + p.2 + 1))) hsplit with he
  have hpoint : ∀ p : ℕ × ℕ,
      Sum.elim (fun q : ℕ × ℕ => famF (q.2 + q.1, q.2))
        (fun q : ℕ × ℕ => famF (q.2, q.1 + q.2 + 1)) (e.symm p)
      = famF p := by
    rintro ⟨a, b⟩
    rcases le_or_gt b a with hle | hlt
    · have him : (Sum.elim (fun p : ℕ × ℕ => (p.2 + p.1, p.2))
          (fun p : ℕ × ℕ => (p.2, p.1 + p.2 + 1))) (Sum.inl (a - b, b)) = (a, b) := by
        simp only [Sum.elim_inl]
        rw [show b + (a - b) = a from by omega]
      have him' : e (Sum.inl (a - b, b)) = (a, b) := him
      have hsymm : e.symm (a, b) = Sum.inl (a - b, b) := by
        rw [← him']
        exact e.symm_apply_apply _
      rw [hsymm, Sum.elim_inl]
      rw [show b + (a - b) = a from by omega]
    · have him : (Sum.elim (fun p : ℕ × ℕ => (p.2 + p.1, p.2))
          (fun p : ℕ × ℕ => (p.2, p.1 + p.2 + 1))) (Sum.inr (b - a - 1, a)) = (a, b) := by
        simp only [Sum.elim_inr]
        rw [show (b - a - 1) + a + 1 = b from by omega]
      have him' : e (Sum.inr (b - a - 1, a)) = (a, b) := him
      have hsymm : e.symm (a, b) = Sum.inr (b - a - 1, a) := by
        rw [← him']
        exact e.symm_apply_apply _
      rw [hsymm, Sum.elim_inr]
      rw [show (b - a - 1) + a + 1 = b from by omega]
  have hfinal : HasSum famF ((∑' k, lcJAp τ θ k) + ∑' k, lcJAn τ θ (k + 1)) := by
    have h1 : HasSum (fun p : ℕ × ℕ =>
        Sum.elim (fun q : ℕ × ℕ => famF (q.2 + q.1, q.2))
          (fun q : ℕ × ℕ => famF (q.2, q.1 + q.2 + 1)) (e.symm p))
        ((∑' k, lcJAp τ θ k) + ∑' k, lcJAn τ θ (k + 1)) :=
      (Equiv.hasSum_iff e.symm).mpr hcomb
    exact (funext hpoint) ▸ h1

  have hval : (∑' k, lcJAp τ θ k) + ∑' k, lcJAn τ θ (k + 1)
      = Complex.exp (Complex.I * (-(τ : ℂ) * ((Real.sin θ : ℝ) : ℂ))) := by
    rw [HasSum.unique hfinal h2d, ← Complex.exp_add, hcd]

  have hw₂sum : Summable (fun k => if k = 0 then 0 else lcJAn τ θ k) := by
    have hle : ∀ k : ℕ, ‖(if k = 0 then 0 else lcJAn τ θ k)‖
        ≤ (τ / 2) ^ k / ((k.factorial : ℕ) : ℝ) := by
      intro k
      rcases eq_or_ne k 0 with rfl | hk0
      · simp
      · rw [if_neg hk0]
        have hz : (((k : ℕ) : ℂ) * ((θ : ℝ) : ℂ)).im = 0 := by simp
        have hno : ‖((-1 : ℂ) ^ k)‖ = 1 := by
          rw [norm_pow]; norm_num
        rw [lcJAn, norm_mul, norm_mul, hno, lcNormExpIm hz, Complex.norm_real, Real.norm_eq_abs,
          one_mul, mul_one]
        exact abs_lcBesselJ_le k τ hτ
    have hn := Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle
      (Real.summable_pow_div_factorial (τ / 2))
    exact hn.of_norm
  have hw₂val : (∑' k, (if k = 0 then 0 else lcJAn τ θ k))
      = ∑' k, lcJAn τ θ (k + 1) := by
    have hshift := Summable.sum_add_tsum_nat_add 1 hw₂sum
    have h0 : ((if (0 : ℕ) = 0 then 0 else lcJAn τ θ 0)) = 0 := by simp
    rw [Finset.sum_range_one, h0, zero_add] at hshift
    simp only [Nat.succ_ne_zero, if_false] at hshift
    exact hshift.symm
  have hP : HasSum (fun k : ℕ => lcJAp τ θ k) (∑' k, lcJAp τ θ k) :=
    (lcJApSummable τ θ hτ).hasSum
  have hW₂ : HasSum (fun k : ℕ => if k = 0 then 0 else lcJAn τ θ k)
      (∑' k, lcJAn τ θ (k + 1)) := by
    have h := hw₂sum.hasSum
    rw [hw₂val] at h
    exact h
  rw [← hval]
  exact HasSum.add hP hW₂

theorem lcBesselJacobiAngerSummable (τ : ℝ) (θ : ℝ) (hτ : 0 ≤ τ) :
    Summable (fun k => lcJAp τ θ k + (if k = 0 then 0 else lcJAn τ θ k)) := by
  have hle : ∀ k : ℕ, ‖(if k = 0 then 0 else lcJAn τ θ k)‖
      ≤ (τ / 2) ^ k / ((k.factorial : ℕ) : ℝ) := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk0
    · simp
    · rw [if_neg hk0]
      have hz : (((k : ℕ) : ℂ) * ((θ : ℝ) : ℂ)).im = 0 := by simp
      have hno : ‖((-1 : ℂ) ^ k)‖ = 1 := by
        rw [norm_pow]; norm_num
      rw [lcJAn, norm_mul, norm_mul, hno, lcNormExpIm hz, Complex.norm_real,
        Real.norm_eq_abs, one_mul, mul_one]
      exact abs_lcBesselJ_le k τ hτ
  have hn := Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle
    (Real.summable_pow_div_factorial (τ / 2))
  exact Summable.add (lcJApSummable τ θ hτ) hn.of_norm

private theorem lcFactorialGePow (q n : ℕ) :
    q.factorial * (q + 1) ^ n ≤ (q + n).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show q + (n + 1) = (q + n) + 1 from by omega, Nat.factorial_succ]
    calc q.factorial * (q + 1) ^ (n + 1)
        = (q + 1) * (q.factorial * (q + 1) ^ n) := by ring
      _ ≤ (q + 1) * (q + n).factorial := Nat.mul_le_mul_left _ ih
      _ ≤ ((q + n) + 1) * (q + n).factorial := Nat.mul_le_mul_right _ (by omega)

theorem lcBesselJacobiAnger_tail (q : ℕ) (τ : ℝ) (θ : ℝ) (hτ0 : 0 ≤ τ)
    (hτle : τ ≤ ((q - 1 : ℕ) : ℝ)) :
    ‖Complex.exp (Complex.I * (-(τ : ℂ) * ((Real.sin θ : ℝ) : ℂ)))
      - ∑ k ∈ Finset.range q, (lcJAp τ θ k + (if k = 0 then 0 else lcJAn τ θ k))‖
      ≤ 4 * τ ^ q / (2 ^ q * ((q.factorial : ℕ) : ℝ)) := by
  have hw := lcBesselJacobiAnger τ θ hτ0
  have hsum := lcBesselJacobiAngerSummable τ θ hτ0
  have hsplit := Summable.sum_add_tsum_nat_add q hsum
  rw [hw.tsum_eq] at hsplit
  have hval : Complex.exp (Complex.I * (-(τ : ℂ) * ((Real.sin θ : ℝ) : ℂ)))
      - ∑ k ∈ Finset.range q, (lcJAp τ θ k + (if k = 0 then 0 else lcJAn τ θ k))
      = ∑' n, (fun k => lcJAp τ θ k + (if k = 0 then 0 else lcJAn τ θ k)) (n + q) := by
    rw [← hsplit]
    ring
  rw [hval]
  have hAp : ∀ k : ℕ, ‖lcJAp τ θ k‖ ≤ (τ / 2) ^ k / ((k.factorial : ℕ) : ℝ) := by
    intro k
    have hz : (((k : ℕ) : ℂ) * ((θ : ℝ) : ℂ)).im = 0 := by simp
    rw [lcJAp, norm_mul, lcNormExpImNeg hz, Complex.norm_real, Real.norm_eq_abs, mul_one]
    exact abs_lcBesselJ_le k τ hτ0
  have hAn : ∀ k : ℕ, ‖lcJAn τ θ k‖ ≤ (τ / 2) ^ k / ((k.factorial : ℕ) : ℝ) := by
    intro k
    have hz : (((k : ℕ) : ℂ) * ((θ : ℝ) : ℂ)).im = 0 := by simp
    have hno : ‖((-1 : ℂ) ^ k)‖ = 1 := by
      rw [norm_pow]; norm_num
    rw [lcJAn, norm_mul, norm_mul, hno, lcNormExpIm hz, Complex.norm_real,
      Real.norm_eq_abs, one_mul, mul_one]
    exact abs_lcBesselJ_le k τ hτ0
  have hWn : ∀ n : ℕ,
      ‖(fun k => lcJAp τ θ k + (if k = 0 then 0 else lcJAn τ θ k)) (n + q)‖
        ≤ 2 * (τ / 2) ^ (n + q) / (((n + q).factorial : ℕ) : ℝ) := by
    intro n
    have hib : ‖(if n + q = 0 then (0 : ℂ) else lcJAn τ θ (n + q))‖
        ≤ ‖lcJAn τ θ (n + q)‖ := by
      by_cases h : n + q = 0
      · rw [if_pos h, norm_zero]; exact norm_nonneg _
      · rw [if_neg h]
    show ‖lcJAp τ θ (n + q) + (if n + q = 0 then (0 : ℂ) else lcJAn τ θ (n + q))‖ ≤ _
    exact le_trans (norm_add_le _ _)
      (le_trans (add_le_add (hAp (n + q)) (le_trans hib (hAn (n + q)))) (le_of_eq (by ring)))
  have hkey : ∀ n : ℕ, τ ^ n * ((q.factorial : ℕ) : ℝ) ≤ (((n + q).factorial : ℕ) : ℝ) := by
    intro n
    have hqm : ((q - 1 : ℕ) : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show (q - 1 : ℕ) ≤ q + 1 from by omega)
    have h1 : (τ : ℝ) ^ n ≤ (((q + 1 : ℕ) : ℝ)) ^ n :=
      pow_le_pow_left₀ hτ0 (hτle.trans hqm) n
    have h2 := lcFactorialGePow q n
    have h2' : (((q.factorial * (q + 1) ^ n : ℕ) : ℝ)) ≤ (((q + n).factorial : ℕ) : ℝ) := by
      exact_mod_cast h2
    rw [Nat.add_comm q n] at h2'
    calc (τ : ℝ) ^ n * ((q.factorial : ℕ) : ℝ)
        ≤ (((q + 1 : ℕ) : ℝ)) ^ n * ((q.factorial : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (((q.factorial * (q + 1) ^ n : ℕ) : ℝ)) := by push_cast; ring
      _ ≤ (((n + q).factorial : ℕ) : ℝ) := h2'
  have hstep : ∀ n : ℕ, 2 * (τ / 2) ^ (n + q) / (((n + q).factorial : ℕ) : ℝ)
      ≤ (2 * (τ / 2) ^ q / ((q.factorial : ℕ) : ℝ)) * (1 / 2) ^ n := by
    intro n
    have hden1 : (0:ℝ) < (((n + q).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hden2 : (0:ℝ) < ((q.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hfin : (τ / 2 : ℝ) ^ n * ((q.factorial : ℕ) : ℝ)
        ≤ (1 / 2 : ℝ) ^ n * (((n + q).factorial : ℕ) : ℝ) := by
      have hm2 : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by
        rw [← mul_pow]
        norm_num
      have hoinv : (1 / 2 : ℝ) ^ n = (2 ^ n)⁻¹ := by
        rw [one_div, inv_pow]
      rw [div_pow_real τ 2 n]
      calc (τ ^ n / 2 ^ n) * ((q.factorial : ℕ) : ℝ)
          = (τ ^ n * ((q.factorial : ℕ) : ℝ)) / 2 ^ n := by
            field_simp
        _ ≤ (((n + q).factorial : ℕ) : ℝ) / 2 ^ n :=
            div_le_div_of_nonneg_right (hkey n) (by positivity)
        _ = (1 / 2 : ℝ) ^ n * (((n + q).factorial : ℕ) : ℝ) := by
            rw [hoinv, div_eq_mul_inv, mul_comm]
    have hsplit2 : (τ / 2 : ℝ) ^ (n + q) = (τ / 2) ^ n * (τ / 2) ^ q := by
      rw [pow_add]
    rw [hsplit2, div_mul_eq_mul_div, div_le_div_iff₀ hden1 hden2]
    have hc : (0:ℝ) ≤ 2 * (τ / 2) ^ q := by positivity
    calc 2 * ((τ / 2) ^ n * (τ / 2) ^ q) * ((q.factorial : ℕ) : ℝ)
        = ((τ / 2) ^ n * ((q.factorial : ℕ) : ℝ)) * (2 * (τ / 2) ^ q) := by ring
      _ ≤ ((1 / 2) ^ n * (((n + q).factorial : ℕ) : ℝ)) * (2 * (τ / 2) ^ q) :=
          mul_le_mul_of_nonneg_right hfin hc
      _ = 2 * (τ / 2) ^ q * (1 / 2) ^ n * (((n + q).factorial : ℕ) : ℝ) := by ring
  have hHsumm : Summable
      (fun n => (2 * (τ / 2) ^ q / ((q.factorial : ℕ) : ℝ)) * (1 / 2 : ℝ) ^ n) :=
    Summable.mul_left _ (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1))
  have hMidsumm : Summable
      (fun n => 2 * (τ / 2) ^ (n + q) / (((n + q).factorial : ℕ) : ℝ)) := by
    have hτ2 : (0 : ℝ) ≤ τ / 2 := div_nonneg hτ0 zero_le_two
    refine Summable.of_nonneg_of_le
      (fun n => div_nonneg (mul_nonneg zero_le_two (pow_nonneg hτ2 _)) (Nat.cast_nonneg _))
      hstep hHsumm
  have hNormsumm : Summable
      (fun n => ‖(fun k => lcJAp τ θ k + (if k = 0 then 0 else lcJAn τ θ k)) (n + q)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hWn hMidsumm
  have hle : ∑' n, ‖(fun k => lcJAp τ θ k
        + (if k = 0 then 0 else lcJAn τ θ k)) (n + q)‖
      ≤ ∑' n, (2 * (τ / 2) ^ q / ((q.factorial : ℕ) : ℝ)) * (1 / 2) ^ n :=
    le_trans (Summable.tsum_le_tsum hWn hNormsumm hMidsumm)
      (Summable.tsum_le_tsum hstep hMidsumm hHsumm)
  refine le_trans (norm_tsum_le_tsum_norm hNormsumm) (le_trans hle ?_)
  have hg : HasSum (fun n => (1 / 2 : ℝ) ^ n) 2 := by
    have h0 := hasSum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)
    rw [show (1 - 1 / 2 : ℝ)⁻¹ = 2 from by norm_num] at h0
    simpa using! h0
  have hH := HasSum.mul_left (2 * (τ / 2) ^ q / ((q.factorial : ℕ) : ℝ)) hg
  rw [hH.tsum_eq]
  have e : (τ / 2 : ℝ) ^ q = τ ^ q / 2 ^ q := div_pow_real τ 2 q
  rw [e]
  have hEq : (2 * (τ ^ q / 2 ^ q) / ((q.factorial : ℕ) : ℝ)) * 2
      = 4 * τ ^ q / (2 ^ q * ((q.factorial : ℕ) : ℝ)) := by
    field_simp
    norm_num
    ring
  rw [hEq]

end Qatlib.Concepts.QsvtCore.PhaseExistence
