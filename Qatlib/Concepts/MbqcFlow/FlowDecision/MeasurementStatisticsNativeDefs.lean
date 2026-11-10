/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.MbqcFlow.FlowDecision
namespace MeasurementStatisticsNative

open Matrix
open scoped Classical BigOperators ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {O : Type} [Fintype O] [DecidableEq O] {D : ℕ}

theorem sum_delta {α : Type} [Fintype α] [DecidableEq α] (a : α) (g : α → ℝ) :
    (∑ x : α, (if a = x then 1 else 0) * g x) = g a := by
  have hconv : ∀ x : α, (if a = x then 1 else 0) * g x = (if x = a then g x else 0) := by
    intro x
    by_cases h : a = x
    · simp [h]
    · have h' : x ≠ a := Ne.symm h
      simp [h, h']
  rw [Finset.sum_congr rfl fun x _ => hconv x]
  rw [Finset.sum_ite_eq']
  simp

noncomputable def povmJointLaw (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) : FinDist (O × O) where
  prob o := (povmRecordLaw E ρ hρ).prob o.1 * (povmRecordLaw E ρ hρ).prob o.2
  nonneg := fun o =>
    mul_nonneg ((povmRecordLaw E ρ hρ).nonneg o.1) ((povmRecordLaw E ρ hρ).nonneg o.2)
  sum_one := by
    calc
      ∑ o : O × O, (povmRecordLaw E ρ hρ).prob o.1 * (povmRecordLaw E ρ hρ).prob o.2
          = ∑ a : O, ∑ b : O,
              (povmRecordLaw E ρ hρ).prob a * (povmRecordLaw E ρ hρ).prob b :=
            Fintype.sum_prod_type _
      _ = ∑ a : O, (povmRecordLaw E ρ hρ).prob a * 1 := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← Finset.mul_sum, (povmRecordLaw E ρ hρ).sum_one, mul_one]
      _ = 1 := by
            rw [← Finset.sum_mul, (povmRecordLaw E ρ hρ).sum_one, mul_one]

theorem povmJointLaw_prob (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (o₁ o₂ : O) :
    (povmJointLaw E ρ hρ).prob (o₁, o₂)
      = (povmRecordLaw E ρ hρ).prob o₁ * (povmRecordLaw E ρ hρ).prob o₂ := rfl

noncomputable def povmKernelMeanIndependent (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (h : O → O → ℝ) : ℝ :=
  (povmJointLaw E ρ hρ).expect (fun o => h o.1 o.2)

noncomputable def povmKernelMeanDiagonal (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (h : O → O → ℝ) : ℝ :=
  (povmRecordLaw E ρ hρ).expect (fun o => h o o)

theorem povmJointLaw_expect_separable (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (f g : O → ℝ) :
    (povmJointLaw E ρ hρ).expect (fun o => f o.1 * g o.2)
      = (povmRecordLaw E ρ hρ).expect f * (povmRecordLaw E ρ hρ).expect g := by
  show (∑ o : O × O, (povmRecordLaw E ρ hρ).prob o.1 * (povmRecordLaw E ρ hρ).prob o.2
      * (f o.1 * g o.2)) = _
  calc
    ∑ o : O × O, (povmRecordLaw E ρ hρ).prob o.1 * (povmRecordLaw E ρ hρ).prob o.2
        * (f o.1 * g o.2)
        = ∑ a : O, ∑ b : O, (povmRecordLaw E ρ hρ).prob a * (povmRecordLaw E ρ hρ).prob b
            * (f a * g b) := Fintype.sum_prod_type _
    _ = ∑ a : O, ((povmRecordLaw E ρ hρ).prob a * f a)
        * ∑ b : O, (povmRecordLaw E ρ hρ).prob b * g b := by
          refine Finset.sum_congr rfl fun a _ => ?_
          calc
            (∑ b : O, (povmRecordLaw E ρ hρ).prob a * (povmRecordLaw E ρ hρ).prob b
                * (f a * g b))
                = ∑ b : O, ((povmRecordLaw E ρ hρ).prob a * f a)
                    * ((povmRecordLaw E ρ hρ).prob b * g b) := by
                      refine Finset.sum_congr rfl fun b _ => ?_
                      ring
            _ = ((povmRecordLaw E ρ hρ).prob a * f a)
                * ∑ b : O, (povmRecordLaw E ρ hρ).prob b * g b := by
                      rw [Finset.mul_sum]
    _ = (∑ a : O, (povmRecordLaw E ρ hρ).prob a * f a)
        * ∑ b : O, (povmRecordLaw E ρ hρ).prob b * g b := by
          rw [Finset.sum_mul]
    _ = _ := rfl

theorem probOf_two {n : ℕ} (p : FinDist O)
    (i j : Fin n) (hne : i ≠ j) (x y : O) :
    ∑ ω : Fin n → O, p.probOf ω * (if ω i = x then 1 else 0) * (if ω j = y then 1 else 0)
      = p.prob x * p.prob y := by
  let gi : Fin n → O → ℝ := fun k z => if k = i then (if z = x then 1 else 0) else 1
  let gj : Fin n → O → ℝ := fun k z => if k = j then (if z = y then 1 else 0) else 1
  let g : Fin n → O → ℝ := fun k z => gi k z * gj k z
  have hgi : ∀ ω : Fin n → O,
      (∏ k : Fin n, gi k (ω k)) = (if ω i = x then 1 else 0) := by
    intro ω
    rw [Finset.prod_eq_single i]
    · simp [gi]
    · intro k _ hki
      simp [gi, hki]
    · intro hcon
      exact absurd (Finset.mem_univ i) hcon
  have hgj : ∀ ω : Fin n → O,
      (∏ k : Fin n, gj k (ω k)) = (if ω j = y then 1 else 0) := by
    intro ω
    rw [Finset.prod_eq_single j]
    · simp [gj]
    · intro k _ hkj
      simp [gj, hkj]
    · intro hcon
      exact absurd (Finset.mem_univ j) hcon
  have hprod : ∀ ω : Fin n → O,
      (∏ k : Fin n, g k (ω k))
        = (if ω i = x then 1 else 0) * (if ω j = y then 1 else 0) := by
    intro ω
    calc
      (∏ k : Fin n, g k (ω k))
          = (∏ k : Fin n, gi k (ω k)) * (∏ k : Fin n, gj k (ω k)) := by
            rw [← Finset.prod_mul_distrib]
      _ = (if ω i = x then 1 else 0) * (if ω j = y then 1 else 0) := by rw [hgi, hgj]
  have hfi : (∑ z, p.prob z * g i z) = p.prob x := by
    have hg : ∀ z, g i z = (if z = x then 1 else 0) := by
      intro z
      simp [g, gi, gj, hne]
    have hconv : ∀ z, p.prob z * g i z = (if z = x then p.prob z else 0) := by
      intro z
      by_cases h : z = x <;> simp [hg, h]
    rw [Finset.sum_congr rfl fun z _ => hconv z]
    rw [Finset.sum_ite_eq']
    simp
  have hfj : (∑ z, p.prob z * g j z) = p.prob y := by
    have hg : ∀ z, g j z = (if z = y then 1 else 0) := by
      intro z
      simp [g, gi, gj, hne.symm]
    have hconv : ∀ z, p.prob z * g j z = (if z = y then p.prob z else 0) := by
      intro z
      by_cases h : z = y <;> simp [hg, h]
    rw [Finset.sum_congr rfl fun z _ => hconv z]
    rw [Finset.sum_ite_eq']
    simp
  have hfk : ∀ k : Fin n, k ≠ i → k ≠ j → (∑ z, p.prob z * g k z) = 1 := by
    intro k hki hkj
    have hg : ∀ z, g k z = 1 := by
      intro z
      simp [g, gi, gj, hki, hkj]
    have hconv : ∀ z, p.prob z * g k z = p.prob z * 1 := by
      intro z
      rw [hg z, mul_one]
    rw [Finset.sum_congr rfl fun z _ => hconv z]
    rw [Finset.sum_congr rfl fun z _ => mul_one (p.prob z)]
    exact p.sum_one
  calc
    ∑ ω : Fin n → O, p.probOf ω * (if ω i = x then 1 else 0) * (if ω j = y then 1 else 0)
        = ∑ ω : Fin n → O, p.probOf ω * (∏ k : Fin n, g k (ω k)) := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [hprod]
          ring
    _ = ∏ k : Fin n, (∑ z, p.prob z * g k z) := p.expect_prod g
    _ = p.prob x * p.prob y := by
          have hsplit : (∏ k : Fin n, (∑ z, p.prob z * g k z))
              = (∑ z, p.prob z * g i z) * (∑ z, p.prob z * g j z) * 1 := by
            have h1 : (∏ k : Fin n, (∑ z, p.prob z * g k z))
                = (∑ z, p.prob z * g i z)
                  * Finset.prod ((Finset.univ : Finset (Fin n)).erase i)
                      (fun k => ∑ z, p.prob z * g k z) := by
              have h := Finset.prod_erase_mul (Finset.univ : Finset (Fin n))
                (fun k => ∑ z, p.prob z * g k z) (Finset.mem_univ i)
              rw [mul_comm] at h
              rw [h]
            have hjmem : j ∈ (Finset.univ : Finset (Fin n)).erase i := by simp [hne.symm]
            have h2 : Finset.prod ((Finset.univ : Finset (Fin n)).erase i)
                  (fun k => ∑ z, p.prob z * g k z)
                = (∑ z, p.prob z * g j z)
                  * Finset.prod (((Finset.univ : Finset (Fin n)).erase i).erase j)
                      (fun k => ∑ z, p.prob z * g k z) := by
              have h := Finset.prod_erase_mul ((Finset.univ : Finset (Fin n)).erase i)
                (fun k => ∑ z, p.prob z * g k z) hjmem
              rw [mul_comm] at h
              rw [h]
            have hrest : Finset.prod (((Finset.univ : Finset (Fin n)).erase i).erase j)
                  (fun k => ∑ z, p.prob z * g k z) = 1 := by
              have hconv : Finset.prod (((Finset.univ : Finset (Fin n)).erase i).erase j)
                  (fun k => ∑ z, p.prob z * g k z)
                  = Finset.prod (((Finset.univ : Finset (Fin n)).erase i).erase j)
                      (fun _ => (1 : ℝ)) := by
                refine Finset.prod_congr rfl fun k hk => ?_
                have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
                have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
                exact hfk k hki hkj
              rw [hconv, Finset.prod_const_one]
            rw [h1, h2, hrest, hfi, hfj]
            ring
          rw [hsplit, hfi, hfj]
          ring

theorem povm_expect_one_record (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (h : O → O → ℝ) {n : ℕ} (i : Fin n) :
    ∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω * h (ω i) (ω i)
      = povmKernelMeanDiagonal E ρ hρ h := by
  have h1 :=
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect_coord (povmRecordLaw E ρ hρ) i
      (fun o => h o o)
  rw [h1]
  rfl

theorem povm_expect_two_records (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (h : O → O → ℝ) {n : ℕ} (i j : Fin n) (hne : i ≠ j) :
    ∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω * h (ω i) (ω j)
      = povmKernelMeanIndependent E ρ hρ h := by
  have hkey : ∀ ω : Fin n → O,
      h (ω i) (ω j)
        = ∑ x : O, ∑ y : O, (if ω i = x then 1 else 0) * (if ω j = y then 1 else 0) * h x y := by
    intro ω
    calc
      h (ω i) (ω j)
          = ∑ x : O, (if ω i = x then 1 else 0) * h x (ω j) := by
              rw [sum_delta]
      _ = ∑ x : O, (if ω i = x then 1 else 0)
              * (∑ y : O, (if ω j = y then 1 else 0) * h x y) := by
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [sum_delta]
      _ = ∑ x : O, ∑ y : O, (if ω i = x then 1 else 0) * (if ω j = y then 1 else 0) * h x y := by
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun y _ => ?_
              ring
  calc
    (∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω * h (ω i) (ω j))
        = ∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω
            * (∑ x : O, ∑ y : O, (if ω i = x then 1 else 0) * (if ω j = y then 1 else 0) * h x y) := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [hkey]
    _ = ∑ ω : Fin n → O, ∑ x : O, (povmRecordLaw E ρ hρ).probOf ω
            * (∑ y : O, (if ω i = x then 1 else 0) * (if ω j = y then 1 else 0) * h x y) := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [Finset.mul_sum]
    _ = ∑ x : O, ∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω
            * (∑ y : O, (if ω i = x then 1 else 0) * (if ω j = y then 1 else 0) * h x y) :=
          Finset.sum_comm
    _ = ∑ x : O, ∑ ω : Fin n → O, ∑ y : O, (povmRecordLaw E ρ hρ).probOf ω
            * ((if ω i = x then 1 else 0) * (if ω j = y then 1 else 0) * h x y) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [Finset.mul_sum]
    _ = ∑ x : O, ∑ y : O, ∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω
            * ((if ω i = x then 1 else 0) * (if ω j = y then 1 else 0) * h x y) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          exact Finset.sum_comm
    _ = ∑ x : O, ∑ y : O, (povmRecordLaw E ρ hρ).prob x * (povmRecordLaw E ρ hρ).prob y * h x y := by
          refine Finset.sum_congr rfl fun x _ => ?_
          refine Finset.sum_congr rfl fun y _ => ?_
          have hprod := probOf_two (povmRecordLaw E ρ hρ) i j hne x y
          calc
            (∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω
                * ((if ω i = x then 1 else 0) * (if ω j = y then 1 else 0) * h x y))
                = ∑ ω : Fin n → O, ((povmRecordLaw E ρ hρ).probOf ω
                    * (if ω i = x then 1 else 0) * (if ω j = y then 1 else 0)) * h x y := by
                      refine Finset.sum_congr rfl fun ω _ => ?_
                      ring
            _ = ((∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω
                    * (if ω i = x then 1 else 0) * (if ω j = y then 1 else 0)) * h x y) := by
                      rw [← Finset.sum_mul]
            _ = ((povmRecordLaw E ρ hρ).prob x * (povmRecordLaw E ρ hρ).prob y) * h x y := by
                      rw [hprod]
    _ = povmKernelMeanIndependent E ρ hρ h := by
          symm
          unfold povmKernelMeanIndependent
          show (∑ o : O × O, ((povmRecordLaw E ρ hρ).prob o.1
              * (povmRecordLaw E ρ hρ).prob o.2) * h o.1 o.2) = _
          rw [Fintype.sum_prod_type]

noncomputable def povmMomentEffectK (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) (A : Operator D) (k : ℕ) : Operator D :=
  ∑ o : O, (Complex.ofReal (povmStatistic E hM A o) ^ k) • E.effect o

theorem re_ofReal_pow (x : ℝ) (k : ℕ) : (Complex.ofReal x ^ k).re = x ^ k := by
  calc
    (Complex.ofReal x ^ k).re = ((x ^ k : ℝ) : ℂ).re := by
      rw [show Complex.ofReal x ^ k = ((x ^ k : ℝ) : ℂ) from (Complex.ofReal_pow x k).symm]
    _ = x ^ k := Complex.ofReal_re _

theorem povm_expect_statistic_pow (E : FinitePOVM O D)
    (hM : Function.Bijective (povmMeasurementMap E)) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (A : Operator D) (k : ℕ) :
    (povmRecordLaw E ρ hρ).expect (fun o => (povmStatistic E hM A o) ^ k)
      = (Matrix.trace (povmMomentEffectK E hM A k * ρ)).re := by
  have hcomplex :
      (∑ o : O, ((povmRecordLaw E ρ hρ).prob o : ℂ)
          * (Complex.ofReal (povmStatistic E hM A o) ^ k))
        = Matrix.trace (povmMomentEffectK E hM A k * ρ) := by
    rw [povmMomentEffectK, Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    rw [povmRecordLaw_prob_complex E ρ hρ o]
    ring
  have hreal :
      (∑ o : O, (povmRecordLaw E ρ hρ).prob o * (povmStatistic E hM A o) ^ k)
        = (∑ o : O, ((povmRecordLaw E ρ hρ).prob o : ℂ)
          * (Complex.ofReal (povmStatistic E hM A o) ^ k)).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, re_ofReal_pow]
    ring
  show ∑ o : O, (povmRecordLaw E ρ hρ).prob o * (povmStatistic E hM A o) ^ k = _
  rw [hreal, hcomplex]

noncomputable def povmUStatistic (h : O → O → ℝ) {n : ℕ} (ω : Fin n → O) : ℝ :=
  (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, h (ω i) (ω j)) / ((n : ℝ) * (n - 1))

theorem povm_expect_UStatistic (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (h : O → O → ℝ) {n : ℕ} (hn : 2 ≤ n) :
    ∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω * povmUStatistic h ω
      = povmKernelMeanIndependent E ρ hρ h := by
  have hswap :
      (∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω
          * (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, h (ω i) (ω j)))
        = ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
            ∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω * h (ω i) (ω j) := by
    calc
      (∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω
          * (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, h (ω i) (ω j)))
          = ∑ ω : Fin n → O, ∑ i : Fin n, (povmRecordLaw E ρ hρ).probOf ω
              * (∑ j ∈ Finset.univ.erase i, h (ω i) (ω j)) := by
                refine Finset.sum_congr rfl fun ω _ => ?_
                rw [Finset.mul_sum]
      _ = ∑ i : Fin n, ∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω
              * (∑ j ∈ Finset.univ.erase i, h (ω i) (ω j)) := Finset.sum_comm
      _ = ∑ i : Fin n, ∑ ω : Fin n → O, ∑ j ∈ Finset.univ.erase i,
              (povmRecordLaw E ρ hρ).probOf ω * h (ω i) (ω j) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun ω _ => ?_
            rw [Finset.mul_sum]
      _ = ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, ∑ ω : Fin n → O,
              (povmRecordLaw E ρ hρ).probOf ω * h (ω i) (ω j) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            exact Finset.sum_comm
  have hpair : ∀ i : Fin n, ∀ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      (∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω * h (ω i) (ω j))
        = povmKernelMeanIndependent E ρ hρ h := by
    intro i j hj
    exact povm_expect_two_records E ρ hρ h i j (Ne.symm (Finset.mem_erase.mp hj).1)
  have hcard : ∀ i : Fin n, ((Finset.univ : Finset (Fin n)).erase i).card = n - 1 := by
    intro i
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  have hcountR : (∑ i : Fin n,
        (((Finset.univ : Finset (Fin n)).erase i).card : ℝ)) = (n : ℝ) * (n - 1) := by
    calc
      (∑ i : Fin n, (((Finset.univ : Finset (Fin n)).erase i).card : ℝ))
          = ∑ _i : Fin n, ((n : ℝ) - 1) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [hcard]
              rw [Nat.cast_sub, Nat.cast_one]
              omega
      _ = (n : ℝ) * (n - 1) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hζ : (∑ i : Fin n, ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      povmKernelMeanIndependent E ρ hρ h)
      = povmKernelMeanIndependent E ρ hρ h * ((n : ℝ) * (n - 1)) := by
    calc
      (∑ i : Fin n, ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          povmKernelMeanIndependent E ρ hρ h)
          = ∑ i : Fin n, (((Finset.univ : Finset (Fin n)).erase i).card : ℝ)
              * povmKernelMeanIndependent E ρ hρ h := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((n : ℝ) * (n - 1)) * povmKernelMeanIndependent E ρ hρ h := by
            rw [← Finset.sum_mul, hcountR]
      _ = povmKernelMeanIndependent E ρ hρ h * ((n : ℝ) * (n - 1)) := by ring
  have hne : ((n : ℝ) * (n - 1)) ≠ 0 := by
    have h3 : (0 : ℝ) < (n : ℝ) * (n - 1) := by
      have h1 : (0 : ℝ) < (n : ℝ) := by
        have : (0 : ℕ) < n := by omega
        exact_mod_cast this
      have h2 : (0 : ℝ) < ((n : ℝ) - 1) := by
        have : (1 : ℕ) < n := by omega
        have h1' : (1 : ℝ) < (n : ℝ) := by exact_mod_cast this
        linarith
      nlinarith
    exact ne_of_gt h3
  have heq : ∀ ω : Fin n → O,
      (povmRecordLaw E ρ hρ).probOf ω * povmUStatistic h ω
        = ((povmRecordLaw E ρ hρ).probOf ω
            * (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, h (ω i) (ω j)))
            / ((n : ℝ) * (n - 1)) := by
    intro ω
    rw [povmUStatistic]
    ring
  calc
    (∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω * povmUStatistic h ω)
        = ∑ ω : Fin n → O, ((povmRecordLaw E ρ hρ).probOf ω
            * (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, h (ω i) (ω j)))
            / ((n : ℝ) * (n - 1)) := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [heq]
    _ = (∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω
            * (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, h (ω i) (ω j)))
            / ((n : ℝ) * (n - 1)) := by
          rw [← Finset.sum_div]
    _ = (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
            ∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω * h (ω i) (ω j))
        / ((n : ℝ) * (n - 1)) := by rw [hswap]
    _ = (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
            povmKernelMeanIndependent E ρ hρ h) / ((n : ℝ) * (n - 1)) := by
          have hinner : (∑ i : Fin n, ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
                ∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω * h (ω i) (ω j))
              = (∑ i : Fin n, ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
                povmKernelMeanIndependent E ρ hρ h) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [hpair i j hj]
          rw [hinner]
    _ = povmKernelMeanIndependent E ρ hρ h := by
          rw [hζ]
          have h3 : ((n : ℝ) * (n - 1)) ≠ 0 := hne
          rw [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ h3, mul_one]

theorem povmJointLaw_expect_diagonal (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (h : O → O → ℝ) :
    (povmJointLaw E ρ hρ).expect (fun o => h o.1 o.1)
      = povmKernelMeanDiagonal E ρ hρ h := by
  show (∑ o : O × O, ((povmRecordLaw E ρ hρ).prob o.1
      * (povmRecordLaw E ρ hρ).prob o.2) * (h o.1 o.1)) = _
  calc
    (∑ o : O × O, ((povmRecordLaw E ρ hρ).prob o.1
        * (povmRecordLaw E ρ hρ).prob o.2) * (h o.1 o.1))
        = ∑ a : O, ∑ b : O, (povmRecordLaw E ρ hρ).prob a
            * (povmRecordLaw E ρ hρ).prob b * (h a a) := Fintype.sum_prod_type _
    _ = ∑ a : O, (povmRecordLaw E ρ hρ).prob a * (h a a) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          have heq : ∀ b : O, (povmRecordLaw E ρ hρ).prob a
                * (povmRecordLaw E ρ hρ).prob b * (h a a)
              = (povmRecordLaw E ρ hρ).prob a
                * ((povmRecordLaw E ρ hρ).prob b * (h a a)) := by
            intro b
            ring
          simp only [heq]
          rw [← Finset.mul_sum, ← Finset.sum_mul, (povmRecordLaw E ρ hρ).sum_one]
          ring
    _ = _ := rfl

theorem povmKernelMean_bias (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (h : O → O → ℝ) :
    povmKernelMeanDiagonal E ρ hρ h - povmKernelMeanIndependent E ρ hρ h
      = (povmJointLaw E ρ hρ).expect (fun o => h o.1 o.1 - h o.1 o.2) := by
  have h1 := povmJointLaw_expect_diagonal E ρ hρ h
  have h2 : (povmJointLaw E ρ hρ).expect (fun o => h o.1 o.1 - h o.1 o.2)
      = (povmJointLaw E ρ hρ).expect (fun o => h o.1 o.1)
        - (povmJointLaw E ρ hρ).expect (fun o => h o.1 o.2) := by
    have heq : ∀ o : O × O,
        (povmJointLaw E ρ hρ).prob o * ((fun o => h o.1 o.1 - h o.1 o.2) o)
          = (povmJointLaw E ρ hρ).prob o * ((fun o => h o.1 o.1) o)
            - (povmJointLaw E ρ hρ).prob o * ((fun o => h o.1 o.2) o) := by
      intro o
      ring
    simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect]
    rw [Finset.sum_congr rfl fun o _ => heq o]
    rw [Finset.sum_sub_distrib]
  rw [h1.symm, h2]
  rfl

theorem povmKernelMeanIndependent_product (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (A : Operator D)
    (hM : Function.Bijective (povmMeasurementMap E)) :
    povmKernelMeanIndependent E ρ hρ
        (fun o₁ o₂ => povmStatistic E hM A o₁ * povmStatistic E hM A o₂)
      = (povmRecordLaw E ρ hρ).expect (povmStatistic E hM A) ^ 2 := by
  unfold povmKernelMeanIndependent
  rw [povmJointLaw_expect_separable]
  ring

theorem povmKernelMeanDiagonal_product (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (A : Operator D)
    (hM : Function.Bijective (povmMeasurementMap E)) :
    povmKernelMeanDiagonal E ρ hρ
        (fun o₁ o₂ => povmStatistic E hM A o₁ * povmStatistic E hM A o₂)
      = (povmRecordLaw E ρ hρ).expect (fun o => (povmStatistic E hM A o) ^ 2) := by
  unfold povmKernelMeanDiagonal
  refine Finset.sum_congr rfl fun o _ => ?_
  ring

theorem povmKernelMean_bias_variance (E : FinitePOVM O D) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (A : Operator D)
    (hM : Function.Bijective (povmMeasurementMap E)) :
    povmKernelMeanDiagonal E ρ hρ
        (fun o₁ o₂ => povmStatistic E hM A o₁ * povmStatistic E hM A o₂)
      - povmKernelMeanIndependent E ρ hρ
        (fun o₁ o₂ => povmStatistic E hM A o₁ * povmStatistic E hM A o₂)
      = (povmRecordLaw E ρ hρ).expect (fun o => (povmStatistic E hM A o) ^ 2)
        - (povmRecordLaw E ρ hρ).expect (povmStatistic E hM A) ^ 2 := by
  rw [povmKernelMeanDiagonal_product, povmKernelMeanIndependent_product]

theorem sum_delta_right {α : Type} [Fintype α] [DecidableEq α] (a : α) (g : α → ℝ) :
    (∑ x : α, g x * (if x = a then 1 else 0)) = g a := by
  have hconv : ∀ x : α, g x * (if x = a then 1 else 0) = (if x = a then g x else 0) := by
    intro x
    by_cases h : x = a <;> simp [h]
  rw [Finset.sum_congr rfl fun x _ => hconv x]
  rw [Finset.sum_ite_eq']
  simp

def campaignFlatten {K L : ℕ} (ω : Fin K → Fin L → O) : List O :=
  (List.ofFn (fun k : Fin K => List.ofFn (ω k))).flatten

theorem campaignFlatten_length {K L : ℕ} (ω : Fin K → Fin L → O) :
    (campaignFlatten ω).length = K * L := by
  have h1 : (List.ofFn (fun k : Fin K => List.ofFn (ω k))).flatten.length
      = (List.map List.length (List.ofFn (fun k : Fin K => List.ofFn (ω k)))).sum :=
    List.length_flatten
  have h2 : (List.map List.length (List.ofFn (fun k : Fin K => List.ofFn (ω k)))).sum
      = ∑ _k : Fin K, L := by
    have hm : List.map List.length (List.ofFn (fun k : Fin K => List.ofFn (ω k)))
        = List.ofFn (fun k : Fin K => (List.ofFn (ω k)).length) := by
      exact List.map_ofFn
    rw [hm, List.sum_ofFn]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [List.length_ofFn]
  rw [campaignFlatten, h1, h2]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp

def nativeAxisTable : List (Fin 3) := [0, 1, 2]

def nativeDrawnAxis (idx : Fin 3) : Fin 3 := nativeAxisTable.getD idx.val 0

def nativeAxisDrawCost (idx : Fin 3) : ℕ := tableScanCost nativeAxisTable idx

theorem nativeDrawnAxis_apply (idx : Fin 3) : nativeDrawnAxis idx = idx := by
  rcases idx with ⟨i, hi⟩
  interval_cases i <;> simp [nativeDrawnAxis, nativeAxisTable]

theorem nativeAxisDrawCost_le (idx : Fin 3) :
    nativeAxisDrawCost idx ≤ nativeAxisTable.length := by
  exact tableScanCost_le nativeAxisTable idx

noncomputable def nativeUniformIndex : FinDist (Fin 3) where
  prob _ := 1 / 3
  nonneg := fun _ => by norm_num
  sum_one := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num

noncomputable def nativeDrawnAxisLaw : FinDist (Fin 3) where
  prob a := ∑ idx : Fin 3, nativeUniformIndex.prob idx
      * (if nativeDrawnAxis idx = a then 1 else 0)
  nonneg := fun a => by
    refine Finset.sum_nonneg fun i _ => ?_
    exact mul_nonneg (nativeUniformIndex.nonneg i) (by split <;> norm_num)
  sum_one := by
    have key : ∀ a : Fin 3, (∑ idx : Fin 3, nativeUniformIndex.prob idx
        * (if nativeDrawnAxis idx = a then 1 else 0)) = 1 / 3 := by
      intro a
      have hd : ∀ idx : Fin 3, nativeDrawnAxis idx = idx := nativeDrawnAxis_apply
      calc
        (∑ idx : Fin 3, nativeUniformIndex.prob idx
            * (if nativeDrawnAxis idx = a then 1 else 0))
            = ∑ idx : Fin 3, nativeUniformIndex.prob idx
                * (if idx = a then 1 else 0) := by
                  refine Finset.sum_congr rfl fun idx _ => ?_
                  by_cases h : idx = a
                  · subst h
                    rw [hd, if_pos rfl]
                  · rw [hd, if_neg h]
        _ = nativeUniformIndex.prob a := by
          rw [sum_delta_right]
    rw [Finset.sum_congr rfl fun a _ => key a]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num

theorem nativeDrawnAxisLaw_prob (a : Fin 3) :
    (nativeDrawnAxisLaw.prob a) = 1 / 3 := by
  have key : ∀ b : Fin 3, (nativeDrawnAxisLaw.prob b) = 1 / 3 := by
    intro b
    have hd : ∀ idx : Fin 3, nativeDrawnAxis idx = idx := nativeDrawnAxis_apply
    calc
      (∑ idx : Fin 3, nativeUniformIndex.prob idx
          * (if nativeDrawnAxis idx = b then 1 else 0))
          = ∑ idx : Fin 3, nativeUniformIndex.prob idx
              * (if idx = b then 1 else 0) := by
                refine Finset.sum_congr rfl fun idx _ => ?_
                by_cases h : idx = b
                · subst h
                  rw [hd, if_pos rfl]
                · rw [hd, if_neg h]
      _ = nativeUniformIndex.prob b := by
        rw [sum_delta_right]
  exact key a

def nativeSelectAxis (history : List (Fin 3 × Fin 2)) : Fin 3 :=
  nativeAxisTable.getD (history.length % 3) 0

def nativeAxisSelectionCost (history : List (Fin 3 × Fin 2)) : ℕ :=
  tableScanCost nativeAxisTable (nativeSelectAxis history)

theorem nativeAxisSelectionCost_le (history : List (Fin 3 × Fin 2)) :
    nativeAxisSelectionCost history ≤ nativeAxisTable.length :=
  tableScanCost_le nativeAxisTable (nativeSelectAxis history)

structure NativeCampaign (K L : ℕ) where

  axisTape : Fin K → Fin L → Fin 3

  basisLabels : Fin K → Fin L → Fin 2

def NativeCampaign.records {K L : ℕ} (c : NativeCampaign K L) :
    Fin K → Fin L → (Fin 3 × Fin 2) :=
  fun k l => (nativeDrawnAxis (c.axisTape k l), c.basisLabels k l)

def NativeCampaign.historyBefore {K L : ℕ} (c : NativeCampaign K L)
    (k : Fin K) (l : Fin L) : List (Fin 3 × Fin 2) :=
  (campaignFlatten c.records).take (k.val * L + l.val)

def nativePayoff : (Fin 3 × Fin 2) → ℚ :=
  fun o => (1 / 3 : ℚ) * (if o.2 = 0 then 1 else -1)

def nativeRationalFold (payoff : O → ℚ) : List O → ℚ × ℕ × ℕ
  | [] => (0, 0, 0)
  | o :: os =>
    let s := nativeRationalFold payoff os
    (payoff o + s.1, s.2.1 + 1, s.2.2 + 1)

theorem nativeRationalFold_spec (payoff : O → ℚ) (os : List O) :
    (nativeRationalFold payoff os).1 = (os.map payoff).sum ∧
    (nativeRationalFold payoff os).2.1 = os.length ∧
    (nativeRationalFold payoff os).2.2 = os.length := by
  induction os with
  | nil => simp [nativeRationalFold]
  | cons o os ih => simp [nativeRationalFold, ih]

def rationalInsertSortedCounted (x : ℚ) : List ℚ → List ℚ × ℕ
  | [] => ([x], 0)
  | y :: ys => if x ≤ y then (x :: y :: ys, 1)
    else let s := rationalInsertSortedCounted x ys; (y :: s.1, s.2 + 1)

theorem rationalInsertSortedCounted_cost_le (x : ℚ) (l : List ℚ) :
    (rationalInsertSortedCounted x l).2 ≤ l.length := by
  induction l with
  | nil => simp [rationalInsertSortedCounted]
  | cons y ys ih =>
    simp only [rationalInsertSortedCounted]
    split
    · simp
    · show (rationalInsertSortedCounted x ys).2 + 1 ≤ ys.length + 1
      exact Nat.succ_le_succ ih

def rationalInsertionSortCounted : List ℚ → List ℚ × ℕ
  | [] => ([], 0)
  | x :: xs =>
    let s := rationalInsertionSortCounted xs
    let t := rationalInsertSortedCounted x s.1
    (t.1, s.2 + t.2)

theorem rationalInsertSortedCounted_length (x : ℚ) (l : List ℚ) :
    (rationalInsertSortedCounted x l).1.length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    simp only [rationalInsertSortedCounted]
    split
    · simp
    · simp [ih]

theorem rationalInsertionSortCounted_length (l : List ℚ) :
    (rationalInsertionSortCounted l).1.length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [rationalInsertionSortCounted]
    have h1 := rationalInsertSortedCounted_length x (rationalInsertionSortCounted xs).1
    rw [h1, ih]
    simp

theorem rationalInsertionSortCounted_cost_le (l : List ℚ) :
    (rationalInsertionSortCounted l).2 ≤ l.length * l.length := by
  induction l with
  | nil => simp [rationalInsertionSortCounted]
  | cons x xs ih =>
    simp only [rationalInsertionSortCounted]
    have h1 : (rationalInsertionSortCounted xs).1.length = xs.length :=
      rationalInsertionSortCounted_length xs
    have h2 : (rationalInsertSortedCounted x (rationalInsertionSortCounted xs).1).2
        ≤ (rationalInsertionSortCounted xs).1.length :=
      rationalInsertSortedCounted_cost_le x _
    calc
      (rationalInsertionSortCounted xs).2
          + (rationalInsertSortedCounted x (rationalInsertionSortCounted xs).1).2
          ≤ xs.length * xs.length + (rationalInsertionSortCounted xs).1.length := by
            exact Nat.add_le_add ih h2
      _ ≤ xs.length * xs.length + xs.length := by rw [h1]
      _ ≤ (xs.length + 1) * (xs.length + 1) := by
            have h3 : xs.length ≤ xs.length + 1 := Nat.le_succ _
            nlinarith [Nat.succ_le_succ h3]

def nativeRationalMedianOfMeansCounted (payoff : O → ℚ) {K L : ℕ}
    (ω : Fin K → Fin L → O) : ℚ × ℕ × ℕ × ℕ :=
  let groups := List.ofFn fun k : Fin K => nativeRationalFold payoff (List.ofFn (ω k))
  let means := groups.map fun g => g.1 / (L : ℚ)
  let sort := rationalInsertionSortCounted means
  (sort.1.getD (K / 2) 0, (groups.map fun g => g.2.1).sum,
    (groups.map fun g => g.2.2).sum, sort.2)

theorem nativeRationalMedianOfMeansCounted_spec (payoff : O → ℚ) {K L : ℕ}
    (ω : Fin K → Fin L → O) :
    (nativeRationalMedianOfMeansCounted payoff ω).2.1 = K * L ∧
    (nativeRationalMedianOfMeansCounted payoff ω).2.2.1 = K * L ∧
    (nativeRationalMedianOfMeansCounted payoff ω).2.2.2 ≤ K * K := by
  have hfold : ∀ k : Fin K, (nativeRationalFold payoff (List.ofFn (ω k))).2.1 = L := by
    intro k
    have h := nativeRationalFold_spec payoff (List.ofFn (ω k))
    rw [h.2.1]
    simp
  have hfold3 : ∀ k : Fin K, (nativeRationalFold payoff (List.ofFn (ω k))).2.2 = L := by
    intro k
    have h := nativeRationalFold_spec payoff (List.ofFn (ω k))
    rw [h.2.2]
    simp
  have hmeans : ((List.ofFn fun k : Fin K => nativeRationalFold payoff (List.ofFn (ω k))).map
      fun g => g.1 / (L : ℚ)).length = K := by
    simp
  have hsort : (rationalInsertionSortCounted
      ((List.ofFn fun k : Fin K => nativeRationalFold payoff (List.ofFn (ω k))).map
        fun g => g.1 / (L : ℚ))).2 ≤ K * K := by
    have := rationalInsertionSortCounted_cost_le
      ((List.ofFn fun k : Fin K => nativeRationalFold payoff (List.ofFn (ω k))).map
        fun g => g.1 / (L : ℚ))
    rw [hmeans] at this
    exact this
  have hsumreads : (∑ k : Fin K, (nativeRationalFold payoff (List.ofFn (ω k))).2.1)
      = K * L := by
    calc
      (∑ k : Fin K, (nativeRationalFold payoff (List.ofFn (ω k))).2.1)
          = ∑ _k : Fin K, L := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [hfold k]
      _ = K * L := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              simp
  have hsumadds : (∑ k : Fin K, (nativeRationalFold payoff (List.ofFn (ω k))).2.2)
      = K * L := by
    calc
      (∑ k : Fin K, (nativeRationalFold payoff (List.ofFn (ω k))).2.2)
          = ∑ _k : Fin K, L := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [hfold3 k]
      _ = K * L := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              simp
  refine ⟨?_, ?_, hsort⟩
  · simp only [nativeRationalMedianOfMeansCounted]
    have hm : List.map (fun g => g.2.1)
        (List.ofFn fun k : Fin K => nativeRationalFold payoff (List.ofFn (ω k)))
        = List.ofFn (fun k : Fin K => (nativeRationalFold payoff (List.ofFn (ω k))).2.1) := by
      exact List.map_ofFn
    rw [hm, List.sum_ofFn (M := ℕ)]
    exact hsumreads
  · simp only [nativeRationalMedianOfMeansCounted]
    have hm : List.map (fun g => g.2.2)
        (List.ofFn fun k : Fin K => nativeRationalFold payoff (List.ofFn (ω k)))
        = List.ofFn (fun k : Fin K => (nativeRationalFold payoff (List.ofFn (ω k))).2.2) := by
      exact List.map_ofFn
    rw [hm, List.sum_ofFn (M := ℕ)]
    exact hsumadds

theorem sum_map_const_nat {A : Type} (l : List A) (c : ℕ) (f : A → ℕ) (h : ∀ a, f a = c) :
    (l.map f).sum = c * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, h a, ih, List.length_cons]
    ring

noncomputable def nativeQuantumCounts {K L : ℕ} (c : NativeCampaign K L) : ℕ × ℕ × ℕ × ℕ :=
  let flat := campaignFlatten c.records
  (flat.length,
    (flat.map (fun o => (ensembleAxisLeaf (pauliBasisMatrix o.1) o.2).gates)).sum,
    (flat.map (fun o => (ensembleAxisLeaf (pauliBasisMatrix o.1) o.2).measurements)).sum,
    (flat.map (fun o => (ensembleAxisLeaf (pauliBasisMatrix o.1) o.2).queries)).sum)

theorem nativeQuantumCounts_spec {K L : ℕ} (c : NativeCampaign K L) :
    nativeQuantumCounts c = (K * L, 2 * (K * L), K * L, 0) := by
  have hlen : (campaignFlatten c.records).length = K * L :=
    campaignFlatten_length c.records
  have hleafg (o : (Fin 3 × Fin 2)) :
      (ensembleAxisLeaf (pauliBasisMatrix o.1) o.2).gates = 2 := by
    rw [ensembleAxisLeaf_eq]
  have hleafm (o : (Fin 3 × Fin 2)) :
      (ensembleAxisLeaf (pauliBasisMatrix o.1) o.2).measurements = 1 := by
    rw [ensembleAxisLeaf_eq]
  have hleafq (o : (Fin 3 × Fin 2)) :
      (ensembleAxisLeaf (pauliBasisMatrix o.1) o.2).queries = 0 := by
    rw [ensembleAxisLeaf_eq]
  simp only [nativeQuantumCounts]
  rw [sum_map_const_nat _ 2 _ hleafg]
  rw [sum_map_const_nat _ 1 _ hleafm]
  rw [sum_map_const_nat _ 0 _ hleafq]
  rw [hlen]
  simp

noncomputable def nativeAxisCostAux (hist : List (Fin 3 × Fin 2)) :
    List (Fin 3 × Fin 2) → ℕ
  | [] => 0
  | o :: os => nativeAxisDrawCost o.1 + nativeAxisSelectionCost hist
      + nativeAxisCostAux (hist ++ [o]) os

noncomputable def nativeAxisCost {K L : ℕ} (c : NativeCampaign K L) : ℕ :=
  nativeAxisCostAux [] (campaignFlatten c.records)

theorem nativeAxisCostAux_le (hist : List (Fin 3 × Fin 2)) (l : List (Fin 3 × Fin 2)) :
    nativeAxisCostAux hist l
      ≤ l.length * (nativeAxisTable.length + nativeAxisTable.length) := by
  induction l generalizing hist with
  | nil => simp [nativeAxisCostAux]
  | cons o os ih =>
    simp only [nativeAxisCostAux]
    have h1 := nativeAxisDrawCost_le o.1
    have h2 := nativeAxisSelectionCost_le hist
    calc
      nativeAxisDrawCost o.1 + nativeAxisSelectionCost hist
          + nativeAxisCostAux (hist ++ [o]) os
          ≤ nativeAxisTable.length + nativeAxisTable.length
              + (os.length * (nativeAxisTable.length + nativeAxisTable.length)) := by
            exact Nat.add_le_add (Nat.add_le_add h1 h2) (ih (hist ++ [o]))
      _ = (os.length + 1) * (nativeAxisTable.length + nativeAxisTable.length) := by ring
      _ = (o :: os).length * (nativeAxisTable.length + nativeAxisTable.length) := by simp

theorem nativeAxisCost_le {K L : ℕ} (c : NativeCampaign K L) :
    nativeAxisCost c
      ≤ (campaignFlatten c.records).length
          * (nativeAxisTable.length + nativeAxisTable.length) :=
  nativeAxisCostAux_le [] (campaignFlatten c.records)

structure NativeMachine where

  addressBits : ℕ

  wordBits : ℕ

  comparisonBits : ℕ

  additionBits : ℕ

  axisDrawBits : ℕ

  recordBits : ℕ

structure NativeLedger where

  copies : ℕ

  gates : ℕ

  measurements : ℕ

  queries : ℕ

  axisDraws : ℕ

  axisDrawBits : ℕ

  axisComparisons : ℕ

  tableReads : ℕ

  statisticReads : ℕ

  rationalAdditions : ℕ

  medianComparisons : ℕ

  bitTime : ℕ

  peakSpace : ℕ

noncomputable def nativeLedger {K L : ℕ} (c : NativeCampaign K L) (m : NativeMachine) :
    NativeLedger :=
  let copies := (nativeQuantumCounts c).1
  let gates := (nativeQuantumCounts c).2.1
  let measurements := (nativeQuantumCounts c).2.2.1
  let queries := (nativeQuantumCounts c).2.2.2
  let axisDraws := (campaignFlatten c.records).length
  let axisDrawBits := m.axisDrawBits
  let axisComparisons := nativeAxisCost c
  let tableReads := (nativeRationalMedianOfMeansCounted nativePayoff c.records).2.1
  let statisticReads := (nativeRationalMedianOfMeansCounted nativePayoff c.records).2.1
  let rationalAdditions := (nativeRationalMedianOfMeansCounted nativePayoff c.records).2.2.1
  let medianComparisons := (nativeRationalMedianOfMeansCounted nativePayoff c.records).2.2.2
  { copies := copies
    gates := gates
    measurements := measurements
    queries := queries
    axisDraws := axisDraws
    axisDrawBits := axisDrawBits
    axisComparisons := axisComparisons
    tableReads := tableReads
    statisticReads := statisticReads
    rationalAdditions := rationalAdditions
    medianComparisons := medianComparisons
    bitTime := axisDraws * axisDrawBits
        + axisComparisons * m.comparisonBits
        + tableReads * (m.addressBits + m.wordBits)
        + statisticReads * m.wordBits
        + rationalAdditions * m.additionBits
        + medianComparisons * m.comparisonBits
    peakSpace := (campaignFlatten c.records).length * m.recordBits
        + K * m.wordBits + K * m.wordBits }

theorem nativeLedger_spec {K L : ℕ} (c : NativeCampaign K L) (m : NativeMachine) :
    (nativeLedger c m).copies = K * L ∧
    (nativeLedger c m).gates = 2 * (K * L) ∧
    (nativeLedger c m).measurements = K * L ∧
    (nativeLedger c m).queries = 0 ∧
    (nativeLedger c m).axisDraws = (campaignFlatten c.records).length ∧
    (nativeLedger c m).tableReads = (campaignFlatten c.records).length ∧
    (nativeLedger c m).statisticReads = (campaignFlatten c.records).length ∧
    (nativeLedger c m).rationalAdditions = (campaignFlatten c.records).length ∧
    (nativeLedger c m).medianComparisons ≤ K * K ∧
    (nativeLedger c m).axisComparisons
        ≤ (campaignFlatten c.records).length
            * (nativeAxisTable.length + nativeAxisTable.length) ∧
    (nativeLedger c m).bitTime
        = (nativeLedger c m).axisDraws * m.axisDrawBits
          + (nativeLedger c m).axisComparisons * m.comparisonBits
          + (nativeLedger c m).tableReads * (m.addressBits + m.wordBits)
          + (nativeLedger c m).statisticReads * m.wordBits
          + (nativeLedger c m).rationalAdditions * m.additionBits
          + (nativeLedger c m).medianComparisons * m.comparisonBits ∧
    (nativeLedger c m).peakSpace
        = (campaignFlatten c.records).length * m.recordBits
          + K * m.wordBits + K * m.wordBits := by
  have hq := nativeQuantumCounts_spec c
  have hmed := nativeRationalMedianOfMeansCounted_spec nativePayoff c.records
  have hax := nativeAxisCost_le c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [nativeLedger]
    rw [hq]
  · simp only [nativeLedger]
    rw [hq]
  · simp only [nativeLedger]
    rw [hq]
  · simp only [nativeLedger]
    rw [hq]
  · simp only [nativeLedger]
  · simp only [nativeLedger]
    rw [hmed.1, campaignFlatten_length]
  · simp only [nativeLedger]
    rw [hmed.1, campaignFlatten_length]
  · simp only [nativeLedger]
    rw [hmed.2.1, campaignFlatten_length]
  · simp only [nativeLedger]
    exact hmed.2.2
  · simp only [nativeLedger]
    exact hax
  · simp only [nativeLedger]
  · simp only [nativeLedger]

end MeasurementStatisticsNative
end Qatlib.Concepts.MbqcFlow.FlowDecision
