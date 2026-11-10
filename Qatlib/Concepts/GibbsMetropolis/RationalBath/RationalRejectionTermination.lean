/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.RationalReject.RationalRejectionSampling
set_option warningAsError false

open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.GibbsMetropolis.RationalBath

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped ENNReal Classical

section Termination

variable {N : ℕ}

noncomputable def rationalTerminalMass (w : Fin N → ℕ) (b : ℕ) (j : Fin N) : ℝ≥0∞ :=
  ∑' t : ℕ, rationalFirstStop w b t j

noncomputable def rationalStopMass (w : Fin N → ℕ) (b : ℕ) (z : Fin N × ℕ) : ℝ≥0∞ :=
  if z.2 = 0 then 0 else rationalFirstStop w b (z.2 - 1) z.1

private theorem rational_reject_le_one (w : Fin N → ℕ) (b : ℕ) :
    rationalRejectMass w b ≤ 1 := by
  have hmul : rationalRejectMass w b * ((2 ^ b : ℕ) : ℝ≥0∞)
      = ((2 ^ b - weightTotal w : ℕ) : ℝ≥0∞) := by
    rw [rationalRejectMass, coinRejectMass, div_eq_mul_inv, mul_assoc,
      ENNReal.inv_mul_cancel
        (by exact ne_of_gt (by exact_mod_cast Nat.two_pow_pos b)) (by simp), mul_one]
  calc rationalRejectMass w b
      = ((2 ^ b - weightTotal w : ℕ) : ℝ≥0∞) / ((2 ^ b : ℕ) : ℝ≥0∞) := by
        rw [rationalRejectMass, coinRejectMass]
    _ ≤ ((2 ^ b : ℕ) : ℝ≥0∞) / ((2 ^ b : ℕ) : ℝ≥0∞) :=
        ENNReal.div_le_div (Nat.cast_le.mpr (Nat.sub_le _ _)) le_rfl
    _ = 1 := by
        rw [div_eq_mul_inv, ENNReal.mul_inv_cancel
          (by exact ne_of_gt (by exact_mod_cast Nat.two_pow_pos b)) (by simp)]

private theorem rational_one_sub_reject (w : Fin N → ℕ) (b : ℕ)
    (hb : weightTotal w ≤ 2 ^ b) :
    1 - rationalRejectMass w b =
      (weightTotal w : ℝ≥0∞) * ((2 ^ b : ℕ) : ℝ≥0∞)⁻¹ := by
  have htop : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ ⊤ := by simp
  have hadd : (weightTotal w : ℝ≥0∞) * ((2 ^ b : ℕ) : ℝ≥0∞)⁻¹
      + rationalRejectMass w b = 1 := by
    rw [rationalRejectMass, coinRejectMass, div_eq_mul_inv, ← add_mul, ← Nat.cast_add]
    have hw : ((weightTotal w + (2 ^ b - weightTotal w : ℕ) : ℕ) : ℝ≥0∞)
        = ((2 ^ b : ℕ) : ℝ≥0∞) := by
      congr 1
      omega
    rw [hw, ENNReal.mul_inv_cancel (a := ((2 ^ b : ℕ) : ℝ≥0∞))
      (Nat.cast_ne_zero.mpr (ne_of_gt (Nat.two_pow_pos b))) htop]
  have hqtop : rationalRejectMass w b ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (rational_reject_le_one w b) (by simp))
  exact (ENNReal.eq_sub_of_add_eq hqtop hadd).symm

private theorem rational_reject_lt_one (w : Fin N → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) :
    rationalRejectMass w b < 1 := by
  rw [← tsub_pos_iff_lt, rational_one_sub_reject w b hb]
  have hWne : (weightTotal w : ℝ≥0∞) ≠ 0 := by positivity
  have hDtop : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ ⊤ := by simp
  exact ENNReal.mul_pos hWne (ENNReal.inv_ne_zero.mpr hDtop)

private theorem rational_first_stop_formula (w : Fin N → ℕ) (b t : ℕ) (j : Fin N)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) :
    rationalFirstStop w b t j = (rationalRejectMass w b) ^ t *
      ((w j : ℝ≥0∞) / ((2 ^ b : ℕ) : ℝ≥0∞)) := by
  calc rationalFirstStop w b t j
      = ((rationalRejectMass w b) ^ t * (w j : ℝ≥0∞)) /
          ((2 ^ b : ℕ) : ℝ≥0∞) :=
        (rational_finite_return_pending_and_first_stop N w b (t + 1) hW hb).2.2 t j |>.1
    _ = (rationalRejectMass w b) ^ t *
          ((w j : ℝ≥0∞) / ((2 ^ b : ℕ) : ℝ≥0∞)) := by
            exact mul_div_assoc _ _ _

private theorem rational_terminal_mass_eq_ratio (w : Fin N → ℕ) (b : ℕ) (j : Fin N)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) :
    rationalTerminalMass w b j = (w j : ℝ≥0∞) / (weightTotal w : ℝ≥0∞) := by
  have hq : rationalRejectMass w b < 1 := rational_reject_lt_one w b hW hb
  have hD0 : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  have hW0 : (weightTotal w : ℝ≥0∞) ≠ 0 := by positivity
  have hWtop : (weightTotal w : ℝ≥0∞) ≠ ⊤ := by simp
  calc rationalTerminalMass w b j
      = ∑' t : ℕ, (rationalRejectMass w b) ^ t *
          ((w j : ℝ≥0∞) / ((2 ^ b : ℕ) : ℝ≥0∞)) := by
        unfold rationalTerminalMass
        exact tsum_congr fun t => rational_first_stop_formula w b t j hW hb
    _ = ((w j : ℝ≥0∞) / ((2 ^ b : ℕ) : ℝ≥0∞)) *
          ((1 - rationalRejectMass w b)⁻¹) := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, mul_comm]
    _ = (w j : ℝ≥0∞) / (weightTotal w : ℝ≥0∞) := by
        rw [← div_eq_mul_inv, rational_one_sub_reject w b hb]
        rw [div_eq_mul_inv]
        have hDinv0 : ((2 ^ b : ℕ) : ℝ≥0∞)⁻¹ ≠ 0 :=
          ENNReal.inv_ne_zero.mpr (by simp)
        have hDinvtop : ((2 ^ b : ℕ) : ℝ≥0∞)⁻¹ ≠ ⊤ :=
          ENNReal.inv_ne_top.mpr hD0
        exact ENNReal.mul_div_mul_right _ _ hDinv0 hDinvtop

private theorem rational_stop_masses_sum_one (w : Fin N → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) :
    (∑ j : Fin N, rationalTerminalMass w b j) = 1 := by
  rw [Finset.sum_congr rfl (fun j _ => rational_terminal_mass_eq_ratio w b j hW hb)]
  calc ∑ j : Fin N, (w j : ℝ≥0∞) / (weightTotal w : ℝ≥0∞)
      = (∑ j : Fin N, (w j : ℝ≥0∞)) * (weightTotal w : ℝ≥0∞)⁻¹ := by
          simp only [div_eq_mul_inv]
          rw [← Finset.sum_mul]
    _ = (weightTotal w : ℝ≥0∞) * (weightTotal w : ℝ≥0∞)⁻¹ := by
          rw [← Nat.cast_sum, weightTotal]
    _ = 1 := ENNReal.mul_inv_cancel (by positivity) (by simp)

noncomputable def rationalStopLaw (w : Fin N → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) : PMF (Fin N × ℕ) := by
  let mass : Fin N × ℕ → ℝ≥0∞ := rationalStopMass w b
  have hmass : ∑' z : Fin N × ℕ, mass z = 1 := by
    rw [tsum_prod_type', tsum_fintype]
    have hinner (j : Fin N) : ∑' t : ℕ, mass (j, t) = rationalTerminalMass w b j := by
      rw [tsum_eq_zero_add' ENNReal.summable]
      simp [mass, rationalStopMass, rationalTerminalMass]
    rw [Finset.sum_congr rfl (fun j _ => hinner j)]
    exact rational_stop_masses_sum_one w b hW hb
  have hs : HasSum mass 1 := by
    have hs' : HasSum mass (∑' z : Fin N × ℕ, mass z) := ENNReal.summable.hasSum
    simpa [hmass] using hs'
  exact ⟨mass, hs⟩

@[simp] theorem rationalStopLaw_apply (w : Fin N → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) (z : Fin N × ℕ) :
    rationalStopLaw w b hW hb z = rationalStopMass w b z := rfl

theorem rational_unbounded_actual_first_stop_law (N : ℕ) (w : Fin N → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) :
    (rationalRejectMass w b < 1) ∧
    (∑ j : Fin N, rationalTerminalMass w b j) = 1 ∧
    (∀ j : Fin N, rationalTerminalMass w b j = ∑' t : ℕ, rationalFirstStop w b t j ∧
      rationalTerminalMass w b j = (w j : ℝ≥0∞) / (weightTotal w : ℝ≥0∞) ∧
      Monotone (fun fuel : ℕ => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rationalRejectionRun w b fuel)
        (fun z => rejectionOutcome z.1 = Sum.inl j)) ∧
      Filter.Tendsto (fun fuel : ℕ => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rationalRejectionRun w b fuel)
        (fun z => rejectionOutcome z.1 = Sum.inl j)) Filter.atTop
        (nhds (rationalTerminalMass w b j))) ∧
    Filter.Tendsto (fun fuel : ℕ => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rationalRejectionRun w b fuel)
      (fun z => rejectionOutcome z.1 = Sum.inr ())) Filter.atTop (nhds (0 : ℝ≥0∞)) ∧
    (∀ j : Fin N, rationalStopLaw w b hW hb (j, 0) = 0 ∧
      ∀ t : ℕ, rationalStopLaw w b hW hb (j, t + 1) = rationalFirstStop w b t j) := by
  have hq1 : rationalRejectMass w b ≤ 1 := rational_reject_le_one w b
  have hq : rationalRejectMass w b < 1 := rational_reject_lt_one w b hW hb
  have hpow : Filter.Tendsto (fun fuel : ℕ => (rationalRejectMass w b) ^ fuel)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq
  have hsuccess (j : Fin N) (fuel : ℕ) :
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rationalRejectionRun w b fuel)
        (fun z => rejectionOutcome z.1 = Sum.inl j) =
      (w j : ℝ≥0∞) / (weightTotal w : ℝ≥0∞) *
        (1 - (rationalRejectMass w b) ^ fuel) :=
    (rational_finite_return_pending_and_first_stop N w b fuel hW hb).2.1 j
  have hterm (j : Fin N) :
      rationalTerminalMass w b j = (w j : ℝ≥0∞) / (weightTotal w : ℝ≥0∞) :=
    rational_terminal_mass_eq_ratio w b j hW hb
  refine ⟨hq, rational_stop_masses_sum_one w b hW hb, ?_, ?_, ?_⟩
  · intro j
    refine ⟨rfl, hterm j, ?_, ?_⟩
    · intro fuel₁ fuel₂ hle
      have hpowle : (rationalRejectMass w b) ^ fuel₂ ≤
          (rationalRejectMass w b) ^ fuel₁ := by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
        rw [pow_add]
        calc (rationalRejectMass w b) ^ fuel₁ *
              (rationalRejectMass w b) ^ k
            ≤ (rationalRejectMass w b) ^ fuel₁ * 1 :=
                by
                  gcongr
                  exact pow_le_one₀
                    (by positivity : (0 : ℝ≥0∞) ≤ rationalRejectMass w b) hq1
          _ = (rationalRejectMass w b) ^ fuel₁ := by simp
      calc Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rationalRejectionRun w b fuel₁)
            (fun z => rejectionOutcome z.1 = Sum.inl j)
          = (w j : ℝ≥0∞) / (weightTotal w : ℝ≥0∞) *
              (1 - (rationalRejectMass w b) ^ fuel₁) := hsuccess j fuel₁
        _ ≤ (w j : ℝ≥0∞) / (weightTotal w : ℝ≥0∞) *
              (1 - (rationalRejectMass w b) ^ fuel₂) :=
              by
                gcongr
        _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rationalRejectionRun w b fuel₂)
              (fun z => rejectionOutcome z.1 = Sum.inl j) := (hsuccess j fuel₂).symm
    · have hsub : Filter.Tendsto
          (fun fuel : ℕ => 1 - (rationalRejectMass w b) ^ fuel)
          Filter.atTop (nhds (1 : ℝ≥0∞)) := by
        have h := ENNReal.Tendsto.sub
          (tendsto_const_nhds : Filter.Tendsto
            (fun _ : ℕ => (1 : ℝ≥0∞)) Filter.atTop (nhds 1))
          hpow (Or.inl (by simp : (1 : ℝ≥0∞) ≠ ⊤))
        simpa using h
      have hmul : Filter.Tendsto
          (fun fuel : ℕ => ((w j : ℝ≥0∞) / (weightTotal w : ℝ≥0∞)) *
            (1 - (rationalRejectMass w b) ^ fuel))
          Filter.atTop (nhds ((w j : ℝ≥0∞) / (weightTotal w : ℝ≥0∞))) := by
        let p : ℝ≥0∞ := (w j : ℝ≥0∞) / (weightTotal w : ℝ≥0∞)
        have hp : Filter.Tendsto (fun _ : ℕ => p) Filter.atTop (nhds p) :=
          tendsto_const_nhds
        simpa [p] using ENNReal.Tendsto.mul hp
          (Or.inr (by simp : (1 : ℝ≥0∞) ≠ ⊤)) hsub
          (Or.inl (by simp : (1 : ℝ≥0∞) ≠ 0))
      have hevent : (fun fuel : ℕ => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rationalRejectionRun w b fuel)
          (fun z => rejectionOutcome z.1 = Sum.inl j)) =
          fun fuel => ((w j : ℝ≥0∞) / (weightTotal w : ℝ≥0∞)) *
            (1 - (rationalRejectMass w b) ^ fuel) := funext (hsuccess j)
      rw [hevent]
      simpa [hterm j] using hmul
  · have hevent : (fun fuel : ℕ => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rationalRejectionRun w b fuel)
        (fun z => rejectionOutcome z.1 = Sum.inr ())) =
        fun fuel => (rationalRejectMass w b) ^ fuel := by
      funext fuel
      exact (rational_finite_return_pending_and_first_stop N w b fuel hW hb).1
    rw [hevent]
    exact hpow
  · intro j
    refine ⟨by simp [rationalStopMass], ?_⟩
    intro t
    simp [rationalStopMass]

private theorem geometric_succ_moment (q : ℝ≥0∞) :
    (∑' t : ℕ, q^t * (t+1 : ℝ≥0∞)) = (1-q)⁻¹ * (1-q)⁻¹ := by
  calc
    (∑' t : ℕ, q^t * (t+1 : ℝ≥0∞)) =
        ∑' t : ℕ, ∑ p ∈ Finset.antidiagonal t, q^p.1 * q^p.2 := by
      apply tsum_congr
      intro t
      rw [Finset.sum_congr rfl (fun p hp => by
        rw [← pow_add, Finset.mem_antidiagonal.mp hp]), Finset.sum_const,
        Finset.Nat.card_antidiagonal]
      simp [nsmul_eq_mul, mul_comm]
    _ = ∑' p : ℕ × ℕ, q^p.1 * q^p.2 := by
      rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq]
      rw [ENNReal.tsum_sigma']
      apply tsum_congr
      intro t
      change (∑ p ∈ Finset.antidiagonal t, q^p.1 * q^p.2) =
        ∑' p : ↥(Finset.antidiagonal t), q^p.val.1 * q^p.val.2
      rw [tsum_fintype]
      exact (Finset.sum_finset_coe (fun p : ℕ × ℕ => q^p.1 * q^p.2)
        (Finset.antidiagonal t)).symm
    _ = (1-q)⁻¹ * (1-q)⁻¹ := by
      rw [tsum_prod_type']
      simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]

private theorem geometric_nat_moment (q : ℝ≥0∞) :
    (∑' t : ℕ, q^t * (t : ℝ≥0∞)) = q * ((1-q)⁻¹ * (1-q)⁻¹) := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, mul_zero, zero_add, pow_succ', Nat.cast_add, Nat.cast_one]
  simp_rw [mul_assoc]
  rw [ENNReal.tsum_mul_left, geometric_succ_moment]

theorem rationalStopLaw_expectation (w : Fin N → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2^b)
    (f : Fin N × ℕ → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalStopLaw w b hW hb) f =
      ∑ j : Fin N, ∑' t : ℕ,
        (rationalRejectMass w b)^t * ((w j : ℝ≥0∞)/((2^b : ℕ) : ℝ≥0∞)) * f (j,t+1) := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  rw [tsum_prod_type', tsum_fintype]
  apply Finset.sum_congr rfl
  intro j _
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [rationalStopLaw_apply, rationalStopMass, if_true, zero_mul, zero_add,
    Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, Nat.add_sub_cancel,
    rational_first_stop_formula w b _ j hW hb]

private theorem rationalStopLaw_affine (w : Fin N → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2^b)
    (a : ℝ≥0∞) (c : Fin N → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalStopLaw w b hW hb)
      (fun z => a * (z.2-1 : ℕ) + c z.1) =
      (a * rationalRejectMass w b +
        ∑ j : Fin N, ((w j : ℝ≥0∞)/((2^b : ℕ) : ℝ≥0∞)) * c j) /
        (1-rationalRejectMass w b) := by
  let q := rationalRejectMass w b
  let s := 1-q
  let p := fun j : Fin N => (w j : ℝ≥0∞)/((2^b : ℕ) : ℝ≥0∞)
  have hs : s ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr (rational_reject_lt_one w b hW hb))
  have hst : s ≠ ⊤ := ne_of_lt (lt_of_le_of_lt tsub_le_self (by simp))
  have hsum : (∑ j : Fin N, p j) = s := by
    simp only [p, div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum]
    exact (rational_one_sub_reject w b hb).symm
  rw [rationalStopLaw_expectation]
  simp only [Nat.add_sub_cancel, mul_add, ENNReal.tsum_add]
  have hinner (j : Fin N) :
      (∑' t : ℕ, q^t * p j * (a * (t : ℝ≥0∞))) =
        p j * a * (q * (s⁻¹ * s⁻¹)) := by
    simp_rw [show ∀ t : ℕ, q^t * p j * (a * (t : ℝ≥0∞)) =
      (p j * a) * (q^t * (t : ℝ≥0∞)) from fun t => by ring]
    rw [ENNReal.tsum_mul_left, geometric_nat_moment]
  have hconst (j : Fin N) : (∑' t : ℕ, q^t * p j * c j) = p j * c j * s⁻¹ := by
    simp_rw [mul_assoc]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, mul_comm]
    change p j * c j * s⁻¹ = p j * (c j * s⁻¹)
    ring
  change (∑ j : Fin N, ((∑' t : ℕ, q^t * p j * (a * (t : ℝ≥0∞))) +
      (∑' t : ℕ, q^t * p j * c j))) = _
  simp_rw [hinner, hconst]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    hsum, ← Finset.sum_mul]
  change s * a * (q * (s⁻¹ * s⁻¹)) + (∑ j : Fin N, p j * c j) * s⁻¹ = _
  have hcancel : s * a * (q * (s⁻¹ * s⁻¹)) = a * q * s⁻¹ := by
    calc s * a * (q * (s⁻¹ * s⁻¹)) = a * q * (s * s⁻¹) * s⁻¹ := by ring
      _ = a * q * s⁻¹ := by rw [ENNReal.mul_inv_cancel hs hst, mul_one]
  rw [hcancel, ← add_mul]
  rfl

theorem rational_unbounded_expected_resources_and_limits (N : ℕ) (w : Fin N → ℕ)
    (b : ℕ) (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2^b) :
    let q := rationalRejectMass w b
    let L := rationalStopLaw w b hW hb
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation L (fun z => (z.2 : ℝ≥0∞)) = 1/(1-q) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation L (fun z => ((b*z.2 : ℕ) : ℝ≥0∞)) = (b : ℝ≥0∞)/(1-q) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation L (fun z => ((N*(z.2-1)+z.1.val+1 : ℕ) : ℝ≥0∞)) = rationalMeanComparisons w b/(1-q) ∧
    (b : ℝ≥0∞)/(1-q) < ⊤ ∧ rationalMeanComparisons w b/(1-q) < ⊤ ∧
    Filter.Tendsto (fun fuel : ℕ => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (rationalRejectionRun w b fuel)) Filter.atTop (nhds (1/(1-q))) ∧
    Filter.Tendsto (fun fuel : ℕ => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalRejectionRun w b fuel)
      (fun z => (rejectionBits z.1 : ℝ≥0∞))) Filter.atTop (nhds ((b : ℝ≥0∞)/(1-q))) ∧
    Filter.Tendsto (fun fuel : ℕ => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalRejectionRun w b fuel)
      (fun z => (rejectionComparisons z.1 : ℝ≥0∞))) Filter.atTop (nhds (rationalMeanComparisons w b/(1-q))) := by
  let q := rationalRejectMass w b
  let L := rationalStopLaw w b hW hb
  have hq : q < 1 := rational_reject_lt_one w b hW hb
  have hs : 1-q ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr hq)
  have hsum : (∑ j : Fin N, (w j : ℝ≥0∞)/((2^b : ℕ) : ℝ≥0∞)) + q = 1 := by
    simpa only [next_inl_mass w b hb, next_inr_mass w b hb] using
      rational_rejection_kernel_normalized w b hb
  have htrials : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation L (fun z => (z.2 : ℝ≥0∞)) = 1/(1-q) := by
    have h := rationalStopLaw_affine w b hW hb 1 (fun _ => 1)
    simp only [one_mul, mul_one] at h
    rw [add_comm, hsum] at h
    rw [rationalStopLaw_expectation] at h ⊢
    simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using h
  have hbits : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation L (fun z => ((b*z.2 : ℕ) : ℝ≥0∞)) =
      (b : ℝ≥0∞)/(1-q) := by
    simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, Nat.cast_mul]
    simp_rw [mul_left_comm (L _) (b : ℝ≥0∞)]
    rw [ENNReal.tsum_mul_left]
    change (b : ℝ≥0∞) * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation L
        (fun z => (z.2 : ℝ≥0∞)) = _
    rw [htrials, mul_one_div]
  have hcomps : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation L
      (fun z => ((N*(z.2-1)+z.1.val+1 : ℕ) : ℝ≥0∞)) = rationalMeanComparisons w b/(1-q) := by
    have h := rationalStopLaw_affine w b hW hb (N : ℝ≥0∞) (fun j => (j.val+1 : ℕ))
    have hk := rational_mean_comparisons_kernel w b hb
    simp only [next_inl_mass w b hb, next_inr_mass w b hb] at hk
    rw [mul_comm (N : ℝ≥0∞), add_comm, hk] at h
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, add_assoc] using h
  have hmean : rationalMeanComparisons w b ≠ ⊤ := by
    unfold rationalMeanComparisons
    exact ne_of_lt (ENNReal.div_lt_top (by finiteness) (by positivity))
  have ht := ENNReal.tendsto_nat_tsum (fun t : ℕ => q^t)
  rw [ENNReal.tsum_geometric, ← one_div] at ht
  have hbt := ENNReal.Tendsto.const_mul ht (Or.inr (by simp : (b : ℝ≥0∞) ≠ ⊤))
  have hct := ENNReal.Tendsto.const_mul ht (Or.inr hmean)
  simp only [mul_one_div] at hbt hct
  refine ⟨htrials, hbits, hcomps, ENNReal.div_lt_top (by simp) hs,
    ENNReal.div_lt_top hmean hs, ?_, ?_, ?_⟩
  · convert ht using 1
    funext fuel
    exact (rational_finite_three_resource_expectations N w b fuel hW hb).1
  · convert hbt using 1
    funext fuel
    exact (rational_finite_three_resource_expectations N w b fuel hW hb).2.1
  · convert hct using 1
    funext fuel
    exact (rational_finite_three_resource_expectations N w b fuel hW hb).2.2.1

end Termination
end Qatlib.Concepts.GibbsMetropolis.RationalBath
