/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupDefs
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupEntropy
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.GibbsMetropolis.RationalBath
open Qatlib.Concepts.LindbladFlow.GkslSemigroup
open Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Foundations.DirichletForm.KmsDirichlet
open Qatlib.Concepts.WalkSearch.TwoLevelLower

set_option autoImplicit false

namespace Qatlib.Concepts.LindbladFlow.GkslSemigroup

open Matrix Qatlib

open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal Classical

noncomputable section

variable {D : ℕ}

theorem initialEntropy_nonneg {σ ρ : Operator D}
    (hσ : IsDensityOperator σ) (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef) :
    0 ≤ initialEntropy σ ρ := by
  have h := relativeEntropy_eq_qRelativeEnt hσ hρ hfull
  unfold initialEntropy
  exact ENNReal.toReal_nonneg.trans (le_of_eq h.symm)

private theorem exp_mul_pow (x : ℝ) (n : ℕ) :
    (Real.exp x : ℝ) ^ n = Real.exp (x * (n : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      congr 1
      push_cast
      ring

theorem mixing_initialState (G : GKSL D) {ρ σ : Operator D}
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef)
    (hself : KmsSelfAdjoint ρ (gkslHeisenbergMap G)) (γ : ℝ)
    (hgap : KmsGapAtLeast ρ (gkslHeisenbergMap G) γ)
    (hσ : IsDensityOperator σ) (t : ℝ) (ht : 0 ≤ t) :
    traceDistance (lindbladSemigroup G t σ) ρ ≤
      Real.exp (-γ * t) * initialStateFactor ρ σ / 2 := by
  have h := lindblad_traceDistance_le_of_heisenberg_kmsGap G hρ hfull hself γ hgap hσ t ht
  simpa only [initialStateFactor] using! h

theorem mixing_normalization (G : GKSL D) {ρ σ : Operator D}
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef)
    (hself : KmsSelfAdjoint ρ (gkslHeisenbergMap G)) (γ : ℝ)
    (hgap : KmsGapAtLeast ρ (gkslHeisenbergMap G) γ)
    (hσ : IsDensityOperator σ) (t : ℝ) (ht : 0 ≤ t) :
    traceDistance (lindbladSemigroup G t σ) ρ ≤
      Real.exp (-γ * t) * referenceWeight ρ / 2 := by
  have h := lindblad_traceDistance_le_inverse_sqrt G hρ hfull hself γ hgap hσ t ht
  simpa only [referenceWeight] using! h

private theorem min_mul_div_two (e a b : ℝ) (he : 0 ≤ e) :
    min (e * a / 2) (e * b / 2) = e * min a b / 2 := by
  by_cases hab : a ≤ b
  · rw [min_eq_left hab]
    have hle : e * a / 2 ≤ e * b / 2 := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hab (by positivity)
      · norm_num
    rw [min_eq_left hle]
  · have hba : b ≤ a := le_of_not_ge hab
    rw [min_eq_right hba]
    have hle : e * b / 2 ≤ e * a / 2 := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hba (by positivity)
      · norm_num
    rw [min_eq_right hle]

theorem mixing_combined (G : GKSL D) {ρ σ : Operator D}
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef)
    (hself : KmsSelfAdjoint ρ (gkslHeisenbergMap G)) (γ : ℝ)
    (hgap : KmsGapAtLeast ρ (gkslHeisenbergMap G) γ)
    (hσ : IsDensityOperator σ) (t : ℝ) (ht : 0 ≤ t) :
    traceDistance (lindbladSemigroup G t σ) ρ ≤
      Real.exp (-γ * t) * min (initialStateFactor ρ σ) (referenceWeight ρ) / 2 := by
  have h1 := mixing_initialState G hρ hfull hself γ hgap hσ t ht
  have h2 := mixing_normalization G hρ hfull hself γ hgap hσ t ht
  have hminBound := min_mul_div_two (Real.exp (-γ * t)) (initialStateFactor ρ σ)
    (referenceWeight ρ) (Real.exp_nonneg _)
  exact (le_min h1 h2).trans_eq hminBound

theorem mixing_time_bound (G : GKSL D) {ρ : Operator D}
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef)
    (hself : KmsSelfAdjoint ρ (gkslHeisenbergMap G)) (γ : ℝ) (hγ : 0 < γ)
    (hgap : KmsGapAtLeast ρ (gkslHeisenbergMap G) γ) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    mixingTime G ρ η ≠ ⊤ ∧ (mixingTime G ρ η).toReal ≤
      Real.log ((referenceWeight ρ + 1) / η) / γ := by
  have h := mixingTime_le_inverse_sqrt G hρ hfull hself γ hγ hgap η hη hη1
  simpa only [referenceWeight] using! h

theorem entropyContraction_iterate_aux (G : GKSL D) (ρ : Operator D) (η : ℝ)
    (hcont : EntropyContractionLaw G ρ η) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    ∀ (n : ℕ) (σ : Operator D), IsDensityOperator σ →
      relativeEntropy (lindbladSemigroup G ((n : ℝ) * h) σ) ρ ≤
        (1 - η * h) ^ n * relativeEntropy σ ρ := by
  have hgh : η * h ≤ 1 := by
    have := mul_le_mul hcont.2.1 hh1 (by linarith) (by linarith)
    nlinarith [this]
  have hfac : 0 ≤ 1 - η * h := by linarith
  intro n
  induction n with
  | zero =>
      intro σ hσ
      simp [lindbladSemigroup_zero_apply]
  | succ n ih =>
      intro σ hσ
      have hτ : IsDensityOperator (lindbladSemigroup G ((n : ℝ) * h) σ) := by
        exact lindbladSemigroup_isDensityOperator G _ (by positivity) σ hσ
      have hsem : lindbladSemigroup G (((n + 1 : ℕ) : ℝ) * h) σ
          = lindbladSemigroup G h (lindbladSemigroup G ((n : ℝ) * h) σ) := by
        calc lindbladSemigroup G (((n + 1 : ℕ) : ℝ) * h) σ
            = lindbladSemigroup G (h + (n : ℝ) * h) σ := by
              congr 1
              push_cast
              ring
          _ = lindbladSemigroup G h (lindbladSemigroup G ((n : ℝ) * h) σ) :=
            lindbladSemigroup_add G h ((n : ℝ) * h) σ
      rw [hsem]
      have hstep := hcont.2.2 h (lindbladSemigroup G ((n : ℝ) * h) σ) hh hh1 hτ
      have hmul := mul_le_mul_of_nonneg_left (ih σ hσ) hfac
      have hpow : (1 - η * h) ^ n * (1 - η * h) = (1 - η * h) ^ (n + 1) := by
        rw [pow_succ]
      calc relativeEntropy (lindbladSemigroup G h (lindbladSemigroup G ((n : ℝ) * h) σ)) ρ
          ≤ (1 - η * h) * relativeEntropy (lindbladSemigroup G ((n : ℝ) * h) σ) ρ := hstep
        _ ≤ (1 - η * h) * ((1 - η * h) ^ n * relativeEntropy σ ρ) := hmul
        _ = (1 - η * h) ^ (n + 1) * relativeEntropy σ ρ := by
          have hre : (1 - η * h) * ((1 - η * h) ^ n * relativeEntropy σ ρ)
              = ((1 - η * h) ^ n * (1 - η * h)) * relativeEntropy σ ρ := by ring
          rw [hre, hpow]

theorem entropyContraction_exponential (G : GKSL D) (ρ : Operator D) (η : ℝ)
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef)
    (hcont : EntropyContractionLaw G ρ η) (σ : Operator D) (hσ : IsDensityOperator σ)
    (t : ℝ) (ht : 0 ≤ t) :
    relativeEntropy (lindbladSemigroup G t σ) ρ ≤
      Real.exp (-η * t) * relativeEntropy σ ρ := by
  by_cases hzero : t = 0
  · subst hzero
    simp [lindbladSemigroup_zero_apply]
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    have hn1 : 1 ≤ ⌈t⌉₊ := Nat.ceil_pos.mpr htpos
    have hnge : t ≤ (⌈t⌉₊ : ℝ) :=
      (Nat.ceil_le (a := t) (n := ⌈t⌉₊)).mp le_rfl
    have hnpos : (0 : ℝ) < ⌈t⌉₊ := by exact_mod_cast hn1
    have hhpos : 0 < t / ⌈t⌉₊ := div_pos htpos hnpos
    have hhle : t / ⌈t⌉₊ ≤ 1 := (div_le_one hnpos).mpr hnge
    have hiter := entropyContraction_iterate_aux G ρ η hcont hhpos hhle
      (⌈t⌉₊) σ hσ
    have hnh : (⌈t⌉₊ : ℝ) * (t / ⌈t⌉₊) = t := by
      field_simp
    rw [hnh] at hiter
    have hgh : η * (t / ⌈t⌉₊) ≤ 1 := by
      have := mul_le_mul hcont.2.1 hhle (by linarith) (by linarith)
      nlinarith [this]
    have hfac : 0 ≤ 1 - η * (t / ⌈t⌉₊) := by linarith
    have hcmp : 1 - η * (t / ⌈t⌉₊) ≤ Real.exp (-(η * (t / ⌈t⌉₊))) := by
      have := Real.add_one_le_exp (-(η * (t / ⌈t⌉₊)))
      linarith
    have hpow : (1 - η * (t / ⌈t⌉₊)) ^ ⌈t⌉₊ ≤
        Real.exp (-(η * (t / ⌈t⌉₊))) ^ ⌈t⌉₊ :=
      pow_le_pow_left₀ hfac hcmp _
    have hexp : Real.exp (-(η * (t / ⌈t⌉₊))) ^ ⌈t⌉₊ = Real.exp (-η * t) := by
      have he : (⌈t⌉₊ : ℝ) * (-(η * (t / ⌈t⌉₊))) = -η * t := by
        calc (⌈t⌉₊ : ℝ) * (-(η * (t / ⌈t⌉₊))) = -(η * ((⌈t⌉₊ : ℝ) * (t / ⌈t⌉₊))) := by ring
          _ = -(η * t) := by rw [hnh]
          _ = -η * t := by ring
      have hthis := (Real.exp_nat_mul (-(η * (t / ⌈t⌉₊))) ⌈t⌉₊).symm
      rw [he] at hthis
      exact hthis
    rw [hexp] at hpow
    have hS0 : 0 ≤ relativeEntropy σ ρ := initialEntropy_nonneg hσ hρ hfull
    have hmul := mul_le_mul_of_nonneg_right hpow hS0
    calc relativeEntropy (lindbladSemigroup G t σ) ρ
        ≤ (1 - η * (t / ⌈t⌉₊)) ^ ⌈t⌉₊ * relativeEntropy σ ρ := hiter
      _ ≤ Real.exp (-η * t) * relativeEntropy σ ρ := hmul

theorem entropyStep_iterate_aux (G : GKSL D) (ρ : Operator D) (η : ℝ)
    (hcont : EntropyStepLaw G ρ η) :
    ∀ (n : ℕ) (σ : Operator D), IsDensityOperator σ →
      relativeEntropy (lindbladSemigroup G (n : ℝ) σ) ρ ≤
        (1 - η) ^ n * relativeEntropy σ ρ := by
  have hfac : 0 ≤ 1 - η := by linarith [hcont.2.1]
  intro n
  induction n with
  | zero =>
      intro σ hσ
      simp [lindbladSemigroup_zero_apply]
  | succ n ih =>
      intro σ hσ
      have hτ : IsDensityOperator (lindbladSemigroup G (n : ℝ) σ) := by
        exact lindbladSemigroup_isDensityOperator G _ (by positivity) σ hσ
      have hsem : lindbladSemigroup G ((n + 1 : ℕ) : ℝ) σ
          = lindbladSemigroup G 1 (lindbladSemigroup G (n : ℝ) σ) := by
        calc lindbladSemigroup G ((n + 1 : ℕ) : ℝ) σ
            = lindbladSemigroup G (1 + (n : ℝ)) σ := by
              congr 1
              push_cast
              ring
          _ = lindbladSemigroup G 1 (lindbladSemigroup G (n : ℝ) σ) :=
            lindbladSemigroup_add G 1 (n : ℝ) σ
      rw [hsem]
      have hstep := hcont.2.2 (lindbladSemigroup G (n : ℝ) σ) hτ
      have hmul := mul_le_mul_of_nonneg_left (ih σ hσ) hfac
      have hpow : (1 - η) ^ n * (1 - η) = (1 - η) ^ (n + 1) := by
        rw [pow_succ]
      calc relativeEntropy (lindbladSemigroup G 1 (lindbladSemigroup G (n : ℝ) σ)) ρ
          ≤ (1 - η) * relativeEntropy (lindbladSemigroup G (n : ℝ) σ) ρ := hstep
        _ ≤ (1 - η) * ((1 - η) ^ n * relativeEntropy σ ρ) := hmul
        _ = (1 - η) ^ (n + 1) * relativeEntropy σ ρ := by
          have hre : (1 - η) * ((1 - η) ^ n * relativeEntropy σ ρ)
              = ((1 - η) ^ n * (1 - η)) * relativeEntropy σ ρ := by ring
          rw [hre, hpow]

theorem entropyContraction_unitStep (G : GKSL D) (ρ : Operator D) (η : ℝ)
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef)
    (hstationary : Qatlib.Concepts.LindbladFlow.GkslSemigroup.IsStationary G ρ)
    (hcont : EntropyStepLaw G ρ η) (σ : Operator D) (hσ : IsDensityOperator σ)
    (t : ℝ) (ht : 1 ≤ t) :
    relativeEntropy (lindbladSemigroup G t σ) ρ ≤
      Real.exp η * Real.exp (-η * t) * relativeEntropy σ ρ := by
  have hiter := entropyStep_iterate_aux G ρ η hcont
  have hnfloor : (Nat.floor t : ℝ) ≤ t := Nat.floor_le (by linarith [ht])
  have hfloor1 : t < (Nat.floor t : ℝ) + 1 := Nat.lt_floor_add_one t
  have hpos : 0 < η := hcont.1
  have hfac : 0 ≤ 1 - η := by linarith [hcont.2.1]
  have hcmp : 1 - η ≤ Real.exp (-η) := by
    have := Real.add_one_le_exp (-η)
    linarith
  have hgeom : ∀ (n : ℕ), (1 - η) ^ n ≤ Real.exp (-(η * (n : ℝ))) := by
    intro n
    have h := pow_le_pow_left₀ hfac hcmp n
    have h2 : (Real.exp (-η) : ℝ) ^ n = Real.exp (-(η * (n : ℝ))) := by
      rw [exp_mul_pow]
      congr 1
      ring
    rw [h2] at h
    exact h
  have hτ : IsDensityOperator (lindbladSemigroup G (Nat.floor t : ℝ) σ) := by
    exact lindbladSemigroup_isDensityOperator G _ (by positivity) σ hσ
  have hsem : lindbladSemigroup G t σ
      = lindbladSemigroup G (t - (Nat.floor t : ℝ)) (lindbladSemigroup G (Nat.floor t : ℝ) σ) := by
    have hsplit : (t - (Nat.floor t : ℝ)) + (Nat.floor t : ℝ) = t := by ring
    calc lindbladSemigroup G t σ
        = lindbladSemigroup G ((t - (Nat.floor t : ℝ)) + (Nat.floor t : ℝ)) σ := by rw [hsplit]
      _ = lindbladSemigroup G (t - (Nat.floor t : ℝ)) (lindbladSemigroup G (Nat.floor t : ℝ) σ) :=
        lindbladSemigroup_add G (t - (Nat.floor t : ℝ)) (Nat.floor t : ℝ) σ
  have hmono := lindbladSemigroup_relativeEntropy_le G hρ hfull hstationary hτ
    (t - (Nat.floor t : ℝ)) (by positivity)
  have hstep : relativeEntropy (lindbladSemigroup G t σ) ρ
      ≤ (1 - η) ^ (Nat.floor t : ℕ) * relativeEntropy σ ρ := by
    rw [hsem]
    calc relativeEntropy (lindbladSemigroup G (t - (Nat.floor t : ℝ))
        (lindbladSemigroup G (Nat.floor t : ℝ) σ)) ρ
        ≤ relativeEntropy (lindbladSemigroup G (Nat.floor t : ℝ) σ) ρ := hmono
      _ ≤ (1 - η) ^ (Nat.floor t : ℕ) * relativeEntropy σ ρ := hiter (Nat.floor t : ℕ) σ hσ
  have hexp1 : Real.exp (-(η * (Nat.floor t : ℝ))) ≤ Real.exp η * Real.exp (-η * t) := by
    have hkey : -(η * (Nat.floor t : ℝ)) ≤ -η * (t - 1) := by
      have hfloor : (Nat.floor t : ℝ) > t - 1 := by linarith [hfloor1]
      nlinarith
    have hexp := Real.exp_le_exp.mpr hkey
    have hid : -η * (t - 1) = η + (-η * t) := by ring
    rw [hid, Real.exp_add] at hexp
    exact hexp
  have hS0 : 0 ≤ relativeEntropy σ ρ := initialEntropy_nonneg hσ hρ hfull
  have hpow := hgeom (Nat.floor t : ℕ)
  have hmul := mul_le_mul_of_nonneg_right hpow hS0
  calc relativeEntropy (lindbladSemigroup G t σ) ρ
      ≤ (1 - η) ^ (Nat.floor t : ℕ) * relativeEntropy σ ρ := hstep
    _ ≤ Real.exp (-(η * (Nat.floor t : ℝ))) * relativeEntropy σ ρ := hmul
    _ ≤ (Real.exp η * Real.exp (-η * t)) * relativeEntropy σ ρ := by
      have h := mul_le_mul_of_nonneg_left hexp1 hS0
      simpa only [mul_comm] using! h

private theorem bernoulli : ∀ (x : ℝ) (n : ℕ), 0 ≤ x → x ≤ 1 →
    (1 - x) ^ n ≥ 1 - (n : ℝ) * x := by
  intro x n
  induction n with
  | zero =>
      intro hx0 hx1
      simp
  | succ n ih =>
      intro hx0 hx1
      rw [pow_succ]
      have h1 : (1 - x) ^ n * (1 - x) ≥ (1 - (n : ℝ) * x) * (1 - x) :=
        mul_le_mul_of_nonneg_right (ih hx0 hx1) (by linarith)
      have hsq : 0 ≤ (n : ℝ) * x ^ 2 := by positivity
      have hid : (1 - (n : ℝ) * x) * (1 - x) = 1 - ((n : ℝ) + 1) * x + (n : ℝ) * x ^ 2 := by
        ring
      have hid2 : ((n : ℝ) + 1) * x = ((n + 1 : ℕ) : ℝ) * x := by
        push_cast
        ring
      linarith [h1, hid, hid2, hsq]

theorem entropyRetained_iterate_aux (G : GKSL D) (ρ : Operator D) (η : ℝ)
    (hcont : RetainedEntropyLaw G ρ η) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    ∀ (n : ℕ) (σ : Operator D), IsDensityOperator σ →
      (1 - η * h) ^ n * relativeEntropy σ ρ ≤
        relativeEntropy (lindbladSemigroup G ((n : ℝ) * h) σ) ρ := by
  have hgh : η * h ≤ 1 := by
    have := mul_le_mul hcont.2.1 hh1 (by linarith) (by linarith)
    nlinarith [this]
  have hfac : 0 ≤ 1 - η * h := by linarith
  intro n
  induction n with
  | zero =>
      intro σ hσ
      simp [lindbladSemigroup_zero_apply]
  | succ n ih =>
      intro σ hσ
      have hτ : IsDensityOperator (lindbladSemigroup G ((n : ℝ) * h) σ) := by
        exact lindbladSemigroup_isDensityOperator G _ (by positivity) σ hσ
      have hsem : lindbladSemigroup G (((n + 1 : ℕ) : ℝ) * h) σ
          = lindbladSemigroup G h (lindbladSemigroup G ((n : ℝ) * h) σ) := by
        calc lindbladSemigroup G (((n + 1 : ℕ) : ℝ) * h) σ
            = lindbladSemigroup G (h + (n : ℝ) * h) σ := by
              congr 1
              push_cast
              ring
          _ = lindbladSemigroup G h (lindbladSemigroup G ((n : ℝ) * h) σ) :=
            lindbladSemigroup_add G h ((n : ℝ) * h) σ
      rw [hsem]
      have hstep := hcont.2.2 h (lindbladSemigroup G ((n : ℝ) * h) σ) hh hh1 hτ
      have hmul := mul_le_mul_of_nonneg_right (ih σ hσ) hfac
      calc (1 - η * h) ^ (n + 1) * relativeEntropy σ ρ
          = ((1 - η * h) ^ n * (1 - η * h)) * relativeEntropy σ ρ := by
            rw [pow_succ]
        _ ≤ (relativeEntropy (lindbladSemigroup G ((n : ℝ) * h) σ) ρ) * (1 - η * h) := by
          convert! hmul using 1; ring
        _ ≤ relativeEntropy (lindbladSemigroup G h (lindbladSemigroup G ((n : ℝ) * h) σ)) ρ := by
          simpa [mul_comm] using! hstep

theorem entropy_retained (G : GKSL D) (ρ : Operator D) (η : ℝ)
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef)
    (hcont : RetainedEntropyLaw G ρ η) (σ : Operator D) (hσ : IsDensityOperator σ)
    (t : ℝ) (ht : 0 ≤ t) :
    (1 - η * t) * relativeEntropy σ ρ ≤ relativeEntropy (lindbladSemigroup G t σ) ρ := by
  by_cases hzero : t = 0
  · subst hzero
    simp [lindbladSemigroup_zero_apply]
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    have hn1 : 1 ≤ ⌈t⌉₊ := Nat.ceil_pos.mpr htpos
    have hnge : t ≤ (⌈t⌉₊ : ℝ) := (Nat.ceil_le (a := t) (n := ⌈t⌉₊)).mp le_rfl
    have hnpos : (0 : ℝ) < ⌈t⌉₊ := by exact_mod_cast hn1
    have hhpos : 0 < t / ⌈t⌉₊ := div_pos htpos hnpos
    have hhle : t / ⌈t⌉₊ ≤ 1 := (div_le_one hnpos).mpr hnge
    have hiter := entropyRetained_iterate_aux G ρ η hcont hhpos hhle (⌈t⌉₊) σ hσ
    have hnh : (⌈t⌉₊ : ℝ) * (t / ⌈t⌉₊) = t := by
      field_simp
    rw [hnh] at hiter
    have hx0 : 0 ≤ η * (t / ⌈t⌉₊) :=
      mul_nonneg (le_of_lt hcont.1) (div_nonneg (le_of_lt htpos) (le_of_lt hnpos))
    have hx1 : η * (t / ⌈t⌉₊) ≤ 1 := by
      have := mul_le_mul hcont.2.1 hhle (by linarith) (by linarith)
      nlinarith [this]
    have hbern := bernoulli (η * (t / ⌈t⌉₊)) (⌈t⌉₊) hx0 hx1
    have hscale : (⌈t⌉₊ : ℝ) * (η * (t / ⌈t⌉₊)) = η * t := by
      field_simp
    rw [hscale] at hbern
    have hS0 : 0 ≤ relativeEntropy σ ρ := initialEntropy_nonneg hσ hρ hfull
    have hmul := mul_le_mul_of_nonneg_left hbern hS0
    calc (1 - η * t) * relativeEntropy σ ρ
        ≤ (1 - η * (t / ⌈t⌉₊)) ^ ⌈t⌉₊ * relativeEntropy σ ρ := by
          simpa only [mul_comm] using! hmul
      _ ≤ relativeEntropy (lindbladSemigroup G t σ) ρ := hiter

theorem entropy_monotone (G : GKSL D) {ρ σ : Operator D}
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef) (hstationary : Qatlib.Concepts.LindbladFlow.GkslSemigroup.IsStationary G ρ)
    (hσ : IsDensityOperator σ) (t : ℝ) (ht : 0 ≤ t) :
    relativeEntropy (lindbladSemigroup G t σ) ρ ≤ relativeEntropy σ ρ :=
  lindbladSemigroup_relativeEntropy_le G hρ hfull hstationary hσ t ht

theorem entropyStepLaw_of_contractionLaw {G : GKSL D} {ρ : Operator D} {η : ℝ}
    (h : EntropyContractionLaw G ρ η) : EntropyStepLaw G ρ η := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro σ hσ
  simpa using! (h.2.2 1 σ (by norm_num) (by norm_num) hσ)

def clause2_endpoint (d : MixingEntropyData D) : MixingEntropyInterface D where
  gen := d.gen
  ref := d.ref
  gapRate := d.gapRate
  entropyRate := d.entropyRate
  mixingInitialState := fun σ hσ t ht =>
    mixing_initialState (σ := σ) d.gen d.refDensity d.refFull d.selfAdj d.gapRate d.gapHyp hσ t ht
  mixingNormalization := fun σ hσ t ht =>
    mixing_normalization (σ := σ) d.gen d.refDensity d.refFull d.selfAdj d.gapRate d.gapHyp hσ t ht
  mixingCombined := fun σ hσ t ht =>
    mixing_combined (σ := σ) d.gen d.refDensity d.refFull d.selfAdj d.gapRate d.gapHyp hσ t ht
  mixingTimeBound := fun η hη hη1 =>
    mixing_time_bound d.gen d.refDensity d.refFull d.selfAdj d.gapRate d.gapPos d.gapHyp
      η hη hη1
  entropyContraction := fun σ hσ t ht =>
    entropyContraction_exponential d.gen d.ref d.entropyRate d.refDensity d.refFull
      d.entropyLaw σ hσ t ht
  entropyUnitStep := fun σ hσ t ht =>
    entropyContraction_unitStep d.gen d.ref d.entropyRate d.refDensity d.refFull
      (stationary_of_heisenberg_kmsSelfAdjoint d.gen d.ref d.refDensity.1 d.selfAdj)
      (entropyStepLaw_of_contractionLaw d.entropyLaw) σ hσ t ht
  entropyMonotone := fun σ hσ t ht =>
    entropy_monotone (σ := σ) d.gen d.refDensity d.refFull
      (stationary_of_heisenberg_kmsSelfAdjoint d.gen d.ref d.refDensity.1 d.selfAdj)
      hσ t ht

theorem mixingEntropyData_rate_independent {d : MixingEntropyData D} {η' : ℝ}
    (hη' : EntropyContractionLaw d.gen d.ref η') :
    ∃ d' : MixingEntropyData D, d'.gapRate = d.gapRate ∧ d'.entropyRate = η' := by
  refine ⟨{ d with entropyRate := η', entropyLaw := hη' }, rfl, rfl⟩

theorem clause2_endpoint_entropy_rate_free {d : MixingEntropyData D} :
    ∀ (η' : ℝ), EntropyContractionLaw d.gen d.ref η' →
      ∃ d' : MixingEntropyData D, d'.gapRate = d.gapRate ∧ d'.entropyRate = η' := by
  intro η' h
  exact mixingEntropyData_rate_independent (d := d) h

theorem ckAcceptJump_eq (E : Fin D → ℝ) (β : ℝ) (i j : Fin D) (hij : i ≠ j) :
    ckAcceptJump E β i j = ((Real.sqrt (thermalAcceptance E β i j) : ℂ)) • ckRankOne i j := by
  simp [ckAcceptJump, hij]

theorem ckAcceptJump_self (E : Fin D → ℝ) (β : ℝ) (i : Fin D) :
    ckAcceptJump E β i i = 0 := by
  simp [ckAcceptJump]

theorem ckAccept_detailedBalance (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) (i j : Fin D) :
    thermalAcceptance E β i j * (diagonalGibbsDist D hD E β).prob i
      = thermalAcceptance E β j i * (diagonalGibbsDist D hD E β).prob j := by
  rw [diagonalGibbsDist_prob, diagonalGibbsDist_prob]
  have h := thermalAcceptance_detailed E β i j
  have hZ : diagonalGibbsPartition D E β ≠ 0 :=
    ne_of_gt (diagonalGibbsPartition_pos D hD E β)
  rw [← mul_div_assoc, ← mul_div_assoc]
  have h' : thermalAcceptance E β i j * Real.exp (-β * E i)
      = thermalAcceptance E β j i * Real.exp (-β * E j) := by
    simpa [mul_comm] using! h
  rw [div_eq_div_iff hZ hZ]
  rw [h']

theorem ckRankOne_target_class (E : Fin D → ℝ) (i j : Fin D) :
    ckEnergyClass E j * ckRankOne i j = ckRankOne i j := by
  ext r c
  rw [ckEnergyClass, Matrix.diagonal_mul]
  by_cases hrc : r = j ∧ c = i
  · obtain ⟨h1, h2⟩ := hrc
    subst h1
    subst h2
    simp [ckRankOne]
  · by_cases h1 : r = j
    · have h2 : c ≠ i := by
        intro hc
        exact hrc ⟨h1, hc⟩
      simp [ckRankOne, h1, h2]
    · simp [ckRankOne, h1]

theorem ckRankOne_source_class (E : Fin D → ℝ) (i j : Fin D) :
    ckRankOne i j * ckEnergyClass E i = ckRankOne i j := by
  ext r c
  rw [ckEnergyClass, Matrix.mul_diagonal]
  by_cases hrc : r = j ∧ c = i
  · obtain ⟨h1, h2⟩ := hrc
    subst h1
    subst h2
    simp [ckRankOne]
  · by_cases h2 : c = i
    · have h1 : r ≠ j := by
        intro hr
        exact hrc ⟨hr, h2⟩
      simp [ckRankOne, h1, h2]
    · simp [ckRankOne, h2]

theorem ckJump_target_class (E : Fin D → ℝ) (β : ℝ) (i j : Fin D) :
    ckEnergyClass E j * ckAcceptJump E β i j = ckAcceptJump E β i j := by
  by_cases hij : i = j
  · subst hij
    simp [ckAcceptJump, ckEnergyClass]
  · rw [ckAcceptJump_eq E β i j hij, Matrix.mul_smul, ckRankOne_target_class E i j]

theorem ckJump_source_class (E : Fin D → ℝ) (β : ℝ) (i j : Fin D) :
    ckAcceptJump E β i j * ckEnergyClass E i = ckAcceptJump E β i j := by
  by_cases hij : i = j
  · subst hij
    simp [ckAcceptJump, ckEnergyClass]
  · rw [ckAcceptJump_eq E β i j hij, Matrix.smul_mul, ckRankOne_source_class E i j]

theorem ckRunReadouts_exceeds_assumed (m nStar D : ℕ) (hns : 4 * D ≤ nStar) (hm : 0 < m) :
    m * (D * 2 * 2) < ckRunReadouts m nStar := by
  have hD2 : D * 2 * 2 = 4 * D := by ring
  rw [hD2, ckRunReadouts, ckStepReadouts]
  calc m * (4 * D) ≤ m * nStar := Nat.mul_le_mul_left m hns
    _ < m * (2 + nStar) := Nat.mul_lt_mul_of_pos_left (by omega) hm

theorem ckRankOne_apply (i j r c : Fin D) :
    ckRankOne i j r c = if r = j ∧ c = i then 1 else 0 := rfl

theorem ckRankOne_adjoint (i j : Fin D) : (ckRankOne i j)ᴴ = ckRankOne j i := by
  ext r c
  simp [ckRankOne, Matrix.conjTranspose_apply, and_comm]

theorem ckRankOne_mul_entry (a b c d R C : Fin D) :
    (∑ j : Fin D, (ckRankOne a b R j) * (ckRankOne c d j C))
      = if R = b ∧ C = c ∧ a = d then 1 else 0 := by
  classical
  simp only [ckRankOne_apply]
  by_cases h1 : R = b
  · by_cases h2 : C = c
    · by_cases h3 : a = d
      · subst h3
        rw [Fintype.sum_eq_single a]
        · simp [h1, h2]
        · intro x hx
          simp [hx]
      · rw [Finset.sum_eq_zero]
        · simp [h1, h2, h3]
        · intro x _
          by_cases hxa : x = a
          · subst hxa
            simp [h1, h2, h3]
          · simp [hxa]
    · rw [Finset.sum_eq_zero]
      · simp [h1, h2]
      · intro x _
        by_cases hxa : x = a
        · subst hxa
          simp [h1, h2]
        · simp [hxa]
  · rw [Finset.sum_eq_zero]
    · simp [h1]
    · intro x _
      by_cases hxa : x = a
      · subst hxa
        simp [h1]
      · simp [hxa]

theorem ckRankOne_mul (a b c d : Fin D) :
    ckRankOne a b * ckRankOne c d = if a = d then ckRankOne c b else 0 := by
  classical
  ext R C
  rw [Matrix.mul_apply, ckRankOne_mul_entry]
  by_cases h3 : a = d
  · rw [if_pos h3]
    simp only [ckRankOne_apply]
    simp [h3]
  · rw [if_neg h3]
    simp [h3]

theorem ckRankOne_mul_diagonal (a b : Fin D) (p : Fin D → ℝ) :
    ckRankOne a b * Matrix.diagonal (fun k => (p k : ℂ)) = (p a : ℂ) • ckRankOne a b := by
  ext r c
  rw [Matrix.mul_diagonal, Matrix.smul_apply]
  simp only [ckRankOne_apply]
  by_cases h1 : r = b
  · by_cases h2 : c = a
    · subst h1
      subst h2
      simp
    · simp [h1, h2]
  · simp [h1]

theorem diagonal_mul_ckRankOne (a b : Fin D) (p : Fin D → ℝ) :
    Matrix.diagonal (fun k => (p k : ℂ)) * ckRankOne a b = (p b : ℂ) • ckRankOne a b := by
  ext r c
  rw [Matrix.diagonal_mul, Matrix.smul_apply]
  simp only [ckRankOne_apply]
  by_cases h1 : r = b
  · by_cases h2 : c = a
    · subst h1
      subst h2
      simp
    · simp [h1, h2]
  · simp [h1]

private theorem smul_mul_smul (c d : ℂ) (M N : Operator D) :
    (c • M) * (d • N) = (c * d) • (M * N) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

private theorem smul_mul_mul_smul (c d : ℂ) (M N P : Operator D) :
    (c • M) * N * (d • P) = (c * d) • (M * N * P) := by
  calc (c • M) * N * (d • P)
      = d • (((c • M) * N) * P) := by rw [Matrix.mul_smul]
    _ = d • ((c • (M * N)) * P) := by rw [Matrix.smul_mul]
    _ = d • (c • ((M * N) * P)) := by rw [Matrix.smul_mul]
    _ = (d * c) • ((M * N) * P) := by rw [smul_smul]
    _ = (c * d) • (M * N * P) := by rw [mul_comm, Matrix.mul_assoc]

private theorem smul_mul_smul_mul (c d : ℂ) (M N P : Operator D) :
    (c • M) * (d • N) * P = (c * d) • (M * N * P) := by
  calc (c • M) * (d • N) * P
      = (c * d) • (M * N) * P := by rw [smul_mul_smul]
    _ = (c * d) • ((M * N) * P) := by rw [Matrix.smul_mul]
    _ = (c * d) • (M * N * P) := by rw [Matrix.mul_assoc]

private theorem mul_smul_mul_smul (c d : ℂ) (M N P : Operator D) :
    P * (c • M) * (d • N) = (c * d) • (P * (M * N)) := by
  calc P * (c • M) * (d • N)
      = d • (((P * (c • M)) * N)) := by rw [Matrix.mul_smul]
    _ = d • ((c • (P * M)) * N) := by rw [Matrix.mul_smul]
    _ = d • (c • ((P * M) * N)) := by rw [Matrix.smul_mul]
    _ = (c * d) • ((P * M) * N) := by rw [smul_smul, mul_comm]
    _ = (c * d) • (P * (M * N)) := by rw [Matrix.mul_assoc]

private theorem half_add (X : Operator D) : (1 / 2 : ℂ) • (X + X) = X := by
  ext r c
  simp [Matrix.smul_apply, Matrix.add_apply]
  ring

theorem ckAcceptJump_dissipator (E : Fin D → ℝ) (β : ℝ) (p : Fin D → ℝ) (i j : Fin D) :
    ckAcceptJump E β i j * Matrix.diagonal (fun t => (p t : ℂ)) * (ckAcceptJump E β i j)ᴴ
      - (1 / 2 : ℂ) • ((ckAcceptJump E β i j)ᴴ * ckAcceptJump E β i j
          * Matrix.diagonal (fun t => (p t : ℂ))
        + Matrix.diagonal (fun t => (p t : ℂ)) * (ckAcceptJump E β i j)ᴴ
          * ckAcceptJump E β i j)
      = ((thermalAcceptance E β i j : ℂ) * (p i : ℂ)) • (ckRankOne j j - ckRankOne i i) := by
  classical
  by_cases hij : i = j
  · subst hij
    simp [ckAcceptJump]
  · have ha : 0 ≤ thermalAcceptance E β i j := (thermalAcceptance_pos E β i j).le
    have hsq : (Real.sqrt (thermalAcceptance E β i j) : ℂ)
        * (Real.sqrt (thermalAcceptance E β i j) : ℂ)
        = (thermalAcceptance E β i j : ℂ) := by
      rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt ha]
    have hL : ((Real.sqrt (thermalAcceptance E β i j) : ℂ) • ckRankOne i j)ᴴ
        = (Real.sqrt (thermalAcceptance E β i j) : ℂ) • ckRankOne j i := by
      rw [Matrix.conjTranspose_smul, ckRankOne_adjoint]
      simp [Complex.conj_ofReal]
    have h1 : ckAcceptJump E β i j * Matrix.diagonal (fun t => (p t : ℂ))
          * (ckAcceptJump E β i j)ᴴ
        = ((thermalAcceptance E β i j : ℂ) * (p i : ℂ)) • ckRankOne j j := by
      rw [ckAcceptJump_eq E β i j hij, hL]
      calc (Real.sqrt (thermalAcceptance E β i j) : ℂ) • ckRankOne i j
            * Matrix.diagonal (fun t => (p t : ℂ))
            * ((Real.sqrt (thermalAcceptance E β i j) : ℂ) • ckRankOne j i)
          = ((Real.sqrt (thermalAcceptance E β i j) : ℂ)
            * (Real.sqrt (thermalAcceptance E β i j) : ℂ))
            • (ckRankOne i j * Matrix.diagonal (fun t => (p t : ℂ)) * ckRankOne j i) :=
            smul_mul_mul_smul _ _ _ _ _
        _ = ((Real.sqrt (thermalAcceptance E β i j) : ℂ)
            * (Real.sqrt (thermalAcceptance E β i j) : ℂ))
            • ((p i : ℂ) • (ckRankOne i j * ckRankOne j i)) := by
              rw [ckRankOne_mul_diagonal, Matrix.smul_mul]
        _ = ((Real.sqrt (thermalAcceptance E β i j) : ℂ)
            * (Real.sqrt (thermalAcceptance E β i j) : ℂ))
            • ((p i : ℂ) • ckRankOne j j) := by
              rw [ckRankOne_mul, if_pos rfl]
        _ = ((thermalAcceptance E β i j : ℂ) * (p i : ℂ)) • ckRankOne j j := by
              rw [smul_smul, hsq]
    have h2 : (ckAcceptJump E β i j)ᴴ * ckAcceptJump E β i j
          * Matrix.diagonal (fun t => (p t : ℂ))
        = ((thermalAcceptance E β i j : ℂ) * (p i : ℂ)) • ckRankOne i i := by
      rw [ckAcceptJump_eq E β i j hij, hL]
      calc (Real.sqrt (thermalAcceptance E β i j) : ℂ) • ckRankOne j i
            * ((Real.sqrt (thermalAcceptance E β i j) : ℂ) • ckRankOne i j)
            * Matrix.diagonal (fun t => (p t : ℂ))
          = ((Real.sqrt (thermalAcceptance E β i j) : ℂ)
            * (Real.sqrt (thermalAcceptance E β i j) : ℂ))
            • (ckRankOne j i * ckRankOne i j
              * Matrix.diagonal (fun t => (p t : ℂ))) :=
            smul_mul_smul_mul _ _ _ _ _
        _ = ((Real.sqrt (thermalAcceptance E β i j) : ℂ)
            * (Real.sqrt (thermalAcceptance E β i j) : ℂ))
            • ((p i : ℂ) • ckRankOne i i) := by
              rw [ckRankOne_mul, if_pos rfl, ckRankOne_mul_diagonal]
        _ = ((thermalAcceptance E β i j : ℂ) * (p i : ℂ)) • ckRankOne i i := by
              rw [smul_smul, hsq]
    have h3 : Matrix.diagonal (fun t => (p t : ℂ)) * (ckAcceptJump E β i j)ᴴ
          * ckAcceptJump E β i j
        = ((thermalAcceptance E β i j : ℂ) * (p i : ℂ)) • ckRankOne i i := by
      rw [ckAcceptJump_eq E β i j hij, hL]
      calc Matrix.diagonal (fun t => (p t : ℂ))
            * ((Real.sqrt (thermalAcceptance E β i j) : ℂ) • ckRankOne j i)
            * ((Real.sqrt (thermalAcceptance E β i j) : ℂ) • ckRankOne i j)
          = ((Real.sqrt (thermalAcceptance E β i j) : ℂ)
            * (Real.sqrt (thermalAcceptance E β i j) : ℂ))
            • (Matrix.diagonal (fun t => (p t : ℂ))
              * (ckRankOne j i * ckRankOne i j)) :=
            mul_smul_mul_smul _ _ _ _ _
        _ = ((Real.sqrt (thermalAcceptance E β i j) : ℂ)
            * (Real.sqrt (thermalAcceptance E β i j) : ℂ))
            • ((p i : ℂ) • ckRankOne i i) := by
              rw [ckRankOne_mul, if_pos rfl, diagonal_mul_ckRankOne]
        _ = ((thermalAcceptance E β i j : ℂ) * (p i : ℂ)) • ckRankOne i i := by
              rw [smul_smul, hsq]
    rw [h1, h2, h3]
    calc ((thermalAcceptance E β i j : ℂ) * (p i : ℂ)) • ckRankOne j j
          - ((1 / 2 : ℂ) • (((thermalAcceptance E β i j : ℂ) * (p i : ℂ)) • ckRankOne i i
            + ((thermalAcceptance E β i j : ℂ) * (p i : ℂ)) • ckRankOne i i))
        = ((thermalAcceptance E β i j : ℂ) * (p i : ℂ)) • ckRankOne j j
          - ((thermalAcceptance E β i j : ℂ) * (p i : ℂ)) • ckRankOne i i := by
              rw [half_add]
        _ = ((thermalAcceptance E β i j : ℂ) * (p i : ℂ))
            • (ckRankOne j j - ckRankOne i i) := by
              rw [← smul_sub]

theorem ckDissipatorTerm_eq (E : Fin D → ℝ) (β : ℝ) (p : Fin D → ℝ) (i j : Fin D) :
    ckDissipatorTerm E β p i j
      = ((thermalAcceptance E β i j : ℂ) * (p i : ℂ)) • ckRankOne j j
        - ((thermalAcceptance E β i j : ℂ) * (p i : ℂ)) • ckRankOne i i := by
  unfold ckDissipatorTerm
  rw [smul_sub]

private def ckTermTarget (E : Fin D → ℝ) (β : ℝ) (p : Fin D → ℝ)
    (q : Fin D × Fin D) : Operator D :=
  ((thermalAcceptance E β q.1 q.2 : ℂ) * (p q.1 : ℂ)) • ckRankOne q.2 q.2

private def ckTermSource (E : Fin D → ℝ) (β : ℝ) (p : Fin D → ℝ)
    (q : Fin D × Fin D) : Operator D :=
  ((thermalAcceptance E β q.1 q.2 : ℂ) * (p q.1 : ℂ)) • ckRankOne q.1 q.1

theorem ckDissipator_sum_zero (E : Fin D → ℝ) (β : ℝ) (p : Fin D → ℝ)
    (hbal : ∀ i j : Fin D,
      thermalAcceptance E β i j * p i = thermalAcceptance E β j i * p j) :
    ∑ q : Fin D × Fin D, ckDissipatorTerm E β p q.1 q.2 = 0 := by
  classical
  have hbalC : ∀ i j : Fin D,
      ((thermalAcceptance E β i j : ℂ) * (p i : ℂ))
        = ((thermalAcceptance E β j i : ℂ) * (p j : ℂ)) := by
    intro i j
    have h := hbal i j
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, h]
  have hswap : (∑ q : Fin D × Fin D, ckTermTarget E β p q)
      = ∑ q : Fin D × Fin D, ckTermSource E β p q := by
    calc (∑ q : Fin D × Fin D, ckTermTarget E β p q)
        = ∑ q : Fin D × Fin D,
            ckTermTarget E β p (Equiv.prodComm (Fin D) (Fin D) q) :=
          (Equiv.sum_comp (Equiv.prodComm (Fin D) (Fin D)) (ckTermTarget E β p)).symm
      _ = ∑ q : Fin D × Fin D, ckTermSource E β p q := by
        refine Finset.sum_congr rfl ?_
        intro q _
        simp only [ckTermTarget, ckTermSource, Equiv.prodComm_apply, Prod.swap]
        rw [hbalC q.2 q.1]
  calc (∑ q : Fin D × Fin D, ckDissipatorTerm E β p q.1 q.2)
      = ∑ q : Fin D × Fin D, (ckTermTarget E β p q - ckTermSource E β p q) := by
        refine Finset.sum_congr rfl ?_
        intro q _
        exact ckDissipatorTerm_eq E β p q.1 q.2
    _ = (∑ q : Fin D × Fin D, ckTermTarget E β p q)
        - ∑ q : Fin D × Fin D, ckTermSource E β p q :=
      Finset.sum_sub_distrib (s := Finset.univ) _ _
    _ = 0 := by rw [hswap]; simp

theorem ckDissipator_sum_bridge (E : Fin D → ℝ) (β : ℝ) (p : Fin D → ℝ) :
    (∑ k : Fin (D * D), ckJumpDissipator E β p k)
      = ∑ q : Fin D × Fin D, ckDissipatorTerm E β p q.1 q.2 := by
  classical
  show (∑ k : Fin (D * D), ckJumpDissipator E β p k)
      = ∑ q : Fin D × Fin D, ckDissipatorTerm E β p q.1 q.2
  calc (∑ k : Fin (D * D), ckJumpDissipator E β p k)
      = ∑ q : Fin D × Fin D, ckJumpDissipator E β p (finProdFinEquiv q) :=
        (Equiv.sum_comp finProdFinEquiv (ckJumpDissipator E β p)).symm
    _ = ∑ q : Fin D × Fin D, ckDissipatorTerm E β p q.1 q.2 := by
        refine Finset.sum_congr rfl ?_
        intro q _
        simp only [ckJumpDissipator, ckJumps, Equiv.symm_apply_apply]
        exact ckAcceptJump_dissipator E β p q.1 q.2

theorem ckHamiltonian_comm (E : Fin D → ℝ) (p : Fin D → ℝ) :
    ckHamiltonian E * Matrix.diagonal (fun t => (p t : ℂ))
      = Matrix.diagonal (fun t => (p t : ℂ)) * ckHamiltonian E := by
  unfold ckHamiltonian
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  ring

theorem ckGenerator_gibbs_fixed (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) :
    lindbladApply (ckGenerator E β) (diagonalGibbsDensity D hD E β) = 0 := by
  classical
  set p := (diagonalGibbsDist D hD E β).prob with hp
  have hρ : diagonalGibbsDensity D hD E β = Matrix.diagonal (fun i => (p i : ℂ)) := by
    rw [diagonalGibbsDensity_eq]
  have hbal : ∀ i j : Fin D,
      thermalAcceptance E β i j * p i = thermalAcceptance E β j i * p j := by
    intro i j
    have h := ckAccept_detailedBalance D hD E β i j
    simpa [hp] using! h
  have hjump : (∑ k : Fin (D * D), ckJumpDissipator E β p k) = 0 := by
    rw [ckDissipator_sum_bridge E β p]
    exact ckDissipator_sum_zero E β p hbal
  rw [lindbladApply, hρ]
  change (-Complex.I) • (ckHamiltonian E * Matrix.diagonal (fun i => (p i : ℂ))
      - Matrix.diagonal (fun i => (p i : ℂ)) * ckHamiltonian E)
      + (∑ j : Fin (D * D), ckJumpDissipator E β p j) = 0
  rw [ckHamiltonian_comm E p, hjump]
  simp

theorem ckGenerator_gibbs_stationary (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) :
    Qatlib.Concepts.LindbladFlow.GkslSemigroup.IsStationary (ckGenerator E β)
      (diagonalGibbsDensity D hD E β) :=
  stationary_of_generator_zero (ckGenerator E β) _ (ckGenerator_gibbs_fixed D hD E β)

theorem ckGenerator_gibbs_semigroup (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (t : ℝ) (ht : 0 ≤ t) :
    lindbladSemigroup (ckGenerator E β) t (diagonalGibbsDensity D hD E β)
      = diagonalGibbsDensity D hD E β :=
  (ckGenerator_gibbs_stationary D hD E β) t ht

theorem ckGenerator_gibbs_euler_taylor (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (h : ℝ) (hh : 0 ≤ h) :
    gkslEulerMap (ckGenerator E β) h (diagonalGibbsDensity D hD E β)
      = diagonalGibbsDensity D hD E β
        + ((h : ℂ) ^ 2) • (gkslDrift (ckGenerator E β)
            * diagonalGibbsDensity D hD E β * (gkslDrift (ckGenerator E β))ᴴ) := by
  rw [gkslEulerMap_taylor (ckGenerator E β) h hh]
  rw [ckGenerator_gibbs_fixed D hD E β]
  simp

theorem ckGenerator_gibbs_euler_window_error (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1) (n : ℕ) :
    ‖((gkslEulerMap (ckGenerator E β) h)^[n]) (diagonalGibbsDensity D hD E β)
        - diagonalGibbsDensity D hD E β‖
      ≤ (n : ℝ) * (‖gkslDrift (ckGenerator E β)‖ ^ 2
        + (2 * ‖(ckGenerator E β).ham‖ + 2 * ∑ j, ‖(ckGenerator E β).jumps j‖ ^ 2) ^ 2
          * Real.exp (2 * ‖(ckGenerator E β).ham‖
            + 2 * ∑ j, ‖(ckGenerator E β).jumps j‖ ^ 2)) * h ^ 2
        * Real.exp ((2 * ‖(ckGenerator E β).ham‖ + 2 * ∑ j, ‖(ckGenerator E β).jumps j‖ ^ 2
          + ‖gkslDrift (ckGenerator E β)‖ ^ 2) * ((n : ℝ) * h))
        * ‖diagonalGibbsDensity D hD E β‖ := by
  have herr := gkslEulerMap_iterate_error (ckGenerator E β) h hh hh1 n
    (diagonalGibbsDensity D hD E β)
  rw [ckGenerator_gibbs_semigroup D hD E β ((n : ℝ) * h) (by positivity)] at herr
  exact herr

theorem ckAccept_transport (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (i j : Fin D) (hij : i ≠ j) :
    D * thermalKernel D E β i j = thermalAcceptance E β i j := by
  rw [thermalKernel_offdiag D E β hij]
  field_simp

theorem ckRejectRecovery_transport (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (i : Fin D) :
    D * (1 - thermalKernel D E β i i)
      = ∑ j' ∈ (Finset.univ : Finset (Fin D)).erase i, thermalAcceptance E β i j' := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  rw [thermalKernel, if_pos rfl, sub_sub_cancel]
  rw [(Finset.sum_div (Finset.univ.erase i) (fun j' => thermalAcceptance E β i j')
    (D : ℝ)).symm]
  field_simp

open Filter

open scoped Topology

theorem ckRejectMass_eq (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (i : Fin D) :
    ckRejectMass D E β i
      = 1 - ∑ j' ∈ (Finset.univ : Finset (Fin D)).erase i,
          thermalAcceptance E β i j' / (D : ℝ) := by
  unfold ckRejectMass
  rw [thermalKernel, if_pos rfl]

private theorem ckErase_nonempty (D : ℕ) (hD : 1 < D) (i : Fin D) :
    ((Finset.univ : Finset (Fin D)).erase i).Nonempty := by
  rw [← Finset.card_pos]
  rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  omega

theorem ckRejectMass_pos (D : ℕ) (hD : 1 < D) (E : Fin D → ℝ) (β : ℝ) (i : Fin D) :
    0 < ckRejectMass D E β i := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (Nat.zero_lt_of_lt hD)
  have hcardlt : ((Finset.univ : Finset (Fin D)).erase i).card < D := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  have hsum : (∑ j' ∈ (Finset.univ : Finset (Fin D)).erase i,
      thermalAcceptance E β i j' / (D : ℝ)) < 1 := by
    calc _ ≤ ∑ _ ∈ (Finset.univ : Finset (Fin D)).erase i, (1:ℝ) / (D : ℝ) := by
          refine Finset.sum_le_sum fun j' _ => ?_
          exact div_le_div_of_nonneg_right (thermalAcceptance_le_one E β i j') hDpos.le
      _ = (((Finset.univ : Finset (Fin D)).erase i).card : ℝ) / (D : ℝ) := by
          rw [Finset.sum_const, div_eq_mul_inv]
          ring
      _ < 1 := by
          rw [div_lt_one hDpos]
          have hcl : (((Finset.univ : Finset (Fin D)).erase i).card : ℝ) < D := by
            exact_mod_cast hcardlt
          exact hcl
  rw [ckRejectMass_eq]
  linarith

theorem ckRejectMass_lt_one (D : ℕ) (hD : 1 < D) (E : Fin D → ℝ) (β : ℝ) (i : Fin D) :
    ckRejectMass D E β i < 1 := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (Nat.zero_lt_of_lt hD)
  obtain ⟨j', hj'⟩ := ckErase_nonempty D hD i
  have hpos : (0:ℝ) < ∑ j'' ∈ (Finset.univ : Finset (Fin D)).erase i,
      thermalAcceptance E β i j'' / (D : ℝ) := by
    refine Finset.sum_pos' (fun j'' _ => ?_) ⟨j', hj', ?_⟩
    · exact div_nonneg (thermalAcceptance_pos E β i j'').le hDpos.le
    · exact div_pos (thermalAcceptance_pos E β i j') hDpos
  rw [ckRejectMass_eq]
  linarith

theorem ckRejectMass_one (E : Fin 1 → ℝ) (β : ℝ) (i : Fin 1) :
    ckRejectMass 1 E β i = 1 := by
  have hi : i = 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)
  subst hi
  unfold ckRejectMass
  rw [thermalKernel, if_pos rfl]
  simp

theorem ckAcceptInflow_one (E : Fin 1 → ℝ) (β : ℝ) (p : Fin 1 → ℝ) (i : Fin 1) :
    ckAcceptInflow 1 E β p i = 0 := by
  have hi : i = 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)
  subst hi
  unfold ckAcceptInflow
  simp

theorem ckAcceptInflow_eq_kernel (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (p : Fin D → ℝ) (j : Fin D) :
    ckAcceptInflow D E β p j
      = ∑ i ∈ (Finset.univ : Finset (Fin D)).erase j, thermalKernel D E β i j * p i := by
  unfold ckAcceptInflow
  refine Finset.sum_congr rfl fun i hi => ?_
  have hne : i ≠ j := (Finset.mem_erase.mp hi).1
  rw [thermalKernel_offdiag D E β hne]

theorem ckOneStepInflow_eq_kernel (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (p : Fin D → ℝ) (j : Fin D) :
    ckOneStepInflow D E β p j = ∑ i : Fin D, thermalKernel D E β i j * p i := by
  have hsum : (∑ i ∈ (Finset.univ : Finset (Fin D)).erase j,
        thermalKernel D E β i j * p i)
      + thermalKernel D E β j j * p j
      = ∑ i : Fin D, thermalKernel D E β i j * p i :=
    Finset.sum_erase_add (Finset.univ : Finset (Fin D))
      (fun i => thermalKernel D E β i j * p i) (Finset.mem_univ j)
  rw [ckOneStepInflow, ckAcceptInflow_eq_kernel, ckRejectPart, ckRejectMass, hsum]

theorem ckOneStep_sum (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) (p : Fin D → ℝ) :
    ∑ j : Fin D, ckOneStepInflow D E β p j = ∑ i : Fin D, p i := by
  rw [Finset.sum_congr rfl fun j _ => ckOneStepInflow_eq_kernel D E β p j]
  calc (∑ j : Fin D, ∑ i : Fin D, thermalKernel D E β i j * p i)
      = ∑ i : Fin D, ∑ j : Fin D, thermalKernel D E β i j * p i := by
        rw [Finset.sum_comm]
    _ = ∑ i : Fin D, p i * (∑ j : Fin D, thermalKernel D E β i j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_mul]
        ring
    _ = ∑ i : Fin D, p i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hrow := (diagonal_metropolis_transition_reversible D hD E β).1.2 i
        rw [hrow, mul_one]

theorem ckOneStep_gibbs_fixed (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) (j : Fin D) :
    ∑ i : Fin D, (diagonalGibbsDist D hD E β).prob i * thermalKernel D E β i j
      = (diagonalGibbsDist D hD E β).prob j :=
  ((diagonal_metropolis_transition_reversible D hD E β).2.2.1).2.2 j

theorem ckRecoveryTerm_eq (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (p : Fin D → ℝ) (j : Fin D) (n : ℕ) :
    ckRecoveryTerm D E β p j n = (ckRejectMass D E β j) ^ n * p j := rfl

theorem ckRecoveryTail_eq (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (p : Fin D → ℝ) (j : Fin D) (N : ℕ)
    (h0 : 0 ≤ ckRejectMass D E β j) (h1 : ckRejectMass D E β j < 1) :
    ckRecoveryTail D E β p j N
      = (ckRejectMass D E β j) ^ N * p j / (1 - ckRejectMass D E β j) := by
  classical
  set r := ckRejectMass D E β j with hr
  have hgeom : HasSum (fun n : ℕ => r ^ n) (1 - r)⁻¹ := hasSum_geometric_of_lt_one h0 h1
  have hshift : HasSum (fun n : ℕ => r ^ (N + n)) (r ^ N * (1 - r)⁻¹) := by
    have heq : (fun n : ℕ => r ^ (N + n)) = fun n => r ^ N * r ^ n := by
      funext n
      rw [pow_add]
    rw [heq]
    exact hgeom.mul_left (r ^ N)
  have hmain : HasSum (fun n : ℕ => ckRecoveryTerm D E β p j (N + n))
      (p j * (r ^ N * (1 - r)⁻¹)) := by
    have heq : (fun n : ℕ => ckRecoveryTerm D E β p j (N + n))
        = fun n => p j * (r ^ (N + n)) := by
      funext n
      simp [ckRecoveryTerm, hr, mul_comm]
    rw [heq]
    exact hshift.mul_left (p j)
  rw [ckRecoveryTail]
  rw [hmain.tsum_eq]
  rw [div_eq_mul_inv]
  ring

theorem ckRecoveryTail_succ (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (p : Fin D → ℝ) (j : Fin D) (N : ℕ)
    (h0 : 0 ≤ ckRejectMass D E β j) (h1 : ckRejectMass D E β j < 1) :
    ckRecoveryTail D E β p j (N + 1)
      = ckRejectMass D E β j * ckRecoveryTail D E β p j N := by
  rw [ckRecoveryTail_eq D E β p j (N + 1) h0 h1, ckRecoveryTail_eq D E β p j N h0 h1]
  rw [pow_succ]
  ring

theorem ckRecoveryTail_tendsto_zero (D : ℕ) (hD : 1 < D) (E : Fin D → ℝ) (β : ℝ)
    (p : Fin D → ℝ) (j : Fin D) :
    Tendsto (ckRecoveryTail D E β p j) atTop (𝓝 0) := by
  have h0 := ckRejectMass_pos D hD E β j
  have h1 := ckRejectMass_lt_one D hD E β j
  have hgeom : Tendsto (fun N : ℕ => (ckRejectMass D E β j) ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt h0) h1
  have hconst : Tendsto (fun N : ℕ => (ckRejectMass D E β j) ^ N * p j
      / (1 - ckRejectMass D E β j)) atTop (𝓝 0) := by
    have hc : Tendsto (fun N : ℕ => (p j / (1 - ckRejectMass D E β j))
        * (ckRejectMass D E β j) ^ N) atTop
        (𝓝 ((p j / (1 - ckRejectMass D E β j)) * 0)) :=
      hgeom.const_mul (p j / (1 - ckRejectMass D E β j))
    have hc' : (fun N : ℕ => (ckRejectMass D E β j) ^ N * p j
        / (1 - ckRejectMass D E β j))
        = fun N => (p j / (1 - ckRejectMass D E β j)) * (ckRejectMass D E β j) ^ N := by
      funext N
      rw [div_eq_mul_inv]
      ring
    rw [hc']
    simpa using! hc
  have hfun : (fun N : ℕ => ckRecoveryTail D E β p j N)
      = fun N => (ckRejectMass D E β j) ^ N * p j / (1 - ckRejectMass D E β j) := by
    funext N
    rw [ckRecoveryTail_eq D E β p j N (le_of_lt h0) h1]
  have hmain : Tendsto (fun N : ℕ => ckRecoveryTail D E β p j N) atTop (𝓝 0) := by
    rw [hfun]
    exact hconst
  exact hmain

theorem ckRecoveryTailTotal_le (D : ℕ) (hD : 1 < D) (E : Fin D → ℝ) (β : ℝ)
    (p : Fin D → ℝ) (hp : ∀ j, 0 ≤ p j) (N : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hle : ∀ j, ckRejectMass D E β j ≤ ρ) :
    ckRecoveryTailTotal D E β p N ≤ ρ ^ N * (∑ j : Fin D, p j) / (1 - ρ) := by
  have hper : ∀ j, ckRecoveryTail D E β p j N
      ≤ ρ ^ N * p j / (1 - ρ) := by
    intro j
    have h0 := ckRejectMass_pos D hD E β j
    have hlt := ckRejectMass_lt_one D hD E β j
    have hposr : 0 < 1 - ckRejectMass D E β j := by linarith
    have hposρ : 0 < 1 - ρ := by linarith
    have hinv : (1 : ℝ) / (1 - ckRejectMass D E β j) ≤ (1 : ℝ) / (1 - ρ) :=
      one_div_le_one_div_of_le hposρ (by linarith [hle j])
    have hA : (ckRejectMass D E β j) ^ N * p j ≤ ρ ^ N * p j :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_of_lt h0) (hle j) N) (hp j)
    have hA0 : 0 ≤ (ckRejectMass D E β j) ^ N * p j :=
      mul_nonneg (pow_nonneg (le_of_lt h0) N) (hp j)
    have hB0 : 0 ≤ ρ ^ N * p j := mul_nonneg (pow_nonneg hρ0 N) (hp j)
    have hinv0 : 0 ≤ (1 : ℝ) / (1 - ckRejectMass D E β j) := div_nonneg zero_le_one hposr.le
    rw [ckRecoveryTail_eq D E β p j N (le_of_lt h0) hlt]
    calc (ckRejectMass D E β j) ^ N * p j / (1 - ckRejectMass D E β j)
        = (ckRejectMass D E β j) ^ N * p j * ((1:ℝ) / (1 - ckRejectMass D E β j)) := by
          field_simp
      _ ≤ ρ ^ N * p j * ((1:ℝ) / (1 - ρ)) :=
            mul_le_mul hA hinv hinv0 hB0
      _ = ρ ^ N * p j / (1 - ρ) := by field_simp
  calc ckRecoveryTailTotal D E β p N
      = ∑ j : Fin D, ckRecoveryTail D E β p j N := rfl
    _ ≤ ∑ j : Fin D, ρ ^ N * p j / (1 - ρ) := Finset.sum_le_sum fun j _ => hper j
    _ = ρ ^ N * (∑ j : Fin D, p j) / (1 - ρ) := by
        calc (∑ j : Fin D, ρ ^ N * p j / (1 - ρ))
            = (∑ j : Fin D, ρ ^ N * p j) / (1 - ρ) := (Finset.sum_div _ _ _).symm
          _ = (ρ ^ N * ∑ j : Fin D, p j) / (1 - ρ) := by rw [Finset.mul_sum]

theorem ckWindowError_cost (D : ℕ) (hD : 1 < D) (E : Fin D → ℝ) (β : ℝ) (p : Fin D → ℝ)
    (m nStar : ℕ) (j : Fin D) :
    ckRecoveryTail D E β p j nStar
        ≤ p j * (ckRejectMass D E β j) ^ nStar / (1 - ckRejectMass D E β j)
      ∧ ckStepReadouts nStar = 2 + nStar
      ∧ ckRunReadouts m nStar = m * (2 + nStar) := by
  have h0 := ckRejectMass_pos D hD E β j
  have h1 := ckRejectMass_lt_one D hD E β j
  have htail := ckRecoveryTail_eq D E β p j nStar (le_of_lt h0) h1
  have hkey : (ckRejectMass D E β j) ^ nStar * p j / (1 - ckRejectMass D E β j)
      = p j * (ckRejectMass D E β j) ^ nStar / (1 - ckRejectMass D E β j) := by ring
  refine ⟨?_, rfl, rfl⟩
  rw [htail, hkey]

theorem ckAcceptance_same_class (E : Fin D → ℝ) (β : ℝ) (i j : Fin D) (h : E i = E j) :
    thermalAcceptance E β i j = 1 := by
  unfold thermalAcceptance
  rw [h, sub_self]
  simp

theorem ckAcceptance_uphill (E : Fin D → ℝ) (β : ℝ) (i j : Fin D)
    (hβ : 0 < β) (h : E i < E j) :
    thermalAcceptance E β i j = Real.exp (-β * (E j - E i))
      ∧ thermalAcceptance E β i j < 1 := by
  unfold thermalAcceptance
  have hne : 0 < E j - E i := sub_pos.mpr h
  have hmul : 0 < β * (E j - E i) := mul_pos hβ hne
  have hneg : -β * (E j - E i) < 0 := by
    rw [neg_mul]
    exact neg_lt_zero.mpr hmul
  have hlt : Real.exp (-β * (E j - E i)) < 1 := Real.exp_lt_one_iff.mpr hneg
  refine ⟨min_eq_right hlt.le, ?_⟩
  rw [min_eq_right hlt.le]
  exact hlt

theorem ckAcceptance_downhill (E : Fin D → ℝ) (β : ℝ) (i j : Fin D)
    (hβ : 0 < β) (h : E j < E i) :
    thermalAcceptance E β i j = 1 := by
  unfold thermalAcceptance
  have hne : 0 < E i - E j := sub_pos.mpr h
  have hmul : 0 < β * (E i - E j) := mul_pos hβ hne
  have hpos : 0 < -β * (E j - E i) := by
    have hkey : -β * (E j - E i) = β * (E i - E j) := by ring
    rw [hkey]
    exact hmul
  have hexp : 1 < Real.exp (-β * (E j - E i)) := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hpos
  exact min_eq_left hexp.le

theorem ckClassFlow_same (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (i j : Fin D)
    (h : E i = E j) :
    thermalAcceptance E β i j / (D : ℝ) = 1 / (D : ℝ) := by
  rw [ckAcceptance_same_class E β i j h]

theorem ckClassFlow_downhill (D : ℕ) (E : Fin D → ℝ) (β : ℝ) (i j : Fin D)
    (hβ : 0 < β) (h : E j < E i) :
    thermalAcceptance E β i j / (D : ℝ) = 1 / (D : ℝ) := by
  rw [ckAcceptance_downhill E β i j hβ h]

theorem ckClassFlow_uphill (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) (i j : Fin D)
    (hβ : 0 < β) (h : E i < E j) :
    thermalAcceptance E β i j / (D : ℝ) < 1 / (D : ℝ) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  exact div_lt_div_of_pos_right ((ckAcceptance_uphill E β i j hβ h).2) hDpos

def clause3_endpoint (E : Fin D → ℝ) (β : ℝ) : CkGeneratorInterface D where
  energy := E
  temp := β
  gibbsFixed := fun hD => ckGenerator_gibbs_fixed D hD E β
  gibbsSemigroup := fun hD t ht => ckGenerator_gibbs_semigroup D hD E β t ht
  jumpFilter := fun i j =>
    ⟨ckJump_target_class E β i j, ckJump_source_class E β i j⟩
  detailedBalance := fun hD i j => ckAccept_detailedBalance D hD E β i j
  windowError := fun hD h hh hh1 n =>
    ckGenerator_gibbs_euler_window_error D hD E β h hh hh1 n
  acceptTransport := fun hD i j hij => ckAccept_transport D hD E β i j hij
  rejectTransport := fun hD i => ckRejectRecovery_transport D hD E β i
  oneStepAssembly := fun hD p => ckOneStep_sum D hD E β p
  oneStepGibbs := fun hD j => ckOneStep_gibbs_fixed D hD E β j
  recoveryWindow := fun hD p N j =>
    ckRecoveryTail_eq D E β p j N
      (le_of_lt (ckRejectMass_pos D hD E β j)) (ckRejectMass_lt_one D hD E β j)
  realizedCost := fun m nStar hns hm => ckRunReadouts_exceeds_assumed m nStar D hns hm

theorem entropyContractionLaw_mono {G : GKSL D} {ρ : Operator D} {η η' : ℝ}
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef)
    (h : EntropyContractionLaw G ρ η) (hη' : 0 < η') (hη'1 : η' ≤ η) :
    EntropyContractionLaw G ρ η' := by
  refine ⟨hη', ⟨by linarith [h.2.1], ?_⟩⟩
  intro hh σ hpos hle hσ
  have hstep := h.2.2 hh σ hpos hle hσ
  have hS0 : 0 ≤ relativeEntropy σ ρ := initialEntropy_nonneg hσ hρ hfull
  have hfac : 1 - η * hh ≤ 1 - η' * hh := by
    have hmul := mul_le_mul_of_nonneg_left hη'1 hpos.le
    linarith
  calc relativeEntropy (lindbladSemigroup G hh σ) ρ
      ≤ (1 - η * hh) * relativeEntropy σ ρ := hstep
    _ ≤ (1 - η' * hh) * relativeEntropy σ ρ :=
          mul_le_mul_of_nonneg_right hfac hS0

theorem clause2_endpoint_entropy_rate_not_pinned {d : MixingEntropyData D} :
    ∃ d' : MixingEntropyData D,
      d'.gapRate = d.gapRate ∧ d'.entropyRate = d.entropyRate / 2
      ∧ d.entropyRate / 2 < d.entropyRate := by
  have hη' : 0 < d.entropyRate / 2 := by linarith [d.entropyLaw.1]
  have hη'1 : d.entropyRate / 2 ≤ d.entropyRate := by linarith
  have hlaw : EntropyContractionLaw d.gen d.ref (d.entropyRate / 2) :=
    entropyContractionLaw_mono d.refDensity d.refFull d.entropyLaw hη' hη'1
  obtain ⟨d', hg, he⟩ := mixingEntropyData_rate_independent hlaw
  exact ⟨d', hg, he, by linarith [d.entropyLaw.1]⟩

theorem diagonalGibbsDist_flat (D : ℕ) (hD : 0 < D) (β : ℝ) (i : Fin D) :
    (diagonalGibbsDist D hD (fun _ => 0) β).prob i = 1 / (D : ℝ) := by
  have hZ : diagonalGibbsPartition D (fun _ => 0) β = (D : ℝ) := by
    unfold diagonalGibbsPartition
    simp [Real.exp_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [diagonalGibbsDist_prob, hZ]
  simp [Real.exp_zero]

theorem referenceWeight_flatGibbs (D : ℕ) (hD : 0 < D) (β : ℝ) :
    referenceWeight (diagonalGibbsDensity D hD (fun _ => 0) β) = Real.sqrt (D : ℝ) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hρ : diagonalGibbsDensity D hD (fun _ => 0) β
      = Matrix.diagonal (fun k : Fin D => Complex.ofReal (1 / (D : ℝ))) := by
    ext r c
    by_cases hrc : r = c
    · subst hrc
      simp [diagonalGibbsDensity, diagonalGibbsDist_flat D hD β r]
    · simp [diagonalGibbsDensity, hrc]
  have hsqrt : CFC.sqrt (Matrix.diagonal (fun k : Fin D => Complex.ofReal (1 / (D : ℝ))))
      = Matrix.diagonal (fun k : Fin D => Complex.ofReal (Real.sqrt (1 / (D : ℝ)))) := by
    exact CFC_sqrt_diagonal (fun _ => 1 / (D : ℝ)) (fun _ => by positivity)
  have hinv : (Matrix.diagonal (fun k : Fin D => Complex.ofReal (Real.sqrt (1 / (D : ℝ)))))⁻¹
      = Matrix.diagonal (fun k : Fin D => (Complex.ofReal (Real.sqrt (1 / (D : ℝ))))⁻¹) := by
    exact diagonal_inv_eq _ (fun k => Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.2 (by positivity))))
  have hsqrtD : Real.sqrt (1 / (D : ℝ)) = 1 / Real.sqrt (D : ℝ) := by
    rw [Real.sqrt_div (by norm_num) (D : ℝ), Real.sqrt_one]
  have hinvval : (Complex.ofReal (Real.sqrt (1 / (D : ℝ))))⁻¹
      = Complex.ofReal (Real.sqrt (D : ℝ)) := by
    have h1 : (Complex.ofReal (1 / Real.sqrt (D : ℝ)))⁻¹
        = Complex.ofReal ((1 / Real.sqrt (D : ℝ))⁻¹) :=
      (Complex.ofReal_inv (1 / Real.sqrt (D : ℝ))).symm
    rw [hsqrtD, h1]
    have hne : (Real.sqrt (D : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hDpos)
    field_simp
  have hmat : Matrix.diagonal (fun k : Fin D => (Complex.ofReal (Real.sqrt (1 / (D : ℝ))))⁻¹)
      = Matrix.diagonal (fun k : Fin D => Complex.ofReal (Real.sqrt (D : ℝ))) := by
    ext r c
    by_cases hrc : r = c
    · subst hrc
      simp only [Matrix.diagonal_apply]
      exact hinvval
    · simp [hrc]
  have hnorm : ‖Matrix.diagonal (fun k : Fin D => Complex.ofReal (Real.sqrt (D : ℝ)))‖
      = Real.sqrt (D : ℝ) := by
    rw [Matrix.l2_opNorm_diagonal]
    have hpi : ‖fun _ : Fin D => Complex.ofReal (Real.sqrt (D : ℝ))‖
        = ‖Complex.ofReal (Real.sqrt (D : ℝ))‖ := by
      refine le_antisymm ?_ ?_
      · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
        intro i
        simp
      · exact norm_le_pi_norm (fun _ : Fin D => Complex.ofReal (Real.sqrt (D : ℝ)))
          (⟨0, hD⟩ : Fin D)
    rw [hpi]
    exact Complex.norm_of_nonneg (Real.sqrt_nonneg _)
  unfold referenceWeight
  rw [hρ, hsqrt, hinv, hmat]
  exact hnorm

theorem referenceWeight_unbounded (M : ℝ) :
    ∃ (D : ℕ) (hD : 0 < D) (β : ℝ),
      referenceWeight (diagonalGibbsDensity D hD (fun _ => 0) β) > M := by
  set n := (Nat.ceil M + 1 : ℕ) with hn
  refine ⟨n ^ 2, by positivity, 0, ?_⟩
  rw [referenceWeight_flatGibbs, Nat.cast_pow]
  have hnpos : (0 : ℝ) ≤ (n : ℝ) := by
    have : (0:ℕ) ≤ n := by omega
    exact_mod_cast this
  have hsq : Real.sqrt ((n : ℝ) ^ 2) = (n : ℝ) := by
    have h2 : Real.sqrt ((n : ℝ) ^ 2) = Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by
      rw [pow_two, Real.sqrt_mul hnpos (n : ℝ)]
    rw [h2, Real.mul_self_sqrt hnpos]
  rw [hsq]
  have hceil : (M : ℝ) + 1 ≤ (n : ℝ) := by
    have h1 := Nat.le_ceil M
    have h1' : (M : ℝ) ≤ (Nat.ceil M : ℝ) := by exact_mod_cast h1
    have h2 : (Nat.ceil M : ℕ) + 1 ≤ n := by simp [hn]
    have h2' : ((Nat.ceil M : ℕ) + 1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
    linarith
  linarith

theorem mixingTimeBound_prefactor_grows (D : ℕ) (hD : 0 < D) (β : ℝ) (γ η : ℝ) :
    Real.log ((referenceWeight (diagonalGibbsDensity D hD (fun _ => 0) β) + 1) / η) / γ
      = Real.log ((Real.sqrt (D : ℝ) + 1) / η) / γ := by
  rw [referenceWeight_flatGibbs]

theorem thermalAcceptance_highTemperature (E : Fin D → ℝ) (i j : Fin D) :
    thermalAcceptance E 0 i j = 1 := by
  unfold thermalAcceptance
  rw [neg_zero, zero_mul, Real.exp_zero]
  exact min_eq_left (by norm_num)

theorem thermalKernel_highTemperature (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (i j : Fin D) :
    thermalKernel D E 0 i j = 1 / (D : ℝ) := by
  by_cases hij : i = j
  · subst hij
    rw [thermalKernel, if_pos rfl]
    have hsum : (∑ j' ∈ (Finset.univ : Finset (Fin D)).erase i,
        thermalAcceptance E 0 i j' / (D : ℝ)) = 1 - 1 / (D : ℝ) := by
      have h1 : (∑ j' ∈ (Finset.univ : Finset (Fin D)).erase i,
          thermalAcceptance E 0 i j' / (D : ℝ))
          = ∑ j' ∈ (Finset.univ : Finset (Fin D)).erase i, (1 : ℝ) / (D : ℝ) := by
        refine Finset.sum_congr rfl fun j' _ => ?_
        rw [thermalAcceptance_highTemperature E i j']
      have h2 : (∑ j' ∈ (Finset.univ : Finset (Fin D)).erase i, (1 : ℝ) / (D : ℝ))
          + (1 : ℝ) / (D : ℝ) = 1 := by
        rw [Finset.sum_erase_add (Finset.univ : Finset (Fin D))
          (fun _ => (1 : ℝ) / (D : ℝ)) (Finset.mem_univ i)]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        rw [nsmul_eq_mul]
        have hne : (D : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
        field_simp
      rw [h1]
      linarith
    rw [hsum]
    ring
  · rw [thermalKernel, if_neg hij, thermalAcceptance_highTemperature E i j]

theorem ckRejectMass_highTemperature (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (j : Fin D) :
    ckRejectMass D E 0 j = 1 / (D : ℝ) := by
  rw [ckRejectMass_eq]
  have hsum : (∑ j' ∈ (Finset.univ : Finset (Fin D)).erase j,
      thermalAcceptance E 0 j j' / (D : ℝ)) = 1 - 1 / (D : ℝ) := by
    have h1 : (∑ j' ∈ (Finset.univ : Finset (Fin D)).erase j,
        thermalAcceptance E 0 j j' / (D : ℝ))
        = ∑ j' ∈ (Finset.univ : Finset (Fin D)).erase j, (1 : ℝ) / (D : ℝ) := by
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [thermalAcceptance_highTemperature E j j']
    have h2 : (∑ j' ∈ (Finset.univ : Finset (Fin D)).erase j, (1 : ℝ) / (D : ℝ))
        + (1 : ℝ) / (D : ℝ) = 1 := by
      rw [Finset.sum_erase_add (Finset.univ : Finset (Fin D))
        (fun _ => (1 : ℝ) / (D : ℝ)) (Finset.mem_univ j)]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [nsmul_eq_mul]
      have hne : (D : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
      field_simp
    rw [h1]
    linarith
  rw [hsum]
  ring

theorem ckOneStepInflow_highTemperature (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ)
    (p : Fin D → ℝ) (hpsum : ∑ i : Fin D, p i = 1) (j : Fin D) :
    ckOneStepInflow D E 0 p j = 1 / (D : ℝ) := by
  rw [ckOneStepInflow_eq_kernel]
  calc (∑ i : Fin D, thermalKernel D E 0 i j * p i)
      = ∑ i : Fin D, (1 / (D : ℝ)) * p i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [thermalKernel_highTemperature D hD E i j]
    _ = (1 / (D : ℝ)) * (∑ i : Fin D, p i) := by rw [Finset.mul_sum]
    _ = 1 / (D : ℝ) := by rw [hpsum, mul_one]

theorem ckRecoveryTail_highTemperature (D : ℕ) (hD : 1 < D) (E : Fin D → ℝ)
    (p : Fin D → ℝ) (j : Fin D) (N : ℕ) :
    ckRecoveryTail D E 0 p j N = (1 / (D : ℝ)) ^ N * p j / (1 - 1 / (D : ℝ)) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (Nat.zero_lt_of_lt hD)
  have hD0 : 0 < D := Nat.zero_lt_of_lt hD
  have hrw : ckRejectMass D E 0 j = 1 / (D : ℝ) :=
    ckRejectMass_highTemperature D hD0 E j
  have hnonneg : 0 ≤ ckRejectMass D E 0 j := by
    rw [hrw]
    positivity
  have hD1 : (1 : ℝ) < D := by exact_mod_cast hD
  have hlt : ckRejectMass D E 0 j < 1 := by
    rw [hrw]
    exact (div_lt_iff₀ hDpos).mpr (by linarith)
  rw [ckRecoveryTail_eq D E 0 p j N hnonneg hlt, hrw]

theorem clause3_own_sampler_only (D : ℕ) (E₁ E₂ : Fin D → ℝ) (β₁ β₂ : ℝ)
    (h : E₁ = E₂) (hβ : β₁ = β₂) (p : Fin D → ℝ) (N : ℕ) (j : Fin D) :
    ckRecoveryTail D E₂ β₂ p j N = ckRecoveryTail D E₁ β₁ p j N := by
  rw [h, hβ]

theorem ckConsumer_transition_matrix (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) :
    IsTransitionMatrix (ckConsumerKernel D E β) := by
  have h := diagonal_metropolis_transition_reversible D hD E β
  exact h.1

theorem ckConsumer_reversible_gibbs (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) :
    IsReversible (ckConsumerKernel D E β) (diagonalGibbsDist D hD E β).prob := by
  have h := diagonal_metropolis_transition_reversible D hD E β
  exact h.2.1

theorem ckConsumer_stationary_gibbs (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) :
    Qatlib.Concepts.WalkSearch.TwoLevelLower.IsStationary (ckConsumerKernel D E β)
      (diagonalGibbsDist D hD E β).prob := by
  have h := diagonal_metropolis_transition_reversible D hD E β
  exact h.2.2.1

end

end Qatlib.Concepts.LindbladFlow.GkslSemigroup
