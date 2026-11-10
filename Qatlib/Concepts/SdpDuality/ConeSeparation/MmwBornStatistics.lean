/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.SharedMatrixOptimization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.SdpDuality.ConeSeparation.SdpDuality
open Qatlib.Concepts.MatrixWeights.ApproxGibbs
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G7
open Qatlib.Concepts.MatrixWeights.WeightsCore
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Qatlib.Concepts.SdpDuality.ConeSeparation

open Qatlib
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib
open scoped BigOperators Classical ComplexOrder Matrix.Norms.L2Operator

noncomputable section

structure MmwAdaptiveRun (O D T : ℕ) where

  round : (t : ℕ) → (ht : t < T) → (Fin t → Fin O) → MmwRound O D

def MmwAdaptiveRun.prefixOf {O D T : ℕ} (R : MmwAdaptiveRun O D T)
    (t : ℕ) (ht : t < T) (ω : Fin T → Fin O) : Fin t → Fin O :=
  fun s => ω ⟨(s : ℕ), Nat.lt_trans s.isLt ht⟩

def MmwAdaptiveRun.roundAt {O D T : ℕ} (R : MmwAdaptiveRun O D T) (t : Fin T)
    (ω : Fin T → Fin O) : MmwRound O D :=
  R.round (t : ℕ) t.isLt (R.prefixOf (t : ℕ) t.isLt ω)

def MmwAdaptiveRun.transcriptProb {O D T : ℕ} (R : MmwAdaptiveRun O D T)
    (ω : Fin T → Fin O) : ℝ :=
  ∏ t : Fin T, (R.roundAt t ω).law.prob (ω t)

def MmwAdaptiveRun.recordOf {O D T : ℕ} (R : MmwAdaptiveRun O D T) (t : Fin T)
    (ω : Fin T → Fin O) : ℝ :=
  (R.roundAt t ω).record (ω t)

def MmwAdaptiveRun.payoffOf {O D T : ℕ} (R : MmwAdaptiveRun O D T) (t : Fin T)
    (ω : Fin T → Fin O) : ℝ :=
  (R.roundAt t ω).actualPayoff

def MmwAdaptiveRun.devAt {O D T : ℕ} (R : MmwAdaptiveRun O D T) (t : Fin T)
    (ω : Fin T → Fin O) : ℝ :=
  R.recordOf t ω - R.payoffOf t ω

def MmwAdaptiveRun.cumRecord {O D T : ℕ} (R : MmwAdaptiveRun O D T)
    (ω : Fin T → Fin O) : ℝ :=
  ∑ t : Fin T, R.recordOf t ω

def MmwAdaptiveRun.cumPayoff {O D T : ℕ} (R : MmwAdaptiveRun O D T)
    (ω : Fin T → Fin O) : ℝ :=
  ∑ t : Fin T, R.payoffOf t ω

def MmwAdaptiveRun.cumDev {O D T : ℕ} (R : MmwAdaptiveRun O D T)
    (ω : Fin T → Fin O) : ℝ :=
  ∑ t : Fin T, R.devAt t ω

def MmwAdaptiveRun.eventMass {O D T : ℕ} (R : MmwAdaptiveRun O D T)
    (E : Finset (Fin T → Fin O)) : ℝ :=
  ∑ ω ∈ E, R.transcriptProb ω

theorem MmwAdaptiveRun.transcriptProb_nonneg {O D T : ℕ}
    (R : MmwAdaptiveRun O D T) (ω : Fin T → Fin O) : 0 ≤ R.transcriptProb ω :=
  Finset.prod_nonneg fun t _ => (R.roundAt t ω).law.nonneg _

def MmwAdaptiveRun.trunc {O D : ℕ} {T : ℕ} (R : MmwAdaptiveRun O D (T + 1)) :
    MmwAdaptiveRun O D T where
  round t ht h := R.round t (Nat.lt_succ_of_lt ht) h

def MmwAdaptiveRun.lastRound {O D : ℕ} {T : ℕ} (R : MmwAdaptiveRun O D (T + 1)) :
    (Fin T → Fin O) → MmwRound O D :=
  R.round T (Nat.lt_succ_self T)

theorem snoc_val_lt {O T : ℕ} (π : Fin T → Fin O) (o : Fin O) (k : ℕ)
    (h : k < T) :
    (show Fin (T + 1) → Fin O from Fin.snoc π o) ⟨k, Nat.lt_succ_of_lt h⟩
      = π ⟨k, h⟩ := by
  simp only [Fin.snoc]
  split
  · rfl
  · omega

theorem MmwAdaptiveRun.prefixOf_snoc_cast {O D : ℕ} {T : ℕ}
    (R : MmwAdaptiveRun O D (T + 1)) (t : ℕ) (ht : t < T)
    (π : Fin T → Fin O) (o : Fin O) :
    R.prefixOf t (Nat.lt_succ_of_lt ht) (Fin.snoc π o)
      = R.trunc.prefixOf t ht π := by
  funext s
  exact snoc_val_lt π o ↑s (Nat.lt_trans s.isLt ht)

theorem MmwAdaptiveRun.prefixOf_snoc_last {O D : ℕ} {T : ℕ}
    (R : MmwAdaptiveRun O D (T + 1)) (π : Fin T → Fin O) (o : Fin O) :
    R.prefixOf T (Nat.lt_succ_self T) (Fin.snoc π o) = π := by
  funext s
  exact snoc_val_lt π o ↑s s.isLt

def transcriptSnocEquiv (T O : ℕ) :
    (Fin T → Fin O) × Fin O ≃ (Fin (T + 1) → Fin O) where
  toFun p := Fin.snoc p.1 p.2
  invFun ω := (Fin.init ω, ω (Fin.last T))
  left_inv p := by
    refine Prod.ext ?_ ?_
    · simp [Fin.init_snoc]
    · simp [Fin.snoc_last]
  right_inv ω := by simp [Fin.snoc_init_self]

theorem sum_transcripts_snoc {O : ℕ} {M : Type} [AddCommMonoid M] {T : ℕ}
    (g : (Fin (T + 1) → Fin O) → M) :
    (∑ ω : Fin (T + 1) → Fin O, g ω)
      = ∑ π : Fin T → Fin O, ∑ o : Fin O, g (Fin.snoc π o) := by
  rw [← Fintype.sum_equiv (transcriptSnocEquiv T O)
    (fun p => g (transcriptSnocEquiv T O p)) g (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun y _ => rfl

theorem sum_transcripts_zero {O : ℕ} (g : (Fin 0 → Fin O) → ℝ) :
    (∑ ω : Fin 0 → Fin O, g ω) = g (fun i => Fin.elim0 i) := by
  haveI : Unique (Fin 0 → Fin O) :=
    ⟨⟨fun i => Fin.elim0 i⟩, fun a => funext fun i => Fin.elim0 i⟩
  rw [Finset.univ_unique, Finset.sum_singleton]
  exact congrArg g (Subsingleton.elim _ _)

theorem MmwAdaptiveRun.roundAt_castSucc_snoc {O D : ℕ} {T : ℕ}
    (R : MmwAdaptiveRun O D (T + 1)) (t : Fin T) (π : Fin T → Fin O)
    (o : Fin O) :
    R.roundAt t.castSucc (Fin.snoc π o) = R.trunc.roundAt t π := by
  show R.round (t : ℕ) (Nat.lt_succ_of_lt t.isLt)
      (R.prefixOf (t : ℕ) (Nat.lt_succ_of_lt t.isLt) (Fin.snoc π o))
      = R.trunc.roundAt t π
  rw [prefixOf_snoc_cast]
  rfl

theorem MmwAdaptiveRun.roundAt_snoc_last {O D : ℕ} {T : ℕ}
    (R : MmwAdaptiveRun O D (T + 1)) (π : Fin T → Fin O) (o : Fin O) :
    R.roundAt (Fin.last T) (Fin.snoc π o) = R.lastRound π := by
  show R.round T (Nat.lt_succ_self T)
      (R.prefixOf T (Nat.lt_succ_self T) (Fin.snoc π o)) = R.lastRound π
  exact congrArg (R.round T (Nat.lt_succ_self T)) (prefixOf_snoc_last R π o)

theorem MmwAdaptiveRun.recordOf_castSucc_snoc {O D : ℕ} {T : ℕ}
    (R : MmwAdaptiveRun O D (T + 1)) (t : Fin T) (π : Fin T → Fin O)
    (o : Fin O) :
    R.recordOf t.castSucc (Fin.snoc π o) = R.trunc.recordOf t π := by
  simp only [MmwAdaptiveRun.recordOf]
  rw [roundAt_castSucc_snoc, Fin.snoc_castSucc]

theorem MmwAdaptiveRun.payoffOf_castSucc_snoc {O D : ℕ} {T : ℕ}
    (R : MmwAdaptiveRun O D (T + 1)) (t : Fin T) (π : Fin T → Fin O)
    (o : Fin O) :
    R.payoffOf t.castSucc (Fin.snoc π o) = R.trunc.payoffOf t π := by
  simp only [MmwAdaptiveRun.payoffOf]
  rw [roundAt_castSucc_snoc]

theorem MmwAdaptiveRun.recordOf_snoc_last {O D : ℕ} {T : ℕ}
    (R : MmwAdaptiveRun O D (T + 1)) (π : Fin T → Fin O) (o : Fin O) :
    R.recordOf (Fin.last T) (Fin.snoc π o) = (R.lastRound π).record o := by
  simp only [MmwAdaptiveRun.recordOf]
  rw [roundAt_snoc_last, Fin.snoc_last]

theorem MmwAdaptiveRun.payoffOf_snoc_last {O D : ℕ} {T : ℕ}
    (R : MmwAdaptiveRun O D (T + 1)) (π : Fin T → Fin O) (o : Fin O) :
    R.payoffOf (Fin.last T) (Fin.snoc π o) = (R.lastRound π).actualPayoff := by
  simp only [MmwAdaptiveRun.payoffOf]
  rw [roundAt_snoc_last]

theorem MmwAdaptiveRun.transcriptProb_snoc {O D : ℕ} {T : ℕ}
    (R : MmwAdaptiveRun O D (T + 1)) (π : Fin T → Fin O) (o : Fin O) :
    R.transcriptProb (Fin.snoc π o)
      = R.trunc.transcriptProb π * (R.lastRound π).law.prob o := by
  simp only [MmwAdaptiveRun.transcriptProb]
  rw [Fin.prod_univ_castSucc, roundAt_snoc_last, Fin.snoc_last]
  refine congrArg (fun p => p * (R.lastRound π).law.prob o) ?_
  exact Finset.prod_congr rfl fun t _ => by
    rw [roundAt_castSucc_snoc, Fin.snoc_castSucc]

theorem MmwAdaptiveRun.cumDev_snoc {O D : ℕ} {T : ℕ}
    (R : MmwAdaptiveRun O D (T + 1)) (π : Fin T → Fin O) (o : Fin O) :
    R.cumDev (Fin.snoc π o) = R.trunc.cumDev π
      + ((R.lastRound π).record o - (R.lastRound π).actualPayoff) := by
  have h1 : ∀ t : Fin T,
      R.devAt t.castSucc (Fin.snoc π o) = R.trunc.devAt t π := by
    intro t
    simp only [MmwAdaptiveRun.devAt]
    rw [recordOf_castSucc_snoc, payoffOf_castSucc_snoc]
  have h2 : R.devAt (Fin.last T) (Fin.snoc π o)
      = (R.lastRound π).record o - (R.lastRound π).actualPayoff := by
    simp only [MmwAdaptiveRun.devAt]
    rw [recordOf_snoc_last, payoffOf_snoc_last]
  show ∑ t : Fin (T + 1), R.devAt t (Fin.snoc π o)
      = ∑ t : Fin T, R.trunc.devAt t π
        + ((R.lastRound π).record o - (R.lastRound π).actualPayoff)
  rw [Fin.sum_univ_castSucc, h2, Finset.sum_congr rfl (fun t _ => h1 t)]

theorem cond_record_mean {O D T : ℕ} (R : MmwAdaptiveRun O D T) (t : ℕ)
    (ht : t < T) (h : Fin t → Fin O) :
    (∑ o : Fin O, (R.round t ht h).law.prob o * (R.round t ht h).record o)
      = (R.round t ht h).actualPayoff :=
  mmwRound_record_mean (R.round t ht h)

theorem actualPayoff_mem_unit {O D : ℕ} (r : MmwRound O D) :
    0 ≤ r.actualPayoff ∧ r.actualPayoff ≤ 1 := by
  have h := (mmwRound_record_mean r).symm
  rw [h]
  refine ⟨Finset.sum_nonneg fun o _ => mul_nonneg (r.law.nonneg o) (r.hf o).1, ?_⟩
  have hle : (∑ o : Fin O, r.law.prob o * r.f o) ≤ ∑ o : Fin O, r.law.prob o * 1 :=
    Finset.sum_le_sum fun o _ => mul_le_mul_of_nonneg_left (r.hf o).2 (r.law.nonneg o)
  have h1 : ∑ o : Fin O, r.law.prob o * 1 = 1 := by
    rw [← Finset.sum_mul, r.law.sum_one, mul_one]
  rw [h1] at hle
  exact hle

theorem devAt_abs_le_one {O D T : ℕ} (R : MmwAdaptiveRun O D T) (t : Fin T)
    (ω : Fin T → Fin O) : |R.devAt t ω| ≤ 1 := by
  have h1 := (R.roundAt t ω).hf (ω t)
  have h2 := actualPayoff_mem_unit (R.roundAt t ω)
  simp only [MmwAdaptiveRun.devAt, MmwAdaptiveRun.recordOf, MmwAdaptiveRun.payoffOf,
    MmwRound.record]
  rw [abs_le]
  constructor <;> linarith

theorem expect_snoc {O D : ℕ} {T : ℕ} (R : MmwAdaptiveRun O D (T + 1))
    (F : (Fin (T + 1) → Fin O) → ℝ) :
    (∑ ω : Fin (T + 1) → Fin O, R.transcriptProb ω * F ω)
      = ∑ π : Fin T → Fin O, R.trunc.transcriptProb π
          * (∑ o : Fin O, (R.lastRound π).law.prob o * F (Fin.snoc π o)) := by
  rw [sum_transcripts_snoc (g := fun ω => R.transcriptProb ω * F ω)]
  refine Finset.sum_congr rfl fun π _ => ?_
  simp only [MmwAdaptiveRun.transcriptProb_snoc]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun o _ => by ring

theorem MmwAdaptiveRun.transcriptProb_sum {O D : ℕ} :
    ∀ (T : ℕ) (R : MmwAdaptiveRun O D T),
      (∑ ω : Fin T → Fin O, R.transcriptProb ω) = 1 := by
  intro T
  induction T with
  | zero =>
    intro R
    rw [sum_transcripts_zero]
    simp [MmwAdaptiveRun.transcriptProb]
  | succ T ih =>
    intro R
    have h := expect_snoc R (fun _ => (1 : ℝ))
    simp only [mul_one] at h
    have hin : ∀ π : Fin T → Fin O,
        (∑ o : Fin O, (R.lastRound π).law.prob o) = 1 := fun π =>
      (R.lastRound π).law.sum_one
    rw [h]
    simp only [hin, mul_one]
    exact ih R.trunc

theorem cumDev_expect_zero {O D : ℕ} :
    ∀ (T : ℕ) (R : MmwAdaptiveRun O D T),
      (∑ ω : Fin T → Fin O, R.transcriptProb ω * R.cumDev ω) = 0 := by
  intro T
  induction T with
  | zero =>
    intro R
    simp [MmwAdaptiveRun.cumDev, MmwAdaptiveRun.devAt]
  | succ T ih =>
    intro R
    rw [expect_snoc R R.cumDev]
    simp only [MmwAdaptiveRun.cumDev_snoc]
    have hin : ∀ π : Fin T → Fin O,
        (∑ o : Fin O, (R.lastRound π).law.prob o
            * (R.trunc.cumDev π + ((R.lastRound π).record o
                - (R.lastRound π).actualPayoff)))
          = R.trunc.cumDev π := by
      intro π
      have hsplit : ∀ o : Fin O,
          (R.lastRound π).law.prob o
              * (R.trunc.cumDev π + ((R.lastRound π).record o
                - (R.lastRound π).actualPayoff))
            = (R.lastRound π).law.prob o * R.trunc.cumDev π
              + ((R.lastRound π).law.prob o * (R.lastRound π).record o
                - (R.lastRound π).law.prob o * (R.lastRound π).actualPayoff) :=
        fun o => by ring
      have h1 : (∑ o : Fin O, (R.lastRound π).law.prob o * R.trunc.cumDev π)
          = R.trunc.cumDev π := by
        rw [← Finset.sum_mul, (R.lastRound π).law.sum_one, one_mul]
      have h2 : (∑ o : Fin O, (R.lastRound π).law.prob o * (R.lastRound π).record o)
          = (R.lastRound π).actualPayoff :=
        mmwRound_record_mean (R.lastRound π)
      have h3 : (∑ o : Fin O,
            (R.lastRound π).law.prob o * (R.lastRound π).actualPayoff)
          = (R.lastRound π).actualPayoff := by
        rw [← Finset.sum_mul, (R.lastRound π).law.sum_one, one_mul]
      rw [Finset.sum_congr rfl (fun o _ => hsplit o), Finset.sum_add_distrib,
        Finset.sum_sub_distrib, h1, h2, h3]
      ring
    simp only [hin]
    exact ih R.trunc

theorem cumRecord_eq {O D T : ℕ} (R : MmwAdaptiveRun O D T) (ω : Fin T → Fin O) :
    R.cumRecord ω = R.cumPayoff ω + R.cumDev ω := by
  simp only [MmwAdaptiveRun.cumRecord, MmwAdaptiveRun.cumPayoff, MmwAdaptiveRun.cumDev,
    MmwAdaptiveRun.devAt]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem exp_le_cosh_sinh (lam x : ℝ) (hx : -1 ≤ x) (hx' : x ≤ 1) :
    Real.exp (lam * x) ≤ Real.cosh lam + Real.sinh lam * x := by
  have h := Real.exp_mul_le_cosh_add_mul_sinh (abs_le.mpr ⟨hx, hx'⟩) lam
  rw [mul_comm x lam, mul_comm x (Real.sinh lam)] at h
  exact h

theorem exp_chord_law {O : ℕ} (p d : Fin O → ℝ) (hp0 : ∀ o, 0 ≤ p o)
    (hp1 : ∑ o, p o = 1) (hd : ∀ o, |d o| ≤ 1) (hmean : ∑ o, p o * d o = 0)
    (lam : ℝ) :
    (∑ o, p o * Real.exp (lam * d o)) ≤ Real.cosh lam := by
  have hchord : ∀ o : Fin O,
      Real.exp (lam * d o) ≤ Real.cosh lam + Real.sinh lam * d o :=
    fun o => exp_le_cosh_sinh lam (d o) (abs_le.mp (hd o)).1 (abs_le.mp (hd o)).2
  have hdistrib : ∀ o : Fin O,
      p o * (Real.cosh lam + Real.sinh lam * d o)
      = p o * Real.cosh lam + p o * (Real.sinh lam * d o) := fun o => by ring
  have hsplit : (∑ o, p o * (Real.cosh lam + Real.sinh lam * d o))
      = (∑ o, p o * Real.cosh lam) + (∑ o, p o * (Real.sinh lam * d o)) := by
    rw [Finset.sum_congr rfl (fun o _ => hdistrib o), Finset.sum_add_distrib]
  have hc : (∑ o : Fin O, p o * Real.cosh lam) = Real.cosh lam := by
    rw [← Finset.sum_mul, hp1, one_mul]
  have hs : (∑ o : Fin O, p o * (Real.sinh lam * d o)) = 0 := by
    have hre : ∀ o : Fin O,
        p o * (Real.sinh lam * d o) = Real.sinh lam * (p o * d o) := fun o => by ring
    rw [Finset.sum_congr rfl (fun o _ => hre o), ← Finset.mul_sum, hmean, mul_zero]
  calc (∑ o, p o * Real.exp (lam * d o))
      ≤ ∑ o, p o * (Real.cosh lam + Real.sinh lam * d o) :=
        Finset.sum_le_sum fun o _ => mul_le_mul_of_nonneg_left (hchord o) (hp0 o)
    _ = Real.cosh lam := by rw [hsplit, hc, hs, add_zero]

theorem lastRound_dev_mean {O D : ℕ} {T : ℕ} (R : MmwAdaptiveRun O D (T + 1))
    (π : Fin T → Fin O) :
    (∑ o : Fin O, (R.lastRound π).law.prob o
        * ((R.lastRound π).record o - (R.lastRound π).actualPayoff)) = 0 := by
  have hsplit : ∀ o : Fin O,
      (R.lastRound π).law.prob o * ((R.lastRound π).record o
          - (R.lastRound π).actualPayoff)
        = (R.lastRound π).law.prob o * (R.lastRound π).record o
          - (R.lastRound π).law.prob o * (R.lastRound π).actualPayoff :=
    fun o => by ring
  have h2 : (∑ o : Fin O, (R.lastRound π).law.prob o * (R.lastRound π).record o)
      = (R.lastRound π).actualPayoff :=
    mmwRound_record_mean (R.lastRound π)
  have h3 : (∑ o : Fin O,
        (R.lastRound π).law.prob o * (R.lastRound π).actualPayoff)
      = (R.lastRound π).actualPayoff := by
    rw [← Finset.sum_mul, (R.lastRound π).law.sum_one, one_mul]
  rw [Finset.sum_congr rfl (fun o _ => hsplit o), Finset.sum_sub_distrib, h2, h3,
    sub_self]

theorem cumDev_mgf {O D : ℕ} :
    ∀ (T : ℕ) (R : MmwAdaptiveRun O D T) (lam : ℝ),
      (∑ ω : Fin T → Fin O, R.transcriptProb ω * Real.exp (lam * R.cumDev ω))
        ≤ (Real.cosh lam) ^ T := by
  intro T
  induction T with
  | zero =>
    intro R lam
    rw [sum_transcripts_zero]
    simp [MmwAdaptiveRun.transcriptProb, MmwAdaptiveRun.cumDev,
      MmwAdaptiveRun.devAt]
  | succ T ih =>
    intro R lam
    rw [expect_snoc R (fun ω => Real.exp (lam * R.cumDev ω))]
    simp only [MmwAdaptiveRun.cumDev_snoc]
    have hd : ∀ π : Fin T → Fin O, ∀ o : Fin O,
        |(R.lastRound π).record o - (R.lastRound π).actualPayoff| ≤ 1 := by
      intro π o
      have h1 := (R.lastRound π).hf o
      have h2 := actualPayoff_mem_unit (R.lastRound π)
      simp only [MmwRound.record]
      rw [abs_le]
      constructor <;> linarith
    have hin : ∀ π : Fin T → Fin O,
        (∑ o : Fin O, (R.lastRound π).law.prob o
            * Real.exp (lam * (R.trunc.cumDev π
              + ((R.lastRound π).record o - (R.lastRound π).actualPayoff))))
      ≤ Real.exp (lam * R.trunc.cumDev π) * Real.cosh lam := by
      intro π
      have hexp : ∀ o : Fin O,
          Real.exp (lam * (R.trunc.cumDev π
              + ((R.lastRound π).record o - (R.lastRound π).actualPayoff)))
          = Real.exp (lam * R.trunc.cumDev π)
            * Real.exp (lam * ((R.lastRound π).record o
              - (R.lastRound π).actualPayoff)) := by
        intro o
        rw [show lam * (R.trunc.cumDev π
              + ((R.lastRound π).record o - (R.lastRound π).actualPayoff))
            = lam * R.trunc.cumDev π
              + lam * ((R.lastRound π).record o
                - (R.lastRound π).actualPayoff) from by ring,
          Real.exp_add]
      have hring : ∀ o : Fin O,
          (R.lastRound π).law.prob o
              * Real.exp (lam * (R.trunc.cumDev π
                + ((R.lastRound π).record o - (R.lastRound π).actualPayoff)))
          = Real.exp (lam * R.trunc.cumDev π)
              * ((R.lastRound π).law.prob o
                * Real.exp (lam * ((R.lastRound π).record o
                  - (R.lastRound π).actualPayoff))) := by
        intro o
        rw [hexp o]
        ring
      rw [Finset.sum_congr rfl (fun o _ => hring o), ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (exp_chord_law (R.lastRound π).law.prob
          (fun o => (R.lastRound π).record o - (R.lastRound π).actualPayoff)
          (R.lastRound π).law.nonneg (R.lastRound π).law.sum_one
          (hd π) (lastRound_dev_mean R π) lam)
        (Real.exp_nonneg _)
    have hprod : ∀ π : Fin T → Fin O,
        R.trunc.transcriptProb π
          * (Real.exp (lam * R.trunc.cumDev π) * Real.cosh lam)
        = (R.trunc.transcriptProb π * Real.exp (lam * R.trunc.cumDev π))
          * Real.cosh lam := fun π => by ring
    calc (∑ π : Fin T → Fin O, R.trunc.transcriptProb π
            * (∑ o : Fin O, (R.lastRound π).law.prob o
                * Real.exp (lam * (R.trunc.cumDev π
                  + ((R.lastRound π).record o - (R.lastRound π).actualPayoff)))))
        ≤ ∑ π : Fin T → Fin O, R.trunc.transcriptProb π
            * (Real.exp (lam * R.trunc.cumDev π) * Real.cosh lam) :=
          Finset.sum_le_sum fun π _ => mul_le_mul_of_nonneg_left (hin π)
            (R.trunc.transcriptProb_nonneg π)
      _ = (∑ π : Fin T → Fin O,
            R.trunc.transcriptProb π * Real.exp (lam * R.trunc.cumDev π))
          * Real.cosh lam := by
          rw [Finset.sum_congr rfl (fun π _ => hprod π), ← Finset.sum_mul]
      _ ≤ (Real.cosh lam) ^ T * Real.cosh lam :=
          mul_le_mul_of_nonneg_right (ih R.trunc lam) (Real.cosh_pos lam).le
      _ = (Real.cosh lam) ^ (T + 1) := by rw [pow_succ]

theorem upperTail_bound {O D T : ℕ} (R : MmwAdaptiveRun O D T) (δ lam : ℝ)
    (hlam : 0 ≤ lam) :
    R.eventMass ((Finset.univ : Finset (Fin T → Fin O)).filter
      (fun ω => δ ≤ R.cumDev ω))
      ≤ Real.exp ((T : ℝ) * lam ^ 2 / 2 - lam * δ) := by
  have hP : ∀ ω, 0 ≤ R.transcriptProb ω := R.transcriptProb_nonneg
  unfold MmwAdaptiveRun.eventMass
  calc (∑ ω ∈ (Finset.univ : Finset (Fin T → Fin O)).filter
          (fun ω => δ ≤ R.cumDev ω), R.transcriptProb ω)
      ≤ (∑ ω ∈ (Finset.univ : Finset (Fin T → Fin O)).filter
          (fun ω => δ ≤ R.cumDev ω),
          R.transcriptProb ω * Real.exp (lam * (R.cumDev ω - δ))) := by
        refine Finset.sum_le_sum fun ω hω => ?_
        have hm : (1 : ℝ) ≤ Real.exp (lam * (R.cumDev ω - δ)) :=
          Real.one_le_exp_iff.mpr
            (mul_nonneg hlam (sub_nonneg.mpr (Finset.mem_filter.mp hω).2))
        exact le_mul_of_one_le_right (hP ω) hm
    _ = (∑ ω ∈ (Finset.univ : Finset (Fin T → Fin O)).filter
          (fun ω => δ ≤ R.cumDev ω),
          R.transcriptProb ω * (Real.exp (lam * R.cumDev ω)
            * Real.exp (-(lam * δ)))) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [show lam * (R.cumDev ω - δ) = lam * R.cumDev ω + -(lam * δ) from by ring,
          ← Real.exp_add]
    _ ≤ (∑ ω : Fin T → Fin O,
          R.transcriptProb ω * (Real.exp (lam * R.cumDev ω)
            * Real.exp (-(lam * δ)))) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun ω _ _ => mul_nonneg (hP ω)
            (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)))
    _ = Real.exp (-(lam * δ))
        * (∑ ω : Fin T → Fin O,
            R.transcriptProb ω * Real.exp (lam * R.cumDev ω)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ω _ => by ring
    _ ≤ Real.exp (-(lam * δ)) * (Real.cosh lam) ^ T :=
        mul_le_mul_of_nonneg_left (cumDev_mgf T R lam) (Real.exp_nonneg _)
    _ ≤ Real.exp (-(lam * δ)) * (Real.exp (lam ^ 2 / 2)) ^ T :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Real.cosh_pos lam).le
            (Real.cosh_le_exp_half_sq lam) T)
          (Real.exp_nonneg _)
    _ = Real.exp (-(lam * δ)) * Real.exp ((T : ℝ) * (lam ^ 2 / 2)) := by
        rw [← Real.exp_nat_mul]
    _ = Real.exp ((T : ℝ) * lam ^ 2 / 2 - lam * δ) := by
        rw [show (T : ℝ) * lam ^ 2 / 2 - lam * δ
            = -(lam * δ) + (T : ℝ) * (lam ^ 2 / 2) from by ring,
          ← Real.exp_add]

theorem upperTail_exp {O D T : ℕ} (R : MmwAdaptiveRun O D T) (δ : ℝ)
    (hδ : 0 < δ) :
    R.eventMass ((Finset.univ : Finset (Fin T → Fin O)).filter
      (fun ω => δ ≤ R.cumDev ω))
      ≤ Real.exp (-(δ ^ 2) / (2 * (T : ℝ))) := by
  rcases Nat.eq_zero_or_pos T with hT0 | hTpos
  · subst hT0
    have hc : ∀ ω : Fin 0 → Fin O, R.cumDev ω = 0 := by
      intro ω
      simp [MmwAdaptiveRun.cumDev]
    have hempty : (∑ ω ∈ (Finset.univ : Finset (Fin 0 → Fin O)).filter
        (fun ω => δ ≤ R.cumDev ω), R.transcriptProb ω) = 0 :=
      Finset.sum_eq_zero fun ω hω =>
        absurd (Finset.mem_filter.mp hω).2 (by rw [hc ω]; linarith)
    unfold MmwAdaptiveRun.eventMass
    rw [hempty]
    exact (Real.exp_pos _).le
  · have hTpos' : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hTpos
    have hbound := upperTail_bound R δ (δ / (T : ℝ))
      (div_nonneg hδ.le hTpos'.le)
    have hexp : (T : ℝ) * (δ / (T : ℝ)) ^ 2 / 2 - (δ / (T : ℝ)) * δ
        = -(δ ^ 2) / (2 * (T : ℝ)) := by
      field_simp
      ring
    rwa [hexp] at hbound

theorem lowerTail_bound {O D T : ℕ} (R : MmwAdaptiveRun O D T) (δ lam : ℝ)
    (hδ : 0 ≤ δ) (hlam : lam ≤ 0) :
    R.eventMass ((Finset.univ : Finset (Fin T → Fin O)).filter
      (fun ω => R.cumDev ω ≤ -δ))
      ≤ Real.exp ((T : ℝ) * lam ^ 2 / 2 + lam * δ) := by
  have hP : ∀ ω, 0 ≤ R.transcriptProb ω := R.transcriptProb_nonneg
  unfold MmwAdaptiveRun.eventMass
  calc (∑ ω ∈ (Finset.univ : Finset (Fin T → Fin O)).filter
          (fun ω => R.cumDev ω ≤ -δ), R.transcriptProb ω)
      ≤ (∑ ω ∈ (Finset.univ : Finset (Fin T → Fin O)).filter
          (fun ω => R.cumDev ω ≤ -δ),
          R.transcriptProb ω * Real.exp (lam * (R.cumDev ω + δ))) := by
        refine Finset.sum_le_sum fun ω hω => ?_
        have hm : (1 : ℝ) ≤ Real.exp (lam * (R.cumDev ω + δ)) :=
          Real.one_le_exp_iff.mpr
            (mul_nonneg_of_nonpos_of_nonpos hlam
              (by have := (Finset.mem_filter.mp hω).2; linarith))
        exact le_mul_of_one_le_right (hP ω) hm
    _ = (∑ ω ∈ (Finset.univ : Finset (Fin T → Fin O)).filter
          (fun ω => R.cumDev ω ≤ -δ),
          R.transcriptProb ω * (Real.exp (lam * R.cumDev ω)
            * Real.exp (lam * δ))) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [show lam * (R.cumDev ω + δ) = lam * R.cumDev ω + lam * δ from by ring,
          ← Real.exp_add]
    _ ≤ (∑ ω : Fin T → Fin O,
          R.transcriptProb ω * (Real.exp (lam * R.cumDev ω)
            * Real.exp (lam * δ))) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun ω _ _ => mul_nonneg (hP ω)
            (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)))
    _ = Real.exp (lam * δ)
        * (∑ ω : Fin T → Fin O,
            R.transcriptProb ω * Real.exp (lam * R.cumDev ω)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ω _ => by ring
    _ ≤ Real.exp (lam * δ) * (Real.cosh lam) ^ T :=
        mul_le_mul_of_nonneg_left (cumDev_mgf T R lam) (Real.exp_nonneg _)
    _ ≤ Real.exp (lam * δ) * (Real.exp (lam ^ 2 / 2)) ^ T :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Real.cosh_pos lam).le
            (Real.cosh_le_exp_half_sq lam) T)
          (Real.exp_nonneg _)
    _ = Real.exp (lam * δ) * Real.exp ((T : ℝ) * (lam ^ 2 / 2)) := by
        rw [← Real.exp_nat_mul]
    _ = Real.exp ((T : ℝ) * lam ^ 2 / 2 + lam * δ) := by
        rw [show (T : ℝ) * lam ^ 2 / 2 + lam * δ
            = lam * δ + (T : ℝ) * (lam ^ 2 / 2) from by ring,
          ← Real.exp_add]

theorem lowerTail_exp {O D T : ℕ} (R : MmwAdaptiveRun O D T) (δ : ℝ)
    (hδ : 0 < δ) :
    R.eventMass ((Finset.univ : Finset (Fin T → Fin O)).filter
      (fun ω => R.cumDev ω ≤ -δ))
      ≤ Real.exp (-(δ ^ 2) / (2 * (T : ℝ))) := by
  rcases Nat.eq_zero_or_pos T with hT0 | hTpos
  · subst hT0
    have hc : ∀ ω : Fin 0 → Fin O, R.cumDev ω = 0 := by
      intro ω
      simp [MmwAdaptiveRun.cumDev]
    have hempty : (∑ ω ∈ (Finset.univ : Finset (Fin 0 → Fin O)).filter
        (fun ω => R.cumDev ω ≤ -δ), R.transcriptProb ω) = 0 :=
      Finset.sum_eq_zero fun ω hω =>
        absurd (Finset.mem_filter.mp hω).2 (by rw [hc ω]; linarith)
    unfold MmwAdaptiveRun.eventMass
    rw [hempty]
    exact (Real.exp_pos _).le
  · have hTpos' : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hTpos
    have hbound := lowerTail_bound R δ (-(δ / (T : ℝ))) hδ.le
      (neg_nonpos.mpr (div_nonneg hδ.le hTpos'.le))
    have hexp : (T : ℝ) * (-(δ / (T : ℝ))) ^ 2 / 2 + (-(δ / (T : ℝ))) * δ
        = -(δ ^ 2) / (2 * (T : ℝ)) := by
      field_simp
      ring
    rwa [hexp] at hbound

theorem deviation_failure_mass {O D T : ℕ} (R : MmwAdaptiveRun O D T)
    (δ : ℝ) (hδ : 0 < δ) :
    R.eventMass ((Finset.univ : Finset (Fin T → Fin O)).filter
      (fun ω => δ ≤ |R.cumDev ω|))
      ≤ 2 * Real.exp (-(δ ^ 2) / (2 * (T : ℝ))) := by
  have hsub : ((Finset.univ : Finset (Fin T → Fin O)).filter
        (fun ω => δ ≤ |R.cumDev ω|))
      ⊆ ((Finset.univ : Finset (Fin T → Fin O)).filter
          (fun ω => δ ≤ R.cumDev ω))
        ∪ ((Finset.univ : Finset (Fin T → Fin O)).filter
          (fun ω => R.cumDev ω ≤ -δ)) := by
    intro ω hω
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    rcases le_or_gt 0 (R.cumDev ω) with h | h
    · exact Or.inl (by rwa [abs_of_nonneg h] at hω)
    · refine Or.inr ?_
      rw [abs_of_neg h] at hω
      linarith
  have hdisj : Disjoint
      ((Finset.univ : Finset (Fin T → Fin O)).filter (fun ω => δ ≤ R.cumDev ω))
      ((Finset.univ : Finset (Fin T → Fin O)).filter
        (fun ω => R.cumDev ω ≤ -δ)) := by
    rw [Finset.disjoint_right]
    intro ω hωn hωp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hωn hωp
    linarith
  have hP : ∀ ω, 0 ≤ R.transcriptProb ω := R.transcriptProb_nonneg
  calc R.eventMass ((Finset.univ : Finset (Fin T → Fin O)).filter
        (fun ω => δ ≤ |R.cumDev ω|))
      ≤ R.eventMass (((Finset.univ : Finset (Fin T → Fin O)).filter
          (fun ω => δ ≤ R.cumDev ω))
        ∪ ((Finset.univ : Finset (Fin T → Fin O)).filter
          (fun ω => R.cumDev ω ≤ -δ))) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ω _ _ => hP ω)
    _ = R.eventMass ((Finset.univ : Finset (Fin T → Fin O)).filter
          (fun ω => δ ≤ R.cumDev ω))
        + R.eventMass ((Finset.univ : Finset (Fin T → Fin O)).filter
          (fun ω => R.cumDev ω ≤ -δ)) := by
        unfold MmwAdaptiveRun.eventMass
        rw [Finset.sum_union hdisj]
    _ ≤ Real.exp (-(δ ^ 2) / (2 * (T : ℝ)))
        + Real.exp (-(δ ^ 2) / (2 * (T : ℝ))) :=
        add_le_add (upperTail_exp R δ hδ) (lowerTail_exp R δ hδ)
    _ = 2 * Real.exp (-(δ ^ 2) / (2 * (T : ℝ))) := by ring

structure MmwRunBornReceipt (O D T : ℕ) where

  run : MmwAdaptiveRun O D T

  δ : ℝ

  hδ : 0 < δ

  stopEvent : Finset (Fin T → Fin O)

  timeoutEvent : Finset (Fin T → Fin O)

  hdisj : Disjoint stopEvent timeoutEvent

  hcharged : stopEvent ∪ timeoutEvent ⊆
    (Finset.univ : Finset (Fin T → Fin O)).filter
      (fun ω => δ ≤ |run.cumDev ω|)

def MmwRunBornReceipt.stopMass {O D T : ℕ} (S : MmwRunBornReceipt O D T) : ℝ :=
  S.run.eventMass S.stopEvent

def MmwRunBornReceipt.timeoutMass {O D T : ℕ} (S : MmwRunBornReceipt O D T) : ℝ :=
  S.run.eventMass S.timeoutEvent

theorem MmwRunBornReceipt.discipline {O D T : ℕ} (S : MmwRunBornReceipt O D T) :
    0 ≤ S.stopMass ∧ 0 ≤ S.timeoutMass ∧
      S.stopMass + S.timeoutMass
        ≤ 2 * Real.exp (-(S.δ ^ 2) / (2 * (T : ℝ))) := by
  have hP : ∀ ω, 0 ≤ S.run.transcriptProb ω := S.run.transcriptProb_nonneg
  refine ⟨Finset.sum_nonneg fun ω _ => hP ω,
    Finset.sum_nonneg fun ω _ => hP ω, ?_⟩
  calc S.stopMass + S.timeoutMass
      = S.run.eventMass (S.stopEvent ∪ S.timeoutEvent) := by
        unfold MmwRunBornReceipt.stopMass MmwRunBornReceipt.timeoutMass
          MmwAdaptiveRun.eventMass
        rw [Finset.sum_union S.hdisj]
    _ ≤ S.run.eventMass ((Finset.univ : Finset (Fin T → Fin O)).filter
        (fun ω => S.δ ≤ |S.run.cumDev ω|)) :=
        Finset.sum_le_sum_of_subset_of_nonneg S.hcharged (fun ω _ _ => hP ω)
    _ ≤ 2 * Real.exp (-(S.δ ^ 2) / (2 * (T : ℝ))) :=
        deviation_failure_mass S.run S.δ S.hδ

def MmwAdaptiveRun.lossAt {O D T : ℕ} (R : MmwAdaptiveRun O D T) (t : Fin T)
    (h : Fin (t : ℕ) → Fin O) : Operator D :=
  (R.round (t : ℕ) t.isLt h).observable

def MmwAdaptiveRun.lossSequence {O D T : ℕ} (R : MmwAdaptiveRun O D T)
    (ω : Fin T → Fin O) : ℕ → Operator D :=
  fun s => if hs : s < T
    then (R.round s hs (R.prefixOf s hs ω)).observable
    else 0

def MmwAdaptiveRun.comparatorLoss {O D T : ℕ} (R : MmwAdaptiveRun O D T)
    (σ : Operator D) (ω : Fin T → Fin O) : ℝ :=
  ∑ t : Fin T, (Matrix.trace (R.lossAt t (R.prefixOf (t : ℕ) t.isLt ω) * σ)).re

def MmwAdaptiveRun.followsGibbsUpdate {O D T : ℕ} (R : MmwAdaptiveRun O D T)
    (η : ℝ) : Prop :=
  ∀ (ω : Fin T → Fin O) (t : Fin T),
    (R.roundAt t ω).ρ
      = Qatlib.Concepts.MatrixWeights.WeightsCore.mmwState D (R.lossSequence ω) η (t : ℕ)

theorem lossSequence_hermitian_unit {O D T : ℕ} (R : MmwAdaptiveRun O D T)
    (ω : Fin T → Fin O) (s : ℕ) :
    (R.lossSequence ω s).IsHermitian ∧ ‖R.lossSequence ω s‖ ≤ 1 := by
  unfold MmwAdaptiveRun.lossSequence
  split
  · rename_i hs
    exact ⟨payoffObservable_hermitian _ _, (mmwRound_record_psd_unit _).2⟩
  · exact ⟨Matrix.isHermitian_zero, by simp⟩

theorem pointwise_gibbs_regret {O D T : ℕ} (R : MmwAdaptiveRun O D T)
    (η : ℝ) (σ : Operator D)
    (hD : 0 < D) (hη : 0 < η) (hη1 : η ≤ 1) (hσ : IsDensityOperator σ)
    (hG : R.followsGibbsUpdate η) (ω : Fin T → Fin O) :
    R.cumPayoff ω ≤ R.comparatorLoss σ ω + η * (T : ℝ) + Real.log D / η := by
  have hM : ∀ s, (R.lossSequence ω s).IsHermitian ∧ ‖R.lossSequence ω s‖ ≤ 1 :=
    lossSequence_hermitian_unit R ω
  have hg8 := matrix_mw_noncommuting_regret D T (R.lossSequence ω) η σ
    hD hη hη1 hM hσ
  have hstate : ∀ t : Fin T,
      (Matrix.trace (R.lossSequence ω (t : ℕ)
        * Qatlib.Concepts.MatrixWeights.WeightsCore.mmwState D (R.lossSequence ω) η (t : ℕ))).re
        = R.payoffOf t ω := by
    intro t
    have hst := hG ω t
    have hloss : R.lossSequence ω (t : ℕ) = (R.roundAt t ω).observable := by
      unfold MmwAdaptiveRun.lossSequence MmwAdaptiveRun.roundAt
      rw [dif_pos t.isLt]
    rw [hloss, ← hst]
    rfl
  have hlhs : η * (∑ t ∈ Finset.range T,
      (Matrix.trace (R.lossSequence ω t
        * Qatlib.Concepts.MatrixWeights.WeightsCore.mmwState D (R.lossSequence ω) η t)).re)
      = η * R.cumPayoff ω := by
    congr 1
    rw [Finset.sum_range]
    exact Finset.sum_congr rfl fun t _ => hstate t
  have hcomp : ∀ t : Fin T,
      (Matrix.trace (R.lossSequence ω (t : ℕ) * σ)).re
        = (Matrix.trace (R.lossAt t (R.prefixOf (t : ℕ) t.isLt ω) * σ)).re := by
    intro t
    unfold MmwAdaptiveRun.lossSequence MmwAdaptiveRun.lossAt
    rw [dif_pos t.isLt]
  have hrhs : η * (∑ t ∈ Finset.range T,
      (Matrix.trace (R.lossSequence ω t * σ)).re)
      = η * R.comparatorLoss σ ω := by
    congr 1
    rw [Finset.sum_range]
    exact Finset.sum_congr rfl fun t _ => hcomp t
  have hmul : η * (R.comparatorLoss σ ω + η * (T : ℝ) + Real.log D / η)
      = η * R.comparatorLoss σ ω + η ^ 2 * (T : ℝ) + Real.log D := by
    field_simp
  have hkey : η * R.cumPayoff ω
      ≤ η * (R.comparatorLoss σ ω + η * (T : ℝ) + Real.log D / η) := by
    rw [hmul]
    linarith
  exact (mul_le_mul_iff_of_pos_left hη).mp hkey

theorem expected_recorded_le_comparator {O D T : ℕ}
    (R : MmwAdaptiveRun O D T) (η : ℝ) (σ : Operator D)
    (hD : 0 < D) (hη : 0 < η) (hη1 : η ≤ 1) (hσ : IsDensityOperator σ)
    (hG : R.followsGibbsUpdate η) :
    (∑ ω : Fin T → Fin O, R.transcriptProb ω * R.cumRecord ω)
      ≤ (∑ ω : Fin T → Fin O, R.transcriptProb ω * R.comparatorLoss σ ω)
        + η * (T : ℝ) + Real.log D / η := by
  have hP : ∀ ω, 0 ≤ R.transcriptProb ω := R.transcriptProb_nonneg
  have hsplit : (∑ ω : Fin T → Fin O, R.transcriptProb ω * R.cumRecord ω)
      = (∑ ω : Fin T → Fin O, R.transcriptProb ω * R.cumPayoff ω)
        + (∑ ω : Fin T → Fin O, R.transcriptProb ω * R.cumDev ω) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ω _ => by
      rw [cumRecord_eq R ω]; ring
  have hzero := cumDev_expect_zero T R
  have hpt : ∀ ω : Fin T → Fin O,
      R.cumPayoff ω ≤ R.comparatorLoss σ ω + η * (T : ℝ) + Real.log D / η :=
    pointwise_gibbs_regret R η σ hD hη hη1 hσ hG
  have hconst : (∑ ω : Fin T → Fin O, R.transcriptProb ω)
      * (η * (T : ℝ) + Real.log D / η) = η * (T : ℝ) + Real.log D / η := by
    rw [MmwAdaptiveRun.transcriptProb_sum T R, one_mul]
  have hdist : ∀ ω : Fin T → Fin O,
      R.transcriptProb ω * (R.comparatorLoss σ ω + η * (T : ℝ) + Real.log D / η)
      = R.transcriptProb ω * R.comparatorLoss σ ω
        + R.transcriptProb ω * (η * (T : ℝ) + Real.log D / η) := fun ω => by ring
  have hstep : (∑ ω : Fin T → Fin O,
      R.transcriptProb ω * (R.comparatorLoss σ ω + η * (T : ℝ)
        + Real.log D / η))
      = (∑ ω : Fin T → Fin O, R.transcriptProb ω * R.comparatorLoss σ ω)
        + (∑ ω : Fin T → Fin O,
            R.transcriptProb ω * (η * (T : ℝ) + Real.log D / η)) := by
    rw [Finset.sum_congr rfl (fun ω _ => hdist ω), Finset.sum_add_distrib]
  calc (∑ ω : Fin T → Fin O, R.transcriptProb ω * R.cumRecord ω)
      = (∑ ω : Fin T → Fin O, R.transcriptProb ω * R.cumPayoff ω) := by
        rw [hsplit, hzero, add_zero]
    _ ≤ (∑ ω : Fin T → Fin O,
          R.transcriptProb ω * (R.comparatorLoss σ ω + η * (T : ℝ)
            + Real.log D / η)) :=
        Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hpt ω) (hP ω)
    _ = (∑ ω : Fin T → Fin O, R.transcriptProb ω * R.comparatorLoss σ ω)
        + (∑ ω : Fin T → Fin O,
            R.transcriptProb ω * (η * (T : ℝ) + Real.log D / η)) := hstep
    _ = (∑ ω : Fin T → Fin O, R.transcriptProb ω * R.comparatorLoss σ ω)
        + (η * (T : ℝ) + Real.log D / η) := by
        rw [← Finset.sum_mul, hconst]
    _ = (∑ ω : Fin T → Fin O, R.transcriptProb ω * R.comparatorLoss σ ω)
        + η * (T : ℝ) + Real.log D / η := (add_assoc _ _ _).symm

theorem frontier1 :
    (∀ (O D T : ℕ) (R : MmwAdaptiveRun O D T) (t : ℕ) (ht : t < T)
        (h : Fin t → Fin O),
      (∑ o : Fin O, (R.round t ht h).law.prob o * (R.round t ht h).record o)
        = (R.round t ht h).actualPayoff) ∧
    (∀ (O D T : ℕ) (R : MmwAdaptiveRun O D T),
      (∑ ω : Fin T → Fin O, R.transcriptProb ω * R.cumDev ω) = 0) ∧
    (∀ (O D T : ℕ) (R : MmwAdaptiveRun O D T) (δ : ℝ), 0 < δ →
      R.eventMass ((Finset.univ : Finset (Fin T → Fin O)).filter
        (fun ω => δ ≤ |R.cumDev ω|))
        ≤ 2 * Real.exp (-(δ ^ 2) / (2 * (T : ℝ)))) ∧
    (∀ (O D T : ℕ) (S : MmwRunBornReceipt O D T),
      0 ≤ S.stopMass ∧ 0 ≤ S.timeoutMass ∧
        S.stopMass + S.timeoutMass
          ≤ 2 * Real.exp (-(S.δ ^ 2) / (2 * (T : ℝ)))) ∧
    (∀ (O D T : ℕ) (R : MmwAdaptiveRun O D T) (η : ℝ) (σ : Operator D),
      0 < D → 0 < η → η ≤ 1 → IsDensityOperator σ → R.followsGibbsUpdate η →
      (∑ ω : Fin T → Fin O, R.transcriptProb ω * R.cumRecord ω)
        ≤ (∑ ω : Fin T → Fin O, R.transcriptProb ω * R.comparatorLoss σ ω)
          + η * (T : ℝ) + Real.log D / η) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro O D T R t ht h
    exact cond_record_mean R t ht h
  · intro O D T R
    exact cumDev_expect_zero T R
  · intro O D T R δ hδ
    exact deviation_failure_mass R δ hδ
  · intro O D T S
    exact MmwRunBornReceipt.discipline S
  · intro O D T R η σ hD hη hη1 hσ hG
    exact expected_recorded_le_comparator R η σ hD hη hη1 hσ hG

end
end Qatlib.Concepts.SdpDuality.ConeSeparation
