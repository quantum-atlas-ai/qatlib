/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Papers.QPowerSimon97.StandardModel.JointSeparation
import Mathlib.Data.Nat.Pairing
import Mathlib.Order.Filter.AtTopBot.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AbelianDecoders.SimonDecoding
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Papers.QPowerSimon97.Recovery
open Qatlib.Papers.QPowerSimon97.Recovery.SimonAssembly
open Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstruction

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QPowerSimon97.StandardDefs

open Qatlib
open scoped Classical BigOperators ENNReal

def simonGoodDraw (n : ℕ) (ob : Bool × (BooleanVec n → BooleanVec n)) : Prop :=
  (ob.1 = false ∧ Function.Injective ob.2) ∨
    (ob.1 = true ∧ ∃ s : BooleanVec n, s ≠ 0 ∧ SimonStrictTwoToOne s ob.2)

def simonBadInd (n : ℕ) (ob : Bool × (BooleanVec n → BooleanVec n)) : ℝ≥0∞ :=
  if simonGoodDraw n ob then 0 else 1

private lemma simonBadInd_le_one (n : ℕ)
    (ob : Bool × (BooleanVec n → BooleanVec n)) : simonBadInd n ob ≤ 1 := by
  unfold simonBadInd
  split <;> simp

private lemma expectation_le_of_support {α : Type*} {p : PMF α} {f g : α → ℝ≥0∞}
    (h : ∀ a, p a ≠ 0 → f a ≤ g a) : expectation p f ≤ expectation p g := by
  show ∑' a, p a * f a ≤ ∑' a, p a * g a
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases hp : p a = 0
  · simp [hp]
  · exact mul_le_mul_right (h a hp) _

theorem simonBad_mass_le (n : ℕ) :
    expectation (simonOracleConstruction n) (simonBadInd n) ≤
      (1 / 2 : ℝ≥0∞) * (2 ^ n : ℝ≥0∞)⁻¹ := by
  have htwo (s : BooleanVec n) :
      expectation (simonTwoToOneDist s) (fun f => simonBadInd n (true, f)) ≤
        (if s = 0 then (1 : ℝ≥0∞) else 0) := by
    refine (expectation_le_of_support ?_).trans_eq (expectation_const _ _)
    intro f hf
    by_cases hs : s = 0
    · rw [if_pos hs]
      exact simonBadInd_le_one n _
    · rw [if_neg hs]
      have hn : 1 ≤ n := by
        by_contra h
        have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
        subst hn0
        exact hs (Subsingleton.elim s 0)
      have hstr := simonTwoToOneDist_of_pos hn s hf
      have hg : simonGoodDraw n (true, f) :=
        Or.inr ⟨rfl, s, hs, hstr⟩
      simp [simonBadInd, hg]
  have hperm :
      expectation (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n)))
        (fun (π : Equiv.Perm (BooleanVec n)) =>
          simonBadInd n (false, (π : BooleanVec n → BooleanVec n))) = 0 := by
    have hfun : (fun (π : Equiv.Perm (BooleanVec n)) =>
        simonBadInd n (false, (π : BooleanVec n → BooleanVec n))) = fun _ => 0 := by
      funext π
      have hg : simonGoodDraw n (false, (π : BooleanVec n → BooleanVec n)) :=
        Or.inl ⟨rfl, π.injective⟩
      simp [simonBadInd, hg]
    rw [hfun, expectation_const]
  have hpermU :
      expectation ((PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n))).map
          (fun (π : Equiv.Perm (BooleanVec n)) => (π : BooleanVec n → BooleanVec n)))
          (fun f => simonBadInd n (false, f)) = 0 := by
    rw [expectation_map]
    exact hperm
  unfold simonOracleConstruction
  rw [expectation_bind]
  refine le_trans
    (b := expectation (PMF.uniformOfFintype' (BooleanVec n))
      (fun s => (1 / 2 : ℝ≥0∞) * (if s = 0 then 1 else 0))) ?_ ?_
  · apply expectation_le_of_forall
    intro s
    rw [expectation_bind, expectation_uniform_bool]
    simp only [Bool.false_eq_true, if_false, if_true, expectation_map]
    calc
      (1 / 2 : ℝ≥0∞) *
          expectation (simonTwoToOneDist s) (fun f => simonBadInd n (true, f)) +
        (1 / 2 : ℝ≥0∞) *
          expectation ((PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n))).map
            (fun (π : Equiv.Perm (BooleanVec n)) => (π : BooleanVec n → BooleanVec n)))
            (fun f => simonBadInd n (false, f))
          ≤ (1 / 2 : ℝ≥0∞) * (if s = 0 then 1 else 0) + (1 / 2 : ℝ≥0∞) * 0 := by
            gcongr
            · exact htwo s
            · simp [hpermU]
      _ = (1 / 2 : ℝ≥0∞) * (if s = 0 then 1 else 0) := by rw [mul_zero, add_zero]
  · rw [expectation_const_mul, expectation_uniform_zero_indicator]

theorem simonGood_mass_lower (n : ℕ) :
    1 - (1 / 2 : ℝ≥0∞) * (2 ^ n : ℝ≥0∞)⁻¹ ≤
      expectation (simonOracleConstruction n)
        (fun ob => if simonGoodDraw n ob then 1 else 0) := by
  have hsum :
      expectation (simonOracleConstruction n)
          (fun ob => if simonGoodDraw n ob then 1 else 0) +
        expectation (simonOracleConstruction n) (simonBadInd n) = 1 := by
    rw [← expectation_add]
    calc
      expectation (simonOracleConstruction n)
          (fun ob => (if simonGoodDraw n ob then 1 else 0) + simonBadInd n ob)
          = expectation (simonOracleConstruction n) (fun _ => 1) := by
            apply expectation_congr
            intro ob
            by_cases hg : simonGoodDraw n ob <;> simp [simonBadInd, hg]
      _ = 1 := expectation_const _ 1
  have hbad := simonBad_mass_le n
  have hne : expectation (simonOracleConstruction n) (simonBadInd n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := (1 / 2 : ℝ≥0∞) * (2 ^ n : ℝ≥0∞)⁻¹) ?_ hbad
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.inv_ne_top.mpr (by positivity))
  have heq : expectation (simonOracleConstruction n)
        (fun ob => if simonGoodDraw n ob then 1 else 0) =
      1 - expectation (simonOracleConstruction n) (simonBadInd n) :=
    ENNReal.eq_sub_of_add_eq hne hsum
  rw [heq]
  exact tsub_le_tsub_left hbad 1

theorem simonQuantumSuccess_good (n : ℕ) (hn : 64 ≤ n)
    (ob : Bool × (BooleanVec n → BooleanVec n)) (hgood : simonGoodDraw n ob) :
    ENNReal.ofReal (7 / 8) ≤ simonQuantumSuccess n (2 * n) n ob := by
  obtain ⟨b, f⟩ := ob
  simp only [simonGoodDraw] at hgood
  have h7sub : 1 - ENNReal.ofReal (1 / 8 : ℝ) = ENNReal.ofReal (7 / 8 : ℝ) := by
    rw [← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 1 / 8)]
    norm_num
  rcases hgood with ⟨hb, hinj⟩ | ⟨hb, s, hs, hstr⟩
  · subst hb
    have hrej : (simonAmplifiedReject f (n + 2 * n) n) true ≤
        ENNReal.ofReal ((n : ℝ) * (1 / 2 : ℝ) ^ (2 * n)) :=
      (simonNegligibleErrorAmplification n (BooleanVec n) f (2 * n) n (by omega)).1 hinj
    have h8 : ENNReal.ofReal ((n : ℝ) * (1 / 2 : ℝ) ^ (2 * n)) ≤
        ENNReal.ofReal (1 / 8 : ℝ) :=
      ENNReal.ofReal_le_ofReal (simonPaperFalseReject_le_eighth n hn)
    calc
      ENNReal.ofReal (7 / 8 : ℝ) = 1 - ENNReal.ofReal (1 / 8 : ℝ) := h7sub.symm
      _ ≤ 1 - ENNReal.ofReal ((n : ℝ) * (1 / 2 : ℝ) ^ (2 * n)) :=
        tsub_le_tsub_left h8 1
      _ ≤ 1 - (simonAmplifiedReject f (n + 2 * n) n) true := tsub_le_tsub_left hrej 1
      _ = simonQuantumSuccess n (2 * n) n (false, f) := by
        simp [simonQuantumSuccess]
  · subst hb
    have hcard : Nat.card {x : BooleanVec n | f x ≠ f (x + s)} * (n + 2 * n) ≤ 2 ^ n := by
      have hempty : {x : BooleanVec n | f x ≠ f (x + s)} = ∅ := by
        ext x
        simp [hstr.1 x]
      simp [hempty]
    have hrej : (simonAmplifiedReject f (n + 2 * n) n) false ≤
        ENNReal.ofReal ((3 / 4 : ℝ) ^ n) :=
      (simonNegligibleErrorAmplification n (BooleanVec n) f (2 * n) n (by omega)).2.1
        s hs hcard
    have h8 : ENNReal.ofReal ((3 / 4 : ℝ) ^ n) ≤ ENNReal.ofReal (1 / 8 : ℝ) :=
      ENNReal.ofReal_le_ofReal (simonThreeQuarters_pow_le n hn)
    have htot := simonReject_total f (n + 2 * n) n
    have hbne : (simonAmplifiedReject f (n + 2 * n) n) false ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top
        (PMF.coe_le_one (simonAmplifiedReject f (n + 2 * n) n) false)
    have heq : (simonAmplifiedReject f (n + 2 * n) n) true =
        1 - (simonAmplifiedReject f (n + 2 * n) n) false :=
      ENNReal.eq_sub_of_add_eq hbne htot
    calc
      ENNReal.ofReal (7 / 8 : ℝ) = 1 - ENNReal.ofReal (1 / 8 : ℝ) := h7sub.symm
      _ ≤ 1 - ENNReal.ofReal ((3 / 4 : ℝ) ^ n) := tsub_le_tsub_left h8 1
      _ ≤ 1 - (simonAmplifiedReject f (n + 2 * n) n) false := tsub_le_tsub_left hrej 1
      _ = (simonAmplifiedReject f (n + 2 * n) n) true := heq.symm
      _ = simonQuantumSuccess n (2 * n) n (true, f) := by
        simp [simonQuantumSuccess]

theorem simonNumericGap (n : ℕ) (hn : 64 ≤ n) :
    ENNReal.ofReal (5 / 8 : ℝ) <
      ENNReal.ofReal (2 / 3 : ℝ) *
        (1 - (1 / 2 : ℝ≥0∞) * (2 ^ n : ℝ≥0∞)⁻¹) := by
  have hpow : (16 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ n := by
    calc (16 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (4 : ℕ) := by norm_num
      _ ≤ (2 : ℝ≥0∞) ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
  have hinv : (2 ^ n : ℝ≥0∞)⁻¹ ≤ (16 : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.mpr hpow
  have h16 : (16 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 16 : ℝ) := by
    rw [show (1 / 16 : ℝ) = ((16 : ℝ))⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have hc : (1 / 2 : ℝ≥0∞) * (2 ^ n : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal (1 / 32 : ℝ) := by
    calc
      (1 / 2 : ℝ≥0∞) * (2 ^ n : ℝ≥0∞)⁻¹ ≤ (1 / 2 : ℝ≥0∞) * (16 : ℝ≥0∞)⁻¹ := by
        gcongr
      _ = ENNReal.ofReal (1 / 32 : ℝ) := by
        have hhalf : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
          rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
            ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
          norm_num
        rw [hhalf, h16, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        norm_num
  have h31 : (1 : ℝ≥0∞) - ENNReal.ofReal (1 / 32 : ℝ) = ENNReal.ofReal (31 / 32 : ℝ) := by
    rw [← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 1 / 32)]
    norm_num
  have hsub : ENNReal.ofReal (31 / 32 : ℝ) ≤
      1 - (1 / 2 : ℝ≥0∞) * (2 ^ n : ℝ≥0∞)⁻¹ := by
    rw [← h31]
    exact tsub_le_tsub_left hc 1
  have hmul : ENNReal.ofReal (2 / 3 : ℝ) * ENNReal.ofReal (31 / 32 : ℝ) =
      ENNReal.ofReal (31 / 48 : ℝ) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    norm_num
  have hlt : ENNReal.ofReal (5 / 8 : ℝ) < ENNReal.ofReal (31 / 48 : ℝ) := by
    rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 31 / 48)]
    norm_num
  calc
    ENNReal.ofReal (5 / 8 : ℝ) < ENNReal.ofReal (31 / 48 : ℝ) := hlt
    _ = ENNReal.ofReal (2 / 3 : ℝ) * ENNReal.ofReal (31 / 32 : ℝ) := hmul.symm
    _ ≤ ENNReal.ofReal (2 / 3 : ℝ) *
        (1 - (1 / 2 : ℝ≥0∞) * (2 ^ n : ℝ≥0∞)⁻¹) := by
      gcongr

theorem exists_good_low (n : ℕ) (hn : 64 ≤ n) (q : ℕ)
    (hq : (q : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 4))
    (P : PMF (SimonQueryTree n)) (hP : SimonQueryTree.bounded P q) :
    ∃ ob, simonGoodDraw n ob ∧
      SimonQueryTree.guessMass P ob.2 ob.1 < ENNReal.ofReal (2 / 3 : ℝ) := by
  by_contra h
  push Not at h
  have hclass : expectation (simonOracleConstruction n)
      (fun ob => SimonQueryTree.guessMass P ob.2 ob.1) ≤
      ENNReal.ofReal (5 / 8 : ℝ) := by
    have h0 := simonClassicalRandomOracleBound_realBudget n (by omega) q P hP hq
    have h0' : expectation (simonOracleConstruction n)
        (fun ob => SimonQueryTree.guessMass P ob.2 ob.1) ≤
        ENNReal.ofReal (1 / 2 + (2 : ℝ) ^ (-(n : ℝ) / 2)) := by
      simpa only [simonOracleGuessMass] using! h0
    have h1 : ENNReal.ofReal (1 / 2 + (2 : ℝ) ^ (-(n : ℝ) / 2)) ≤
        ENNReal.ofReal (5 / 8 : ℝ) := by
      apply ENNReal.ofReal_le_ofReal
      have := simonExponentHalf_le n hn
      linarith
    exact h0'.trans h1
  have hpoint : ∀ ob, ENNReal.ofReal (2 / 3 : ℝ) *
        (if simonGoodDraw n ob then 1 else 0) ≤
      SimonQueryTree.guessMass P ob.2 ob.1 := by
    intro ob
    by_cases hg : simonGoodDraw n ob
    · rw [if_pos hg, mul_one]
      exact h ob hg
    · rw [if_neg hg, mul_zero]
      exact zero_le
  have hmarkov : ENNReal.ofReal (2 / 3 : ℝ) *
        expectation (simonOracleConstruction n)
          (fun ob => if simonGoodDraw n ob then 1 else 0) ≤
      expectation (simonOracleConstruction n)
        (fun ob => SimonQueryTree.guessMass P ob.2 ob.1) := by
    rw [← expectation_const_mul]
    exact expectation_le_of_forall hpoint
  have hlower : ENNReal.ofReal (5 / 8 : ℝ) <
      expectation (simonOracleConstruction n)
        (fun ob => SimonQueryTree.guessMass P ob.2 ob.1) := by
    have hnum := simonNumericGap n hn
    have hmono : ENNReal.ofReal (2 / 3 : ℝ) *
        (1 - (1 / 2 : ℝ≥0∞) * (2 ^ n : ℝ≥0∞)⁻¹) ≤
        ENNReal.ofReal (2 / 3 : ℝ) *
          expectation (simonOracleConstruction n)
            (fun ob => if simonGoodDraw n ob then 1 else 0) := by
      gcongr
      exact simonGood_mass_lower n
    exact hnum.trans_le (hmono.trans hmarkov)
  exact (not_lt_of_ge hclass) hlower

def simonOracleLanguage
    (A : (N : ℕ) → Bool × (BooleanVec N → BooleanVec N)) : Set ℕ :=
  {N | (A N).1 = true}

def simonClassicalDecides
    (A : (N : ℕ) → Bool × (BooleanVec N → BooleanVec N))
    (P : (m N : ℕ) → PMF (SimonQueryTree N)) (m : ℕ) : Prop :=
  ∀ᶠ N in Filter.atTop,
    ENNReal.ofReal (2 / 3 : ℝ) < SimonQueryTree.guessMass (P m N) (A N).2 (A N).1

def simonQuantumDecides
    (A : (N : ℕ) → Bool × (BooleanVec N → BooleanVec N)) : Prop :=
  ∀ᶠ N in Filter.atTop,
    ENNReal.ofReal (2 / 3 : ℝ) ≤ simonQuantumSuccess N (2 * N) N (A N)

theorem exists_length_of_index (m N₀ : ℕ) :
    ∃ N ≥ N₀, (Nat.unpair N).1 = m := by
  refine ⟨Nat.pair m (max N₀ 64), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (Nat.right_le_pair m (max N₀ 64))
  · simp [Nat.unpair_pair]

theorem simon_infiniteOracle_separation
    (q : ℕ → ℕ) (hq : ∀ N, (q N : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) / 4))
    (P : (m N : ℕ) → PMF (SimonQueryTree N))
    (hP : ∀ m N, SimonQueryTree.bounded (P m N) (q N)) :
    ∃ A : (N : ℕ) → Bool × (BooleanVec N → BooleanVec N),
      simonQuantumDecides A ∧
        (∀ m, ¬ simonClassicalDecides A P m) := by
  classical
  have hex : ∀ m N, 64 ≤ N → ∃ ob : Bool × (BooleanVec N → BooleanVec N),
      simonGoodDraw N ob ∧
        SimonQueryTree.guessMass (P m N) ob.2 ob.1 <
          ENNReal.ofReal (2 / 3 : ℝ) := by
    intro m N hN
    exact exists_good_low N hN (q N) (hq N) (P m N) (hP m N)
  let A : (N : ℕ) → Bool × (BooleanVec N → BooleanVec N) :=
    fun N => if h : 64 ≤ N then Classical.choose (hex (Nat.unpair N).1 N h) else (false, id)
  have hA : ∀ N (h : 64 ≤ N),
      A N = Classical.choose (hex (Nat.unpair N).1 N h) := by
    intro N h
    simp only [A, dif_pos h]
  refine ⟨A, ?_, ?_⟩
  · rw [simonQuantumDecides]
    filter_upwards [Filter.eventually_ge_atTop 64] with N hN
    rw [hA N hN]
    exact le_trans
      (by norm_num : ENNReal.ofReal (2 / 3 : ℝ) ≤ ENNReal.ofReal (7 / 8 : ℝ))
      (simonQuantumSuccess_good N hN _
        (Classical.choose_spec (hex (Nat.unpair N).1 N hN)).1)
  · intro m
    rw [simonClassicalDecides]
    apply Filter.not_eventually.mpr
    rw [Filter.frequently_atTop]
    intro N₀
    refine ⟨Nat.pair m (max N₀ 64), ?_, ?_⟩
    · exact le_trans (le_max_left _ _) (Nat.right_le_pair m (max N₀ 64))
    · have hN64 : 64 ≤ Nat.pair m (max N₀ 64) :=
        le_trans (le_max_right _ _) (Nat.right_le_pair m (max N₀ 64))
      have hidx : (Nat.unpair (Nat.pair m (max N₀ 64))).1 = m := by
        simp [Nat.unpair_pair]
      have hsmall : SimonQueryTree.guessMass
          (P m (Nat.pair m (max N₀ 64)))
          (A (Nat.pair m (max N₀ 64))).2
          (A (Nat.pair m (max N₀ 64))).1 < ENNReal.ofReal (2 / 3 : ℝ) := by
        have h0 : SimonQueryTree.guessMass
            (P (Nat.unpair (Nat.pair m (max N₀ 64))).1 (Nat.pair m (max N₀ 64)))
            (A (Nat.pair m (max N₀ 64))).2
            (A (Nat.pair m (max N₀ 64))).1 < ENNReal.ofReal (2 / 3 : ℝ) := by
          rw [hA (Nat.pair m (max N₀ 64)) hN64]
          exact (Classical.choose_spec
            (hex (Nat.unpair (Nat.pair m (max N₀ 64))).1
              (Nat.pair m (max N₀ 64)) hN64)).2
        rwa [hidx] at h0
      exact not_lt_of_ge (le_of_lt hsmall)

end Qatlib.Papers.QPowerSimon97.StandardDefs
