/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCircuitYao93.QuantumComm.GramAcceptance
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCircuitYao93.QuantumComm.ProtocolLowerBound

open Matrix
open scoped BigOperators
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QCircuitYao93.QuantumComm.GramAcceptance

def wordWeight {m : ℕ} (x : Fin m → Bool) : ℕ :=
  (Finset.univ.filter fun i => x i = true).card

def onesWord (m k : ℕ) : Fin m → Bool := fun i => decide (i.val < k)

theorem wordWeight_onesWord (m k : ℕ) (hk : k ≤ m) :
    wordWeight (onesWord m k) = k := by
  classical
  have hset : (Finset.univ.filter fun i : Fin m => onesWord m k i = true) =
      (Finset.univ : Finset (Fin k)).image (fun j => (⟨j.val, by omega⟩ : Fin m)) := by
    ext i
    simp only [onesWord, decide_eq_true_eq, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · intro hi
      exact ⟨⟨i.val, hi⟩, rfl⟩
    · rintro ⟨j, -, rfl⟩
      exact j.isLt
  unfold wordWeight
  rw [hset, Finset.card_image_of_injective _ (fun a b h => by
      apply Fin.ext
      simpa using h), Finset.card_univ, Fintype.card_fin]

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n k l : ℕ}

def acceptProb (a : (Fin n → Bool) → ι → QState (Fin k → Bool))
    (b : (Fin n → Bool) → ι → QState (Fin l → Bool)) (x y : Fin n → Bool) : ℝ :=
  ∑ p : (Fin k → Bool) × (Fin l → Bool),
    ‖(∑ ε, TensorState (a x ε) (b y ε)) p‖ ^ 2

theorem acceptProb_gram (a : (Fin n → Bool) → ι → QState (Fin k → Bool))
    (b : (Fin n → Bool) → ι → QState (Fin l → Bool)) (x y : Fin n → Bool) :
    acceptProb a b x y =
      (∑ ε, ∑ ε', Inner (a x ε) (a x ε') * Inner (b y ε) (b y ε')).re :=
  lemma3_acceptance_mass (fun ε => a x ε) (fun ε => b y ε)

theorem abs_inner_le_one {I : Type} [Fintype I] [DecidableEq I] {ψ φ : QState I}
    (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) (hφ : ∑ i, ‖φ i‖ ^ 2 = 1) :
    ‖Inner ψ φ‖ ≤ 1 := by
  have hnorm : ‖Inner ψ φ‖ ≤ ∑ i, ‖ψ i‖ * ‖φ i‖ := by
    rw [inner_apply]
    refine (norm_sum_le _ _).trans_eq ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_mul, Complex.norm_conj]
  have hcs : (∑ i, ‖ψ i‖ * ‖φ i‖) ^ 2 ≤ 1 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset I)
      (fun i => ‖ψ i‖) (fun i => ‖φ i‖)
    rw [hψ, hφ, mul_one] at h
    exact h
  have hnonneg : 0 ≤ ∑ i, ‖ψ i‖ * ‖φ i‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith

theorem abs_re_inner_le_one {I : Type} [Fintype I] [DecidableEq I] {ψ φ : QState I}
    (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) (hφ : ∑ i, ‖φ i‖ ^ 2 = 1) :
    |(Inner ψ φ).re| ≤ 1 :=
  (Complex.abs_re_le_norm _).trans (abs_inner_le_one hψ hφ)

theorem abs_im_inner_le_one {I : Type} [Fintype I] [DecidableEq I] {ψ φ : QState I}
    (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) (hφ : ∑ i, ‖φ i‖ ^ 2 = 1) :
    |(Inner ψ φ).im| ≤ 1 :=
  (Complex.abs_im_le_norm _).trans (abs_inner_le_one hψ hφ)

theorem norm_le_abs_re_add_abs_im (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| := by
  calc ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ := by
        rw [Complex.re_add_im]
    _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |z.re| + |z.im| := by
        rw [norm_mul, Complex.norm_I, mul_one]
        simp

def gridFin (M : ℕ) (L : ℝ) (hLpos : 0 < L) (hLM : L ^ 3 ≤ (M : ℝ))
    (u : ℝ) (hu : |u| ≤ 1) : Fin (2 * M + 1) :=
  ⟨⌊(u + 1) * L ^ 3⌋₊, by
    have hL3 : (0 : ℝ) < L ^ 3 := by positivity
    have hu1 : (0 : ℝ) ≤ u + 1 := by
      have := (abs_le.mp hu).1
      linarith
    have h1 : (u + 1) * L ^ 3 ≤ 2 * (M : ℝ) := by
      have h2 : u + 1 ≤ 2 := by linarith [(abs_le.mp hu).2]
      calc (u + 1) * L ^ 3 ≤ 2 * L ^ 3 :=
            mul_le_mul_of_nonneg_right h2 hL3.le
        _ ≤ 2 * (M : ℝ) := by linarith
    have h2 : ⌊(u + 1) * L ^ 3⌋₊ ≤ ⌊2 * (M : ℝ)⌋₊ := Nat.floor_mono h1
    have h3 : ⌊2 * (M : ℝ)⌋₊ = 2 * M := by
      rw [show (2 : ℝ) * (M : ℝ) = ((2 * M : ℕ) : ℝ) by push_cast; ring]
      exact Nat.floor_natCast _
    rw [h3] at h2
    omega⟩

theorem gridFin_close {M : ℕ} {L : ℝ} (hLpos : 0 < L) (hLM : L ^ 3 ≤ (M : ℝ))
    {u v : ℝ} (hu : |u| ≤ 1) (hv : |v| ≤ 1)
    (h : gridFin M L hLpos hLM u hu = gridFin M L hLpos hLM v hv) :
    |u - v| < 1 / L ^ 3 := by
  have hL3 : (0 : ℝ) < L ^ 3 := by positivity
  have hfloor : ⌊(u + 1) * L ^ 3⌋₊ = ⌊(v + 1) * L ^ 3⌋₊ := by
    simpa [gridFin] using congrArg Fin.val h
  set m : ℕ := ⌊(u + 1) * L ^ 3⌋₊ with hm
  have hu1 : (0 : ℝ) ≤ u + 1 := by
    have := (abs_le.mp hu).1; linarith
  have hv1 : (0 : ℝ) ≤ v + 1 := by
    have := (abs_le.mp hv).1; linarith
  have hux : (m : ℝ) ≤ (u + 1) * L ^ 3 := by
    simpa [hm] using Nat.floor_le (mul_nonneg hu1 hL3.le)
  have huy : (u + 1) * L ^ 3 < (m : ℝ) + 1 := by
    simpa [hm] using Nat.lt_floor_add_one ((u + 1) * L ^ 3)
  have hvx : (m : ℝ) ≤ (v + 1) * L ^ 3 := by
    have := Nat.floor_le (mul_nonneg hv1 hL3.le)
    rw [← hfloor] at this
    exact this
  have hvy : (v + 1) * L ^ 3 < (m : ℝ) + 1 := by
    have := Nat.lt_floor_add_one ((v + 1) * L ^ 3)
    rw [← hfloor] at this
    exact this
  have hdiff : |(u + 1) * L ^ 3 - (v + 1) * L ^ 3| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  have hEq : (u + 1) * L ^ 3 - (v + 1) * L ^ 3 = (u - v) * L ^ 3 := by ring
  rw [hEq, abs_mul, abs_of_pos hL3] at hdiff
  rw [lt_div_iff₀ hL3]
  exact hdiff

abbrev FeatureSpace (M : ℕ) (ι : Type) :=
  (ι × ι → Fin (2 * M + 1)) × (ι × ι → Fin (2 * M + 1))

def feature (M : ℕ) (L : ℝ) (hLpos : 0 < L) (hLM : L ^ 3 ≤ (M : ℝ))
    (b : (Fin n → Bool) → ι → QState (Fin l → Bool))
    (hb : ∀ y ε, ∑ i, ‖b y ε i‖ ^ 2 = 1) (y : Fin n → Bool) : FeatureSpace M ι :=
  (fun p => gridFin M L hLpos hLM (Inner (b y p.1) (b y p.2)).re
      (abs_re_inner_le_one (hb y p.1) (hb y p.2)),
   fun p => gridFin M L hLpos hLM (Inner (b y p.1) (b y p.2)).im
      (abs_im_inner_le_one (hb y p.1) (hb y p.2)))

theorem card_featureSpace (M : ℕ) :
    Fintype.card (FeatureSpace M ι) =
      (2 * M + 1) ^ (2 * Fintype.card ι * Fintype.card ι) := by
  have hcard : Fintype.card (ι × ι) = Fintype.card ι * Fintype.card ι :=
    Fintype.card_prod _ _
  simp only [FeatureSpace, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, hcard]
  rw [← pow_add]
  congr 1
  ring

theorem feature_gram_close {M : ℕ} {L : ℝ} (hLpos : 0 < L) (hLM : L ^ 3 ≤ (M : ℝ))
    (b : (Fin n → Bool) → ι → QState (Fin l → Bool))
    (hb : ∀ y ε, ∑ i, ‖b y ε i‖ ^ 2 = 1)
    {y y' : Fin n → Bool} (h : feature M L hLpos hLM b hb y = feature M L hLpos hLM b hb y')
    (ε ε' : ι) :
    ‖Inner (b y ε) (b y ε') - Inner (b y' ε) (b y' ε')‖ ≤ 2 / L ^ 3 := by
  have hre := congrArg (fun f => f.1 (ε, ε')) h
  have him := congrArg (fun f => f.2 (ε, ε')) h
  have hre' : |(Inner (b y ε) (b y ε')).re - (Inner (b y' ε) (b y' ε')).re| < 1 / L ^ 3 :=
    gridFin_close hLpos hLM (abs_re_inner_le_one (hb y ε) (hb y ε'))
      (abs_re_inner_le_one (hb y' ε) (hb y' ε')) hre
  have him' : |(Inner (b y ε) (b y ε')).im - (Inner (b y' ε) (b y' ε')).im| < 1 / L ^ 3 :=
    gridFin_close hLpos hLM (abs_im_inner_le_one (hb y ε) (hb y ε'))
      (abs_im_inner_le_one (hb y' ε) (hb y' ε')) him
  have hnorm := norm_le_abs_re_add_abs_im
    (Inner (b y ε) (b y ε') - Inner (b y' ε) (b y' ε'))
  rw [Complex.sub_re, Complex.sub_im] at hnorm
  have hL3 : (0 : ℝ) < L ^ 3 := by positivity
  have hsum : (1 : ℝ) / L ^ 3 + 1 / L ^ 3 = 2 / L ^ 3 := by ring
  linarith [hnorm, hre'.le, him'.le]

theorem acceptProb_close {M : ℕ} {L : ℝ} (hLpos : 0 < L) (hLM : L ^ 3 ≤ (M : ℝ))
    (a : (Fin n → Bool) → ι → QState (Fin k → Bool))
    (b : (Fin n → Bool) → ι → QState (Fin l → Bool))
    (ha : ∀ x ε, ∑ i, ‖a x ε i‖ ^ 2 = 1)
    (hb : ∀ y ε, ∑ i, ‖b y ε i‖ ^ 2 = 1)
    {y y' : Fin n → Bool} (h : feature M L hLpos hLM b hb y = feature M L hLpos hLM b hb y')
    (x : Fin n → Bool) :
    |acceptProb a b x y - acceptProb a b x y'| ≤
      (Fintype.card ι : ℝ) ^ 2 * (2 / L ^ 3) := by
  classical
  have hL3 : (0 : ℝ) < L ^ 3 := by positivity
  have hsum_eq :
      (∑ ε, ∑ ε', Inner (a x ε) (a x ε') * Inner (b y ε) (b y ε'))
        - (∑ ε, ∑ ε', Inner (a x ε) (a x ε') * Inner (b y' ε) (b y' ε'))
        = ∑ ε, ∑ ε', Inner (a x ε) (a x ε')
            * (Inner (b y ε) (b y ε') - Inner (b y' ε) (b y' ε')) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ε' _ => ?_
    ring
  have hdiff : acceptProb a b x y - acceptProb a b x y' =
      (∑ ε, ∑ ε',
        Inner (a x ε) (a x ε')
          * (Inner (b y ε) (b y ε') - Inner (b y' ε) (b y' ε'))).re := by
    rw [acceptProb_gram, acceptProb_gram, ← Complex.sub_re, hsum_eq]
  rw [hdiff]
  calc |(∑ ε, ∑ ε',
        Inner (a x ε) (a x ε')
          * (Inner (b y ε) (b y ε') - Inner (b y' ε) (b y' ε'))).re|
      ≤ ‖∑ ε, ∑ ε',
        Inner (a x ε) (a x ε')
          * (Inner (b y ε) (b y ε') - Inner (b y' ε) (b y' ε'))‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ∑ ε, ‖∑ ε',
        Inner (a x ε) (a x ε')
          * (Inner (b y ε) (b y ε') - Inner (b y' ε) (b y' ε'))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ ε, ∑ ε',
        ‖Inner (a x ε) (a x ε')‖
          * ‖Inner (b y ε) (b y ε') - Inner (b y' ε) (b y' ε')‖ := by
        refine Finset.sum_le_sum fun ε _ => ?_
        refine (norm_sum_le _ _).trans ?_
        refine Finset.sum_le_sum fun ε' _ => ?_
        rw [norm_mul]
    _ ≤ ∑ ε, ∑ ε', 1 * (2 / L ^ 3) := by
        refine Finset.sum_le_sum fun ε _ => ?_
        refine Finset.sum_le_sum fun ε' _ => ?_
        have h1 : ‖Inner (a x ε) (a x ε')‖ ≤ 1 :=
          abs_inner_le_one (ha x ε) (ha x ε')
        have h2 : ‖Inner (b y ε) (b y ε') - Inner (b y' ε) (b y' ε')‖ ≤ 2 / L ^ 3 :=
          feature_gram_close hLpos hLM b hb h ε ε'
        exact mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = (Fintype.card ι : ℝ) ^ 2 * (2 / L ^ 3) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

theorem exists_feature_collision {M : ℕ} {L : ℝ} (hLpos : 0 < L) (hLM : L ^ 3 ≤ (M : ℝ))
    (b : (Fin n → Bool) → ι → QState (Fin l → Bool))
    (hb : ∀ y ε, ∑ i, ‖b y ε i‖ ^ 2 = 1)
    (hnum : Fintype.card (FeatureSpace M ι) < n + 1) :
    ∃ k₁ k₂ : Fin (n + 1), k₁ ≠ k₂ ∧
      feature M L hLpos hLM b hb (onesWord n k₁.val) =
        feature M L hLpos hLM b hb (onesWord n k₂.val) := by
  have hcard : Fintype.card (Fin (n + 1)) = n + 1 := Fintype.card_fin _
  have hlt : Fintype.card (FeatureSpace M ι) < Fintype.card (Fin (n + 1)) := by
    rw [hcard]; exact hnum
  obtain ⟨k₁, k₂, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin (n + 1) => feature M L hLpos hLM b hb (onesWord n k.val)) hlt
  exact ⟨k₁, k₂, hne, heq⟩

theorem theorem4_no_cheap_protocol {M : ℕ} {L : ℝ} (hLpos : 0 < L) (hLM : L ^ 3 ≤ (M : ℝ))
    (a : (Fin n → Bool) → ι → QState (Fin k → Bool))
    (b : (Fin n → Bool) → ι → QState (Fin l → Bool))
    (ha : ∀ x ε, ∑ i, ‖a x ε i‖ ^ 2 = 1)
    (hb : ∀ y ε, ∑ i, ‖b y ε i‖ ^ 2 = 1)
    (hnum : Fintype.card (FeatureSpace M ι) < n + 1)
    (hgap : 6 * (Fintype.card ι : ℝ) ^ 2 < L ^ 3)
    (hacc : ∀ x y : Fin n → Bool, n ≤ wordWeight x + wordWeight y →
      (2 : ℝ) / 3 < acceptProb a b x y)
    (hrej : ∀ x y : Fin n → Bool, wordWeight x + wordWeight y < n →
      acceptProb a b x y < (1 : ℝ) / 3) :
    False := by
  classical

  obtain ⟨k₁, k₂, hne, hfeat⟩ := exists_feature_collision hLpos hLM b hb hnum
  have hval : k₁.val ≠ k₂.val := fun h => hne (Fin.ext h)

  obtain ⟨klo, khi, hlt, hfeat'⟩ :
      ∃ klo khi : Fin (n + 1), klo.val < khi.val ∧
        feature M L hLpos hLM b hb (onesWord n klo.val) =
          feature M L hLpos hLM b hb (onesWord n khi.val) := by
    rcases lt_or_gt_of_ne hval with h | h
    · exact ⟨k₁, k₂, h, hfeat⟩
    · exact ⟨k₂, k₁, h, hfeat.symm⟩

  set x : Fin n → Bool := onesWord n (n - khi.val) with hx
  set yhi : Fin n → Bool := onesWord n khi.val with hyhi
  set ylo : Fin n → Bool := onesWord n klo.val with hylo
  have hkhi : khi.val ≤ n := by omega
  have hklo : klo.val ≤ n := by omega
  have hxw : wordWeight x = n - khi.val := wordWeight_onesWord n _ (by omega)
  have hhiw : wordWeight yhi = khi.val := wordWeight_onesWord n _ hkhi
  have hlow : wordWeight ylo = klo.val := wordWeight_onesWord n _ hklo
  have hacc' : (2 : ℝ) / 3 < acceptProb a b x yhi := by
    apply hacc
    rw [hxw, hhiw]; omega
  have hrej' : acceptProb a b x ylo < (1 : ℝ) / 3 := by
    apply hrej
    rw [hxw, hlow]; omega

  have hclose := acceptProb_close hLpos hLM a b ha hb hfeat'.symm x
  have hL3 : (0 : ℝ) < L ^ 3 := by positivity
  have hgap' : (Fintype.card ι : ℝ) ^ 2 * (2 / L ^ 3) < (1 : ℝ) / 3 := by
    have hmul : (Fintype.card ι : ℝ) ^ 2 * (2 / L ^ 3)
        = 2 * (Fintype.card ι : ℝ) ^ 2 / L ^ 3 := by ring
    rw [hmul, div_lt_iff₀ hL3]
    nlinarith [hgap]
  have hdiff : acceptProb a b x yhi - acceptProb a b x ylo < (1 : ℝ) / 3 := by
    have h1 : |acceptProb a b x yhi - acceptProb a b x ylo| ≤
        (Fintype.card ι : ℝ) ^ 2 * (2 / L ^ 3) := hclose
    have h2 := abs_lt.mp (lt_of_le_of_lt h1 hgap')
    linarith [h2.2]
  linarith

end Qatlib.Papers.QCircuitYao93.QuantumComm.ProtocolLowerBound
