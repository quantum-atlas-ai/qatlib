/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources.ResidualReadout
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic

/-! An all-residual upper bound for a forward-valid-or-zero inverse.
The source phases are arbitrary. Rejection and every residual remain in
the actual residual/Fourier state; no normalization or oracle is assumed. -/

set_option autoImplicit false
namespace Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources

open Matrix
open scoped BigOperators ComplexConjugate Classical

variable {K G C : Type} [AddGroup K] [Fintype K] [DecidableEq K]
  [AddCommGroup G] [Fintype G] [DecidableEq G]
  [Fintype C] [DecidableEq C]

/-- Definition of pqc Residual Passing Source in the Modular Fourier construction. -/
noncomputable def pqcResidualPassingSource (f : K → G × C)
    (guess : G × C → K) (ψ : QState K) : QState K :=
  fun k => if guess (f k) = 0 then 0 else ψ k

/-- Definition of pqc Residual Fallback Source in the Modular Fourier construction. -/
noncomputable def pqcResidualFallbackSource (f : K → G × C)
    (guess : G × C → K) (ψ : QState K) : QState K :=
  fun k => if guess (f k) = 0 then ψ k else 0

omit [AddCommGroup G] [Fintype G] [Fintype C] in
/-- The actual finite-label construction satisfies `pqc_residual_state_apply_recover` with all displayed hypotheses. -/
theorem pqc_residual_state_apply_recover (f : K → G × C)
    (guess : G × C → K) (ψ : QState K) (l : G × C) (r : K) :
    pqcResidualState f guess ψ (l,r) =
      if f (r+guess l) = l then ψ (r+guess l) else 0 := by
  unfold pqcResidualState pqcResidualFrame
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id_eq, Matrix.one_apply]
  rw [Finset.sum_eq_single (r+guess l)]
  · by_cases hf : f (r+guess l) = l
    · simp [pqcResidualEncode,hf]
    · have hl : l ≠ f (r+guess l) := Ne.symm hf
      simp [pqcResidualEncode,hf,hl]
  · intro k _ hk
    have hn : (l,r) ≠ pqcResidualEncode f guess k := by
      intro he
      have hc : r+guess l = k := calc
        _ = pqcResidualRecover guess (l,r) := rfl
        _ = pqcResidualRecover guess (pqcResidualEncode f guess k) :=
          congrArg (pqcResidualRecover guess) he
        _ = k := pqc_residual_recover_encode f guess k
      exact hk hc.symm
    simp [hn]
  · simp

/-- The actual finite-label construction satisfies `norm_sum_sq_le_card` with all displayed hypotheses. -/
private theorem norm_sum_sq_le_card {I : Type} (s : Finset I) (v : I → ℂ) :
    ‖∑ i ∈ s, v i‖^2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖v i‖^2 := by
  calc
    _ ≤ (∑ i ∈ s, ‖v i‖)^2 := by
      gcongr
      exact norm_sum_le s v
    _ ≤ _ := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖v i‖)
      simpa using h

/-- The actual finite-label construction satisfies `fourier_support_bound` with all displayed hypotheses. -/
private theorem fourier_support_bound (v : QState G) (η : AddChar G ℂ)
    (s : Finset G) (hs : ∀ y, y ∉ s → v y = 0) :
    BornProb (fourier v) η ≤
      (Fintype.card G : ℝ)⁻¹ * (s.card : ℝ) * ∑ y : G, BornProb v y := by
  have heq : (∑ y : G, conj (η y)*v y) = ∑ y ∈ s, conj (η y)*v y := by
    symm
    apply Finset.sum_subset (Finset.subset_univ s)
    intro y _ hy
    simp [hs y hy]
  have hn := norm_sum_sq_le_card s (fun y => conj (η y)*v y)
  have ht (y : G) : ‖conj (η y)*v y‖^2 = BornProb v y := by
    simp [BornProb,AddChar.norm_apply]
  simp_rw [ht] at hn
  have hsum : (∑ y ∈ s, BornProb v y) ≤ ∑ y : G, BornProb v y :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun y _ _ => bornProb_nonneg v y)
  rw [bornProb_fourier,heq,norm_mul,mul_pow,
    norm_fourierScale_sq]
  calc
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ((s.card : ℝ)*∑ y ∈ s, BornProb v y) :=
      mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ ≤ _ := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hsum
          (show 0 ≤ (Fintype.card G : ℝ)⁻¹ * (s.card : ℝ) by positivity)

omit [AddCommGroup G] [Fintype C] in
/-- The actual finite-label construction satisfies `pqc_residual_code_mass` with all displayed hypotheses. -/
theorem pqc_residual_code_mass (f : K → G × C) (guess : G × C → K)
    (ψ : QState K) (c : C) :
    (∑ r : K, ∑ y : G, BornProb (pqcResidualState f guess ψ) ((y,c),r)) =
      ∑ k : K, if (f k).2 = c then BornProb ψ k else 0 := by
  have hr (y : G) :
      (∑ r : K, BornProb (pqcResidualState f guess ψ) ((y,c),r)) =
        ∑ k : K, if f k = (y,c) then BornProb ψ k else 0 := by
    have ht (r : K) : BornProb (pqcResidualState f guess ψ) ((y,c),r) =
        if f (r+guess (y,c)) = (y,c) then BornProb ψ (r+guess (y,c)) else 0 := by
      rw [BornProb,pqc_residual_state_apply_recover]
      split_ifs <;> simp [BornProb]
    simp_rw [ht]
    exact Equiv.sum_comp (Equiv.addRight (guess (y,c)))
      (fun k : K => if f k = (y,c) then BornProb ψ k else 0)
  rw [Finset.sum_comm]
  simp_rw [hr]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : (f k).2 = c
  · have ht (y : G) : f k = (y,c) ↔ y = (f k).1 := by
      constructor
      · intro h
        exact (congrArg Prod.fst h).symm
      · intro h
        exact Prod.ext h.symm hc
    simp_rw [ht]
    simp [hc]
  · have ht (y : G) : f k ≠ (y,c) := by
      intro h
      exact hc (congrArg Prod.snd h)
    simp [ht,hc]

omit [Fintype K] [AddCommGroup G] [Fintype G] [DecidableEq G] [Fintype C] [DecidableEq C] in
/-- The actual finite-label construction satisfies `passing_born_le` with all displayed hypotheses. -/
private theorem passing_born_le (f : K → G × C) (guess : G × C → K)
    (ψ : QState K) (k : K) :
    BornProb (pqcResidualPassingSource f guess ψ) k ≤ BornProb ψ k := by
  by_cases h : guess (f k) = 0
  · simp [BornProb,pqcResidualPassingSource,h]
  · simp [BornProb,pqcResidualPassingSource,h]

omit [AddGroup K] [AddCommGroup G] in
/-- The actual finite-label construction satisfies `pqc_residual_correct_mass_born_flat` with all displayed hypotheses. -/
theorem pqc_residual_correct_mass_born_flat (f : K → G × C)
    (guess : G × C → K) (ψ : QState K) (kept : Finset C) (amp : C → ℝ)
    (hflat : ∀ k, (f k).2 ∈ kept → BornProb ψ k = (amp (f k).2)^2) :
    pqcResidualCorrectMass f guess ψ kept =
      ∑ c ∈ kept, (amp c)^2 * (pqcResidualGoodLabels f guess c).card := by
  rw [pqc_residual_correct_mass_labels]
  apply Finset.sum_congr rfl
  intro c hc
  have ht (y : G) :
      (if f (guess (y,c)) = (y,c) then BornProb ψ (guess (y,c)) else 0) =
        if f (guess (y,c)) = (y,c) then (amp c)^2 else 0 := by
    by_cases hf : f (guess (y,c)) = (y,c)
    · have hp := hflat (guess (y,c)) (by simpa [hf] using hc)
      simpa [hf] using hp
    · simp [hf]
  simp_rw [ht]
  rw [← Finset.sum_filter]
  simp [pqcResidualGoodLabels,mul_comm]

omit [AddGroup K] [DecidableEq K] [AddCommGroup G] [Fintype G] [DecidableEq G] [Fintype C] in
/-- The actual finite-label construction satisfies `code_mass_born_flat` with all displayed hypotheses. -/
private theorem code_mass_born_flat (f : K → G × C) (ψ : QState K)
    (kept : Finset C) (amp : C → ℝ)
    (hflat : ∀ k, (f k).2 ∈ kept → BornProb ψ k = (amp (f k).2)^2)
    (ell : ℕ) (hcard : ∀ c ∈ kept, (Finset.univ.filter fun k => (f k).2 = c).card = ell)
    (c : C) (hc : c ∈ kept) :
    (∑ k : K, if (f k).2 = c then BornProb ψ k else 0) = (ell : ℝ)*(amp c)^2 := by
  have ht (k : K) :
      (if (f k).2 = c then BornProb ψ k else 0) =
        if (f k).2 = c then (amp c)^2 else 0 := by
    by_cases hk : (f k).2 = c
    · have hp := hflat k (by simpa [hk] using hc)
      simpa [hk] using hp
    · simp [hk]
  simp_rw [ht]
  rw [← Finset.sum_filter]
  simp [hcard c hc]

omit [AddGroup K] [DecidableEq K] [AddCommGroup G] [Fintype G] [DecidableEq G] [Fintype C] in
/-- The actual finite-label construction satisfies `accepted_mass_codes` with all displayed hypotheses. -/
private theorem accepted_mass_codes (f : K → G × C) (ψ : QState K) (kept : Finset C) :
    (∑ c ∈ kept, ∑ k : K, if (f k).2 = c then BornProb ψ k else 0) =
      pqcResidualAcceptedMass f ψ kept := by
  rw [Finset.sum_comm]
  unfold pqcResidualAcceptedMass
  apply Finset.sum_congr rfl
  intro k _
  simp [eq_comm]

omit [AddCommGroup G] [Fintype C] in
/-- The actual finite-label construction satisfies `passing_support` with all displayed hypotheses. -/
private theorem passing_support (f : K → G × C) (guess : G × C → K)
    (ψ : QState K) (kept : Finset C)
    (hvalid : ∀ y c, c ∈ kept → f (guess (y,c)) = (y,c) ∨ guess (y,c) = 0)
    (c : C) (hc : c ∈ kept) (r : K) (y : G)
    (hy : y ∉ pqcResidualGoodLabels f guess c) :
    pqcResidualState f guess (pqcResidualPassingSource f guess ψ) ((y,c),r) = 0 := by
  have hf : f (guess (y,c)) ≠ (y,c) := by
    simpa [pqcResidualGoodLabels] using hy
  have hg : guess (y,c) = 0 := (hvalid y c hc).resolve_left hf
  rw [pqc_residual_state_apply_recover]
  simp only [hg,add_zero]
  by_cases hr : f r = (y,c)
  · simp [hr,pqcResidualPassingSource,hg]
  · simp [hr]

omit [Fintype C] in
/-- The actual finite-label construction satisfies `passing_code_readout_le` with all displayed hypotheses. -/
private theorem passing_code_readout_le (f : K → G × C) (guess : G × C → K)
    (ψ : QState K) (kept : Finset C) (amp : C → ℝ) (η : AddChar G ℂ)
    (hflat : ∀ k, (f k).2 ∈ kept → BornProb ψ k = (amp (f k).2)^2)
    (ell : ℕ) (hcard : ∀ c ∈ kept, (Finset.univ.filter fun k => (f k).2 = c).card = ell)
    (hvalid : ∀ y c, c ∈ kept → f (guess (y,c)) = (y,c) ∨ guess (y,c) = 0)
    (c : C) (hc : c ∈ kept) :
    (∑ r : K, BornProb (pqcResidualFourierState f guess
      (pqcResidualPassingSource f guess ψ)) (η,(c,r))) ≤
      (Fintype.card G : ℝ)⁻¹ * (ell : ℝ) *
        ((amp c)^2 * (pqcResidualGoodLabels f guess c).card) := by
  have hm : (∑ k : K, if (f k).2 = c then
      BornProb (pqcResidualPassingSource f guess ψ) k else 0) ≤ (ell : ℝ)*(amp c)^2 := by
    rw [← code_mass_born_flat f ψ kept amp hflat ell hcard c hc]
    apply Finset.sum_le_sum
    intro k _
    by_cases hk : (f k).2 = c
    · simpa [hk] using passing_born_le f guess ψ k
    · simp [hk]
  calc
    _ ≤ ∑ r : K, (Fintype.card G : ℝ)⁻¹ *
        ((pqcResidualGoodLabels f guess c).card : ℝ) *
        ∑ y : G, BornProb (pqcResidualState f guess
          (pqcResidualPassingSource f guess ψ)) ((y,c),r) := by
      apply Finset.sum_le_sum
      intro r _
      exact fourier_support_bound _ η (pqcResidualGoodLabels f guess c)
        (fun y hy => passing_support f guess ψ kept hvalid c hc r y hy)
    _ = (Fintype.card G : ℝ)⁻¹ * ((pqcResidualGoodLabels f guess c).card : ℝ) *
        ∑ k : K, if (f k).2 = c then
          BornProb (pqcResidualPassingSource f guess ψ) k else 0 := by
      rw [← Finset.mul_sum,pqc_residual_code_mass]
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ((pqcResidualGoodLabels f guess c).card : ℝ) *
        ((ell : ℝ)*(amp c)^2) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

/-- The actual finite-label construction satisfies `pqc_residual_passing_readout_upper` with all displayed hypotheses. -/
theorem pqc_residual_passing_readout_upper (f : K → G × C) (guess : G × C → K)
    (ψ : QState K) (kept : Finset C) (amp : C → ℝ) (η : AddChar G ℂ)
    (hflat : ∀ k, (f k).2 ∈ kept → BornProb ψ k = (amp (f k).2)^2)
    (ell : ℕ) (hcard : ∀ c ∈ kept, (Finset.univ.filter fun k => (f k).2 = c).card = ell)
    (hvalid : ∀ y c, c ∈ kept → f (guess (y,c)) = (y,c) ∨ guess (y,c) = 0) :
    pqcResidualAcceptedReadoutMass f guess (pqcResidualPassingSource f guess ψ) kept η ≤
      (ell : ℝ)/Fintype.card G * pqcResidualCorrectMass f guess ψ kept := by
  unfold pqcResidualAcceptedReadoutMass
  simp only [MeasureProb,Finset.sum_product,Finset.sum_singleton]
  calc
    _ ≤ ∑ c ∈ kept, (Fintype.card G : ℝ)⁻¹ * (ell : ℝ) *
        ((amp c)^2 * (pqcResidualGoodLabels f guess c).card) :=
      Finset.sum_le_sum fun c hc =>
        passing_code_readout_le f guess ψ kept amp η hflat ell hcard hvalid c hc
    _ = _ := by
      rw [pqc_residual_correct_mass_born_flat f guess ψ kept amp hflat,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [div_eq_mul_inv]
      ring

omit [AddCommGroup G] [Fintype G] [Fintype C] in
/-- The actual finite-label construction satisfies `fallback_row` with all displayed hypotheses. -/
private theorem fallback_row (f : K → G × C) (guess : G × C → K)
    (ψ : QState K) (l : G × C) (r : K) :
    pqcResidualState f guess (pqcResidualFallbackSource f guess ψ) (l,r) =
      if f r = l ∧ guess l = 0 then ψ r else 0 := by
  rw [pqc_residual_state_apply_recover]
  by_cases hg : guess l = 0
  · simp only [hg,add_zero]
    by_cases hf : f r = l <;> simp [hf,pqcResidualFallbackSource,hg]
  · by_cases hf : f (r+guess l) = l
    · simp [hf,pqcResidualFallbackSource,hg]
    · simp [hf,hg]

omit [AddCommGroup G] [Fintype G] [Fintype C] in
/-- The actual finite-label construction satisfies `fallback_support` with all displayed hypotheses. -/
private theorem fallback_support (f : K → G × C) (guess : G × C → K)
    (ψ : QState K) (c : C) (r : K) (y : G) (hy : y ∉ ({(f r).1} : Finset G)) :
    pqcResidualState f guess (pqcResidualFallbackSource f guess ψ) ((y,c),r) = 0 := by
  have hf : f r ≠ (y,c) := by
    intro h
    have hfst := congrArg Prod.fst h
    exact hy (by simpa using hfst.symm)
  simp [fallback_row,hf]

omit [AddCommGroup G] [Fintype G] [DecidableEq G] [Fintype C] in
/-- The actual finite-label construction satisfies `fallback_mass_le_difference` with all displayed hypotheses. -/
private theorem fallback_mass_le_difference (f : K → G × C) (guess : G × C → K)
    (ψ : QState K) (kept : Finset C) (hzero : (f 0).2 ∉ kept) :
    pqcResidualAcceptedMass f (pqcResidualFallbackSource f guess ψ) kept ≤
      pqcResidualAcceptedMass f ψ kept-pqcResidualCorrectMass f guess ψ kept := by
  unfold pqcResidualAcceptedMass pqcResidualCorrectMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : (f k).2 ∈ kept
  · simp only [if_pos hk]
    by_cases hg : guess (f k) = 0
    · have hn : guess (f k) ≠ k := by
        intro h
        have hz : k = 0 := h.symm.trans hg
        exact hzero (by simpa [hz] using hk)
      have hF : BornProb (pqcResidualFallbackSource f guess ψ) k = BornProb ψ k := by
        simp [BornProb,pqcResidualFallbackSource,hg]
      rw [hF]
      simp [hk,hn]
    · have hF : BornProb (pqcResidualFallbackSource f guess ψ) k = 0 := by
        simp [BornProb,pqcResidualFallbackSource,hg]
      rw [hF]
      by_cases he : guess (f k) = k
      · simp [hk,he]
      · simpa [hk,he] using bornProb_nonneg ψ k
  · simp [hk]

omit [Fintype C] in
/-- The actual finite-label construction satisfies `pqc_residual_fallback_readout_upper` with all displayed hypotheses. -/
theorem pqc_residual_fallback_readout_upper (f : K → G × C) (guess : G × C → K)
    (ψ : QState K) (kept : Finset C) (η : AddChar G ℂ) (hzero : (f 0).2 ∉ kept) :
    pqcResidualAcceptedReadoutMass f guess (pqcResidualFallbackSource f guess ψ) kept η ≤
      (pqcResidualAcceptedMass f ψ kept-pqcResidualCorrectMass f guess ψ kept)/Fintype.card G := by
  have hm := fallback_mass_le_difference f guess ψ kept hzero
  unfold pqcResidualAcceptedReadoutMass
  simp only [MeasureProb,Finset.sum_product,Finset.sum_singleton]
  calc
    _ ≤ ∑ c ∈ kept, ∑ r : K, (Fintype.card G : ℝ)⁻¹ *
        ∑ y : G, BornProb (pqcResidualState f guess
          (pqcResidualFallbackSource f guess ψ)) ((y,c),r) := by
      apply Finset.sum_le_sum
      intro c _
      apply Finset.sum_le_sum
      intro r _
      simpa [BornProb,pqcResidualFourierState] using fourier_support_bound
        (fun y => pqcResidualState f guess (pqcResidualFallbackSource f guess ψ) ((y,c),r)) η
        {(f r).1} (fun y hy => fallback_support f guess ψ c r y hy)
    _ = (Fintype.card G : ℝ)⁻¹ *
        pqcResidualAcceptedMass f (pqcResidualFallbackSource f guess ψ) kept := by
      simp_rw [← Finset.mul_sum,pqc_residual_code_mass]
      rw [accepted_mass_codes]
    _ ≤ _ := by
      simpa only [div_eq_mul_inv,mul_comm] using
        mul_le_mul_of_nonneg_left hm
          (show 0 ≤ (Fintype.card G : ℝ)⁻¹ by positivity)

/-- The actual finite-label construction satisfies `norm_add_sq_two` with all displayed hypotheses. -/
private theorem norm_add_sq_two (a b : ℂ) :
    ‖a+b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
  have h : ‖a+b‖^2 ≤ (‖a‖+‖b‖)^2 := by
    gcongr
    exact norm_add_le a b
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

omit [Fintype C] in
/-- The actual finite-label construction satisfies `residual_fourier_add` with all displayed hypotheses. -/
private theorem residual_fourier_add (f : K → G × C) (guess : G × C → K)
    (ψ φ : QState K) (z : AddChar G ℂ × (C × K)) :
    pqcResidualFourierState f guess (fun k => ψ k+φ k) z =
      pqcResidualFourierState f guess ψ z+pqcResidualFourierState f guess φ z := by
  simp [pqcResidualFourierState,fourier_apply,pqcResidualState,
    Matrix.mulVec,dotProduct,mul_add,Finset.sum_add_distrib]

omit [Fintype C] in
/-- The actual finite-label construction satisfies `pqc_residual_readout_split_upper` with all displayed hypotheses. -/
theorem pqc_residual_readout_split_upper (f : K → G × C) (guess : G × C → K)
    (ψ : QState K) (kept : Finset C) (η : AddChar G ℂ) :
    pqcResidualAcceptedReadoutMass f guess ψ kept η ≤
      2*(pqcResidualAcceptedReadoutMass f guess (pqcResidualPassingSource f guess ψ) kept η+
        pqcResidualAcceptedReadoutMass f guess (pqcResidualFallbackSource f guess ψ) kept η) := by
  have hs : ψ = fun k => pqcResidualPassingSource f guess ψ k+pqcResidualFallbackSource f guess ψ k := by
    funext k
    by_cases h : guess (f k) = 0 <;>
      simp [pqcResidualPassingSource,pqcResidualFallbackSource,h]
  have ht (z : AddChar G ℂ × (C × K)) :
      BornProb (pqcResidualFourierState f guess ψ) z ≤
        2*(BornProb (pqcResidualFourierState f guess (pqcResidualPassingSource f guess ψ)) z+
          BornProb (pqcResidualFourierState f guess (pqcResidualFallbackSource f guess ψ)) z) := by
    unfold BornProb
    have heq := congrArg (fun v => pqcResidualFourierState f guess v z) hs
    rw [residual_fourier_add] at heq
    rw [heq]
    exact norm_add_sq_two _ _
  unfold pqcResidualAcceptedReadoutMass
  simp only [MeasureProb]
  calc
    _ ≤ ∑ z ∈ ({η} ×ˢ (kept ×ˢ Finset.univ)),
        2*(BornProb (pqcResidualFourierState f guess (pqcResidualPassingSource f guess ψ)) z+
          BornProb (pqcResidualFourierState f guess (pqcResidualFallbackSource f guess ψ)) z) :=
      Finset.sum_le_sum fun z _ => ht z
    _ = _ := by simp [mul_add,Finset.mul_sum,Finset.sum_add_distrib]

/-- The real accepted Fourier event, with all residuals retained. The inverse
must return a same-code valid preimage or zero; accepted source phases are
arbitrary. Correct and accepted masses are the actual existing definitions. -/
theorem pqc_residual_fourier_valid_or_zero_upper (f : K → G × C)
    (guess : G × C → K) (ψ : QState K) (kept : Finset C) (amp : C → ℝ)
    (η : AddChar G ℂ) (ell : ℕ)
    (hflat : ∀ k, (f k).2 ∈ kept → BornProb ψ k = (amp (f k).2)^2)
    (hcard : ∀ c ∈ kept, (Finset.univ.filter fun k => (f k).2 = c).card = ell)
    (hzero : (f 0).2 ∉ kept)
    (hvalid : ∀ y c, c ∈ kept → f (guess (y,c)) = (y,c) ∨ guess (y,c) = 0) :
    pqcResidualAcceptedReadoutMass f guess ψ kept η ≤
      2*((ell : ℝ)/Fintype.card G * pqcResidualCorrectMass f guess ψ kept+
        (pqcResidualAcceptedMass f ψ kept-pqcResidualCorrectMass f guess ψ kept)/Fintype.card G) := by
  have ht := pqc_residual_readout_split_upper f guess ψ kept η
  have hp := pqc_residual_passing_readout_upper f guess ψ kept amp η hflat ell hcard hvalid
  have hf := pqc_residual_fallback_readout_upper f guess ψ kept η hzero
  linarith

end Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources
