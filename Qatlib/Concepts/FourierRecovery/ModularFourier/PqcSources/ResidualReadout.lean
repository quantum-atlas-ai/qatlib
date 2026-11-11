/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources.ResidualEncoding
import Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic.State
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic

/-! Reference-character readout of the actual residual encoding.
Rejected codes and every nonzero residual remain in the state. The source
need only have a constant complex amplitude within each accepted block,
times the character of its public Fourier label. No efficient inverse,
Gaussian profile, original-noise transport or gate compiler is assumed. -/

set_option autoImplicit false
namespace Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources

open Matrix
open scoped BigOperators ComplexConjugate Classical

variable {K G C : Type} [AddGroup K] [Fintype K] [DecidableEq K]
  [AddCommGroup G] [Fintype G] [DecidableEq G]
  [Fintype C] [DecidableEq C]

/-- Definition of pqc Residual Correct Mass in the Modular Fourier construction. -/
noncomputable def pqcResidualCorrectMass (f : K → G × C) (guess : G × C → K)
    (ψ : QState K) (kept : Finset C) : ℝ :=
  ∑ k, if (f k).2 ∈ kept ∧ guess (f k) = k then BornProb ψ k else 0

/-- Definition of pqc Residual Accepted Mass in the Modular Fourier construction. -/
noncomputable def pqcResidualAcceptedMass (f : K → G × C)
    (ψ : QState K) (kept : Finset C) : ℝ :=
  ∑ k, if (f k).2 ∈ kept then BornProb ψ k else 0

/-- Definition of pqc Residual Good Labels in the Modular Fourier construction. -/
noncomputable def pqcResidualGoodLabels (f : K → G × C)
    (guess : G × C → K) (c : C) : Finset G :=
  Finset.univ.filter fun y => f (guess (y,c)) = (y,c)

/-- Definition of pqc Residual Fourier State in the Modular Fourier construction. -/
noncomputable def pqcResidualFourierState (f : K → G × C)
    (guess : G × C → K) (ψ : QState K) :
    QState (AddChar G ℂ × (C × K)) :=
  fun z => fourier
    (fun y => pqcResidualState f guess ψ ((y,z.2.1),z.2.2)) z.1

omit [AddGroup K] [AddCommGroup G] in
/-- The actual finite-label construction satisfies `pqc_residual_correct_mass_labels` with all displayed hypotheses. -/
theorem pqc_residual_correct_mass_labels (f : K → G × C)
    (guess : G × C → K) (ψ : QState K) (kept : Finset C) :
    pqcResidualCorrectMass f guess ψ kept =
      ∑ c ∈ kept, ∑ y : G,
        if f (guess (y,c)) = (y,c) then BornProb ψ (guess (y,c)) else 0 := by
  have hdouble :
      (∑ l : G × C, if f (guess l) = l ∧ l.2 ∈ kept then BornProb ψ (guess l) else 0) =
        ∑ k : K, if guess (f k) = k ∧ (f k).2 ∈ kept then BornProb ψ k else 0 := by
    calc
      _ = ∑ l : G × C, ∑ k : K,
          if k = guess l then
            if f k = l ∧ l.2 ∈ kept then BornProb ψ k else 0 else 0 := by simp
      _ = ∑ k : K, ∑ l : G × C,
          if k = guess l then
            if f k = l ∧ l.2 ∈ kept then BornProb ψ k else 0 else 0 :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        have hterm (l : G × C) :
            (if k = guess l then
              if f k = l ∧ l.2 ∈ kept then BornProb ψ k else 0 else 0) =
            (if l = f k then
              if guess (f k) = k ∧ (f k).2 ∈ kept then BornProb ψ k else 0 else 0) := by
          by_cases hl : l = f k
          · subst l
            by_cases hg : guess (f k) = k
            · simp [hg]
            · have hk : k ≠ guess (f k) := Ne.symm hg
              simp [hg,hk]
          · have hf : f k ≠ l := Ne.symm hl
            simp [hl,hf]
        simp_rw [hterm]
        simp
  unfold pqcResidualCorrectMass
  have hcomm (k : K) :
      (if (f k).2 ∈ kept ∧ guess (f k) = k then BornProb ψ k else 0) =
        if guess (f k) = k ∧ (f k).2 ∈ kept then BornProb ψ k else 0 := by
    by_cases hp : (f k).2 ∈ kept <;> by_cases hg : guess (f k) = k <;> simp [hp,hg]
  simp_rw [hcomm]
  rw [← hdouble, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [show ∀ c : C, ∀ y : G,
      (if f (guess (y,c)) = (y,c) ∧ c ∈ kept then BornProb ψ (guess (y,c)) else 0) =
        if c ∈ kept then
          (if f (guess (y,c)) = (y,c) then BornProb ψ (guess (y,c)) else 0) else 0 from
    fun c y => by by_cases hc : c ∈ kept <;> simp [hc]]
  simp [Finset.sum_ite_irrel, Finset.sum_ite_mem]

omit [Fintype C] in
/-- The actual finite-label construction satisfies `pqc_residual_fourier_amplitude` with all displayed hypotheses. -/
theorem pqc_residual_fourier_amplitude (f : K → G × C)
    (guess : G × C → K) (ψ : QState K) (kept : Finset C)
    (amp : C → ℂ) (η : AddChar G ℂ)
    (hflat : ∀ k, (f k).2 ∈ kept → ψ k = amp (f k).2 * η (f k).1)
    (c : C) (hc : c ∈ kept) :
    pqcResidualFourierState f guess ψ (η,(c,0)) =
      fourierScale G * amp c *
        (pqcResidualGoodLabels f guess c).card := by
  unfold pqcResidualFourierState
  rw [fourier_apply]
  simp_rw [pqc_residual_state_apply_zero]
  have hterm (y : G) :
      conj (η y) * (if f (guess (y,c)) = (y,c) then ψ (guess (y,c)) else 0) =
        if f (guess (y,c)) = (y,c) then amp c else 0 := by
    by_cases hf : f (guess (y,c)) = (y,c)
    · have hp := hflat (guess (y,c)) (by simpa [hf] using hc)
      rw [if_pos hf, hp]
      simp only [hf]
      have hn : conj (η y) * η y = 1 := by
        simpa [AddChar.norm_apply] using Complex.conj_mul' (η y)
      calc
        conj (η y) * (amp c * η y) = amp c * (conj (η y) * η y) := by ring
        _ = _ := by simp [hn]
    · simp [hf]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, pqcResidualGoodLabels]
  ring

omit [Fintype C] in
/-- The actual finite-label construction satisfies `pqc_residual_fourier_good_born` with all displayed hypotheses. -/
theorem pqc_residual_fourier_good_born (f : K → G × C)
    (guess : G × C → K) (ψ : QState K) (kept : Finset C)
    (amp : C → ℂ) (η : AddChar G ℂ)
    (hflat : ∀ k, (f k).2 ∈ kept → ψ k = amp (f k).2 * η (f k).1)
    (c : C) (hc : c ∈ kept) :
    BornProb (pqcResidualFourierState f guess ψ) (η,(c,0)) =
      (Fintype.card G : ℝ)⁻¹ * ‖amp c‖ ^ 2 *
        ((pqcResidualGoodLabels f guess c).card : ℝ) ^ 2 := by
  rw [BornProb, pqc_residual_fourier_amplitude f guess ψ kept amp η hflat c hc]
  simp only [norm_mul, mul_pow, norm_fourierScale_sq,
    Complex.norm_natCast]

omit [AddGroup K] in
/-- The actual finite-label construction satisfies `pqc_residual_correct_mass_flat` with all displayed hypotheses. -/
theorem pqc_residual_correct_mass_flat (f : K → G × C)
    (guess : G × C → K) (ψ : QState K) (kept : Finset C)
    (amp : C → ℂ) (η : AddChar G ℂ)
    (hflat : ∀ k, (f k).2 ∈ kept → ψ k = amp (f k).2 * η (f k).1) :
    pqcResidualCorrectMass f guess ψ kept =
      ∑ c ∈ kept, ‖amp c‖ ^ 2 * (pqcResidualGoodLabels f guess c).card := by
  rw [pqc_residual_correct_mass_labels]
  apply Finset.sum_congr rfl
  intro c hc
  have hterm (y : G) :
      (if f (guess (y,c)) = (y,c) then BornProb ψ (guess (y,c)) else 0) =
        if f (guess (y,c)) = (y,c) then ‖amp c‖ ^ 2 else 0 := by
    by_cases hf : f (guess (y,c)) = (y,c)
    · have hp := hflat (guess (y,c)) (by simpa [hf] using hc)
      simp [hf,BornProb,hp,AddChar.norm_apply]
    · simp [hf]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  simp [pqcResidualGoodLabels, mul_comm]

omit [AddGroup K] [DecidableEq K] [DecidableEq G] [Fintype C] in
/-- The actual finite-label construction satisfies `pqc_residual_accepted_mass_flat` with all displayed hypotheses. -/
theorem pqc_residual_accepted_mass_flat (f : K → G × C)
    (ψ : QState K) (kept : Finset C) (amp : C → ℂ) (η : AddChar G ℂ)
    (hflat : ∀ k, (f k).2 ∈ kept → ψ k = amp (f k).2 * η (f k).1)
    (ell : ℕ) (hcard : ∀ c ∈ kept, (Finset.univ.filter fun k => (f k).2 = c).card = ell) :
    pqcResidualAcceptedMass f ψ kept = (ell : ℝ) * ∑ c ∈ kept, ‖amp c‖ ^ 2 := by
  have hexpand : pqcResidualAcceptedMass f ψ kept =
      ∑ c ∈ kept, ∑ k : K, if (f k).2 = c then BornProb ψ k else 0 := by
    rw [Finset.sum_comm]
    unfold pqcResidualAcceptedMass
    apply Finset.sum_congr rfl
    intro k _
    simp [eq_comm]
  rw [hexpand, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  have hterm (k : K) :
      (if (f k).2 = c then BornProb ψ k else 0) =
        if (f k).2 = c then ‖amp c‖ ^ 2 else 0 := by
    by_cases hk : (f k).2 = c
    · have hp := hflat k (by simpa [hk] using hc)
      simp [hk,BornProb,hp,AddChar.norm_apply]
    · simp [hk]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  simp [hcard c hc]

omit [AddGroup K] [AddCommGroup G] [Fintype G] [DecidableEq G] [Fintype C] in
/-- The actual finite-label construction satisfies `pqc_residual_accepted_mass_le_one` with all displayed hypotheses. -/
theorem pqc_residual_accepted_mass_le_one (f : K → G × C)
    (ψ : QState K) (kept : Finset C) (hψ : Normalized ψ) :
    pqcResidualAcceptedMass f ψ kept ≤ 1 := by
  calc
    _ ≤ ∑ k : K, BornProb ψ k := by
      unfold pqcResidualAcceptedMass
      exact Finset.sum_le_sum fun k _ => by
        split_ifs
        · exact le_rfl
        · exact bornProb_nonneg ψ k
    _ = 1 := hψ

/-- The actual finite-label construction satisfies `pqc_residual_fourier_state_normalized` with all displayed hypotheses. -/
theorem pqc_residual_fourier_state_normalized (f : K → G × C)
    (guess : G × C → K) (ψ : QState K) (hψ : Normalized ψ) :
    Normalized (pqcResidualFourierState f guess ψ) := by
  have hres := pqc_residual_state_normalized f guess ψ hψ
  have hfiber (e : C × K) :
      (∑ χ : AddChar G ℂ,
        ‖fourier (fun y => pqcResidualState f guess ψ ((y,e.1),e.2)) χ‖^2) =
        ∑ y : G, ‖pqcResidualState f guess ψ ((y,e.1),e.2)‖^2 := by
    have h := inner_fourier
      (fun y => pqcResidualState f guess ψ ((y,e.1),e.2))
      (fun y => pqcResidualState f guess ψ ((y,e.1),e.2))
    rw [inner_self, inner_self, ← Complex.ofReal_sum, ← Complex.ofReal_sum] at h
    exact Complex.ofReal_injective h
  unfold Normalized pqcResidualFourierState
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [hfiber]
  rw [Finset.sum_comm]
  simpa only [Normalized, Fintype.sum_prod_type] using hres

/-- Definition of pqc Residual Good Readout Mass in the Modular Fourier construction. -/
noncomputable def pqcResidualGoodReadoutMass (f : K → G × C)
    (guess : G × C → K) (ψ : QState K) (kept : Finset C)
    (η : AddChar G ℂ) : ℝ :=
  ∑ c ∈ kept, BornProb (pqcResidualFourierState f guess ψ) (η,(c,0))

/-- Definition of pqc Residual Accepted Readout Mass in the Modular Fourier construction. -/
noncomputable def pqcResidualAcceptedReadoutMass (f : K → G × C)
    (guess : G × C → K) (ψ : QState K) (kept : Finset C)
    (η : AddChar G ℂ) : ℝ :=
  MeasureProb (pqcResidualFourierState f guess ψ)
    ({η} ×ˢ (kept ×ˢ Finset.univ))

omit [Fintype C] in
/-- The actual finite-label construction satisfies `pqc_residual_good_readout_formula` with all displayed hypotheses. -/
theorem pqc_residual_good_readout_formula (f : K → G × C)
    (guess : G × C → K) (ψ : QState K) (kept : Finset C)
    (amp : C → ℂ) (η : AddChar G ℂ)
    (hflat : ∀ k, (f k).2 ∈ kept → ψ k = amp (f k).2 * η (f k).1) :
    pqcResidualGoodReadoutMass f guess ψ kept η =
      (Fintype.card G : ℝ)⁻¹ * ∑ c ∈ kept,
        ‖amp c‖ ^ 2 * ((pqcResidualGoodLabels f guess c).card : ℝ) ^ 2 := by
  unfold pqcResidualGoodReadoutMass
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c hc => by
    simpa only [mul_assoc] using pqc_residual_fourier_good_born f guess ψ kept amp η hflat c hc

/-- The actual finite-label construction satisfies `pqc_residual_good_readout_le_marginal` with all displayed hypotheses. -/
theorem pqc_residual_good_readout_le_marginal (f : K → G × C)
    (guess : G × C → K) (ψ : QState K) (kept : Finset C)
    (η : AddChar G ℂ) :
    pqcResidualGoodReadoutMass f guess ψ kept η ≤
      MarginalProbLeft (pqcResidualFourierState f guess ψ) {η} := by
  calc
    _ ≤ ∑ c : C, BornProb (pqcResidualFourierState f guess ψ) (η,(c,0)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ kept)
        (fun c _ _ => bornProb_nonneg _ _)
    _ ≤ ∑ c : C, ∑ r : K, BornProb (pqcResidualFourierState f guess ψ) (η,(c,r)) := by
      apply Finset.sum_le_sum
      intro c _
      exact Finset.single_le_sum
        (fun r _ => bornProb_nonneg (pqcResidualFourierState f guess ψ) (η,(c,r)))
        (Finset.mem_univ (0 : K))
    _ = _ := by
      simp [MarginalProbLeft,MeasureProb,Fintype.sum_prod_type]

/-- The actual finite-label construction satisfies `pqc_residual_good_readout_le_accepted` with all displayed hypotheses. -/
theorem pqc_residual_good_readout_le_accepted (f : K → G × C)
    (guess : G × C → K) (ψ : QState K) (kept : Finset C)
    (η : AddChar G ℂ) :
    pqcResidualGoodReadoutMass f guess ψ kept η ≤
      pqcResidualAcceptedReadoutMass f guess ψ kept η := by
  unfold pqcResidualGoodReadoutMass pqcResidualAcceptedReadoutMass
  simp only [MeasureProb,Finset.sum_product,Finset.sum_singleton]
  apply Finset.sum_le_sum
  intro c _
  exact Finset.single_le_sum
    (fun r _ => bornProb_nonneg (pqcResidualFourierState f guess ψ) (η,(c,r)))
    (Finset.mem_univ (0 : K))

/-- The accepted actual Fourier event is lower bounded by the square of the
joint source-correct mass. Full accepted fibers have exactly ell elements;
no assumption makes the forward map injective or the inverse correct. -/
theorem pqc_residual_fourier_recall_lower (f : K → G × C)
    (guess : G × C → K) (ψ : QState K) (kept : Finset C)
    (amp : C → ℂ) (η : AddChar G ℂ)
    (hψ : Normalized ψ)
    (hflat : ∀ k, (f k).2 ∈ kept → ψ k = amp (f k).2 * η (f k).1)
    (ell : ℕ) (hcard : ∀ c ∈ kept, (Finset.univ.filter fun k => (f k).2 = c).card = ell) :
    (ell : ℝ) / Fintype.card G * (pqcResidualCorrectMass f guess ψ kept)^2 ≤
      pqcResidualAcceptedReadoutMass f guess ψ kept η := by
  let W : ℝ := ∑ c ∈ kept, ‖amp c‖^2
  let T : ℝ := ∑ c ∈ kept,
    ‖amp c‖^2 * ((pqcResidualGoodLabels f guess c).card : ℝ)^2
  have hcs : (pqcResidualCorrectMass f guess ψ kept)^2 ≤ W*T := by
    rw [pqc_residual_correct_mass_flat f guess ψ kept amp η hflat]
    have h := Finset.sum_mul_sq_le_sq_mul_sq kept
      (fun c => ‖amp c‖)
      (fun c => ‖amp c‖ * ((pqcResidualGoodLabels f guess c).card : ℝ))
    convert h using 1 <;> (try dsimp [W,T]) <;> congr 1 <;>
      apply Finset.sum_congr rfl <;> intro c _ <;> ring
  have hmass : pqcResidualAcceptedMass f ψ kept = (ell : ℝ)*W :=
    pqc_residual_accepted_mass_flat f ψ kept amp η hflat ell hcard
  have hread : pqcResidualGoodReadoutMass f guess ψ kept η =
      (Fintype.card G : ℝ)⁻¹*T :=
    pqc_residual_good_readout_formula f guess ψ kept amp η hflat
  have hscale : (ell : ℝ)*(pqcResidualCorrectMass f guess ψ kept)^2 ≤
      pqcResidualAcceptedMass f ψ kept * T := by
    calc
      _ ≤ (ell : ℝ)*(W*T) := mul_le_mul_of_nonneg_left hcs (Nat.cast_nonneg _)
      _ = _ := by rw [hmass]; ring
  have hnonneg : 0 ≤ pqcResidualGoodReadoutMass f guess ψ kept η :=
    Finset.sum_nonneg fun c _ => bornProb_nonneg _ _
  calc
    _ = (Fintype.card G : ℝ)⁻¹*((ell : ℝ)*(pqcResidualCorrectMass f guess ψ kept)^2) := by
      rw [div_eq_mul_inv]; ring
    _ ≤ (Fintype.card G : ℝ)⁻¹*(pqcResidualAcceptedMass f ψ kept*T) :=
      mul_le_mul_of_nonneg_left hscale (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = pqcResidualAcceptedMass f ψ kept * pqcResidualGoodReadoutMass f guess ψ kept η := by
      rw [hread]; ring
    _ ≤ pqcResidualGoodReadoutMass f guess ψ kept η :=
      mul_le_of_le_one_left hnonneg (pqc_residual_accepted_mass_le_one f ψ kept hψ)
    _ ≤ _ := pqc_residual_good_readout_le_accepted f guess ψ kept η

end Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources
