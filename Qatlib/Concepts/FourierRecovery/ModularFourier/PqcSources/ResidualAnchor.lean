/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources.ResidualReadoutUpper
import Mathlib.Tactic.GCongr

/-! Public residual anchors in the actual residual/Fourier state.
Source vectors and guesses are arbitrary. Uniform whole-block anchors
preserve readout up to a squared-success bound and control the actual
mean correct-source mass. The enumeration family is supplied; source
preparation, uniform implementation and full costs remain separate.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic

set_option autoImplicit false
namespace Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources
open Matrix
open scoped BigOperators ComplexConjugate Classical

variable {K G C : Type} [AddGroup K] [Fintype K] [DecidableEq K]
  [AddCommGroup G] [Fintype G] [DecidableEq G]
  [Fintype C] [DecidableEq C]

/-- Definition of pqc Residual Row Labels in the Modular Fourier construction. -/
noncomputable def pqcResidualRowLabels (f : K → G × C)
    (guess : G × C → K) (c : C) (r : K) : Finset G :=
  Finset.univ.filter fun y => f (r+guess (y,c)) = (y,c)

/-- The actual finite-label construction satisfies `anchor_norm_sum_sq_le_card` with all displayed hypotheses. -/
private theorem anchor_norm_sum_sq_le_card {I : Type} (s : Finset I) (v : I → ℂ) :
    ‖∑ i ∈ s, v i‖^2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖v i‖^2 := by
  calc
    _ ≤ (∑ i ∈ s, ‖v i‖)^2 := by
      gcongr
      exact norm_sum_le s v
    _ ≤ _ := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖v i‖)
      simpa using h

/-- The actual finite-label construction satisfies `anchor_fourier_support_bound` with all displayed hypotheses. -/
private theorem anchor_fourier_support_bound (v : QState G) (η : AddChar G ℂ)
    (s : Finset G) (hs : ∀ y, y ∉ s → v y = 0) :
    BornProb (fourier v) η ≤
      (Fintype.card G : ℝ)⁻¹ * (s.card : ℝ) * ∑ y : G, BornProb v y := by
  have heq : (∑ y : G, conj (η y)*v y) = ∑ y ∈ s, conj (η y)*v y := by
    symm
    apply Finset.sum_subset (Finset.subset_univ s)
    intro y _ hy
    simp [hs y hy]
  have hn := anchor_norm_sum_sq_le_card s (fun y => conj (η y)*v y)
  have ht (y : G) : ‖conj (η y)*v y‖^2 = BornProb v y := by
    simp [BornProb,AddChar.norm_apply]
  simp_rw [ht] at hn
  have hsum : (∑ y ∈ s, BornProb v y) ≤ ∑ y : G, BornProb v y :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun y _ _ => bornProb_nonneg v y)
  rw [bornProb_fourier,heq,norm_mul,mul_pow,norm_fourierScale_sq]
  calc
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ((s.card : ℝ)*∑ y ∈ s, BornProb v y) :=
      mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsum
        (show 0 ≤ (Fintype.card G : ℝ)⁻¹ * (s.card : ℝ) by positivity)

omit [Fintype C] in
/-- The actual finite-label construction satisfies `pqc_residual_arbitrary_row_readout_bound` with all displayed hypotheses. -/
theorem pqc_residual_arbitrary_row_readout_bound (f : K → G × C)
    (guess : G × C → K) (ψ : QState K) (η : AddChar G ℂ) (c : C) (r : K) :
    BornProb (pqcResidualFourierState f guess ψ) (η,(c,r)) ≤
      (Fintype.card G : ℝ)⁻¹ * ((pqcResidualRowLabels f guess c r).card : ℝ) *
        ∑ y : G, BornProb (pqcResidualState f guess ψ) ((y,c),r) := by
  apply anchor_fourier_support_bound
  intro y hy
  rw [pqc_residual_state_apply_recover]
  have hf : f (r+guess (y,c)) ≠ (y,c) := by
    simpa [pqcResidualRowLabels] using hy
  simp [hf]

omit [AddGroup K] [DecidableEq K] [AddCommGroup G] [Fintype G] [DecidableEq G] [Fintype C] in
/-- The actual finite-label construction satisfies `anchor_accepted_mass_codes` with all displayed hypotheses. -/
private theorem anchor_accepted_mass_codes (f : K → G × C) (ψ : QState K)
    (kept : Finset C) :
    (∑ c ∈ kept, ∑ k : K, if (f k).2 = c then BornProb ψ k else 0) =
      pqcResidualAcceptedMass f ψ kept := by
  rw [Finset.sum_comm]
  unfold pqcResidualAcceptedMass
  apply Finset.sum_congr rfl
  intro k _
  simp [eq_comm]

/-- The actual finite-label construction satisfies `pqc_residual_arbitrary_readout_moment` with all displayed hypotheses. -/
theorem pqc_residual_arbitrary_readout_moment (f : K → G × C)
    (guess : G × C → K) (ψ : QState K) (kept : Finset C) (η : AddChar G ℂ) :
    (pqcResidualAcceptedReadoutMass f guess ψ kept η)^2 ≤
      (Fintype.card G : ℝ)⁻¹ * pqcResidualAcceptedMass f ψ kept *
        (∑ c ∈ kept, ∑ r : K, ((pqcResidualRowLabels f guess c r).card : ℝ) *
          BornProb (pqcResidualFourierState f guess ψ) (η,(c,r))) := by
  let s : Finset (C × K) := kept ×ˢ Finset.univ
  let z : C × K → ℝ := fun p => BornProb (pqcResidualFourierState f guess ψ) (η,p)
  let m : C × K → ℝ := fun p => (pqcResidualRowLabels f guess p.1 p.2).card
  let e : C × K → ℝ := fun p => ∑ y : G,
    BornProb (pqcResidualState f guess ψ) ((y,p.1),p.2)
  let inv : ℝ := (Fintype.card G : ℝ)⁻¹
  have hz (p : C × K) : 0 ≤ z p := bornProb_nonneg _ _
  have hm (p : C × K) : 0 ≤ m p := Nat.cast_nonneg _
  have he (p : C × K) : 0 ≤ e p := Finset.sum_nonneg fun _ _ => bornProb_nonneg _ _
  have hi : 0 ≤ inv := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hbound (p : C × K) : z p ≤ inv*m p*e p :=
    pqc_residual_arbitrary_row_readout_bound f guess ψ η p.1 p.2
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := z) (f := fun p => m p*z p) (g := fun p => inv*e p)
    (fun p _ => mul_nonneg (hm p) (hz p))
    (fun p _ => mul_nonneg hi (he p))
    (fun p _ => calc
      (z p)^2 = z p*z p := by ring
      _ ≤ z p*(inv*m p*e p) := mul_le_mul_of_nonneg_left (hbound p) (hz p)
      _ = (m p*z p)*(inv*e p) := by ring)
  have hread : pqcResidualAcceptedReadoutMass f guess ψ kept η = ∑ p ∈ s, z p := by
    simp [pqcResidualAcceptedReadoutMass,MeasureProb,s,z,Finset.sum_product]
  have hemass : (∑ p ∈ s, e p) = pqcResidualAcceptedMass f ψ kept := by
    simp only [s,Finset.sum_product,e]
    simp_rw [pqc_residual_code_mass]
    exact anchor_accepted_mass_codes f ψ kept
  have hsum : (∑ p ∈ s, inv*e p) = inv*pqcResidualAcceptedMass f ψ kept := by
    rw [← Finset.mul_sum,hemass]
  rw [← hread,hsum] at hcs
  have hmoment : (∑ p ∈ s, m p*z p) =
      ∑ c ∈ kept, ∑ r : K, ((pqcResidualRowLabels f guess c r).card : ℝ) *
        BornProb (pqcResidualFourierState f guess ψ) (η,(c,r)) := by
    simp [s,m,z,Finset.sum_product]
  rw [hmoment] at hcs
  simpa only [inv,mul_assoc,mul_left_comm,mul_comm] using hcs

end Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources



set_option autoImplicit false
namespace Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic
open scoped BigOperators Classical

variable {K G C J : Type} [AddGroup K] [DecidableEq K]
  [AddCommGroup G] [DecidableEq G] [DecidableEq C]

/-- Definition of pqc Residual Anchor Offset in the Modular Fourier construction. -/
def pqcResidualAnchorOffset (f : K → G × C) (guess : G × C → K)
    (anchor : C → J → K) (j : J) (c : C) : K :=
  anchor c j - guess (f (anchor c j))

/-- Definition of pqc Residual Anchor Guess in the Modular Fourier construction. -/
def pqcResidualAnchorGuess (f : K → G × C) (guess : G × C → K)
    (anchor : C → J → K) (j : J) (l : G × C) : K :=
  let v := pqcResidualAnchorOffset f guess anchor j l.2 + guess l
  if f v = l then v else 0

omit [DecidableEq K] [AddCommGroup G] in
/-- The actual finite-label construction satisfies `pqc_residual_anchor_valid_or_zero` with all displayed hypotheses. -/
theorem pqc_residual_anchor_valid_or_zero (f : K → G × C)
    (guess : G × C → K) (anchor : C → J → K) (j : J) (l : G × C) :
    f (pqcResidualAnchorGuess f guess anchor j l) = l ∨
      pqcResidualAnchorGuess f guess anchor j l = 0 := by
  unfold pqcResidualAnchorGuess
  dsimp only
  split_ifs with h
  · exact Or.inl h
  · exact Or.inr rfl

variable [Fintype K] [Fintype G] [Fintype C]

omit [AddCommGroup G] [Fintype G] [Fintype C] in
/-- The actual finite-label construction satisfies `pqc_residual_anchor_state_zero_eq` with all displayed hypotheses. -/
theorem pqc_residual_anchor_state_zero_eq (f : K → G × C)
    (guess : G × C → K) (anchor : C → J → K) (j : J)
    (ψ : QState K) (kept : Finset C) (hzero : (f 0).2 ∉ kept)
    (c : C) (hc : c ∈ kept) (y : G) :
    pqcResidualState f (pqcResidualAnchorGuess f guess anchor j) ψ ((y,c),0) =
      pqcResidualState f guess ψ ((y,c),pqcResidualAnchorOffset f guess anchor j c) := by
  rw [pqc_residual_state_apply_zero, pqc_residual_state_apply_recover]
  have hz : f 0 ≠ (y,c) := by
    intro h
    exact hzero (by simpa [h] using hc)
  unfold pqcResidualAnchorGuess
  dsimp only
  split_ifs with h
  · simp
  · simp_all

omit [Fintype C] in
/-- The actual finite-label construction satisfies `pqc_residual_anchor_fourier_zero_eq` with all displayed hypotheses. -/
theorem pqc_residual_anchor_fourier_zero_eq (f : K → G × C)
    (guess : G × C → K) (anchor : C → J → K) (j : J)
    (ψ : QState K) (kept : Finset C) (hzero : (f 0).2 ∉ kept)
    (c : C) (hc : c ∈ kept) (η : AddChar G ℂ) :
    pqcResidualFourierState f (pqcResidualAnchorGuess f guess anchor j) ψ (η,(c,0)) =
      pqcResidualFourierState f guess ψ
        (η,(c,pqcResidualAnchorOffset f guess anchor j c)) := by
  unfold pqcResidualFourierState
  congr 1
  funext y
  exact pqc_residual_anchor_state_zero_eq f guess anchor j ψ kept hzero c hc y

omit [Fintype C] in
/-- The actual finite-label construction satisfies `pqc_residual_anchor_born_zero_eq` with all displayed hypotheses. -/
theorem pqc_residual_anchor_born_zero_eq (f : K → G × C)
    (guess : G × C → K) (anchor : C → J → K) (j : J)
    (ψ : QState K) (kept : Finset C) (hzero : (f 0).2 ∉ kept)
    (c : C) (hc : c ∈ kept) (η : AddChar G ℂ) :
    BornProb (pqcResidualFourierState f (pqcResidualAnchorGuess f guess anchor j) ψ)
      (η,(c,0)) =
      BornProb (pqcResidualFourierState f guess ψ)
        (η,(c,pqcResidualAnchorOffset f guess anchor j c)) := by
  unfold BornProb
  rw [pqc_residual_anchor_fourier_zero_eq f guess anchor j ψ kept hzero c hc η]

variable [Fintype J] [DecidableEq J]

/-- Definition of pqc Residual Anchor Good Readout in the Modular Fourier construction. -/
noncomputable def pqcResidualAnchorGoodReadout (f : K → G × C)
    (guess : G × C → K) (anchor : C → J → K) (j : J)
    (ψ : QState K) (kept : Finset C) (η : AddChar G ℂ) : ℝ :=
  pqcResidualGoodReadoutMass f (pqcResidualAnchorGuess f guess anchor j) ψ kept η

omit [Fintype C] [Fintype J] [DecidableEq J] in
/-- The actual finite-label construction satisfies `pqc_residual_anchor_good_readout_measure` with all displayed hypotheses. -/
theorem pqc_residual_anchor_good_readout_measure (f : K → G × C)
    (guess : G × C → K) (anchor : C → J → K) (j : J)
    (ψ : QState K) (kept : Finset C) (η : AddChar G ℂ) :
    pqcResidualAnchorGoodReadout f guess anchor j ψ kept η =
      MeasureProb (pqcResidualFourierState f (pqcResidualAnchorGuess f guess anchor j) ψ)
        ({η} ×ˢ (kept ×ˢ {0})) := by
  simp [pqcResidualAnchorGoodReadout,pqcResidualGoodReadoutMass,MeasureProb]

/-- Definition of pqc Residual Anchor Mean Good Readout in the Modular Fourier construction. -/
noncomputable def pqcResidualAnchorMeanGoodReadout (f : K → G × C)
    (guess : G × C → K) (anchor : C → J → K)
    (ψ : QState K) (kept : Finset C) (η : AddChar G ℂ) : ℝ :=
  (Fintype.card J : ℝ)⁻¹ *
    ∑ j : J, pqcResidualAnchorGoodReadout f guess anchor j ψ kept η

omit [AddGroup K] [DecidableEq J] in
/-- The actual finite-label construction satisfies `sum_comp_count` with all displayed hypotheses. -/
private theorem sum_comp_count (a : J → K) (z : K → ℝ) :
    (∑ j : J, z (a j)) =
      ∑ r : K, ((Finset.univ.filter fun j : J => a j = r).card : ℝ) * z r := by
  calc
    _ = ∑ j : J, ∑ r : K, if a j = r then z r else 0 := by simp
    _ = ∑ r : K, ∑ j : J, if a j = r then z r else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [← Finset.sum_filter]
      simp

omit [Fintype C] [DecidableEq J] in
/-- The actual finite-label construction satisfies `pqc_residual_anchor_mean_good_readout_count` with all displayed hypotheses. -/
theorem pqc_residual_anchor_mean_good_readout_count (f : K → G × C)
    (guess : G × C → K) (anchor : C → J → K)
    (ψ : QState K) (kept : Finset C) (hzero : (f 0).2 ∉ kept)
    (η : AddChar G ℂ) :
    pqcResidualAnchorMeanGoodReadout f guess anchor ψ kept η =
      (Fintype.card J : ℝ)⁻¹ * ∑ c ∈ kept, ∑ r : K,
        ((Finset.univ.filter fun j : J =>
          pqcResidualAnchorOffset f guess anchor j c = r).card : ℝ) *
        BornProb (pqcResidualFourierState f guess ψ) (η,(c,r)) := by
  unfold pqcResidualAnchorMeanGoodReadout pqcResidualAnchorGoodReadout pqcResidualGoodReadoutMass
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  simp_rw [pqc_residual_anchor_born_zero_eq f guess anchor _ ψ kept hzero c hc η]
  exact sum_comp_count (fun j => pqcResidualAnchorOffset f guess anchor j c)
    (fun r => BornProb (pqcResidualFourierState f guess ψ) (η,(c,r)))

omit [Fintype C] [AddCommGroup G] [Fintype K] [DecidableEq J] in
/-- The actual finite-label construction satisfies `pqc_residual_anchor_offset_count` with all displayed hypotheses. -/
theorem pqc_residual_anchor_offset_count (f : K → G × C)
    (guess : G × C → K) (anchor : C → J → K) (c : C) (r : K)
    (hcode : ∀ j, (f (anchor c j)).2 = c)
    (hinj : Function.Injective (anchor c))
    (hcover : ∀ k, (f k).2 = c → ∃ j, anchor c j = k) :
    (Finset.univ.filter fun j : J =>
      pqcResidualAnchorOffset f guess anchor j c = r).card =
    (Finset.univ.filter fun y : G => f (r + guess (y,c)) = (y,c)).card := by
  classical
  have hlabel (j : J) : f (anchor c j) = ((f (anchor c j)).1,c) :=
    Prod.ext rfl (hcode j)
  have hpoint (j : J)
      (hj : pqcResidualAnchorOffset f guess anchor j c = r) :
      anchor c j = r + guess (f (anchor c j)) := by
    rw [← hj]
    simp [pqcResidualAnchorOffset]
  apply Finset.card_bij (fun j _ => (f (anchor c j)).1)
  · intro j hj
    have hr := (Finset.mem_filter.mp hj).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← hlabel j, ← hpoint j hr]
  · intro j hj j' hj' hy
    apply hinj
    rw [hpoint j (Finset.mem_filter.mp hj).2,
      hpoint j' (Finset.mem_filter.mp hj').2, hlabel j, hlabel j', hy]
  · intro y hy
    have hf := (Finset.mem_filter.mp hy).2
    obtain ⟨j,hj⟩ := hcover (r + guess (y,c)) (congrArg Prod.snd hf)
    refine ⟨j, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change anchor c j - guess (f (anchor c j)) = r
      rw [hj, hf]
      simp
    · simp [hj, hf]

omit [Fintype C] [DecidableEq J] in
/-- The actual finite-label construction satisfies `pqc_residual_anchor_mean_good_readout_rows` with all displayed hypotheses. -/
theorem pqc_residual_anchor_mean_good_readout_rows (f : K → G × C)
    (guess : G × C → K) (anchor : C → J → K)
    (ψ : QState K) (kept : Finset C) (hzero : (f 0).2 ∉ kept)
    (hcode : ∀ c ∈ kept, ∀ j, (f (anchor c j)).2 = c)
    (hinj : ∀ c ∈ kept, Function.Injective (anchor c))
    (hcover : ∀ c ∈ kept, ∀ k, (f k).2 = c → ∃ j, anchor c j = k)
    (η : AddChar G ℂ) :
    pqcResidualAnchorMeanGoodReadout f guess anchor ψ kept η =
      (Fintype.card J : ℝ)⁻¹ * ∑ c ∈ kept, ∑ r : K,
        ((Finset.univ.filter fun y : G =>
          f (r + guess (y,c)) = (y,c)).card : ℝ) *
        BornProb (pqcResidualFourierState f guess ψ) (η,(c,r)) := by
  rw [pqc_residual_anchor_mean_good_readout_count f guess anchor ψ kept hzero η]
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro r _
  rw [pqc_residual_anchor_offset_count f guess anchor c r
    (hcode c hc) (hinj c hc) (hcover c hc)]

end Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources


namespace Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic
open scoped BigOperators Classical

variable {K G C J : Type} [AddGroup K] [Fintype K] [DecidableEq K]
  [AddCommGroup G] [Fintype G] [DecidableEq G] [Fintype C] [DecidableEq C]
  [Fintype J] [DecidableEq J] [Nonempty J]

omit [DecidableEq J] in
/-- The actual finite-label construction satisfies `pqc_residual_anchor_readout_conversion` with all displayed hypotheses. -/
theorem pqc_residual_anchor_readout_conversion (f : K → G × C)
    (guess : G × C → K) (anchor : C → J → K)
    (ψ : QState K) (kept : Finset C) (hzero : (f 0).2 ∉ kept)
    (hcode : ∀ c ∈ kept, ∀ j, (f (anchor c j)).2 = c)
    (hinj : ∀ c ∈ kept, Function.Injective (anchor c))
    (hcover : ∀ c ∈ kept, ∀ k, (f k).2 = c → ∃ j, anchor c j = k)
    (η : AddChar G ℂ) :
    (pqcResidualAcceptedReadoutMass f guess ψ kept η)^2 ≤
      ((Fintype.card J : ℝ)/(Fintype.card G : ℝ)) *
        pqcResidualAcceptedMass f ψ kept *
        pqcResidualAnchorMeanGoodReadout f guess anchor ψ kept η := by
  have hj : (Fintype.card J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [pqc_residual_anchor_mean_good_readout_rows f guess anchor ψ kept hzero
    hcode hinj hcover η]
  have h := pqc_residual_arbitrary_readout_moment f guess ψ kept η
  have hg : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  convert h using 1
  simp only [pqcResidualRowLabels]
  field_simp [hj,hg]

end Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources

namespace Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic
open scoped BigOperators Classical

variable {K G C J : Type} [AddGroup K] [Fintype K] [DecidableEq K]
  [AddCommGroup G] [Fintype G] [DecidableEq G]
  [Fintype C] [DecidableEq C] [Fintype J]

omit [AddCommGroup G] in
/-- The actual finite-label construction satisfies `pqc_residual_correct_mass_zero_rows` with all displayed hypotheses. -/
theorem pqc_residual_correct_mass_zero_rows (f : K → G × C)
    (guess : G × C → K) (ψ : QState K) (kept : Finset C) :
    pqcResidualCorrectMass f guess ψ kept =
      ∑ c ∈ kept, ∑ y : G, BornProb (pqcResidualState f guess ψ) ((y,c),0) := by
  rw [pqc_residual_correct_mass_labels]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hf : f (guess (y,c)) = (y,c) <;>
    simp [BornProb, pqc_residual_state_apply_zero, hf]

omit [AddCommGroup G] in
/-- The actual finite-label construction satisfies `pqc_residual_anchor_mean_correct_rows` with all displayed hypotheses. -/
theorem pqc_residual_anchor_mean_correct_rows (f : K → G × C)
    (guess : G × C → K) (anchor : C → J → K)
    (ψ : QState K) (kept : Finset C) (hzero : (f 0).2 ∉ kept)
    (hcode : ∀ c ∈ kept, ∀ j, (f (anchor c j)).2 = c)
    (hinj : ∀ c ∈ kept, Function.Injective (anchor c))
    (hcover : ∀ c ∈ kept, ∀ k, (f k).2 = c → ∃ j, anchor c j = k) :
    (Fintype.card J : ℝ)⁻¹ * ∑ j : J,
      pqcResidualCorrectMass f (pqcResidualAnchorGuess f guess anchor j) ψ kept =
    (Fintype.card J : ℝ)⁻¹ * ∑ c ∈ kept, ∑ r : K,
      ((pqcResidualRowLabels f guess c r).card : ℝ) *
        ∑ y : G, BornProb (pqcResidualState f guess ψ) ((y,c),r) := by
  congr 1
  simp_rw [pqc_residual_correct_mass_zero_rows]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  simp_rw [BornProb, pqc_residual_anchor_state_zero_eq f guess anchor _ ψ kept hzero c hc]
  rw [sum_comp_count (fun j => pqcResidualAnchorOffset f guess anchor j c)
    (fun r => ∑ y : G, ‖pqcResidualState f guess ψ ((y,c),r)‖^2)]
  apply Finset.sum_congr rfl
  intro r _
  rw [pqc_residual_anchor_offset_count f guess anchor c r
    (hcode c hc) (hinj c hc) (hcover c hc)]
  rfl

/-- The actual finite-label construction satisfies `pqc_residual_anchor_readout_le_mean_correct` with all displayed hypotheses. -/
theorem pqc_residual_anchor_readout_le_mean_correct [Nonempty J] (f : K → G × C)
    (guess : G × C → K) (anchor : C → J → K)
    (ψ : QState K) (kept : Finset C) (hzero : (f 0).2 ∉ kept)
    (hcode : ∀ c ∈ kept, ∀ j, (f (anchor c j)).2 = c)
    (hinj : ∀ c ∈ kept, Function.Injective (anchor c))
    (hcover : ∀ c ∈ kept, ∀ k, (f k).2 = c → ∃ j, anchor c j = k)
    (η : AddChar G ℂ) :
    pqcResidualAcceptedReadoutMass f guess ψ kept η ≤
      ((Fintype.card J : ℝ)/(Fintype.card G : ℝ)) *
        ((Fintype.card J : ℝ)⁻¹ * ∑ j : J,
          pqcResidualCorrectMass f (pqcResidualAnchorGuess f guess anchor j) ψ kept) := by
  have hj : (Fintype.card J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hg : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [pqc_residual_anchor_mean_correct_rows f guess anchor ψ kept hzero hcode hinj hcover]
  have h : pqcResidualAcceptedReadoutMass f guess ψ kept η ≤
      (Fintype.card G : ℝ)⁻¹ * ∑ c ∈ kept, ∑ r : K,
        ((pqcResidualRowLabels f guess c r).card : ℝ) *
          ∑ y : G, BornProb (pqcResidualState f guess ψ) ((y,c),r) := by
    unfold pqcResidualAcceptedReadoutMass
    simp only [MeasureProb,Finset.sum_product,Finset.sum_singleton]
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c _
    apply Finset.sum_le_sum
    intro r _
    simpa only [Finset.mul_sum,mul_assoc] using
      pqc_residual_arbitrary_row_readout_bound f guess ψ η c r
  convert h using 1
  field_simp [hj,hg]

end Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources
