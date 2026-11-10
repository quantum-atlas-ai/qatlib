/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorRegisters.RegisterModel.QmaCompletenessLocalEnergy
import Qatlib.Foundations.InstrumentCore.Measurement.Basic
open Qatlib.Foundations.InstrumentCore.Measurement
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription

namespace Qatlib.Concepts.SpectralReadout.PhaseReadout
open Qatlib Matrix
open Qatlib.Concepts.TensorRegisters.RegisterModel
open scoped Classical BigOperators Kronecker
set_option autoImplicit false
noncomputable section

theorem mass_nonneg {I : Type} [Fintype I] (ψ : QState I) : 0 ≤ mass ψ :=
  Finset.sum_nonneg (fun i _ => sq_nonneg ‖ψ i‖)

theorem mass_zero_iff {I : Type} [Fintype I] (ψ : QState I) : mass ψ=0 ↔ ψ=0 := by
  constructor
  · intro h
    funext i
    have hz : ‖ψ i‖^2=0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖ψ j‖)).mp h i (Finset.mem_univ i)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · intro h
    rw [h]
    simp [mass]

theorem energy_real_smul {I : Type} [Fintype I] (H : Matrix I I ℂ)
    (r : ℝ) (ψ : QState I) : energy H ((r:ℂ) • ψ)=r^2*energy H ψ := by
  calc
    energy H ((r:ℂ) • ψ)=
        ∑i,∑j,r^2*((starRingEnd ℂ) (ψ i)*H i j*ψ j).re := by
      rw [energy_entries]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [Pi.smul_apply,smul_eq_mul,map_mul,Complex.conj_ofReal]
      have he : (r:ℂ)*(starRingEnd ℂ) (ψ i)*H i j*((r:ℂ)*ψ j)=
          ((r*r:ℝ):ℂ)*((starRingEnd ℂ) (ψ i)*H i j*ψ j) := by push_cast; ring
      rw [he]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,pow_two]
    _ = r^2*energy H ψ := by rw [energy_entries]; simp only [Finset.mul_sum]

theorem mass_real_smul {I : Type} [Fintype I] (r : ℝ) (ψ : QState I) :
    mass ((r:ℂ) • ψ)=r^2*mass ψ := by
  simp only [mass,Pi.smul_apply,smul_eq_mul,norm_mul,mul_pow,Complex.norm_real,
    Real.norm_eq_abs,sq_abs,Finset.mul_sum]

theorem homogeneous_lower {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (b : ℝ)
    (h : ∀ψ : QState I,Normalized ψ → b≤energy H ψ) (ψ : QState I) :
    b*mass ψ≤energy H ψ := by
  by_cases hz : ψ=0
  · subst ψ
    simp [mass,energy,Qatlib.Foundations.PureStateMath.Inner]
  · have hp : 0 < mass ψ := lt_of_le_of_ne (mass_nonneg ψ)
      (Ne.symm (fun h0 => hz ((mass_zero_iff ψ).mp h0)))
    let θ := PostMeasure ψ Finset.univ
    have hm : MeasureProb ψ Finset.univ=mass ψ := rfl
    have hθ : Normalized θ := normalized_postMeasure (hm.symm ▸ hp)
    have hs : (Real.sqrt (mass ψ):ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hp).ne'
    have hr : (Real.sqrt (mass ψ):ℂ) • θ=ψ := by
      funext i
      simp only [θ,PostMeasure,Pi.smul_apply,smul_eq_mul,collapse_apply,Finset.mem_univ,ite_true]
      change (Real.sqrt (mass ψ):ℂ)*((Real.sqrt (mass ψ):ℂ)⁻¹*ψ i)=ψ i
      rw [← mul_assoc,mul_inv_cancel₀ hs,one_mul]
    have he := energy_real_smul H (Real.sqrt (mass ψ)) θ
    rw [hr,Real.sq_sqrt (mass_nonneg ψ)] at he
    calc
      b*mass ψ=mass ψ*b := mul_comm _ _
      _ ≤ mass ψ*energy H θ := mul_le_mul_of_nonneg_left (h θ hθ) (mass_nonneg ψ)
      _ = energy H ψ := he.symm

def goodPart {m n : ℕ} (η : QState (Clock m×Reg n)) : QState (Clock m×Reg n) :=
  fun p => if LegalClock p.1 then η p else 0

def badPart {m n : ℕ} (η : QState (Clock m×Reg n)) : QState (Clock m×Reg n) :=
  fun p => if LegalClock p.1 then 0 else η p

def restricted {m n : ℕ} (η : QState (Clock m×Reg n)) : QState (Fin (m+1)×Reg n) :=
  fun p => η (unary p.1,p.2)

theorem parts_add {m n : ℕ} (η : QState (Clock m×Reg n)) : goodPart η+badPart η=η := by
  funext p
  by_cases h : LegalClock p.1 <;> simp [goodPart,badPart,h]

theorem parts_mass {m n : ℕ} (η : QState (Clock m×Reg n)) :
    mass (goodPart η)+mass (badPart η)=mass η := by
  simp only [mass,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : LegalClock p.1 <;> simp [goodPart,badPart,h]

theorem historyFrame_apply_clock {m n : ℕ} (ψ : QState (Fin (m+1)×Reg n))
    (c : Clock m) (z : Reg n) :
    (historyFrame m n*ᵥψ) (c,z)=∑t,clockFrame m c t*ψ (t,z) := by
  simp [historyFrame,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Matrix.one_apply,mul_ite]

theorem historyFrame_apply {m n : ℕ} (ψ : QState (Fin (m+1)×Reg n))
    (c : Clock m) (z : Reg n) :
    (historyFrame m n*ᵥψ) (c,z)=if LegalClock c then ψ (decode c,z) else 0 := by
  rw [historyFrame_apply_clock]
  by_cases hc : LegalClock c
  · obtain ⟨t,ht⟩ := (legal_iff_unary c).mp hc
    rw [← ht] at hc ⊢
    simp [clockFrame,(unary_injective m).eq_iff,hc,decode_unary]
  · have hn : ∀t : Fin (m+1),c≠unary t := by
      intro t ht
      exact hc (ht ▸ unary_legal t)
    simp [clockFrame,hn,hc]

theorem embed_restricted {m n : ℕ} (η : QState (Clock m×Reg n)) :
    historyFrame m n*ᵥrestricted η=goodPart η := by
  funext ⟨c,z⟩
  rw [historyFrame_apply]
  by_cases hc : LegalClock c
  · simp [restricted,goodPart,hc,unary_decode c hc]
  · simp [goodPart,hc]

theorem restricted_mass {m n : ℕ} (η : QState (Clock m×Reg n)) :
    mass (restricted η)=mass (goodPart η) := by
  rw [← embed_restricted]
  exact (historyFrame_mass m n (restricted η)).symm

theorem clock_good_zero {m n : ℕ} (η : QState (Clock m×Reg n)) :
    TensorGate (clockPenalty m) (1:Matrix (Reg n) (Reg n) ℂ)*ᵥgoodPart η=0 := by
  rw [← embed_restricted,Matrix.mulVec_mulVec,lifted_clockPenalty_annihilates_history,Matrix.zero_mulVec]

theorem clock_bad_energy_lower {m n : ℕ} (η : QState (Clock m×Reg n)) :
    mass (badPart η)≤energy (TensorGate (clockPenalty m) (1:Matrix (Reg n) (Reg n) ℂ)) (badPart η) := by
  change mass (badPart η)≤energy (clockPenalty m⊗ₖ(1:Matrix (Reg n) (Reg n) ℂ)) (badPart η)
  rw [energy_tensor_one]
  calc
    mass (badPart η)=∑z : Reg n,mass (fun c : Clock m => badPart η (c,z)) := (mass_fibers _).symm
    _ = ∑z : Reg n,∑c : Clock m,if LegalClock c then (0:ℝ) else ‖badPart η (c,z)‖^2 := by
      apply Finset.sum_congr rfl
      intro z _
      unfold mass
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : LegalClock c <;> simp [badPart,hc]
    _ ≤ ∑z : Reg n,energy (clockPenalty m) (fun c : Clock m => badPart η (c,z)) :=
      Finset.sum_le_sum (fun _ _ => clockPenalty_energy_lower _)

def SectorPreserving {m n : ℕ} (H : Matrix (Clock m×Reg n) (Clock m×Reg n) ℂ) : Prop :=
  ∀p q,H p q≠0 → (LegalClock p.1 ↔ LegalClock q.1)

theorem sector_energy_parts {m n : ℕ} (H : Matrix (Clock m×Reg n) (Clock m×Reg n) ℂ)
    (hH : SectorPreserving H) (η : QState (Clock m×Reg n)) :
    energy H η=energy H (goodPart η)+energy H (badPart η) := by
  rw [energy_entries,energy_entries,energy_entries,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hp : LegalClock p.1 <;> by_cases hq : LegalClock q.1
  · simp [goodPart,badPart,hp,hq]
  · have hz : H p q=0 := by
      by_contra hn
      exact hq ((hH p q hn).mp hp)
    simp [goodPart,badPart,hp,hq,hz]
  · have hz : H p q=0 := by
      by_contra hn
      exact hp ((hH p q hn).mpr hq)
    simp [goodPart,badPart,hp,hq,hz]
  · simp [goodPart,badPart,hp,hq]

theorem intertwine_energy {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (V : Matrix J I ℂ) (hV : Vᴴ*V=1)
    (H : Matrix J J ℂ) (A : Matrix I I ℂ) (h : H*V=V*A) (ψ : QState I) :
    energy H (V*ᵥψ)=energy A ψ := by
  rw [energy,Matrix.mulVec_mulVec,h,← Matrix.mulVec_mulVec,
    inner_mulVec_left_rect,Matrix.mulVec_mulVec,hV,Matrix.one_mulVec]
  rfl

theorem sector_zero {m n : ℕ} :
    SectorPreserving (0:Matrix (Clock m×Reg n) (Clock m×Reg n) ℂ) := by
  intro p q h
  exact False.elim (h rfl)

theorem sector_add {m n : ℕ} (H K : Matrix (Clock m×Reg n) (Clock m×Reg n) ℂ)
    (hH : SectorPreserving H) (hK : SectorPreserving K) : SectorPreserving (H+K) := by
  intro p q h
  by_cases hz : H p q=0
  · have hk : K p q≠0 := by intro hk; simp [hz,hk] at h
    exact hK p q hk
  · exact hH p q hz

theorem sector_sub {m n : ℕ} (H K : Matrix (Clock m×Reg n) (Clock m×Reg n) ℂ)
    (hH : SectorPreserving H) (hK : SectorPreserving K) : SectorPreserving (H-K) := by
  intro p q h
  by_cases hz : H p q=0
  · have hk : K p q≠0 := by intro hk; simp [hz,hk] at h
    exact hK p q hk
  · exact hH p q hz

theorem sector_smul {m n : ℕ} (c : ℂ) (H : Matrix (Clock m×Reg n) (Clock m×Reg n) ℂ)
    (hH : SectorPreserving H) : SectorPreserving (c • H) := by
  intro p q h
  apply hH p q
  intro hz
  simp [hz] at h

theorem tensor_sector {m n : ℕ} (M : Matrix (Clock m) (Clock m) ℂ)
    (U : Matrix (Reg n) (Reg n) ℂ)
    (hM : ∀c d,M c d≠0 → (LegalClock c ↔ LegalClock d)) : SectorPreserving (TensorGate M U) := by
  intro p q h
  change M p.1 q.1*U p.2 q.2≠0 at h
  apply hM p.1 q.1
  intro hz
  simp [hz] at h

theorem diagonal_clock_sector {m : ℕ} (w : Clock m→ℂ) :
    ∀c d,Matrix.diagonal w c d≠0 → (LegalClock c ↔ LegalClock d) := by
  intro c d h
  by_cases hc : c=d
  · subst d
    rfl
  · simp [hc] at h

theorem clock_sector (m n : ℕ) :
    SectorPreserving (TensorGate (clockPenalty m) (1:Matrix (Reg n) (Reg n) ℂ)) :=
  tensor_sector _ _ (diagonal_clock_sector _)

theorem propagation_sector {m n : ℕ} (i : Fin m) (U : Matrix (Reg n) (Reg n) ℂ) :
    SectorPreserving (physicalPropagation i U) := by
  have hp : SectorPreserving (TensorGate (postProjector i) (1:Matrix (Reg n) (Reg n) ℂ)) :=
    tensor_sector _ _ (diagonal_clock_sector _)
  have hq : SectorPreserving (TensorGate (preProjector i) (1:Matrix (Reg n) (Reg n) ℂ)) :=
    tensor_sector _ _ (diagonal_clock_sector _)
  have hh : SectorPreserving (TensorGate (hop i) U) := tensor_sector _ _ (hop_nonzero_sector i)
  have ha : SectorPreserving (TensorGate (hop i)ᴴ Uᴴ) := by
    apply tensor_sector
    intro c d h
    have ht : hop i d c≠0 := by intro hz; simp [Matrix.conjTranspose_apply,hz] at h
    exact (hop_nonzero_sector i d c ht).symm
  exact sector_smul _ _ (sector_sub _ _ (sector_sub _ _ (sector_add _ _ hp hq) hh) ha)

theorem input_sector {m n : ℕ} (j : Fin n) : SectorPreserving (physicalInput (m:=m) j) :=
  tensor_sector _ _ (diagonal_clock_sector _)

theorem output_sector {m n : ℕ} (j : Fin n) : SectorPreserving (physicalOutput (m:=m) j) :=
  tensor_sector _ _ (diagonal_clock_sector _)

theorem energy_add {I : Type} [Fintype I] (H K : Matrix I I ℂ) (ψ : QState I) :
    energy (H+K) ψ=energy H ψ+energy K ψ := by
  simp only [energy_entries,Matrix.add_apply,mul_add,add_mul,Complex.add_re,Finset.sum_add_distrib]

theorem energy_matrix_real_smul {I : Type} [Fintype I] (r : ℝ) (H : Matrix I I ℂ)
    (ψ : QState I) : energy ((r:ℂ) • H) ψ=r*energy H ψ := by
  rw [energy_entries,energy_entries]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.smul_apply,smul_eq_mul]
  have he : (starRingEnd ℂ) (ψ i)*((r:ℂ)*H i j)*ψ j=
      (r:ℂ)*((starRingEnd ℂ) (ψ i)*H i j*ψ j) := by ring
  rw [he]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

theorem full_space_lower {m n : ℕ}
    (H : Matrix (Clock m×Reg n) (Clock m×Reg n) ℂ)
    (A : Matrix (Fin (m+1)×Reg n) (Fin (m+1)×Reg n) ℂ)
    (hSector : SectorPreserving H) (hFrame : H*historyFrame m n=historyFrame m n*A)
    (b K J : ℝ) (hK : 0≤K) (hJ : K+1≤J) (hb : b≤1)
    (hLegal : ∀ψ : QState (Fin (m+1)×Reg n),Normalized ψ → b≤energy A ψ)
    (hRest : ∀ψ : QState (Clock m×Reg n),-K*mass ψ≤energy H ψ)
    (η : QState (Clock m×Reg n)) (hη : Normalized η) :
    b≤energy (H+(J:ℂ) • TensorGate (clockPenalty m) (1:Matrix (Reg n) (Reg n) ℂ)) η := by
  let D := TensorGate (clockPenalty m) (1:Matrix (Reg n) (Reg n) ℂ)
  let T := H+(J:ℂ) • D
  have hJ0 : 0≤J := by linarith
  have hDgood : energy D (goodPart η)=0 := by
    simp [D,energy,clock_good_zero,Qatlib.Foundations.PureStateMath.inner_apply]
  have hGoodEq : energy T (goodPart η)=energy A (restricted η) := by
    change energy (H+(J:ℂ) • D) (goodPart η)=energy A (restricted η)
    rw [energy_add,energy_matrix_real_smul,hDgood,mul_zero,add_zero,← embed_restricted]
    exact intertwine_energy _ (historyFrame_isometry m n) _ _ hFrame _
  have hGood : b*mass (goodPart η)≤energy T (goodPart η) := by
    rw [hGoodEq,← restricted_mass]
    exact homogeneous_lower A b hLegal _
  have hBad : mass (badPart η)≤energy T (badPart η) := by
    change mass (badPart η)≤energy (H+(J:ℂ) • D) (badPart η)
    rw [energy_add,energy_matrix_real_smul]
    have h1 := hRest (badPart η)
    have h2 := mul_le_mul_of_nonneg_left (clock_bad_energy_lower η) hJ0
    have h3 := mul_nonneg (sub_nonneg.mpr hJ) (mass_nonneg (badPart η))
    nlinarith
  have hm : mass (goodPart η)+mass (badPart η)=1 := (parts_mass η).trans hη
  have hbMass : b*mass (badPart η) ≤ mass (badPart η) := by
    nlinarith [mass_nonneg (badPart η)]
  have ht : SectorPreserving T := sector_add _ _ hSector (sector_smul _ _ (clock_sector m n))
  change b≤energy T η
  calc
    b=b*mass (goodPart η)+b*mass (badPart η) := by rw [← mul_add,hm,mul_one]
    _ ≤ energy T (goodPart η)+energy T (badPart η) := add_le_add hGood (hbMass.trans hBad)
    _ = energy T η := (sector_energy_parts T ht η).symm

end
end Qatlib.Concepts.SpectralReadout.PhaseReadout
