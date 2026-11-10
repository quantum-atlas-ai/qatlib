/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiSectorHelpers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.SpectralFilter.PhaseReadout

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Matrix
open scoped Classical BigOperators

theorem ti_state_inner (n t : ℕ) (p q : Fin n → ℂ) :
    Qatlib.Foundations.PureStateMath.Inner (tiPolynomialState n t p) (tiPolynomialState n t q)=Qatlib.Foundations.PureStateMath.Inner p q := by
  have hs : (Real.sqrt 2 : ℂ)⁻¹*(Real.sqrt 2 : ℂ)⁻¹=(1/2:ℂ) := by
    simpa only [Nat.cast_ofNat,one_div] using inv_sqrt_mul_inv_sqrt (by norm_num : 0<(2:ℕ))
  have hf (i : Fin n) :
      (starRingEnd ℂ) (tiPolynomialState n t p ⟨i.val,by have := i.isLt; omega⟩)*
        tiPolynomialState n t q ⟨i.val,by have := i.isLt; omega⟩ =
      (1/2:ℂ)*((starRingEnd ℂ) (p i)*q i) := by
    rw [ti_state_first,ti_state_first]
    simp only [map_mul,map_inv₀,Complex.conj_ofReal]
    calc
      _ = ((Real.sqrt 2 : ℂ)⁻¹*(Real.sqrt 2 : ℂ)⁻¹)*((starRingEnd ℂ) (p i)*q i) := by ring
      _ = _ := by rw [hs]
  have hb (i : Fin n) :
      (starRingEnd ℂ) (tiPolynomialState n t p ⟨n+i.val,by have := i.isLt; omega⟩)*
        tiPolynomialState n t q ⟨n+i.val,by have := i.isLt; omega⟩ =
      (1/2:ℂ)*((starRingEnd ℂ) (p i)*q i) := by
    rw [ti_state_second,ti_state_second]
    simp only [map_mul,map_inv₀,Complex.conj_ofReal,map_pow,map_neg,map_one]
    calc
      _ = ((Real.sqrt 2 : ℂ)⁻¹*(Real.sqrt 2 : ℂ)⁻¹)*
          ((-1:ℂ)^t*(-1:ℂ)^t)*((starRingEnd ℂ) (p i)*q i) := by ring
      _ = _ := by rw [hs,ti_parity_square, mul_one]
  rw [inner_apply,ti_sum_halves,inner_apply]
  simp_rw [hf,hb]
  rw [← Finset.mul_sum]
  ring

theorem ti_state_readout (n t : ℕ) (p : Fin n → ℂ) (y : Fin n) :
    Qatlib.Foundations.PureStateMath.Inner (tiPolynomialReadoutVector n t y) (tiPolynomialState n t p)=p y := by
  rw [tiPolynomialReadoutVector,ti_state_inner]
  simp [inner_apply,Ket]

theorem ti_readout_orthogonal (n t : ℕ) (y z : Fin n) :
    Qatlib.Foundations.PureStateMath.Inner (tiPolynomialReadoutVector n t y) (tiPolynomialReadoutVector n t z)=
      if y=z then 1 else 0 := by
  rw [tiPolynomialReadoutVector,tiPolynomialReadoutVector,ti_state_inner,inner_ket_ket]

theorem ti_state_norm_sum (n t : ℕ) (p : Fin n → ℂ) :
    (∑ i,Complex.normSq (tiPolynomialState n t p i))=∑ i,Complex.normSq (p i) := by
  have hs : Complex.normSq ((Real.sqrt 2 : ℂ)⁻¹)=(1/2:ℝ) := by
    rw [Complex.normSq_inv,Complex.normSq_ofReal,← pow_two,Real.sq_sqrt (by norm_num)]
    norm_num
  rw [ti_sum_halves]
  simp only [ti_state_first,ti_state_second,Complex.normSq_mul,hs,map_pow,
    Complex.normSq_neg,map_one,one_pow,one_mul,← Finset.mul_sum]
  ring

theorem ti_normalized_sector_coefficients (n t : ℕ) [NeZero n] (ψ : QState (Fin (2*n)))
    (hψ : Normalized ψ) (hp : ApplyGate ((tiTranslation n)^n) ψ=(-1:ℂ)^t • ψ) :
    ∑ i : Fin n,Complex.normSq ((Real.sqrt 2 : ℂ)*ψ ⟨i.val,by have := i.isLt; omega⟩)=1 := by
  have he := ti_sector_representation n t ψ hp
  have hn : ∑ i,Complex.normSq (tiPolynomialState n t
      (fun i => (Real.sqrt 2 : ℂ)*ψ ⟨i.val,by have := i.isLt; omega⟩) i)=1 := by
    rw [← he]
    simpa only [Normalized,← Complex.normSq_eq_norm_sq] using hψ
  rw [ti_state_norm_sum] at hn
  exact hn

theorem ti_sector_readout_mass (n t : ℕ) [NeZero n] (ψ : QState (Fin (2*n)))
    (hψ : Normalized ψ) (hp : ApplyGate ((tiTranslation n)^n) ψ=(-1:ℂ)^t • ψ) :
    (∑ y : Fin n,Complex.normSq (Qatlib.Foundations.PureStateMath.Inner (tiPolynomialReadoutVector n t y) ψ))=1 := by
  have he := ti_sector_representation n t ψ hp
  have hn := ti_normalized_sector_coefficients n t ψ hψ hp
  calc
    _ = ∑ y : Fin n,Complex.normSq (Qatlib.Foundations.PureStateMath.Inner (tiPolynomialReadoutVector n t y)
        (tiPolynomialState n t (fun i => (Real.sqrt 2 : ℂ)*ψ ⟨i.val,by have := i.isLt; omega⟩))) := by rw [← he]
    _ = _ := by simpa only [ti_state_readout] using hn

theorem ti_state_folded (n t : ℕ) (p : Fin n → ℂ) (y : Fin n) :
    MeasureProb (tiPolynomialState n t p) (tiFoldedEvent n y)=Complex.normSq (p y) := by
  have hs : Complex.normSq ((Real.sqrt 2 : ℂ)⁻¹)=(1/2:ℝ) := by
    rw [Complex.normSq_inv,Complex.normSq_ofReal,← pow_two,Real.sq_sqrt (by norm_num)]
    norm_num
  have hf (i : Fin n) : (i.val%n=y.val) ↔ i=y := by
    rw [Nat.mod_eq_of_lt i.isLt]
    exact Fin.val_inj
  have hb (i : Fin n) : ((n+i.val)%n=y.val) ↔ i=y := by
    rw [Nat.add_mod_left,Nat.mod_eq_of_lt i.isLt]
    exact Fin.val_inj
  simp only [MeasureProb,tiFoldedEvent,Finset.sum_filter,BornProb,← Complex.normSq_eq_norm_sq]
  rw [ti_sum_halves]
  simp_rw [hf,hb]
  simp only [ti_state_first,ti_state_second,Complex.normSq_mul,hs,map_pow,
    Complex.normSq_neg,map_one,one_pow,one_mul]
  simp
  ring

theorem ti_sector_folded_eq_readout (n t : ℕ) [NeZero n] (ψ : QState (Fin (2*n)))
    (hp : ApplyGate ((tiTranslation n)^n) ψ=(-1:ℂ)^t • ψ) (y : Fin n) :
    MeasureProb ψ (tiFoldedEvent n y)=Complex.normSq (Qatlib.Foundations.PureStateMath.Inner (tiPolynomialReadoutVector n t y) ψ) := by
  have he := ti_sector_representation n t ψ hp
  conv_lhs => rw [he]
  conv_rhs => rw [he]
  rw [ti_state_folded,ti_state_readout]

theorem ti_sector_readout_value (n t : ℕ) [NeZero n] (ψ : QState (Fin (2*n)))
    (hp : ApplyGate ((tiTranslation n)^n) ψ=(-1:ℂ)^t • ψ) (y : Fin n) :
    Qatlib.Foundations.PureStateMath.Inner (tiPolynomialReadoutVector n t y) ψ =
      (Real.sqrt 2 : ℂ)*ψ ⟨y.val,by have := y.isLt; omega⟩ := by
  have he := ti_sector_representation n t ψ hp
  calc
    _ = Qatlib.Foundations.PureStateMath.Inner (tiPolynomialReadoutVector n t y) (tiPolynomialState n t
        (fun i => (Real.sqrt 2 : ℂ)*ψ ⟨i.val,by have := i.isLt; omega⟩)) := congrArg (Qatlib.Foundations.PureStateMath.Inner _) he
    _ = _ := ti_state_readout n t _ y

theorem ti_translated_correct_first (n t : ℕ) [NeZero n] (p : Fin n → ℂ) (j : Fin (2*n)) :
    ApplyGate ((tiTranslation n)^j.val) (tiPolynomialState n t p)
      ⟨(ospFun n j).val,by have := (ospFun n j).isLt; omega⟩ =
      if j.val<n then (Real.sqrt 2 : ℂ)⁻¹*p 0 else (Real.sqrt 2 : ℂ)⁻¹*((-1:ℂ)^t*p 0) := by
  let e := (finShiftEquiv (2*n))^j.val
  rw [ti_translation_pow,ti_apply_permutation]
  by_cases hj : j.val<n
  · have hy : (ospFun n j).val=j.val := Nat.mod_eq_of_lt hj
    have he : e.symm ⟨(ospFun n j).val,by have := (ospFun n j).isLt; omega⟩ =
        (⟨(0 : Fin n).val,by have := (0 : Fin n).isLt; omega⟩ : Fin (2*n)) := by
      apply e.injective
      rw [Equiv.apply_symm_apply]
      apply Fin.val_injective
      rw [ti_shift_pow_val]
      simp only [Fin.val_zero,zero_add,Nat.mod_eq_of_lt j.isLt]
      exact hy
    rw [if_pos hj]
    change tiPolynomialState n t p (e.symm ⟨(ospFun n j).val,_⟩)=_
    rw [he,ti_state_first]
  · have hy : (ospFun n j).val=j.val-n := by
      change j.val%n=j.val-n
      calc
        _ = ((j.val-n)+n)%n := by congr 1; omega
        _ = (j.val-n)%n := Nat.add_mod_right _ _
        _ = _ := Nat.mod_eq_of_lt (by have := j.isLt; omega)
    have he : e.symm ⟨(ospFun n j).val,by have := (ospFun n j).isLt; omega⟩ =
        (⟨n+(0 : Fin n).val,by have := (0 : Fin n).isLt; omega⟩ : Fin (2*n)) := by
      apply e.injective
      rw [Equiv.apply_symm_apply]
      apply Fin.val_injective
      rw [ti_shift_pow_val]
      simp only [Fin.val_zero,add_zero]
      rw [show n+j.val=(j.val-n)+2*n by omega,Nat.add_mod_right,
        Nat.mod_eq_of_lt (by have := j.isLt; omega)]
      exact hy
    rw [if_neg hj]
    change tiPolynomialState n t p (e.symm ⟨(ospFun n j).val,_⟩)=_
    rw [he,ti_state_second]

theorem ti_translated_readout_correct (n t : ℕ) [NeZero n] (p : Fin n → ℂ) (j : Fin (2*n)) :
    Complex.normSq (Qatlib.Foundations.PureStateMath.Inner (tiPolynomialReadoutVector n t (ospFun n j))
      (ApplyGate ((tiTranslation n)^j.val) (tiPolynomialState n t p)))=Complex.normSq (p 0) := by
  have hs : Complex.normSq (Real.sqrt 2 : ℂ)=2 := by
    rw [Complex.normSq_ofReal,← pow_two,Real.sq_sqrt (by norm_num)]
  rw [ti_sector_readout_value n t _ (ti_translated_sector n t j.val p),ti_translated_correct_first]
  split_ifs <;> simp only [Complex.normSq_mul,Complex.normSq_inv,hs,map_pow,
    Complex.normSq_neg,map_one,one_pow,one_mul]
  all_goals ring

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
