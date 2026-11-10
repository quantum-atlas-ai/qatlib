/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiPolynomialTransitionKernelStat
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiTranslationHelpers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Matrix
open scoped Classical BigOperators

theorem ti_qft_adjoint_entry (n : ℕ) (l i : Fin (2*n)) :
    (QFTMatrix (2*n))ᴴ l i =
      (Real.sqrt (2*n:ℝ) : ℂ)⁻¹ * tiMomentumRoot n l ^ i.val := by
  simp only [Matrix.conjTranspose_apply,qftMatrix_apply,Complex.star_def,map_mul,map_inv₀,
    Complex.conj_ofReal,primRoot_conj_zpow,Nat.cast_mul,Nat.cast_ofNat]
  unfold tiMomentumRoot
  rw [← zpow_natCast,← _root_.zpow_mul]
  congr 1
  congr 1
  ring

theorem ti_fourier_scale (n : ℕ) :
    (Real.sqrt (2*n:ℝ) : ℂ)⁻¹*(Real.sqrt 2 : ℂ)⁻¹*2 =
      (Real.sqrt (n:ℝ) : ℂ)⁻¹ := by
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2),Complex.ofReal_mul,_root_.mul_inv_rev]
  calc
    _ = (Real.sqrt (n:ℝ) : ℂ)⁻¹*
        ((Real.sqrt 2 : ℂ)⁻¹*(Real.sqrt 2 : ℂ)⁻¹*2) := by ring
    _ = _ := by
      have h := inv_sqrt_mul_inv_sqrt (by norm_num : 0<(2:ℕ))
      norm_num only [Nat.cast_ofNat] at h
      rw [h]
      norm_num

theorem ti_parity_factor (t r : ℕ) :
    1+(-1:ℂ)^t*(-1:ℂ)^r = if r%2=t%2 then 2 else 0 := by
  rw [neg_one_pow_eq_pow_mod_two t,neg_one_pow_eq_pow_mod_two r]
  have ht : t%2=0 ∨ t%2=1 := by omega
  have hr : r%2=0 ∨ r%2=1 := by omega
  rcases ht with ht | ht <;> rcases hr with hr | hr <;> norm_num [ht,hr]

theorem ti_fourier_sum (n t : ℕ) (p : Fin n → ℂ) (l : Fin (2*n)) :
    ApplyGate (QFTMatrix (2*n))ᴴ (tiPolynomialState n t p) l =
      (Real.sqrt (2*n:ℝ) : ℂ)⁻¹*(Real.sqrt 2 : ℂ)⁻¹*
        (1+(-1:ℂ)^t*tiMomentumRoot n l^n)*tiPolyEval p (tiMomentumRoot n l) := by
  let z := tiMomentumRoot n l
  let c := (Real.sqrt (2*n:ℝ) : ℂ)⁻¹
  let s := (Real.sqrt 2 : ℂ)⁻¹
  have hfirst : (∑ i : Fin n,
      c*z^i.val*tiPolynomialState n t p ⟨i.val,by have := i.isLt; omega⟩) =
      c*s*tiPolyEval p z := by
    rw [tiPolyEval,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [ti_state_first]
    dsimp [s]
    ring
  have hsecond : (∑ i : Fin n,
      c*z^(n+i.val)*tiPolynomialState n t p ⟨n+i.val,by have := i.isLt; omega⟩) =
      (c*s*((-1:ℂ)^t*z^n))*tiPolyEval p z := by
    rw [tiPolyEval,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [ti_state_second,pow_add]
    dsimp [s]
    ring
  simp only [ApplyGate,Matrix.mulVec,dotProduct]
  simp_rw [ti_qft_adjoint_entry]
  rw [ti_sum_halves]
  change (∑ i : Fin n,c*z^i.val*tiPolynomialState n t p ⟨i.val,_⟩)+
      (∑ i : Fin n,c*z^(n+i.val)*tiPolynomialState n t p ⟨n+i.val,_⟩) = _
  rw [hfirst,hsecond]
  change c*s*tiPolyEval p z+c*s*((-1:ℂ)^t*z^n)*tiPolyEval p z =
    c*s*(1+(-1:ℂ)^t*z^n)*tiPolyEval p z
  ring

theorem ti_polynomial_fourier (n t : ℕ) [NeZero n] (p : Fin n → ℂ) (l : Fin (2*n)) :
    ApplyGate (QFTMatrix (2*n))ᴴ (tiPolynomialState n t p) l =
      if l.val%2=t%2 then
        (Real.sqrt (n:ℝ) : ℂ)⁻¹*tiPolyEval p (tiMomentumRoot n l)
      else 0 := by
  rw [ti_fourier_sum,ti_momentum_root_parity,ti_parity_factor]
  split_ifs
  · rw [ti_fourier_scale]
  · simp

theorem ti_fourier_injective (n : ℕ) [NeZero n] (ψ φ : QState (Fin (2*n)))
    (h : ApplyGate (QFTMatrix (2*n))ᴴ ψ=ApplyGate (QFTMatrix (2*n))ᴴ φ) : ψ=φ := by
  have hF := qftMatrix_unitary (by have := NeZero.pos n; omega : 0<2*n)
  have hFF : QFTMatrix (2*n)*(QFTMatrix (2*n))ᴴ=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hF)
  have he := congrArg (ApplyGate (QFTMatrix (2*n))) h
  dsimp only [ApplyGate] at he
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,hFF,Matrix.one_mulVec] at he
  simpa only [Matrix.one_mulVec] using he

theorem ti_transition_run (n t : ℕ) [NeZero n] (ht : 0<t) (a b : Fin n → ℂ)
    (hm : ∀ z : ℂ,z^n=(-1:ℂ)^t → ‖tiPolyEval a z‖=‖tiPolyEval b z‖) :
    ApplyGate (tiPolynomialTransition n t a b)
      (ApplyGate (PhaseOracle (ospBit n 0)) (tiPolynomialState n (t-1) a)) =
      tiPolynomialState n t b := by
  have hF := qftMatrix_unitary (by have := NeZero.pos n; omega : 0<2*n)
  have hFF : (QFTMatrix (2*n))ᴴ*QFTMatrix (2*n)=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hF)
  have he : (QFTMatrix (2*n))ᴴ*tiPolynomialTransition n t a b =
      Matrix.diagonal (tiTransitionPhase n t a b)*(QFTMatrix (2*n))ᴴ := by
    rw [tiPolynomialTransition,← Matrix.mul_assoc,← Matrix.mul_assoc,hFF,Matrix.one_mul]
  apply ti_fourier_injective n
  rw [ti_query_zero_state n t ht a]
  unfold ApplyGate
  rw [Matrix.mulVec_mulVec,he,← Matrix.mulVec_mulVec,Matrix.mulVec_neg]
  funext l
  rw [Matrix.mulVec_diagonal]
  change tiTransitionPhase n t a b l *
    -(ApplyGate (QFTMatrix (2*n))ᴴ (tiPolynomialState n t a) l) =
    ApplyGate (QFTMatrix (2*n))ᴴ (tiPolynomialState n t b) l
  rw [ti_polynomial_fourier,ti_polynomial_fourier]
  split_ifs with hl
  · calc
      _ = (Real.sqrt (n:ℝ) : ℂ)⁻¹*
          (tiTransitionPhase n t a b l*(-tiPolyEval a (tiMomentumRoot n l))) := by ring
      _ = _ := by rw [ti_transition_phase_eval n t a b hm l hl]
  · simp

theorem tiPolynomialTransitionKernel : TiPolynomialTransitionKernel := by
  refine ⟨ti_polynomial_fourier,?_⟩
  intro n t _ ht a b hm
  exact ⟨ti_transition_phase_norm n t a b hm,ti_transition_unitary n t a b hm,
    ti_transition_commutes n t a b,ti_transition_run n t ht a b hm⟩

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
