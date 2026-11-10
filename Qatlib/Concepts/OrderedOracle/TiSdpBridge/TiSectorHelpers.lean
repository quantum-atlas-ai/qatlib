/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiProgramHelpers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Matrix
open scoped Classical BigOperators

theorem ti_halves_ext {α : Type*} (n : ℕ) (f g : Fin (2*n) → α)
    (hfirst : ∀ i : Fin n,f ⟨i.val,by have := i.isLt; omega⟩=g ⟨i.val,by have := i.isLt; omega⟩)
    (hsecond : ∀ i : Fin n,f ⟨n+i.val,by have := i.isLt; omega⟩=g ⟨n+i.val,by have := i.isLt; omega⟩) :
    f=g := by
  funext j
  by_cases hj : j.val<n
  · exact hfirst ⟨j.val,hj⟩
  · let i : Fin n := ⟨j.val-n,by have := j.isLt; omega⟩
    have he : (⟨n+i.val,by have := i.isLt; omega⟩ : Fin (2*n))=j := by
      ext
      dsimp [i]
      omega
    simpa only [he] using hsecond i

theorem ti_shift_half_first (n : ℕ) [NeZero n] (i : Fin n) :
    ((finShiftEquiv (2*n))^n) ⟨i.val,by have := i.isLt; omega⟩ =
      ⟨n+i.val,by have := i.isLt; omega⟩ := by
  apply Fin.val_injective
  rw [ti_shift_pow_val]
  change (i.val+n)%(2*n)=n+i.val
  rw [Nat.mod_eq_of_lt (by have := i.isLt; omega)]
  omega

theorem ti_shift_half_second (n : ℕ) [NeZero n] (i : Fin n) :
    ((finShiftEquiv (2*n))^n) ⟨n+i.val,by have := i.isLt; omega⟩ =
      ⟨i.val,by have := i.isLt; omega⟩ := by
  apply Fin.val_injective
  rw [ti_shift_pow_val]
  change (n+i.val+n)%(2*n)=i.val
  rw [show n+i.val+n=i.val+2*n by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by have := i.isLt; omega)]

theorem ti_shift_half_involutive (n : ℕ) [NeZero n] :
    Function.Involutive ((finShiftEquiv (2*n))^n) := by
  have ho : (finShiftEquiv (2*n))^(2*n)=1 := by
    ext i
    change (((finShiftEquiv (2*n))^(2*n)) i).val=i.val
    rw [ti_shift_pow_val,Nat.add_mod_right,Nat.mod_eq_of_lt i.isLt]
  have hs : (finShiftEquiv (2*n))^n*(finShiftEquiv (2*n))^n=1 := by
    rw [← pow_add,show n+n=2*n by omega,ho]
  intro i
  have he := congrArg (fun e : Equiv.Perm (Fin (2*n)) => e i) hs
  simpa only [Equiv.Perm.mul_apply,Equiv.Perm.one_apply] using he

theorem ti_half_gate_first (n : ℕ) [NeZero n] (ψ : QState (Fin (2*n))) (i : Fin n) :
    ApplyGate ((tiTranslation n)^n) ψ ⟨i.val,by have := i.isLt; omega⟩ =
      ψ ⟨n+i.val,by have := i.isLt; omega⟩ := by
  rw [ti_translation_pow,applyGate_permMatrix (ti_shift_half_involutive n),ti_shift_half_first]

theorem ti_half_gate_second (n : ℕ) [NeZero n] (ψ : QState (Fin (2*n))) (i : Fin n) :
    ApplyGate ((tiTranslation n)^n) ψ ⟨n+i.val,by have := i.isLt; omega⟩ =
      ψ ⟨i.val,by have := i.isLt; omega⟩ := by
  rw [ti_translation_pow,applyGate_permMatrix (ti_shift_half_involutive n),ti_shift_half_second]

theorem ti_parity_square (t : ℕ) : (-1:ℂ)^t*(-1:ℂ)^t=1 := by
  rw [← pow_two,← pow_mul,show t*2=2*t by omega,pow_mul]
  norm_num

theorem ti_sector_iff (n t : ℕ) [NeZero n] (ψ : QState (Fin (2*n))) :
    ApplyGate ((tiTranslation n)^n) ψ=(-1:ℂ)^t • ψ ↔
      ∀ i : Fin n,ψ ⟨n+i.val,by have := i.isLt; omega⟩=
        (-1:ℂ)^t*ψ ⟨i.val,by have := i.isLt; omega⟩ := by
  constructor
  · intro h i
    have he := congrFun h (⟨i.val,by have := i.isLt; omega⟩ : Fin (2*n))
    simpa only [ti_half_gate_first,Pi.smul_apply,smul_eq_mul] using he
  · intro h
    apply ti_halves_ext n
    · intro i
      simp only [ti_half_gate_first,Pi.smul_apply,smul_eq_mul]
      exact h i
    · intro i
      simp only [ti_half_gate_second,Pi.smul_apply,smul_eq_mul]
      rw [h i,← mul_assoc,ti_parity_square,one_mul]

theorem ti_state_sector (n t : ℕ) [NeZero n] (p : Fin n → ℂ) :
    ApplyGate ((tiTranslation n)^n) (tiPolynomialState n t p)=
      (-1:ℂ)^t • tiPolynomialState n t p := by
  apply (ti_sector_iff n t _).mpr
  intro i
  rw [ti_state_second,ti_state_first]
  ring

theorem ti_sector_representation (n t : ℕ) [NeZero n] (ψ : QState (Fin (2*n)))
    (h : ApplyGate ((tiTranslation n)^n) ψ=(-1:ℂ)^t • ψ) :
    ψ=tiPolynomialState n t (fun i => (Real.sqrt 2 : ℂ)*ψ ⟨i.val,by have := i.isLt; omega⟩) := by
  have hs : (Real.sqrt 2 : ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2))
  have hp := (ti_sector_iff n t ψ).mp h
  apply ti_halves_ext n
  · intro i
    rw [ti_state_first]
    simp only [← mul_assoc,inv_mul_cancel₀ hs,one_mul]
  · intro i
    rw [hp i,ti_state_second]
    simp [hs,mul_left_comm]

theorem ti_commuting_preserves_sector (n t : ℕ) [NeZero n]
    (U : Matrix (Fin (2*n)) (Fin (2*n)) ℂ)
    (hc : tiTranslation n*U=U*tiTranslation n) (ψ : QState (Fin (2*n)))
    (h : ApplyGate ((tiTranslation n)^n) ψ=(-1:ℂ)^t • ψ) :
    ApplyGate ((tiTranslation n)^n) (ApplyGate U ψ)=(-1:ℂ)^t • ApplyGate U ψ := by
  have he := ((show Commute (tiTranslation n) U from hc).pow_left n).eq
  rw [← applyGate_mul,he,applyGate_mul,h]
  simp only [ApplyGate,Matrix.mulVec_smul]

theorem ti_translated_sector (n t r : ℕ) [NeZero n] (p : Fin n → ℂ) :
    ApplyGate ((tiTranslation n)^n) (ApplyGate ((tiTranslation n)^r) (tiPolynomialState n t p)) =
      (-1:ℂ)^t • ApplyGate ((tiTranslation n)^r) (tiPolynomialState n t p) := by
  apply ti_commuting_preserves_sector n t _ ((Commute.refl (tiTranslation n)).pow_right r).eq
  exact ti_state_sector n t p

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
