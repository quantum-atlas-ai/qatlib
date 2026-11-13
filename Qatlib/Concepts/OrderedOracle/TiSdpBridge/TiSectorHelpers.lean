/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiProgramHelpers

/-!
# Half-turn sectors of cyclic translation

This module describes the eigenspaces of half-turn translation on `Fin (2*n)` using the two
coordinate halves. The translation symmetry is motivated by [FarhiEtAl1999], and its
polynomial-state use belongs to the ordered-search framework of [ChildsLandahlParrilo2007]. The
condition in `ti_sector_iff` says that the second half equals the first half multiplied by
`(-1)^t`.

Every vector satisfying this condition is represented by `tiPolynomialState`, with coefficients
obtained by multiplying its first-half coordinates by `sqrt 2`. Matrices commuting with
`tiTranslation` preserve the sector, as do arbitrary translation powers applied to polynomial
states.

## Main statements

* `ti_shift_half_first`, `ti_shift_half_second`, and `ti_shift_half_involutive` describe the
  half-turn permutation.
- `ti_sector_iff` characterizes the half-turn eigenvector condition by coordinates.
- `ti_state_sector` and `ti_sector_representation` relate polynomial states to the sector.
- `ti_commuting_preserves_sector` and `ti_translated_sector` establish sector preservation.

## References

* [Farhi et al., 1999][FarhiEtAl1999], translation symmetry in invariant ordered-search
  algorithms.
* [Childs, Landahl, and Parrilo, 2007][ChildsLandahlParrilo2007], polynomial formulations of
  ordered search.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Matrix
open scoped Classical BigOperators

/-- Proves equality of two functions on `Fin (2*n)` from their equality on both coordinate
halves indexed by `Fin n`. -/
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

/-- Shows that shifting a first-half index `i` by `n` places it at the second-half index `n+i`. -/
theorem ti_shift_half_first (n : ℕ) [NeZero n] (i : Fin n) :
    ((finShiftEquiv (2*n))^n) ⟨i.val,by have := i.isLt; omega⟩ =
      ⟨n+i.val,by have := i.isLt; omega⟩ := by
  apply Fin.val_injective
  rw [ti_shift_pow_val]
  change (i.val+n)%(2*n)=n+i.val
  rw [Nat.mod_eq_of_lt (by have := i.isLt; omega)]
  omega

/-- Shows that shifting a second-half index `n+i` by `n` returns the first-half index `i`. -/
theorem ti_shift_half_second (n : ℕ) [NeZero n] (i : Fin n) :
    ((finShiftEquiv (2*n))^n) ⟨n+i.val,by have := i.isLt; omega⟩ =
      ⟨i.val,by have := i.isLt; omega⟩ := by
  apply Fin.val_injective
  rw [ti_shift_pow_val]
  change (n+i.val+n)%(2*n)=i.val
  rw [show n+i.val+n=i.val+2*n by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by have := i.isLt; omega)]

/-- Proves that the `n`th power of the cyclic shift on `Fin (2*n)` is an involution. -/
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

/-- Computes the first-half coordinate at `i` after half-turn translation as the original
second-half coordinate at `n+i`. -/
theorem ti_half_gate_first (n : ℕ) [NeZero n] (ψ : QState (Fin (2*n))) (i : Fin n) :
    ApplyGate ((tiTranslation n)^n) ψ ⟨i.val,by have := i.isLt; omega⟩ =
      ψ ⟨n+i.val,by have := i.isLt; omega⟩ := by
  rw [ti_translation_pow,applyGate_permMatrix (ti_shift_half_involutive n),ti_shift_half_first]

/-- Computes the second-half coordinate at `n+i` after half-turn translation as the original
first-half coordinate at `i`. -/
theorem ti_half_gate_second (n : ℕ) [NeZero n] (ψ : QState (Fin (2*n))) (i : Fin n) :
    ApplyGate ((tiTranslation n)^n) ψ ⟨n+i.val,by have := i.isLt; omega⟩ =
      ψ ⟨i.val,by have := i.isLt; omega⟩ := by
  rw [ti_translation_pow,applyGate_permMatrix (ti_shift_half_involutive n),ti_shift_half_second]

/-- Shows that the product of two copies of the complex sign `(-1)^t` is one. -/
theorem ti_parity_square (t : ℕ) : (-1:ℂ)^t*(-1:ℂ)^t=1 := by
  rw [← pow_two,← pow_mul,show t*2=2*t by omega,pow_mul]
  norm_num

/-- Characterizes the half-turn eigenvector equation with eigenvalue `(-1)^t` by the coordinate
identity relating the second half to `(-1)^t` times the first half. -/
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

/-- Shows that half-turn translation acts on `tiPolynomialState n t p` by the scalar `(-1)^t`. -/
theorem ti_state_sector (n t : ℕ) [NeZero n] (p : Fin n → ℂ) :
    ApplyGate ((tiTranslation n)^n) (tiPolynomialState n t p)=
      (-1:ℂ)^t • tiPolynomialState n t p := by
  apply (ti_sector_iff n t _).mpr
  intro i
  rw [ti_state_second,ti_state_first]
  ring

/-- Represents every state satisfying the half-turn eigenvector equation with eigenvalue
`(-1)^t` as a polynomial state, using `sqrt 2` times its first-half coordinates as
coefficients. -/
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

/-- Shows that a matrix commuting with cyclic translation maps every state in the `(-1)^t`
half-turn sector into the same sector. -/
theorem ti_commuting_preserves_sector (n t : ℕ) [NeZero n]
    (U : Matrix (Fin (2*n)) (Fin (2*n)) ℂ)
    (hc : tiTranslation n*U=U*tiTranslation n) (ψ : QState (Fin (2*n)))
    (h : ApplyGate ((tiTranslation n)^n) ψ=(-1:ℂ)^t • ψ) :
    ApplyGate ((tiTranslation n)^n) (ApplyGate U ψ)=(-1:ℂ)^t • ApplyGate U ψ := by
  have he := ((show Commute (tiTranslation n) U from hc).pow_left n).eq
  rw [← applyGate_mul,he,applyGate_mul,h]
  simp only [ApplyGate,Matrix.mulVec_smul]

/-- Shows that every natural translation power applied to a time-`t` polynomial state remains in
the half-turn sector with eigenvalue `(-1)^t`. -/
theorem ti_translated_sector (n t r : ℕ) [NeZero n] (p : Fin n → ℂ) :
    ApplyGate ((tiTranslation n)^n) (ApplyGate ((tiTranslation n)^r) (tiPolynomialState n t p)) =
      (-1:ℂ)^t • ApplyGate ((tiTranslation n)^r) (tiPolynomialState n t p) := by
  apply ti_commuting_preserves_sector n t _ ((Commute.refl (tiTranslation n)).pow_right r).eq
  exact ti_state_sector n t p

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
