/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.TwoParticleAntisym
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.Perm
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ManyBodyFermi97.MainResults.SignedOrbit
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators

def permuted {n m : ℕ} (a : Fin n → Fin m) (σ : Equiv.Perm (Fin n)) : Fin n → Fin m :=
  a ∘ σ

theorem permuted_injective {n m : ℕ} (a : Fin n → Fin m) (ha : Function.Injective a) :
    Function.Injective (permuted a) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  apply ha
  exact congrFun h i

def parity {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℂ := (Equiv.Perm.sign σ : ℤ)

theorem parity_normSq {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Complex.normSq (parity σ) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [parity, h]

def raw {n m : ℕ} (a : Fin n → Fin m) : QState (Fin n → Fin m) :=
  ∑ σ : Equiv.Perm (Fin n), parity σ • Ket (permuted a σ)

theorem raw_at_permuted {n m : ℕ} (a : Fin n → Fin m)
    (ha : Function.Injective a) (σ : Equiv.Perm (Fin n)) :
    raw a (permuted a σ) = parity σ := by
  classical
  simp only [raw, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Ket]
  rw [Finset.sum_eq_single σ]
  · simp
  · intro τ _ hτ
    have hne : permuted a σ ≠ permuted a τ := fun h => hτ ((permuted_injective a ha h).symm)
    simp [hne]
  · simp

theorem raw_off_orbit {n m : ℕ} (a : Fin n → Fin m) (x : Fin n → Fin m)
    (hx : x ∉ Set.range (permuted a)) : raw a x = 0 := by
  classical
  simp only [raw, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Ket]
  apply Finset.sum_eq_zero
  intro σ _
  have hne : x ≠ permuted a σ := fun h => hx ⟨σ,h.symm⟩
  simp [hne]

theorem raw_normSq {n m : ℕ} (a : Fin n → Fin m) (ha : Function.Injective a) :
    ∑ x, Complex.normSq (raw a x) = (n.factorial : ℝ) := by
  classical
  rw [← Fintype.sum_of_injective (permuted a) (permuted_injective a ha)
    (fun σ => Complex.normSq (raw a (permuted a σ)))
    (fun x => Complex.normSq (raw a x))]
  · simp [raw_at_permuted a ha, parity_normSq, Fintype.card_perm]
  · intro x hx
    rw [raw_off_orbit a x hx]
    simp
  · intro σ
    rfl

def printed {n m : ℕ} (a : Fin n → Fin m) : QState (Fin n → Fin m) :=
  (((n.factorial : ℝ) : ℂ)⁻¹) • raw a

theorem printed_normSq {n m : ℕ} (a : Fin n → Fin m) (ha : Function.Injective a) :
    ∑ x, Complex.normSq (printed a x) = (n.factorial : ℝ)⁻¹ := by
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp only [printed,Pi.smul_apply,smul_eq_mul,Complex.normSq_mul,
    ← Finset.mul_sum,raw_normSq a ha,Complex.normSq_inv,Complex.normSq_ofReal]
  field_simp

def corrected {n m : ℕ} (a : Fin n → Fin m) : QState (Fin n → Fin m) :=
  ((Real.sqrt (n.factorial : ℝ) : ℂ)⁻¹) • raw a

theorem corrected_normalized {n m : ℕ} (a : Fin n → Fin m)
    (ha : Function.Injective a) : Normalized (corrected a) := by
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  change (∑ x, ‖corrected a x‖^2) = 1
  simp only [← Complex.normSq_eq_norm_sq]
  simp only [corrected, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
    ← Finset.mul_sum, raw_normSq a ha, Complex.normSq_inv, Complex.normSq_ofReal,
    ← pow_two, Real.sq_sqrt (le_of_lt hn)]
  exact inv_mul_cancel₀ (ne_of_gt hn)

theorem parity_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    parity (σ*τ)=parity σ * parity τ := by
  simp [parity,Equiv.Perm.sign_mul]

theorem raw_antisymmetric {n m : ℕ} (a x : Fin n → Fin m)
    (τ : Equiv.Perm (Fin n)) :
    raw a (permuted x τ)=parity τ * raw a x := by
  classical
  simp only [raw,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  calc
    (∑ σ,parity σ * Ket (permuted a σ) (permuted x τ)) =
        ∑ ρ,parity (ρ*τ) * Ket (permuted a (ρ*τ)) (permuted x τ) := by
      exact (Fintype.sum_equiv (Equiv.mulRight τ) _ _ (fun _ => rfl)).symm
    _ = parity τ * ∑ ρ,parity ρ * Ket (permuted a ρ) x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ _
      have he : permuted x τ = permuted a (ρ*τ) ↔ x=permuted a ρ := by
        constructor
        · intro h
          funext i
          simpa [permuted] using congrFun h (τ.symm i)
        · intro h
          subst x
          rfl
      simp only [parity_mul,Ket,he]
      ring

theorem corrected_antisymmetric {n m : ℕ} (a x : Fin n → Fin m)
    (τ : Equiv.Perm (Fin n)) :
    corrected a (permuted x τ)=parity τ * corrected a x := by
  simp only [corrected,Pi.smul_apply,smul_eq_mul,raw_antisymmetric]
  ring

end Qatlib.Papers.ManyBodyFermi97.MainResults.SignedOrbit
