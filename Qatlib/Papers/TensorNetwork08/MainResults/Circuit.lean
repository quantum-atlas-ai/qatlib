/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.TableAccess.ReversibleTable

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TensorNetwork08.MainResults.Circuit

open Matrix
open scoped BigOperators
open Qatlib.Foundations.TableAccess.ReversibleTable

abbrev Reg (n : ℕ) := Fin n → Bool

def zeroReg (n : ℕ) : Reg n := fun _ => false

def lift {n : ℕ} (Q : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (Reg n × Bool) (Reg n × Bool) ℂ :=
  Matrix.of fun p q => if p.2 = q.2 then Q p.1 q.1 else 0

def cnotFun {n : ℕ} (a : Fin n) : Reg n × Bool → Reg n × Bool :=
  fun p => (p.1, if p.1 a then !p.2 else p.2)

theorem cnotFun_involutive {n : ℕ} (a : Fin n) : Function.Involutive (cnotFun a) := by
  intro p
  obtain ⟨s, b⟩ := p
  simp only [cnotFun]
  cases h : s a <;> cases b <;> simp

theorem lift_mulVec_ket {n : ℕ} (Q : Matrix (Reg n) (Reg n) ℂ) (z : Reg n × Bool)
    (i : Reg n × Bool) :
    (lift Q *ᵥ Ket z) i = lift Q i z := by
  simp only [lift, Matrix.mulVec, dotProduct, Matrix.of_apply, Ket]
  rw [Finset.sum_eq_single z]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem conjTranspose_mulVec_apply {I : Type*} [Fintype I] (M : Matrix I I ℂ) (v : I → ℂ)
    (i : I) :
    (Mᴴ *ᵥ v) i = ∑ j, (starRingEnd ℂ) (M j i) * v j := by
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, RCLike.star_def]

theorem conj_mul_eq_norm_sq (z : ℂ) :
    (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  simpa [RCLike.star_def] using RCLike.conj_mul z

theorem fig6_amplitude {n : ℕ} (Q : Matrix (Reg n) (Reg n) ℂ) (a : Fin n) :
    (((lift Q)ᴴ * permMatrix (cnotFun a) * lift Q) *ᵥ Ket (zeroReg n, false))
        (zeroReg n, false)
      = ∑ s : Reg n, if s a = false then ((‖Q s (zeroReg n)‖ ^ 2 : ℝ) : ℂ) else 0 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [conjTranspose_mulVec_apply]
  have hinner : ∀ i : Reg n × Bool,
      (permMatrix (cnotFun a) *ᵥ (lift Q *ᵥ Ket (zeroReg n, false))) i
        = lift Q (cnotFun a i) (zeroReg n, false) := by
    intro i
    rw [applyGate_permMatrix (cnotFun_involutive a), lift_mulVec_ket]
  calc (∑ i : Reg n × Bool,
        (starRingEnd ℂ) (lift Q i (zeroReg n, false))
          * (permMatrix (cnotFun a) *ᵥ (lift Q *ᵥ Ket (zeroReg n, false))) i)
      = ∑ i : Reg n × Bool,
          (starRingEnd ℂ) (lift Q i (zeroReg n, false))
            * lift Q (cnotFun a i) (zeroReg n, false) :=
        Finset.sum_congr rfl fun i _ => by rw [hinner i]
    _ = ∑ s : Reg n, ∑ b : Bool,
          (starRingEnd ℂ) (lift Q (s, b) (zeroReg n, false))
            * lift Q (cnotFun a (s, b)) (zeroReg n, false) := by
        rw [Fintype.sum_prod_type]
    _ = ∑ s : Reg n, if s a = false then ((‖Q s (zeroReg n)‖ ^ 2 : ℝ) : ℂ) else 0 := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Fintype.sum_bool]
        have htrue : (starRingEnd ℂ) (lift Q (s, true) (zeroReg n, false))
            * lift Q (cnotFun a (s, true)) (zeroReg n, false) = 0 := by
          simp [lift]
        have hfalse : (starRingEnd ℂ) (lift Q (s, false) (zeroReg n, false))
            * lift Q (cnotFun a (s, false)) (zeroReg n, false)
            = if s a = false then ((‖Q s (zeroReg n)‖ ^ 2 : ℝ) : ℂ) else 0 := by
          by_cases hs : s a
          · simp [lift, cnotFun, hs]
          · simp only [hs, cnotFun, Bool.false_eq_true, if_false]
            simp [lift, conj_mul_eq_norm_sq]
        rw [htrue, hfalse]
        simp

def p0 {n : ℕ} (Q : Matrix (Reg n) (Reg n) ℂ) (a : Fin n) : ℝ :=
  ∑ s : Reg n, if s a = false then ‖Q s (zeroReg n)‖ ^ 2 else 0

theorem fig6_amplitude_eq_p0 {n : ℕ} (Q : Matrix (Reg n) (Reg n) ℂ) (a : Fin n) :
    (((lift Q)ᴴ * permMatrix (cnotFun a) * lift Q) *ᵥ Ket (zeroReg n, false))
        (zeroReg n, false)
      = ((p0 Q a : ℝ) : ℂ) := by
  rw [fig6_amplitude]
  rw [show ((p0 Q a : ℝ) : ℂ)
      = ∑ s : Reg n, if s a = false then ((‖Q s (zeroReg n)‖ ^ 2 : ℝ) : ℂ) else 0 from by
    simp only [p0]
    push_cast
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : s a = false <;> simp [hs]]

theorem p0_nonneg {n : ℕ} (Q : Matrix (Reg n) (Reg n) ℂ) (a : Fin n) : 0 ≤ p0 Q a := by
  simp only [p0]
  exact Finset.sum_nonneg (fun s _ => by
    split
    · positivity
    · exact le_refl 0)

theorem p0_le_one {n : ℕ} {Q : Matrix (Reg n) (Reg n) ℂ} (a : Fin n)
    (hQ : ∑ s : Reg n, ‖Q s (zeroReg n)‖ ^ 2 = 1) : p0 Q a ≤ 1 := by
  simp only [p0]
  calc (∑ s : Reg n, if s a = false then ‖Q s (zeroReg n)‖ ^ 2 else 0)
      ≤ ∑ s : Reg n, ‖Q s (zeroReg n)‖ ^ 2 := by
        refine Finset.sum_le_sum fun s _ => ?_
        split
        · exact le_refl _
        · positivity
    _ = 1 := hQ

theorem p0_add_compl {n : ℕ} {Q : Matrix (Reg n) (Reg n) ℂ} (a : Fin n)
    (hQ : ∑ s : Reg n, ‖Q s (zeroReg n)‖ ^ 2 = 1) :
    p0 Q a + (∑ s : Reg n, if s a = true then ‖Q s (zeroReg n)‖ ^ 2 else 0) = 1 := by
  simp only [p0]
  rw [← Finset.sum_add_distrib, ← hQ]
  refine Finset.sum_congr rfl fun s _ => ?_
  cases hs : s a <;> simp

end Qatlib.Papers.TensorNetwork08.MainResults.Circuit
