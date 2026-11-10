/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoncommHSP98.MainResults.Basic
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators ComplexConjugate
set_option warningAsError false

namespace Qatlib.Papers.NoncommHSP98.MainResults

def bitSign (d : ZMod 2) : ℝ := (-1 : ℝ) ^ d.val

def bitSignC (d : ZMod 2) : ℂ := (bitSign d : ℂ)

@[simp] lemma bitSign_zero : bitSign 0 = 1 := by
  simp [bitSign]

@[simp] lemma bitSign_one : bitSign (1 : ZMod 2) = -1 := by
  have h : ((1 : ZMod 2)).val = 1 := by
    exact (ZMod.val_eq_one (by norm_num) (1 : ZMod 2)).mpr rfl
  simp [bitSign, h]

lemma bitSign_sq (d : ZMod 2) : bitSign d * bitSign d = 1 := by
  unfold bitSign
  rw [← pow_add, show d.val + d.val = 2 * d.val by omega, pow_mul]
  norm_num

lemma normSq_bitSignC (d : ZMod 2) : Complex.normSq (bitSignC d) = 1 := by
  unfold bitSignC
  rw [Complex.normSq_ofReal, bitSign_sq]

lemma normSq_cphase {N : ℕ} [NeZero N] (k z : ZMod N) :
    Complex.normSq (cphase N k z) = 1 := by
  unfold cphase
  rw [ZMod.stdAddChar_apply]
  exact Circle.normSq_coe _

lemma normSq_one_add_sign (z : ℂ) (hz : Complex.normSq z = 1) (s : ℝ)
    (hs : s * s = 1) :
    Complex.normSq (1 + (s : ℂ) * z) = 2 + 2 * s * z.re := by
  rw [Complex.normSq_add]
  have hm : Complex.normSq ((s : ℂ) * z) = s * s := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal, hz, mul_one]
  have hr : (1 * (starRingEnd ℂ) ((s : ℂ) * z)).re = s * z.re := by
    rw [one_mul, map_mul, Complex.conj_ofReal, Complex.mul_re]
    simp
  rw [Complex.normSq_one, hm, hr, hs]
  ring

def cosetAmp (N : ℕ) [NeZero N] (k0 a c : ZMod N) (d : ZMod 2) : ℂ :=
  cphase N c a * (1 + bitSignC d * cphase N k0 c)

def cosetReadout (N : ℕ) [NeZero N] (k0 a c : ZMod N) (d : ZMod 2) : ℝ :=
  (1 / (4 * (N : ℝ))) * Complex.normSq (cosetAmp N k0 a c d)

def bornReadout (N : ℕ) [NeZero N] (k0 c : ZMod N) (d : ZMod 2) : ℝ :=
  (1 / (N : ℝ)) * ∑ a : ZMod N, cosetReadout N k0 a c d

lemma normSq_cosetAmp {N : ℕ} [NeZero N] (k0 a c : ZMod N) (d : ZMod 2) :
    Complex.normSq (cosetAmp N k0 a c d) = 2 + 2 * bitSign d * cosPhase N k0 c := by
  unfold cosetAmp bitSignC
  rw [Complex.normSq_mul, normSq_cphase, one_mul]
  have h := normSq_one_add_sign (cphase N k0 c) (normSq_cphase k0 c)
    (bitSign d) (bitSign_sq d)
  rw [h]
  rfl

lemma cosetReadout_eq {N : ℕ} [NeZero N] (k0 a c : ZMod N) (d : ZMod 2) :
    cosetReadout N k0 a c d
      = (1 / (4 * (N : ℝ))) * (2 + 2 * bitSign d * cosPhase N k0 c) := by
  unfold cosetReadout
  rw [normSq_cosetAmp]

lemma sum_cosetReadout {N : ℕ} [NeZero N] (k0 c : ZMod N) (d : ZMod 2) :
    ∑ a : ZMod N, cosetReadout N k0 a c d
      = (N : ℝ) * ((1 / (4 * (N : ℝ))) *
          (2 + 2 * bitSign d * cosPhase N k0 c)) := by
  rw [Finset.sum_congr rfl (fun a _ => cosetReadout_eq k0 a c d)]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

theorem bornReadout_eq {N : ℕ} [NeZero N] (k0 c : ZMod N) (d : ZMod 2) :
    bornReadout N k0 c d
      = (1 / (2 * (N : ℝ))) * (1 + bitSign d * cosPhase N k0 c) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  unfold bornReadout
  rw [sum_cosetReadout]
  field_simp
  ring

theorem bornReadout_zero {N : ℕ} [NeZero N] (k0 a : ZMod N) :
    bornReadout N k0 a 0 = readoutZero N k0 a := by
  rw [bornReadout_eq, bitSign_zero, one_mul]
  rfl

theorem bornReadout_one {N : ℕ} [NeZero N] (k0 a : ZMod N) :
    bornReadout N k0 a 1 = readoutOne N k0 a := by
  rw [bornReadout_eq, bitSign_one]
  unfold readoutOne
  ring

@[simp] lemma zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

@[simp] lemma zmod2_two_eq_zero : (2 : ZMod 2) = 0 := by decide

lemma zmod2_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  have h := b.val_lt
  have h2 : b.val = 0 ∨ b.val = 1 := by omega
  rcases h2 with h | h
  · left; exact (ZMod.val_eq_zero b).mp h
  · right; exact (ZMod.val_eq_one (by norm_num) b).mp h

theorem fiber_H2 {N : ℕ} [NeZero N] {R : Type*} {k0 a : ZMod N}
    {γ : DihPt N → R} (hγ : FulfillsDihedralPromise N (H2 N k0) γ) :
    {y : DihPt N | γ y = γ (a, 0)} = {(a, 0), (a + k0, 1)} := by
  ext y
  obtain ⟨u, b⟩ := y
  constructor
  · intro hy
    obtain ⟨h, hh, hmul⟩ := FulfillsDihedralPromise.coset_of_eq hγ hy
    rw [mem_H2] at hh
    rcases hh with h0 | h1
    · subst h0
      simp only [dihMul, Prod.mk.injEq] at hmul
      obtain ⟨h1, h2⟩ := hmul
      have hb : b = 0 := by simpa using! h2
      have hu : u = a := by simpa [hb] using! h1
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      left
      rw [Prod.mk.injEq]
      exact ⟨hu, hb⟩
    · subst h1
      simp only [dihMul, Prod.mk.injEq] at hmul
      obtain ⟨h1, h2⟩ := hmul
      have hb' : b = 1 := by
        have h := congrArg (fun t : ZMod 2 => t + 1) h2
        simpa [add_assoc] using! h
      have hsum : u + (-k0) = a := by simpa [hb'] using! h1
      have hu : u = a + k0 := by
        have := congrArg (fun t : ZMod N => t + k0) hsum
        simpa [add_assoc] using! this
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      right
      rw [Prod.mk.injEq]
      exact ⟨hu, hb'⟩
  · intro hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy
    · rw [hy]
      rfl
    · rw [hy]
      exact FulfillsDihedralPromise.eq_of_coset hγ
        ⟨(k0, 1), by simp [H2], by simp [dihMul, add_assoc]⟩

end Qatlib.Papers.NoncommHSP98.MainResults
