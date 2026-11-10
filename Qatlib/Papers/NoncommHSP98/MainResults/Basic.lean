/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfacesDefs
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open scoped BigOperators ComplexConjugate
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
set_option warningAsError false

namespace Qatlib.Papers.NoncommHSP98.MainResults

abbrev DihPt (N : ℕ) : Type := ZMod N × ZMod 2

def dihMul (N : ℕ) (x y : DihPt N) : DihPt N :=
  (x.1 + (if x.2 = 0 then y.1 else -y.1), x.2 + y.2)

@[simp] lemma dihMul_zero_left (N : ℕ) (y : DihPt N) : dihMul N (0, 0) y = y := by
  ext <;> simp [dihMul]

@[simp] lemma dihMul_zero_right (N : ℕ) (x : DihPt N) : dihMul N x (0, 0) = x := by
  ext <;> simp [dihMul]

def HTriv (N : ℕ) : Set (DihPt N) := {(0, 0)}

def H2 (N : ℕ) (k0 : ZMod N) : Set (DihPt N) := {(0, 0), (k0, 1)}

lemma mem_HTriv {N : ℕ} {x : DihPt N} : x ∈ HTriv N ↔ x = (0, 0) := by
  simp [HTriv]

lemma mem_H2 {N : ℕ} {k0 : ZMod N} {x : DihPt N} :
    x ∈ H2 N k0 ↔ x = (0, 0) ∨ x = (k0, 1) := by
  simp [H2]

def InLeftCoset (N : ℕ) (H : Set (DihPt N)) (x y : DihPt N) : Prop :=
  ∃ h ∈ H, dihMul N x h = y

def FulfillsDihedralPromise (N : ℕ) (H : Set (DihPt N)) {R : Type*}
    (γ : DihPt N → R) : Prop :=
  (∀ x y, InLeftCoset N H x y → γ x = γ y) ∧
  (∀ x y, γ x = γ y → InLeftCoset N H x y)

namespace FulfillsDihedralPromise

variable {N : ℕ} {R : Type*} {H : Set (DihPt N)} {γ : DihPt N → R}

lemma eq_of_coset (hγ : FulfillsDihedralPromise N H γ) {x y : DihPt N}
    (h : InLeftCoset N H x y) : γ x = γ y := hγ.1 x y h

lemma coset_of_eq (hγ : FulfillsDihedralPromise N H γ) {x y : DihPt N}
    (h : γ x = γ y) : InLeftCoset N H x y := hγ.2 x y h

end FulfillsDihedralPromise

theorem promise_H2_zero_test {N : ℕ} {R : Type*} {k0 : ZMod N}
    {γ : DihPt N → R} (hγ : FulfillsDihedralPromise N (H2 N k0) γ) :
    γ (0, 0) = γ (0, 1) ↔ k0 = 0 := by
  constructor
  · intro heq
    obtain ⟨h, hh, hmul⟩ := FulfillsDihedralPromise.coset_of_eq hγ heq
    rw [mem_H2] at hh
    rcases hh with h | h
    · subst h; simp [dihMul] at hmul
    · subst h; simp [dihMul] at hmul; exact hmul
  · intro hk
    refine FulfillsDihedralPromise.eq_of_coset hγ ⟨(0, 1), ?_, by simp [dihMul]⟩
    rw [mem_H2]
    right
    rw [show (0 : ZMod N) = k0 from hk.symm]

theorem promise_HTriv_zero_test {N : ℕ} {R : Type*} {γ : DihPt N → R}
    (hγ : FulfillsDihedralPromise N (HTriv N) γ) :
    γ (0, 0) ≠ γ (0, 1) := by
  intro heq
  obtain ⟨h, hh, hmul⟩ := FulfillsDihedralPromise.coset_of_eq hγ heq
  rw [mem_HTriv] at hh
  subst hh
  simp [dihMul] at hmul

theorem promise_H2_test_iff {N : ℕ} {R : Type*} {k0 k : ZMod N}
    {γ : DihPt N → R} (hγ : FulfillsDihedralPromise N (H2 N k0) γ) :
    γ (0, 0) = γ (k, 1) ↔ k = k0 := by
  constructor
  · intro heq
    obtain ⟨h, hh, hmul⟩ := FulfillsDihedralPromise.coset_of_eq hγ heq
    rw [mem_H2] at hh
    rcases hh with h | h
    · subst h; simp [dihMul] at hmul
    · subst h; simp [dihMul] at hmul; exact hmul.symm
  · intro hk
    rw [hk]
    exact FulfillsDihedralPromise.eq_of_coset hγ ⟨(k0, 1), by simp [H2], by simp [dihMul]⟩

noncomputable def cphase (N : ℕ) [NeZero N] (k z : ZMod N) : ℂ := ZMod.stdAddChar (k * z)

noncomputable def cosPhase (N : ℕ) [NeZero N] (k z : ZMod N) : ℝ := (cphase N k z).re

noncomputable def sinPhase (N : ℕ) [NeZero N] (k z : ZMod N) : ℝ := (cphase N k z).im

lemma cphase_add {N : ℕ} [NeZero N] (a b z : ZMod N) :
    cphase N (a + b) z = cphase N a z * cphase N b z := by
  unfold cphase
  rw [← AddChar.map_add_eq_mul, add_mul]

lemma cphase_neg {N : ℕ} [NeZero N] (a z : ZMod N) :
    cphase N (-a) z = conj (cphase N a z) := by
  unfold cphase
  rw [neg_mul, AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply]
  exact (Circle.coe_inv _).symm.trans (Circle.coe_inv_eq_conj _)

theorem cosPhase_eq_cos {N : ℕ} [NeZero N] (k z : ZMod N) :
    cosPhase N k z = Real.cos (2 * Real.pi * ((k * z).val : ℝ) / N) := by
  unfold cosPhase cphase
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  have harg : (2 * (Real.pi : ℂ) * Complex.I * ((k * z).val : ℂ) / (N : ℂ))
      = ((2 * Real.pi * ((k * z).val : ℝ) / N : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_ofReal_mul_I_re]

theorem sinPhase_eq_sin {N : ℕ} [NeZero N] (k z : ZMod N) :
    sinPhase N k z = Real.sin (2 * Real.pi * ((k * z).val : ℝ) / N) := by
  unfold sinPhase cphase
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  have harg : (2 * (Real.pi : ℂ) * Complex.I * ((k * z).val : ℂ) / (N : ℂ))
      = ((2 * Real.pi * ((k * z).val : ℝ) / N : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_ofReal_mul_I_im]

theorem cosPhase_mem_Icc {N : ℕ} [NeZero N] (k z : ZMod N) :
    cosPhase N k z ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [cosPhase_eq_cos]
  exact Real.cos_mem_Icc _

theorem sum_cosPhase {N : ℕ} [NeZero N] (k : ZMod N) :
    ∑ z : ZMod N, cosPhase N k z = if k = 0 then (N : ℝ) else 0 := by
  classical
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl]
    have hpt : ∀ z : ZMod N, cosPhase N 0 z = 1 := by
      intro z
      unfold cosPhase cphase
      rw [zero_mul, AddChar.map_zero_eq_one]
      simp
    calc ∑ z : ZMod N, cosPhase N 0 z = ∑ _z : ZMod N, (1 : ℝ) :=
          Finset.sum_congr rfl (fun z _ => hpt z)
      _ = (N : ℝ) := by simp
  · rw [if_neg hk]
    have hne : (ZMod.stdAddChar.mulShift k : AddChar (ZMod N) ℂ) ≠ 0 := by
      intro h
      have h1 : ZMod.stdAddChar k = 1 := by
        have hfun := DFunLike.congr_fun h (1 : ZMod N)
        simpa using! hfun
      exact hk (ZMod.injective_stdAddChar (by rw [h1, AddChar.map_zero_eq_one]))
    have hsum := AddChar.sum_eq_ite (ZMod.stdAddChar.mulShift k)
    rw [if_neg hne] at hsum
    have hsum' : ∑ z : ZMod N, cphase N k z = 0 := by
      simpa [cphase] using! hsum
    have hre : (∑ z : ZMod N, cosPhase N k z) = (∑ z : ZMod N, cphase N k z).re := by
      rw [Complex.re_sum]
      simp [cosPhase]
    rw [hre, hsum']
    simp

theorem cosPhase_add_sub {N : ℕ} [NeZero N] (a b z : ZMod N) :
    cosPhase N (a + b) z + cosPhase N (a - b) z
      = 2 * cosPhase N a z * cosPhase N b z := by
  have h1 : cosPhase N (a + b) z
      = (cphase N a z).re * (cphase N b z).re - (cphase N a z).im * (cphase N b z).im := by
    unfold cosPhase
    rw [cphase_add, Complex.mul_re]
  have h2 : cosPhase N (a - b) z
      = (cphase N a z).re * (cphase N b z).re + (cphase N a z).im * (cphase N b z).im := by
    have h : cphase N (a - b) z = cphase N a z * conj (cphase N b z) := by
      rw [sub_eq_add_neg, cphase_add, cphase_neg]
    unfold cosPhase
    rw [h, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [h1, h2]
  unfold cosPhase
  ring

noncomputable def readoutZero (N : ℕ) [NeZero N] (k0 a : ZMod N) : ℝ :=
  (1 / (2 * (N : ℝ))) * (1 + cosPhase N k0 a)

noncomputable def readoutOne (N : ℕ) [NeZero N] (k0 a : ZMod N) : ℝ :=
  (1 / (2 * (N : ℝ))) * (1 - cosPhase N k0 a)

theorem readoutZero_eq_paper {N : ℕ} [NeZero N] (k0 a : ZMod N) :
    readoutZero N k0 a
      = (1 / (N : ℝ)) * (Real.cos (Real.pi * ((k0 * a).val : ℝ) / N)) ^ 2 := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hcos : Real.cos (2 * Real.pi * ((k0 * a).val : ℝ) / N)
      = 2 * (Real.cos (Real.pi * ((k0 * a).val : ℝ) / N)) ^ 2 - 1 := by
    have h := Real.cos_sq (Real.pi * ((k0 * a).val : ℝ) / N)
    have harg : 2 * (Real.pi * ((k0 * a).val : ℝ) / N)
        = 2 * Real.pi * ((k0 * a).val : ℝ) / N := by ring
    rw [harg] at h
    linarith
  unfold readoutZero
  rw [cosPhase_eq_cos, hcos]
  field_simp
  ring

theorem readoutOne_eq_paper {N : ℕ} [NeZero N] (k0 a : ZMod N) :
    readoutOne N k0 a
      = (1 / (N : ℝ)) * (Real.sin (Real.pi * ((k0 * a).val : ℝ) / N)) ^ 2 := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hcos : Real.cos (2 * Real.pi * ((k0 * a).val : ℝ) / N)
      = 1 - 2 * (Real.sin (Real.pi * ((k0 * a).val : ℝ) / N)) ^ 2 := by
    have h := Real.cos_sq (Real.pi * ((k0 * a).val : ℝ) / N)
    have hsin := Real.sin_sq (Real.pi * ((k0 * a).val : ℝ) / N)
    have harg : 2 * (Real.pi * ((k0 * a).val : ℝ) / N)
        = 2 * Real.pi * ((k0 * a).val : ℝ) / N := by ring
    rw [harg] at h
    linarith
  unfold readoutOne
  rw [cosPhase_eq_cos, hcos]
  field_simp
  ring

theorem readoutZero_add_readoutOne {N : ℕ} [NeZero N] (k0 a : ZMod N) :
    readoutZero N k0 a + readoutOne N k0 a = 1 / (N : ℝ) := by
  unfold readoutZero readoutOne
  rw [← mul_add]
  ring_nf

theorem readoutZero_nonneg {N : ℕ} [NeZero N] (k0 a : ZMod N) :
    0 ≤ readoutZero N k0 a := by
  rw [readoutZero_eq_paper]
  positivity

theorem readoutOne_nonneg {N : ℕ} [NeZero N] (k0 a : ZMod N) :
    0 ≤ readoutOne N k0 a := by
  rw [readoutOne_eq_paper]
  positivity

theorem readout_total {N : ℕ} [NeZero N] (k0 : ZMod N) :
    (∑ a : ZMod N, readoutZero N k0 a) + (∑ a : ZMod N, readoutOne N k0 a) = 1 := by
  classical
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hsplit : ∀ a : ZMod N, readoutZero N k0 a + readoutOne N k0 a = 1 / (N : ℝ) :=
    readoutZero_add_readoutOne k0
  rw [← Finset.sum_add_distrib]
  simp only [hsplit]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  field_simp

def Lemma4Statement : Prop :=
  ∀ (N : ℕ) [NeZero N] (k0 a : ZMod N),
    readoutZero N k0 a = (1 / (2 * (N : ℝ))) * (1 + cosPhase N k0 a) ∧
    readoutZero N k0 a = (1 / (N : ℝ)) * (Real.cos (Real.pi * ((k0 * a).val : ℝ) / N)) ^ 2 ∧
    readoutOne N k0 a = (1 / (N : ℝ)) * (Real.sin (Real.pi * ((k0 * a).val : ℝ) / N)) ^ 2 ∧
    0 ≤ readoutZero N k0 a ∧ 0 ≤ readoutOne N k0 a ∧
    readoutZero N k0 a + readoutOne N k0 a = 1 / (N : ℝ)

theorem lemma4_holds : Lemma4Statement := by
  intro N _ k0 a
  exact ⟨rfl, readoutZero_eq_paper k0 a, readoutOne_eq_paper k0 a,
    readoutZero_nonneg k0 a, readoutOne_nonneg k0 a, readoutZero_add_readoutOne k0 a⟩

noncomputable def zAlpha (N : ℕ) (k0 : ZMod N) : ℝ :=
  if k0 = 0 then (1 : ℝ) / N else 2 / N

noncomputable def zMass (N : ℕ) [NeZero N] (k0 z : ZMod N) : ℝ :=
  zAlpha N k0 * ((1 + cosPhase N k0 z) / 2)

theorem zMass_eq_paper {N : ℕ} [NeZero N] (k0 z : ZMod N) :
    zMass N k0 z = zAlpha N k0 * (Real.cos (Real.pi * ((k0 * z).val : ℝ) / N)) ^ 2 := by
  unfold zMass
  rw [cosPhase_eq_cos]
  congr 1
  have h := Real.cos_sq (Real.pi * ((k0 * z).val : ℝ) / N)
  have harg : 2 * (Real.pi * ((k0 * z).val : ℝ) / N)
      = 2 * Real.pi * ((k0 * z).val : ℝ) / N := by ring
  rw [harg] at h
  linarith

theorem zAlpha_nonneg {N : ℕ} [NeZero N] (k0 : ZMod N) : 0 ≤ zAlpha N k0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  unfold zAlpha
  by_cases hk : k0 = 0
  · rw [if_pos hk]; positivity
  · rw [if_neg hk]; positivity

theorem zMass_nonneg {N : ℕ} [NeZero N] (k0 z : ZMod N) : 0 ≤ zMass N k0 z := by
  have hcos : -1 ≤ cosPhase N k0 z := (cosPhase_mem_Icc (N := N) k0 z).1
  have hfac : 0 ≤ (1 + cosPhase N k0 z) / 2 := by linarith
  unfold zMass
  exact mul_nonneg (zAlpha_nonneg k0) hfac

theorem zMass_sum_one {N : ℕ} [NeZero N] (k0 : ZMod N) :
    ∑ z : ZMod N, zMass N k0 z = 1 := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hinner : ∑ z : ZMod N, ((1 + cosPhase N k0 z) / 2)
      = ((N : ℝ) + (if k0 = 0 then (N : ℝ) else 0)) / 2 := by
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card, sum_cosPhase]
    simp
  have hsum : ∑ z : ZMod N, zMass N k0 z
      = zAlpha N k0 * ((N : ℝ) + (if k0 = 0 then (N : ℝ) else 0)) / 2 := by
    calc (∑ z : ZMod N, zMass N k0 z)
        = ∑ z : ZMod N, zAlpha N k0 * ((1 + cosPhase N k0 z) / 2) := by
          unfold zMass; rfl
      _ = zAlpha N k0 * ∑ z : ZMod N, ((1 + cosPhase N k0 z) / 2) :=
          (Finset.mul_sum _ _ _).symm
      _ = _ := by rw [hinner]; ring
  rw [hsum]
  by_cases hk : k0 = 0
  · rw [if_pos hk]
    have hza : zAlpha N k0 = 1 / (N : ℝ) := by unfold zAlpha; rw [if_pos hk]
    rw [hza]
    field_simp
    norm_num
  · rw [if_neg hk]
    have hza : zAlpha N k0 = 2 / (N : ℝ) := by unfold zAlpha; rw [if_neg hk]
    rw [hza]
    field_simp
    ring

noncomputable def zLaw (N : ℕ) [NeZero N] (k0 : ZMod N) : FinDist (ZMod N) where
  prob := zMass N k0
  nonneg := zMass_nonneg k0
  sum_one := zMass_sum_one k0

theorem expect_cosPhase_eq {N : ℕ} [NeZero N] (k0 k : ZMod N) :
    (∑ z : ZMod N, zMass N k0 z * cosPhase N k z)
      = zAlpha N k0 / 2 * ((if k = 0 then (N : ℝ) else 0)
          + ((if k0 + k = 0 then (N : ℝ) else 0)
            + (if k0 - k = 0 then (N : ℝ) else 0)) / 2) := by
  have hpt : ∀ z : ZMod N, zMass N k0 z * cosPhase N k z
      = zAlpha N k0 / 2 * (cosPhase N k z
          + (cosPhase N (k0 + k) z + cosPhase N (k0 - k) z) / 2) := by
    intro z
    unfold zMass
    rw [cosPhase_add_sub k0 k z]
    ring
  calc (∑ z : ZMod N, zMass N k0 z * cosPhase N k z)
      = ∑ z : ZMod N, zAlpha N k0 / 2 * (cosPhase N k z
          + (cosPhase N (k0 + k) z + cosPhase N (k0 - k) z) / 2) :=
        Finset.sum_congr rfl (fun z _ => hpt z)
    _ = zAlpha N k0 / 2 * ((∑ z : ZMod N, cosPhase N k z)
          + ((∑ z : ZMod N, cosPhase N (k0 + k) z)
            + (∑ z : ZMod N, cosPhase N (k0 - k) z)) / 2) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_add_distrib]
    _ = _ := by
        rw [sum_cosPhase, sum_cosPhase, sum_cosPhase]

theorem expect_cosPhase_ge_half {N : ℕ} [NeZero N] {k0 k : ZMod N}
    (hk0 : k0 ≠ 0) (hk : k = k0 ∨ k = -k0) :
    (1 : ℝ) / 2 ≤ ∑ z : ZMod N, zMass N k0 z * cosPhase N k z := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [expect_cosPhase_eq]
  rcases hk with hk | hk
  · rw [hk]
    by_cases h2 : k0 + k0 = 0
    · rw [if_neg hk0, if_pos h2, sub_self, if_pos rfl, zAlpha, if_neg hk0]
      field_simp
      nlinarith [hN]
    · rw [if_neg hk0, if_neg h2, sub_self, if_pos rfl, zAlpha, if_neg hk0]
      field_simp
      nlinarith [hN]
  · rw [hk]
    have hsum0 : k0 + -k0 = 0 := by ring
    have hsub0 : k0 - -k0 = k0 + k0 := by ring
    by_cases h2 : k0 + k0 = 0
    · rw [if_neg (neg_ne_zero.mpr hk0), if_pos hsum0, hsub0, if_pos h2, zAlpha, if_neg hk0]
      field_simp
      nlinarith [hN]
    · rw [if_neg (neg_ne_zero.mpr hk0), if_pos hsum0, hsub0, if_neg h2, zAlpha, if_neg hk0]
      field_simp
      nlinarith [hN]

theorem expect_cosPhase_eq_zero {N : ℕ} [NeZero N] {k0 k : ZMod N}
    (hk : k ≠ 0) (hkp : k ≠ k0) (hkm : k ≠ -k0) :
    ∑ z : ZMod N, zMass N k0 z * cosPhase N k z = 0 := by
  have h1 : k0 + k = 0 ↔ k = -k0 := by
    rw [add_comm, eq_neg_iff_add_eq_zero]
  have h2 : k0 - k = 0 ↔ k = k0 := by
    rw [sub_eq_zero, eq_comm]
  rw [expect_cosPhase_eq, if_neg hk, if_neg (fun h => hkm (h1.mp h)),
    if_neg (fun h => hkp (h2.mp h))]
  ring

lemma probOf_nonneg {X : Type*} [Fintype X] [DecidableEq X] (p : FinDist X) {L : ℕ}
    (ω : Fin L → X) : 0 ≤ p.probOf ω := by
  unfold FinDist.probOf
  exact Finset.prod_nonneg (fun i _ => p.nonneg (ω i))

lemma probEvent_eq_eventMass_independent {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) {L : ℕ} (E : (Fin L → X) → Prop) [DecidablePred E] :
    p.probEvent E = eventMass (independent (fun _ : Fin L => p)) E := by
  classical
  unfold FinDist.probEvent eventMass independent FinDist.probOf
  rfl

lemma eventMass_mono {X : Type*} [Fintype X] (p : FinDist X) {E F : X → Prop}
    [DecidablePred E] [DecidablePred F] (h : ∀ x, E x → F x) :
    eventMass p E ≤ eventMass p F := by
  classical
  have hsub : Finset.univ.filter E ⊆ Finset.univ.filter F := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact h x hx
  unfold eventMass
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => p.nonneg x)

lemma eventMass_congr {X : Type*} [Fintype X] (p : FinDist X) {E F : X → Prop}
    [DecidablePred E] [DecidablePred F] (h : ∀ x, E x ↔ F x) :
    eventMass p E = eventMass p F := by
  classical
  unfold eventMass
  rw [show Finset.univ.filter E = Finset.univ.filter F from
    Finset.filter_congr (fun x _ => h x)]

theorem lemma7_lower {N : ℕ} [NeZero N] {k0 k : ZMod N} {m : ℕ}
    (hm : 0 < m) (hk0 : k0 ≠ 0) (hk : k = k0 ∨ k = -k0) :
    probEvent (zLaw N k0) (fun ω : Fin m → ZMod N =>
        ∑ i, cosPhase N k (ω i) ≤ (m : ℝ) / 4) ≤ Real.exp (-(m : ℝ) / 32) := by
  classical
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hμ : (1 : ℝ) / 2 ≤ (zLaw N k0).expect (fun z => cosPhase N k z) := by
    show (1 : ℝ) / 2 ≤ ∑ z : ZMod N, zMass N k0 z * cosPhase N k z
    exact expect_cosPhase_ge_half hk0 hk
  have hmean : (independent (fun _ : Fin m => zLaw N k0)).expect
      (weightedSum (fun _ : Fin m => (1 : ℝ))
        (fun (_ : Fin m) (z : ZMod N) => cosPhase N k z))
      = (m : ℝ) * (zLaw N k0).expect (fun z => cosPhase N k z) := by
    rw [Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces.independent_weighted_expectation]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hS : (0 : ℝ) < ∑ _ : Fin m, (1 : ℝ) ^ 2 * ((1 : ℝ) - (-1)) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ]
    simp only [nsmul_eq_mul]
    norm_num
    positivity
  have hH := independent_weighted_hoeffding_signed
    (fun _ : Fin m => zLaw N k0) (fun _ : Fin m => (1 : ℝ))
    (fun (_ : Fin m) (z : ZMod N) => cosPhase N k z)
    (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) ((m : ℝ) / 4) (-1)
    (fun _ => by norm_num) (fun _ _ => cosPhase_mem_Icc (N := N) k _) (by positivity)
    (by norm_num) hS
  have himp : ∀ ω : Fin m → ZMod N,
      (∑ i, cosPhase N k (ω i) ≤ (m : ℝ) / 4) →
      ((m : ℝ) / 4 ≤ (-1 : ℝ) *
        (weightedSum (fun _ : Fin m => (1 : ℝ))
          (fun (_ : Fin m) (z : ZMod N) => cosPhase N k z) ω
         - (independent (fun _ : Fin m => zLaw N k0)).expect
            (weightedSum (fun _ : Fin m => (1 : ℝ))
              (fun (_ : Fin m) (z : ZMod N) => cosPhase N k z)))) := by
    intro ω hω
    have hW : weightedSum (fun _ : Fin m => (1 : ℝ))
        (fun (_ : Fin m) (z : ZMod N) => cosPhase N k z) ω
        = ∑ i, cosPhase N k (ω i) := by simp [weightedSum]
    have hmul : (m : ℝ) * (1 / 2) ≤
        (m : ℝ) * (zLaw N k0).expect (fun z => cosPhase N k z) :=
      mul_le_mul_of_nonneg_left hμ hmpos.le
    rw [hW, hmean]
    linarith
  rw [probEvent_eq_eventMass_independent]
  refine le_trans (le_trans (eventMass_mono _ himp) hH) (le_of_eq ?_)
  congr 1
  rw [show (∑ _ : Fin m, (1 : ℝ) ^ 2 * ((1 : ℝ) - (-1)) ^ 2) = 4 * (m : ℝ) from by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring]
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  field_simp
  ring

theorem lemma7_upper {N : ℕ} [NeZero N] {k0 k : ZMod N} {m : ℕ}
    (hm : 0 < m) (hk : k ≠ 0) (hkp : k ≠ k0) (hkm : k ≠ -k0) :
    probEvent (zLaw N k0) (fun ω : Fin m → ZMod N =>
        (m : ℝ) / 4 ≤ ∑ i, cosPhase N k (ω i)) ≤ Real.exp (-(m : ℝ) / 32) := by
  classical
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hμ : (zLaw N k0).expect (fun z => cosPhase N k z) = 0 := by
    show ∑ z : ZMod N, zMass N k0 z * cosPhase N k z = 0
    exact expect_cosPhase_eq_zero hk hkp hkm
  have hmean : (independent (fun _ : Fin m => zLaw N k0)).expect
      (weightedSum (fun _ : Fin m => (1 : ℝ))
        (fun (_ : Fin m) (z : ZMod N) => cosPhase N k z)) = 0 := by
    rw [Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces.independent_weighted_expectation]
    simp [hμ]
  have hS : (0 : ℝ) < ∑ _ : Fin m, (1 : ℝ) ^ 2 * ((1 : ℝ) - (-1)) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ]
    simp only [nsmul_eq_mul]
    norm_num
    positivity
  have hH := independent_weighted_hoeffding_signed
    (fun _ : Fin m => zLaw N k0) (fun _ : Fin m => (1 : ℝ))
    (fun (_ : Fin m) (z : ZMod N) => cosPhase N k z)
    (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) ((m : ℝ) / 4) 1
    (fun _ => by norm_num) (fun _ _ => cosPhase_mem_Icc (N := N) k _) (by positivity)
    (by norm_num) hS
  have hEv : eventMass (independent (fun _ : Fin m => zLaw N k0))
      (fun ω : Fin m → ZMod N => (m : ℝ) / 4 ≤ ∑ i, cosPhase N k (ω i))
      = eventMass (independent (fun _ : Fin m => zLaw N k0))
        (fun ω : Fin m → ZMod N => (m : ℝ) / 4 ≤ (1 : ℝ) *
          (weightedSum (fun _ : Fin m => (1 : ℝ))
            (fun (_ : Fin m) (z : ZMod N) => cosPhase N k z) ω
           - (independent (fun _ : Fin m => zLaw N k0)).expect
              (weightedSum (fun _ : Fin m => (1 : ℝ))
                (fun (_ : Fin m) (z : ZMod N) => cosPhase N k z)))) := by
    apply eventMass_congr
    intro ω
    have hW : weightedSum (fun _ : Fin m => (1 : ℝ))
        (fun (_ : Fin m) (z : ZMod N) => cosPhase N k z) ω
        = ∑ i, cosPhase N k (ω i) := by simp [weightedSum]
    rw [hW, hmean]
    simp
  rw [probEvent_eq_eventMass_independent, hEv]
  refine le_trans hH (le_of_eq ?_)
  congr 1
  rw [show (∑ _ : Fin m, (1 : ℝ) ^ 2 * ((1 : ℝ) - (-1)) ^ 2) = 4 * (m : ℝ) from by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring]
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  field_simp
  ring

def Lemma7Statement : Prop := by
  classical
  exact ∀ (N : ℕ) [NeZero N] (m : ℕ), 0 < m → ∀ (k0 k : ZMod N),
    (k0 ≠ 0 → (k = k0 ∨ k = -k0) →
      probEvent (zLaw N k0) (fun ω : Fin m → ZMod N =>
        ∑ i, cosPhase N k (ω i) ≤ (m : ℝ) / 4) ≤ Real.exp (-(m : ℝ) / 32)) ∧
    (k ≠ 0 → k ≠ k0 → k ≠ -k0 →
      probEvent (zLaw N k0) (fun ω : Fin m → ZMod N =>
        (m : ℝ) / 4 ≤ ∑ i, cosPhase N k (ω i)) ≤ Real.exp (-(m : ℝ) / 32))

theorem lemma7_holds : Lemma7Statement := by
  intro N _ m hm k0 k
  exact ⟨fun hk0 hk => lemma7_lower hm hk0 hk, fun hk hkp hkm => lemma7_upper hm hk hkp hkm⟩

def Candidates (N : ℕ) [NeZero N] : Finset (ZMod N) :=
  Finset.univ.filter (fun k : ZMod N => 1 ≤ k.val ∧ k.val ≤ N / 2)

def kRep (N : ℕ) (k0 : ZMod N) : ZMod N :=
  if k0.val ≤ N / 2 then k0 else -k0

def Theorem5Statement : Prop := by
  classical
  exact ∀ (N : ℕ) [NeZero N], 2 ≤ N → ∀ (k0 : ZMod N), k0 ≠ 0 → ∀ (m : ℕ),
    64 * Real.log N ≤ m →
    1 - 1 / (2 * (N : ℝ)) ≤ probEvent (zLaw N k0) (fun ω : Fin m → ZMod N =>
      ∀ k ∈ Candidates N, k ≠ kRep N k0 →
        ∑ i, cosPhase N k (ω i) < ∑ i, cosPhase N (kRep N k0) (ω i))

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

noncomputable def ncFourier {d : ℕ} (ρ : G → Matrix (Fin d) (Fin d) ℂ) (f : G → ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  ((Real.sqrt ((d : ℝ) / Fintype.card G) : ℝ) : ℂ) • ∑ g, f g • ρ g

noncomputable def fixedProj {d : ℕ} (ρ : G → Matrix (Fin d) (Fin d) ℂ) (H : Finset G) :
    Matrix (Fin d) (Fin d) ℂ :=
  ((H.card : ℂ))⁻¹ • ∑ h ∈ H, ρ h

structure IsMatRep {d : ℕ} (ρ : G → Matrix (Fin d) (Fin d) ℂ) : Prop where
  map_one : ρ 1 = 1
  map_mul : ∀ g h, ρ (g * h) = ρ g * ρ h

noncomputable def setIndicator (H : Finset G) : G → ℂ := fun g => if g ∈ H then 1 else 0

omit [Group G] in

lemma sum_indicator_smul {d : ℕ} (ρ : G → Matrix (Fin d) (Fin d) ℂ) (H : Finset G) :
    (∑ g, setIndicator H g • ρ g) = ∑ h ∈ H, ρ h := by
  classical
  have hpt : ∀ g : G, setIndicator H g • ρ g
      = if g ∈ H then ρ g else (0 : Matrix (Fin d) (Fin d) ℂ) := by
    intro g
    by_cases hg : g ∈ H <;> simp [setIndicator, hg]
  calc (∑ g, setIndicator H g • ρ g)
      = ∑ g, if g ∈ H then ρ g else (0 : Matrix (Fin d) (Fin d) ℂ) :=
        Finset.sum_congr rfl (fun g _ => hpt g)
    _ = Finset.sum (Finset.univ.filter (fun g => g ∈ H)) ρ := by
        exact (Finset.sum_filter (s := (Finset.univ : Finset G))
          (p := fun g => g ∈ H) (f := ρ)).symm
    _ = ∑ h ∈ H, ρ h := by
        rw [show Finset.univ.filter (fun g => g ∈ H) = H from by ext g; simp]

theorem theorem8_ncFourier_indicator {d : ℕ} (ρ : G → Matrix (Fin d) (Fin d) ℂ)
    (_hρ : IsMatRep ρ) (H : Finset G) :
    ncFourier ρ (setIndicator H)
      = (((H.card : ℝ) * Real.sqrt ((d : ℝ) / Fintype.card G) : ℝ) : ℂ) • fixedProj ρ H := by
  classical
  unfold ncFourier fixedProj
  rw [sum_indicator_smul]
  by_cases hH : H = ∅
  · rw [hH]; simp
  · have hcard : (H.card : ℂ) ≠ 0 := by
      have hcardn : H.card ≠ 0 := by
        rw [Finset.card_ne_zero]
        exact Finset.nonempty_iff_ne_empty.mpr hH
      exact_mod_cast hcardn
    rw [smul_smul]
    have hs : (((Real.sqrt ((d : ℝ) / Fintype.card G) : ℝ)) : ℂ)
        = ((((H.card : ℝ) * Real.sqrt ((d : ℝ) / Fintype.card G) : ℝ)) : ℂ)
            * ((H.card : ℂ))⁻¹ := by
      push_cast
      rw [mul_right_comm, mul_inv_cancel₀ hcard, one_mul]
    rw [hs]

def cosetFinset (s : G) (H : Finset G) : Finset G := H.image (fun h => s * h)

omit [Fintype G] in

lemma mem_cosetFinset {s : G} {H : Finset G} {g : G} :
    g ∈ cosetFinset s H ↔ ∃ h ∈ H, s * h = g := by
  unfold cosetFinset
  rw [Finset.mem_image]

lemma sum_coset_smul {d : ℕ} (ρ : G → Matrix (Fin d) (Fin d) ℂ) (hρ : IsMatRep ρ)
    (s : G) (H : Finset G) :
    (∑ g, setIndicator (cosetFinset s H) g • ρ g) = ρ s * ∑ h ∈ H, ρ h := by
  classical
  have hstep : (∑ g, setIndicator (cosetFinset s H) g • ρ g)
      = Finset.sum (Finset.univ.filter (fun g => g ∈ cosetFinset s H)) ρ := by
    have hpt : ∀ g : G, setIndicator (cosetFinset s H) g • ρ g
        = if g ∈ cosetFinset s H then ρ g else (0 : Matrix (Fin d) (Fin d) ℂ) := by
      intro g
      by_cases hg : g ∈ cosetFinset s H <;> simp [setIndicator, hg]
    calc (∑ g, setIndicator (cosetFinset s H) g • ρ g)
        = ∑ g, if g ∈ cosetFinset s H then ρ g else (0 : Matrix (Fin d) (Fin d) ℂ) :=
          Finset.sum_congr rfl (fun g _ => hpt g)
      _ = _ := by
          exact (Finset.sum_filter (s := (Finset.univ : Finset G))
            (p := fun g => g ∈ cosetFinset s H) (f := ρ)).symm
  rw [hstep, show Finset.univ.filter (fun g => g ∈ cosetFinset s H) = cosetFinset s H from by
    ext g; simp]
  rw [cosetFinset, Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [hρ.map_mul]
  · intro x _ y _ hxy
    exact mul_left_cancel hxy

theorem corollary9_coset_indicator {d : ℕ} (ρ : G → Matrix (Fin d) (Fin d) ℂ)
    (hρ : IsMatRep ρ) (s : G) (H : Finset G) :
    ncFourier ρ (setIndicator (cosetFinset s H))
      = (((H.card : ℝ) * Real.sqrt ((d : ℝ) / Fintype.card G) : ℝ) : ℂ) •
          (ρ s * fixedProj ρ H) := by
  classical
  unfold ncFourier fixedProj
  rw [sum_coset_smul ρ hρ s H]
  by_cases hH : H = ∅
  · rw [hH]; simp
  · have hcard : (H.card : ℂ) ≠ 0 := by
      have hcardn : H.card ≠ 0 := by
        rw [Finset.card_ne_zero]
        exact Finset.nonempty_iff_ne_empty.mpr hH
      exact_mod_cast hcardn
    rw [Matrix.mul_smul, smul_smul]
    have hs : (((Real.sqrt ((d : ℝ) / Fintype.card G) : ℝ)) : ℂ)
        = ((((H.card : ℝ) * Real.sqrt ((d : ℝ) / Fintype.card G) : ℝ)) : ℂ)
            * ((H.card : ℂ))⁻¹ := by
      push_cast
      rw [mul_right_comm, mul_inv_cancel₀ hcard, one_mul]
    rw [hs]

def Theorem8Statement : Prop :=
  ∀ (G : Type*) [Group G] [Fintype G] [DecidableEq G] (d : ℕ)
    (ρ : G → Matrix (Fin d) (Fin d) ℂ), IsMatRep ρ →
    ∀ H : Finset G,
      ncFourier ρ (setIndicator H)
        = (((H.card : ℝ) * Real.sqrt ((d : ℝ) / Fintype.card G) : ℝ) : ℂ) •
            fixedProj ρ H

def Corollary9Statement : Prop :=
  ∀ (G : Type*) [Group G] [Fintype G] [DecidableEq G] (d : ℕ)
    (ρ : G → Matrix (Fin d) (Fin d) ℂ), IsMatRep ρ →
    ∀ (s : G) (H : Finset G),
      ncFourier ρ (setIndicator (cosetFinset s H))
        = (((H.card : ℝ) * Real.sqrt ((d : ℝ) / Fintype.card G) : ℝ) : ℂ) •
            (ρ s * fixedProj ρ H)

theorem theorem8_holds : Theorem8Statement := by
  intro G _ _ _ d ρ hρ H
  exact theorem8_ncFourier_indicator ρ hρ H

theorem corollary9_holds : Corollary9Statement := by
  intro G _ _ _ d ρ hρ s H
  exact corollary9_coset_indicator ρ hρ s H

noncomputable def probSingle {X : Type*} [Fintype X] [DecidableEq X] (p : FinDist X)
    (E : X → Prop) [DecidablePred E] : ℝ :=
  Finset.sum (Finset.univ.filter E) p.prob

structure DihAlgorithm (N : ℕ) [NeZero N] (R : Type*) where

  queries : (DihPt N → R) → ℕ

  dist : (DihPt N → R) → FinDist (Option (ZMod N))

def Theorem3Statement : Prop := by
  classical
  exact ∀ (N : ℕ) [NeZero N] (R : Type*), 2 ≤ N →
    ∃ A : DihAlgorithm N R,
      (∀ γ : DihPt N → R, (A.queries γ : ℝ) ≤ 89 * Real.log N / Real.log 2 + 7) ∧
      (∀ γ : DihPt N → R, FulfillsDihedralPromise N (HTriv N) γ →
        probSingle (A.dist γ) (fun o => o = none) = 1) ∧
      (∀ (k0 : ZMod N), k0 ≠ 0 → ∀ γ : DihPt N → R,
        FulfillsDihedralPromise N (H2 N k0) γ →
        1 - 1 / (2 * (N : ℝ)) ≤ probSingle (A.dist γ) (fun o => o = some k0))

structure DihGenAlgorithm (N : ℕ) [NeZero N] (R : Type*) where
  queries : (DihedralGroup N → R) → ℕ
  dist : (DihedralGroup N → R) → FinDist (Finset (DihedralGroup N))

def FulfillsPromise {G : Type*} [Group G] (H : Subgroup G) {R : Type*}
    (γ : G → R) : Prop :=
  (∀ x y, (∃ h ∈ H, x * h = y) → γ x = γ y) ∧
  (∀ x y, γ x = γ y → ∃ h ∈ H, x * h = y)

def Theorem2Statement : Prop := by
  classical
  exact ∀ (N : ℕ) [NeZero N] (R : Type*), 2 ≤ N →
    ∃ A : DihGenAlgorithm N R,
      (∃ c1 c2 : ℝ, 0 < c1 ∧ 0 < c2 ∧
        ∀ γ : DihedralGroup N → R,
          c1 * Real.log N ≤ (A.queries γ : ℝ) ∧
          (A.queries γ : ℝ) ≤ c2 * Real.log N) ∧
      (∀ (H : Subgroup (DihedralGroup N)) (γ : DihedralGroup N → R),
        FulfillsPromise H γ →
        1 - 2 / (N : ℝ) ≤
          probSingle (A.dist γ) (fun X =>
            Subgroup.closure (↑X : Set (DihedralGroup N)) = H))

end Qatlib.Papers.NoncommHSP98.MainResults
