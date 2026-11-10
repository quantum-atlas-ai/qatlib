/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Instantaneous08.MainResults.XProgram
import Qatlib.Papers.Instantaneous08.MainResults.ClassicalApprox.YDistribution
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ZMod.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.Instantaneous08.MainResults.ConstantAction

open Qatlib.Papers.Instantaneous08.MainResults.XProgram

attribute [local instance] Classical.propDecidable

def dot {ι : Type} [Fintype ι] (x y : ι → ZMod 2) : ZMod 2 := x ⬝ᵥ y

def sgn2 (z : ZMod 2) : ℂ := if z = 0 then 1 else -1

@[simp] theorem sgn2_zero : sgn2 0 = 1 := by simp [sgn2]

@[simp] theorem sgn2_one : sgn2 (1 : ZMod 2) = -1 := by
  have h : (1 : ZMod 2) ≠ 0 := by norm_num
  simp [sgn2, h]

theorem sgn2_add (a b : ZMod 2) : sgn2 (a + b) = sgn2 a * sgn2 b := by
  rcases ClassicalApprox.zmod2_eq_zero_or_one a with rfl | rfl <;>
    rcases ClassicalApprox.zmod2_eq_zero_or_one b with rfl | rfl
  · norm_num [sgn2]
  · norm_num [sgn2]
  · norm_num [sgn2]
  · have h2 : (1 : ZMod 2) + 1 = 0 := by decide
    simp only [h2, sgn2, if_true]
    norm_num

def sgn2Hom : Multiplicative (ZMod 2) →* ℂ where
  toFun z := sgn2 z.toAdd
  map_one' := by simp [sgn2]
  map_mul' a b := by
    change sgn2 (Multiplicative.toAdd (a * b)) =
      sgn2 (Multiplicative.toAdd a) * sgn2 (Multiplicative.toAdd b)
    rw [show Multiplicative.toAdd (a * b) =
      Multiplicative.toAdd a + Multiplicative.toAdd b from rfl]
    exact sgn2_add _ _

theorem sgn2_sum {ι : Type} [Fintype ι] (f : ι → ZMod 2) :
    sgn2 (∑ i, f i) = ∏ i, sgn2 (f i) := by
  classical
  have h : ∀ s : Finset ι, sgn2 (∑ i ∈ s, f i) = ∏ i ∈ s, sgn2 (f i) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha, sgn2_add, ih]
  simpa using h Finset.univ

def chi {n : ℕ} (u x : F2Vec n) : ℂ := sgn2 (dot u x)

theorem dot_add {ι : Type} [Fintype ι] (u v x : ι → ZMod 2) :
    (u + v) ⬝ᵥ x = u ⬝ᵥ x + v ⬝ᵥ x := by
  rw [dotProduct, dotProduct, dotProduct, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.add_apply]
  ring

theorem dot_comm {ι : Type} [Fintype ι] (u x : ι → ZMod 2) :
    u ⬝ᵥ x = x ⬝ᵥ u := dotProduct_comm u x

theorem chi_add_left {n : ℕ} (u v x : F2Vec n) :
    chi (u + v) x = chi u x * chi v x := by
  simp only [chi, dot]
  rw [dot_add, sgn2_add]

theorem chi_comm {n : ℕ} (u x : F2Vec n) : chi u x = chi x u := by
  simp only [chi, dot, dot_comm]

@[simp] theorem chi_zero_left {n : ℕ} (x : F2Vec n) : chi 0 x = 1 := by
  simp [chi, dot]

@[simp] theorem chi_zero_right {n : ℕ} (u : F2Vec n) : chi u 0 = 1 := by
  simp [chi, dot]

theorem chi_eq_prod {n : ℕ} (u x : F2Vec n) :
    chi u x = ∏ j, sgn2 (u j * x j) := by
  simp only [chi, dot]
  rw [dotProduct, sgn2_sum]

theorem charSum {n : ℕ} (u : F2Vec n) :
    (∑ x : F2Vec n, chi u x) = if u = 0 then (2 : ℂ) ^ n else 0 := by
  classical
  simp_rw [chi_eq_prod]
  have hprod : (∏ j : Fin n, (∑ b : ZMod 2, sgn2 (u j * b))) =
      ∑ x : F2Vec n, ∏ j, sgn2 (u j * x j) := by
    rw [Finset.prod_univ_sum]
    simp [Fintype.piFinset_univ]
  rw [← hprod]
  have hfactor : ∀ j : Fin n,
      (∑ b : ZMod 2, sgn2 (u j * b)) = if u j = 0 then (2 : ℂ) else 0 := by
    intro j
    by_cases hj : u j = 0
    · simp [hj, sgn2]
    · have h1 : u j = 1 := by
        rcases ClassicalApprox.zmod2_eq_zero_or_one (u j) with h | h
        · exact absurd h hj
        · exact h
      rw [if_neg hj, h1]
      have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by
        apply Finset.ext
        intro b
        simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun _ => ClassicalApprox.zmod2_eq_zero_or_one b, fun _ => trivial⟩
      rw [huniv, Finset.sum_insert (by norm_num), Finset.sum_singleton]
      norm_num [sgn2]
  simp_rw [hfactor]
  by_cases hu : u = 0
  · subst hu
    simp [Finset.prod_const, Fintype.card_fin]
  · rw [if_neg hu]
    obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
      by_contra h
      exact hu (funext fun j => by
        by_contra hj
        exact h ⟨j, hj⟩)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

theorem chi_eq_sgn2 {n : ℕ} (p a : F2Vec n) :
    chi p a = if dot p a = 0 then (1 : ℂ) else -1 := by
  simp [chi, sgn2]

def zCoeff (θ : ℝ) (b : Bool) : ℂ :=
  Complex.exp (Complex.I * (θ : ℂ) * (if b then 1 else -1))

@[simp] theorem zCoeff_true (θ : ℝ) : zCoeff θ true = Complex.exp (Complex.I * (θ : ℂ)) := by
  simp [zCoeff]

@[simp] theorem zCoeff_false (θ : ℝ) :
    zCoeff θ false = Complex.exp (-(Complex.I * (θ : ℂ))) := by
  simp [zCoeff]

theorem cos_add_sin_mul_sign (θ : ℝ) (b : Bool) :
    (Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ) * (if b then 1 else -1) =
      zCoeff θ b := by
  cases b with
  | false =>
      rw [zCoeff_false]
      have harg : -(Complex.I * (θ : ℂ)) = (-(θ : ℂ)) * Complex.I := by ring
      rw [harg, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin,
        Complex.cos_neg, Complex.sin_neg]
      norm_num
      ring
  | true =>
      rw [zCoeff_true]
      have harg : Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I := by ring
      rw [harg, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
      norm_num
      ring

def zAmp {n : ℕ} (k : ℕ) (p : Fin k → F2Vec n) (θ : Fin k → ℝ) (x : F2Vec n) : ℂ :=
  ((Fintype.card (F2Vec n) : ℂ))⁻¹ *
    ∑ a : F2Vec n, chi x a * ∏ i, zCoeff (θ i) (dot (p i) a = 0)

theorem prod_succ {n k : ℕ} (p : Fin (k + 1) → F2Vec n) (θ : Fin (k + 1) → ℝ)
    (a : F2Vec n) :
    (∏ i : Fin (k + 1), zCoeff (θ i) (dot (p i) a = 0)) =
      zCoeff (θ 0) (dot (p 0) a = 0) *
        ∏ i : Fin k, zCoeff (θ i.succ) (dot (p i.succ) a = 0) := by
  rw [Fin.prod_univ_succ]

theorem circuit_eq_zAmp {n k : ℕ} (p : Fin k → F2Vec n) (θ : Fin k → ℝ)
    (x : F2Vec n) : circuit k p θ x = zAmp k p θ x := by
  classical
  induction k generalizing x with
  | zero =>
      have hzamp : zAmp 0 p θ x =
          ((Fintype.card (F2Vec n) : ℂ))⁻¹ * ∑ a : F2Vec n, chi x a := by
        simp [zAmp]
      rw [show circuit 0 p θ x = (if x = 0 then 1 else 0) from rfl, hzamp]
      have hcard : (Fintype.card (F2Vec n) : ℂ) = (2 : ℂ) ^ n := by
        rw [ClassicalApprox.card_f2vec]
        push_cast
        ring
      rw [hcard, charSum x]
      by_cases hx : x = 0
      · simp only [hx, if_true]
        have hne : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
        field_simp
      · rw [if_neg hx, if_neg hx]
        simp
  | succ k ih =>
      have hstep : ∀ x : F2Vec n,
          (∑ a : F2Vec n, chi x a *
              (zCoeff (θ 0) (dot (p 0) a = 0) *
                ∏ i : Fin k, zCoeff (θ i.succ) (dot (p i.succ) a = 0))) =
            (Real.cos (θ 0) : ℂ) *
              (∑ a : F2Vec n, chi x a *
                ∏ i : Fin k, zCoeff (θ i.succ) (dot (p i.succ) a = 0)) +
            Complex.I * (Real.sin (θ 0) : ℂ) *
              (∑ a : F2Vec n, chi (x + p 0) a *
                ∏ i : Fin k, zCoeff (θ i.succ) (dot (p i.succ) a = 0)) := by
        intro x
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        rw [chi_add_left]
        simp only [chi_eq_sgn2]
        have hcos := cos_add_sin_mul_sign (θ 0) (dot (p 0) a = 0)
        rw [← hcos]
        simp only [decide_eq_true_eq]
        ring
      have hprod : ∀ a : F2Vec n,
          (∏ i : Fin (k + 1), zCoeff (θ i) (dot (p i) a = 0)) =
            zCoeff (θ 0) (dot (p 0) a = 0) *
              ∏ i : Fin k, zCoeff (θ i.succ) (dot (p i.succ) a = 0) := by
        intro a
        rw [Fin.prod_univ_succ]
      rw [show circuit (k + 1) p θ x =
          xGate (θ 0) (p 0)
            (circuit k (fun i => p i.succ) (fun i => θ i.succ)) x from rfl]
      simp only [xGate, ih, zAmp]
      simp_rw [hprod]
      rw [hstep]
      ring

theorem prob_eq_normSq_zAmp {n k : ℕ} (p : Fin k → F2Vec n) (θ : Fin k → ℝ)
    (x : F2Vec n) : prob p θ x = Complex.normSq (zAmp k p θ x) := by
  rw [prob, circuit_eq_zAmp]

def signBit (b : Bool) : ℂ := if b then 1 else -1

theorem zCoeff_eq_exp (θ : ℝ) (b : Bool) :
    zCoeff θ b = Complex.exp (Complex.I * (θ : ℂ) * signBit b) := by
  cases b <;> simp [zCoeff, signBit]

theorem signBit_conj (b : Bool) : (starRingEnd ℂ) (signBit b) = signBit b := by
  cases b <;> simp [signBit]

def expAction {n k : ℕ} (p : Fin k → F2Vec n) (θ : ℝ) (a : F2Vec n) : ℂ :=
  Complex.exp (Complex.I * (θ : ℂ) * ∑ i, signBit (dot (p i) a = 0))

theorem prod_zCoeff_const {n k : ℕ} (p : Fin k → F2Vec n) (θ : ℝ) (a : F2Vec n) :
    (∏ i, zCoeff θ (dot (p i) a = 0)) = expAction p θ a := by
  simp only [expAction, zCoeff_eq_exp]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]

theorem chi_mul_chi {n : ℕ} (u v x : F2Vec n) :
    chi x u * chi x v = chi x (u + v) := by
  rw [chi_comm x u, chi_comm x v, ← chi_add_left, chi_comm (u + v) x]

theorem chi_conj {n : ℕ} (u x : F2Vec n) : (starRingEnd ℂ) (chi u x) = chi u x := by
  simp only [chi, sgn2]
  by_cases h : dot u x = 0 <;> simp [h]

def zS {n k : ℕ} (p : Fin k → F2Vec n) (θ : ℝ) (x : F2Vec n) : ℂ :=
  ∑ a, chi x a * expAction p θ a

theorem zAmp_const {n k : ℕ} (p : Fin k → F2Vec n) (θ : ℝ) (x : F2Vec n) :
    zAmp k p (fun _ => θ) x = ((Fintype.card (F2Vec n) : ℂ))⁻¹ * zS p θ x := by
  simp only [zAmp, zS]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by rw [prod_zCoeff_const]

theorem probC_const {n k : ℕ} (p : Fin k → F2Vec n) (θ : ℝ) (x : F2Vec n) :
    (prob p (fun _ => θ) x : ℂ) =
      ((Fintype.card (F2Vec n) : ℂ))⁻¹ * ((Fintype.card (F2Vec n) : ℂ))⁻¹ *
        ((starRingEnd ℂ) (zS p θ x) * zS p θ x) := by
  rw [prob_eq_normSq_zAmp, zAmp_const, Complex.normSq_mul, Complex.normSq_inv,
    Complex.normSq_natCast]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self]
  ring

theorem conj_zS_mul {n k : ℕ} (p : Fin k → F2Vec n) (θ : ℝ) (x : F2Vec n) :
    (starRingEnd ℂ) (zS p θ x) * zS p θ x =
      ∑ a, ∑ b, (starRingEnd ℂ) (expAction p θ a) * expAction p θ b *
        (chi x a * chi x b) := by
  simp only [zS, map_sum, map_mul, chi_conj]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem expAction_conj {n k : ℕ} (p : Fin k → F2Vec n) (θ : ℝ) (a : F2Vec n) :
    (starRingEnd ℂ) (expAction p θ a) =
      Complex.exp (-(Complex.I * (θ : ℂ) * ∑ i, signBit (dot (p i) a = 0))) := by
  rw [expAction, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, signBit_conj, map_sum, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem expAction_conj_mul {n k : ℕ} (p : Fin k → F2Vec n) (θ : ℝ) (a : F2Vec n) :
    (starRingEnd ℂ) (expAction p θ a) * expAction p θ a = 1 := by
  rw [expAction_conj, expAction, ← Complex.exp_add]
  rw [show -(Complex.I * (θ : ℂ) * ∑ i, signBit (dot (p i) a = 0)) +
      Complex.I * (θ : ℂ) * ∑ i, signBit (dot (p i) a = 0) = 0 by ring]
  rw [Complex.exp_zero]

theorem sum_chi_mul_three {n : ℕ} (v a b : F2Vec n) :
    (∑ x : F2Vec n, chi v x * chi x a * chi x b) =
      if v + a + b = 0 then (2 : ℂ) ^ n else 0 := by
  have h : ∀ x : F2Vec n, chi v x * chi x a * chi x b = chi x (v + a + b) := by
    intro x
    rw [chi_comm v x, chi_mul_chi, chi_mul_chi]
  rw [← charSum (v + a + b)]
  exact Finset.sum_congr rfl fun x _ => by rw [h, chi_comm]

theorem add_condition_eq {n : ℕ} (v a b : F2Vec n) :
    (v + a + b = 0) ↔ (b = a + v) := by
  constructor
  · intro h
    have h' : b = v + a := by
      have hshift : (v + a + b) + (v + a) = 0 + (v + a) := by rw [h, zero_add]
      rw [add_assoc (v + a) b (v + a), add_comm b (v + a), ← add_assoc (v + a) (v + a) b,
        add_self_eq_zero_vec, zero_add, zero_add] at hshift
      exact hshift
    rw [h', add_comm v a]
  · intro h
    rw [h]
    rw [← add_assoc (v + a) a v, add_assoc v a a, add_self_eq_zero_vec, add_zero,
      add_self_eq_zero_vec]

theorem sum_chi_probC {n k : ℕ} (p : Fin k → F2Vec n) (θ : ℝ) (v : F2Vec n) :
    (∑ x : F2Vec n, chi v x * (prob p (fun _ => θ) x : ℂ)) =
      ((Fintype.card (F2Vec n) : ℂ))⁻¹ *
        ∑ a, (starRingEnd ℂ) (expAction p θ a) * expAction p θ (a + v) := by
  have hinner : (∑ x : F2Vec n,
        chi v x * ((starRingEnd ℂ) (zS p θ x) * zS p θ x)) =
      (Fintype.card (F2Vec n) : ℂ) *
        ∑ a, (starRingEnd ℂ) (expAction p θ a) * expAction p θ (a + v) := by
    have hexpand : ∀ x : F2Vec n,
        chi v x * ((starRingEnd ℂ) (zS p θ x) * zS p θ x) =
          ∑ a, ∑ b, (starRingEnd ℂ) (expAction p θ a) * expAction p θ b *
            (chi v x * chi x a * chi x b) := by
      intro x
      rw [conj_zS_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    simp_rw [hexpand]
    calc
      (∑ x : F2Vec n, ∑ a, ∑ b, (starRingEnd ℂ) (expAction p θ a) * expAction p θ b *
          (chi v x * chi x a * chi x b)) =
          ∑ a, ∑ x, ∑ b, (starRingEnd ℂ) (expAction p θ a) * expAction p θ b *
            (chi v x * chi x a * chi x b) := by rw [Finset.sum_comm]
      _ = ∑ a, ∑ b, ∑ x, (starRingEnd ℂ) (expAction p θ a) * expAction p θ b *
            (chi v x * chi x a * chi x b) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.sum_comm]
      _ = ∑ a, ∑ b, (starRingEnd ℂ) (expAction p θ a) * expAction p θ b *
            (∑ x : F2Vec n, chi v x * chi x a * chi x b) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.mul_sum]
      _ = ∑ a, ∑ b, (starRingEnd ℂ) (expAction p θ a) * expAction p θ b *
            (if v + a + b = 0 then (2 : ℂ) ^ n else 0) := by
            simp_rw [sum_chi_mul_three]
      _ = ∑ a, (starRingEnd ℂ) (expAction p θ a) * expAction p θ (a + v) *
            (2 : ℂ) ^ n := by
            apply Finset.sum_congr rfl
            intro a _
            simp_rw [add_condition_eq, mul_ite, mul_zero]
            rw [Finset.sum_ite_eq']
            simp
      _ = (2 : ℂ) ^ n * ∑ a, (starRingEnd ℂ) (expAction p θ a) * expAction p θ (a + v) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            ring
      _ = (Fintype.card (F2Vec n) : ℂ) *
            ∑ a, (starRingEnd ℂ) (expAction p θ a) * expAction p θ (a + v) := by
            rw [show (Fintype.card (F2Vec n) : ℂ) = (2 : ℂ) ^ n by
              rw [ClassicalApprox.card_f2vec]; norm_num]
  have hfac : ∀ x : F2Vec n,
      chi v x * ((((Fintype.card (F2Vec n) : ℂ))⁻¹ * ((Fintype.card (F2Vec n) : ℂ))⁻¹) *
            ((starRingEnd ℂ) (zS p θ x) * zS p θ x)) =
        (((Fintype.card (F2Vec n) : ℂ))⁻¹ * ((Fintype.card (F2Vec n) : ℂ))⁻¹) *
          (chi v x * ((starRingEnd ℂ) (zS p θ x) * zS p θ x)) := by
    intro x
    ring
  simp_rw [probC_const]
  simp_rw [hfac]
  rw [← Finset.mul_sum]
  rw [hinner]
  have hNne : ((Fintype.card (F2Vec n) : ℂ)) ≠ 0 := by
    rw [ClassicalApprox.card_f2vec]
    exact_mod_cast pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0)
  rw [show (((Fintype.card (F2Vec n) : ℂ))⁻¹ * ((Fintype.card (F2Vec n) : ℂ))⁻¹) *
        ((Fintype.card (F2Vec n) : ℂ) *
          ∑ a, (starRingEnd ℂ) (expAction p θ a) * expAction p θ (a + v)) =
        ((Fintype.card (F2Vec n) : ℂ))⁻¹ *
          ∑ a, (starRingEnd ℂ) (expAction p θ a) * expAction p θ (a + v) from by
    field_simp]

theorem bias_eq_fourier {n k : ℕ} (p : Fin k → F2Vec n) (θ : ℝ) (s : F2Vec n) :
    (∑ x : F2Vec n, (if dot x s = 0 then (prob p (fun _ => θ) x : ℂ) else 0)) =
      (1 / 2 : ℂ) * (1 + ((Fintype.card (F2Vec n) : ℂ))⁻¹ *
        ∑ a, (starRingEnd ℂ) (expAction p θ a) * expAction p θ (a + s)) := by
  have hind : ∀ x : F2Vec n,
      (if dot x s = 0 then (1 : ℂ) else 0) = (1 + chi s x) / 2 := by
    intro x
    have hds : dot s x = dot x s := dot_comm s x
    by_cases h : dot x s = 0
    · have hs : dot s x = 0 := by rw [hds, h]
      rw [if_pos h, chi_eq_sgn2, if_pos hs]
      norm_num
    · have h1 : dot x s = 1 := by
        rcases ClassicalApprox.zmod2_eq_zero_or_one (dot x s) with h0 | h0
        · exact absurd h0 h
        · exact h0
      have hs : dot s x = 1 := by rw [hds, h1]
      rw [if_neg h, chi_eq_sgn2, if_neg (by rw [hs]; norm_num)]
      norm_num
  have hsum : (∑ x : F2Vec n, (if dot x s = 0 then (prob p (fun _ => θ) x : ℂ) else 0)) =
      (1 / 2 : ℂ) * ((∑ x : F2Vec n, (prob p (fun _ => θ) x : ℂ)) +
        ∑ x : F2Vec n, chi s x * (prob p (fun _ => θ) x : ℂ)) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    have hx : (if dot x s = 0 then (prob p (fun _ => θ) x : ℂ) else 0) =
        ((1 + chi s x) / 2) * (prob p (fun _ => θ) x : ℂ) := by
      by_cases h : dot x s = 0
      · rw [if_pos h, ← hind x, if_pos h]; ring
      · rw [if_neg h, ← hind x, if_neg h]; ring
    rw [hx]
    ring
  rw [hsum]
  have h0 : (∑ x : F2Vec n, (prob p (fun _ => θ) x : ℂ)) =
      ((Fintype.card (F2Vec n) : ℂ))⁻¹ *
        ∑ a, (starRingEnd ℂ) (expAction p θ a) * expAction p θ (a + 0) := by
    simpa using sum_chi_probC p θ 0
  have h1 := sum_chi_probC p θ s
  rw [h0, h1]
  have hzero : ∀ a : F2Vec n, expAction p θ (a + 0) = expAction p θ a := by
    intro a; rw [add_zero]
  simp_rw [hzero]
  have hNne : ((Fintype.card (F2Vec n) : ℂ)) ≠ 0 := by
    rw [ClassicalApprox.card_f2vec]
    exact_mod_cast pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0)
  have hA : ((Fintype.card (F2Vec n) : ℂ))⁻¹ *
      ∑ a, (starRingEnd ℂ) (expAction p θ a) * expAction p θ a = 1 := by
    have hsum1 : (∑ a : F2Vec n,
        (starRingEnd ℂ) (expAction p θ a) * expAction p θ a) =
        (Fintype.card (F2Vec n) : ℂ) := by
      calc (∑ a : F2Vec n, (starRingEnd ℂ) (expAction p θ a) * expAction p θ a) =
          ∑ _a : F2Vec n, (1 : ℂ) := by
            apply Finset.sum_congr rfl
            intro a _
            exact expAction_conj_mul p θ a
        _ = (Fintype.card (F2Vec n) : ℂ) := by simp
    rw [hsum1, inv_mul_cancel₀ hNne]
  rw [hA]
end Qatlib.Papers.Instantaneous08.MainResults.ConstantAction
