/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureDefs
import Qatlib.Concepts.ChannelTheory.Stinespring.PhyslibChannels
import Qatlib.Concepts.ShadowModels.ShadowChannel.QubitConjugationDesign
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Qatlib.Concepts.ChannelTheory.Naimark.ChannelStructureMeasurement
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement

set_option autoImplicit false

open Matrix
open Qatlib
open scoped Classical ComplexOrder BigOperators

variable {D E : ℕ}

namespace Qatlib.Concepts.ChannelTheory.Naimark

noncomputable def naimarkV {D : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    (Λ : POVM O (Fin D)) (e : O ≃ Fin (Fintype.card O)) :
    Matrix (Fin D × Fin (Fintype.card O)) (Fin D) ℂ :=
  fun x j => (Λ.mats (e.symm x.2) ^ (1 / 2 : ℝ)).mat x.1 j

noncomputable def naimarkP {D : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    (e : O ≃ Fin (Fintype.card O)) (o : O) :
    Matrix (Fin D × Fin (Fintype.card O)) (Fin D × Fin (Fintype.card O)) ℂ :=
  fun x y => if x.2 = e o ∧ y.2 = e o ∧ x.1 = y.1 then (1 : ℂ) else 0

theorem naimarkP_self (D : ℕ) {O : Type} [Fintype O] [DecidableEq O]
    (e : O ≃ Fin (Fintype.card O)) (o : O) :
    (naimarkP (D := D) e o).conjTranspose = naimarkP e o := by
  ext x y
  simp only [Matrix.conjTranspose_apply]
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  by_cases h1 : xk = e o <;> by_cases h2 : yk = e o <;> by_cases h3 : xi = yi <;>
    simp [naimarkP, h1, h2, h3, eq_comm, and_comm, and_left_comm, and_assoc]

theorem sum_ite_const {α : Type} [Fintype α] [DecidableEq α] (a : α) (c : ℂ) :
    (∑ k : α, (if k = a then c else 0)) = c := by
  rw [Finset.sum_ite_eq' Finset.univ a (fun _ => c)]
  simp
set_option maxHeartbeats 800000

theorem naimarkP_mul_self {D : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    (e : O ≃ Fin (Fintype.card O)) (o : O) :
    (naimarkP (D := D) e o) * naimarkP e o = naimarkP e o := by
  classical
  ext x y
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  show (∑ z : Fin D × Fin (Fintype.card O),
      naimarkP e o (xi, xk) z * naimarkP e o z (yi, yk))
    = naimarkP e o (xi, xk) (yi, yk)
  simp only [naimarkP]
  rw [Fintype.sum_prod_type]
  have hsum : (∑ a : Fin D, ∑ k : Fin (Fintype.card O),
      (if xk = e o ∧ k = e o ∧ xi = a then (1 : ℂ) else 0) *
        (if k = e o ∧ yk = e o ∧ a = yi then 1 else 0))
      = if xk = e o ∧ yk = e o ∧ xi = yi then (1 : ℂ) else 0 := by
    by_cases h : xk = e o ∧ yk = e o ∧ xi = yi
    · obtain ⟨h1, h2, h3⟩ := h
      rw [if_pos ⟨h1, h2, h3⟩]
      subst h3
      have hmul : ∀ (a : Fin D) (k : Fin (Fintype.card O)),
          (if xk = e o ∧ k = e o ∧ xi = a then (1 : ℂ) else 0) *
            (if k = e o ∧ yk = e o ∧ a = xi then 1 else 0)
          = if k = e o ∧ a = xi then (1 : ℂ) else 0 := by
        intro a k
        by_cases hk : k = e o <;> by_cases ha : a = xi <;>
          simp [h1, h2, hk, ha, eq_comm, and_comm, and_left_comm, and_assoc]
      simp only [hmul]
      rw [Finset.sum_comm]
      rw [Finset.sum_eq_single (e o)]
      · simp only [true_and]
        exact sum_ite_const xi 1
      · intro b _ hb; simp [hb]
      · intro habs; exact absurd (Finset.mem_univ _) habs
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro a _
      apply Finset.sum_eq_zero
      intro k _
      by_cases c1 : xk = e o ∧ k = e o ∧ xi = a <;>
        by_cases c2 : k = e o ∧ yk = e o ∧ a = yi
      · obtain ⟨ha1, _, ha3⟩ := c1
        obtain ⟨_, hb2, hb3⟩ := c2
        exact absurd ⟨ha1, hb2, ha3.trans hb3⟩ h
      · simp [c2]
      · simp [c1]
      · simp [c1, c2]
  exact hsum

theorem naimarkP_mul_of_ne {D : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    (e : O ≃ Fin (Fintype.card O)) {o p : O} (h : o ≠ p) :
    (naimarkP (D := D) e o) * naimarkP e p = 0 := by
  classical
  ext x y
  show (∑ z : Fin D × Fin (Fintype.card O), naimarkP e o x z * naimarkP e p z y) = 0
  apply Finset.sum_eq_zero
  intro z _
  rcases z with ⟨zi, zk⟩
  by_cases hk : zk = e o
  · have hk' : ¬ zk = e p := fun hh => h (e.injective (hk.symm.trans hh))
    simp [naimarkP, hk']
  · have hk' : ¬ zk = e o := hk
    simp [naimarkP, hk']

theorem naimarkP_sum {D : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    (e : O ≃ Fin (Fintype.card O)) :
    (∑ o : O, naimarkP (D := D) e o) = 1 := by
  classical
  ext x y
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  rw [Matrix.sum_apply]
  show (∑ o : O, naimarkP e o (xi, xk) (yi, yk))
    = (1 : Matrix (Fin D × Fin (Fintype.card O)) (Fin D × Fin (Fintype.card O)) ℂ)
        (xi, xk) (yi, yk)
  simp only [naimarkP, Matrix.one_apply]
  by_cases heq : (xi, xk) = (yi, yk)
  · rw [if_pos heq]
    have h1 : xi = yi := congrArg Prod.fst heq
    have h2 : xk = yk := congrArg Prod.snd heq
    have hrew : ∀ o : O,
        (if xk = e o ∧ yk = e o ∧ xi = yi then (1 : ℂ) else 0)
          = if e o = xk then (1 : ℂ) else 0 := by
      intro o
      by_cases hh : e o = xk
      · rw [if_pos hh, if_pos (by exact ⟨hh.symm, h2.symm.trans hh.symm, h1⟩)]
      · rw [if_neg hh, if_neg (fun ⟨ha, _, _⟩ => hh ha.symm)]
    simp only [hrew]
    rw [Equiv.sum_comp e (fun k => if k = xk then (1 : ℂ) else 0)]
    exact sum_ite_const xk 1
  · rw [if_neg heq]
    apply Finset.sum_eq_zero
    intro o _
    rw [if_neg (fun hh => heq (Prod.ext hh.2.2 (hh.1.trans hh.2.1.symm)))]

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid in

theorem naimarkV_isometry {D : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    (Λ : POVM O (Fin D)) (e : O ≃ Fin (Fintype.card O)) :
    Matrix.conjTranspose (naimarkV Λ e) * naimarkV Λ e = 1 := by
  classical
  ext i j
  show (∑ x : Fin D × Fin (Fintype.card O), star (naimarkV Λ e x i) * naimarkV Λ e x j)
    = (1 : Operator D) i j
  rw [Fintype.sum_prod_type]
  simp only [naimarkV]
  rw [Finset.sum_comm]
  have h1 : ∀ k : Fin (Fintype.card O),
      (∑ a : Fin D,
          star ((Λ.mats (e.symm k) ^ (1 / 2 : ℝ)).mat a i) *
            ((Λ.mats (e.symm k) ^ (1 / 2 : ℝ)).mat a j))
        = (((Λ.mats (e.symm k) ^ (1 / 2 : ℝ)).mat).conjTranspose *
          (Λ.mats (e.symm k) ^ (1 / 2 : ℝ)).mat) i j := by
    intro k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [h1]
  rw [Equiv.sum_comp e.symm (fun o =>
    (((Λ.mats o ^ (1 / 2 : ℝ)).mat).conjTranspose * (Λ.mats o ^ (1 / 2 : ℝ)).mat) i j)]
  have h2 : ∀ o : O,
      (((Λ.mats o ^ (1 / 2 : ℝ)).mat).conjTranspose * (Λ.mats o ^ (1 / 2 : ℝ)).mat) i j
        = (Λ.mats o).mat i j := by
    intro o
    rw [HermitianMat.conjTranspose_mat, HermitianMat.pow_half_mul (Λ.nonneg o)]
  simp only [h2]
  rw [← Matrix.sum_apply, ← HermitianMat.mat_finset_sum, Λ.normalized]
  rfl

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid in

theorem naimarkV_P_V {D : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    (Λ : POVM O (Fin D)) (e : O ≃ Fin (Fintype.card O)) (o : O) :
    ((Matrix.conjTranspose (naimarkV Λ e) : Matrix (Fin D) (Fin D × Fin (Fintype.card O)) ℂ)
      * (naimarkP e o * naimarkV Λ e :
        Matrix (Fin D × Fin (Fintype.card O)) (Fin D) ℂ)) = (Λ.mats o).mat := by
  classical
  ext i j
  show (∑ x : Fin D × Fin (Fintype.card O),
      star (naimarkV Λ e x i) *
        (∑ y : Fin D × Fin (Fintype.card O), naimarkP e o x y * naimarkV Λ e y j))
    = (Λ.mats o).mat i j
  simp only [naimarkP, naimarkV]
  have hinner : ∀ x : Fin D × Fin (Fintype.card O),
      (∑ y : Fin D × Fin (Fintype.card O),
          (if x.2 = e o ∧ y.2 = e o ∧ x.1 = y.1 then (1 : ℂ) else 0) *
            ((Λ.mats (e.symm y.2) ^ (1 / 2 : ℝ)).mat y.1 j))
      = if x.2 = e o then ((Λ.mats o ^ (1 / 2 : ℝ)).mat x.1 j) else 0 := by
    intro x
    rcases x with ⟨xi, xk⟩
    simp only [Fintype.sum_prod_type]
    have hk : ∀ a : Fin D,
        (∑ k : Fin (Fintype.card O),
            (if xk = e o ∧ k = e o ∧ xi = a then (1 : ℂ) else 0) *
              ((Λ.mats (e.symm k) ^ (1 / 2 : ℝ)).mat a j))
        = if xk = e o ∧ xi = a then ((Λ.mats o ^ (1 / 2 : ℝ)).mat a j) else 0 := by
      intro a
      rw [Finset.sum_eq_single (e o)]
      · rw [Equiv.symm_apply_apply]
        by_cases h : xk = e o ∧ xi = a
        · obtain ⟨h1, h2⟩ := h
          rw [if_pos (by exact ⟨h1, rfl, h2⟩), if_pos ⟨h1, h2⟩, one_mul]
        · rw [if_neg (fun ⟨hh, _, hh'⟩ => h ⟨hh, hh'⟩), if_neg h, zero_mul]
      · intro k _ hk'
        rw [if_neg (fun ⟨_, hh, _⟩ => hk' hh), zero_mul]
      · intro habs; exact absurd (Finset.mem_univ _) habs
    simp only [hk]
    rw [Finset.sum_eq_single xi]
    · by_cases h : xk = e o
      · rw [if_pos (by exact ⟨h, rfl⟩), if_pos h]
      · rw [if_neg (fun ⟨hh, _⟩ => h hh), if_neg h]
    · intro b _ hb
      rw [if_neg (fun ⟨_, hh⟩ => hb hh.symm)]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  simp only [hinner]
  simp only [Fintype.sum_prod_type]
  have houter : ∀ a : Fin D,
      (∑ k : Fin (Fintype.card O),
          star ((Λ.mats (e.symm k) ^ (1 / 2 : ℝ)).mat a i) *
            (if k = e o then ((Λ.mats o ^ (1 / 2 : ℝ)).mat a j) else 0))
      = star ((Λ.mats o ^ (1 / 2 : ℝ)).mat a i) * ((Λ.mats o ^ (1 / 2 : ℝ)).mat a j) := by
    intro a
    rw [Finset.sum_eq_single (e o)]
    · rw [Equiv.symm_apply_apply, if_pos rfl]
    · intro k _ hk'
      rw [if_neg hk', mul_zero]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  simp only [houter]
  have h1 : (∑ a : Fin D,
        star ((Λ.mats o ^ (1 / 2 : ℝ)).mat a i) * ((Λ.mats o ^ (1 / 2 : ℝ)).mat a j))
      = (((Λ.mats o ^ (1 / 2 : ℝ)).mat).conjTranspose *
        (Λ.mats o ^ (1 / 2 : ℝ)).mat) i j := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [h1, HermitianMat.conjTranspose_mat, HermitianMat.pow_half_mul (Λ.nonneg o)]

theorem naimark_dilation {D : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    (Λ : POVM O (Fin D)) (e : O ≃ Fin (Fintype.card O)) :
    NaimarkDilation Λ (Fintype.card O) (naimarkV Λ e) (naimarkP e) := by
  refine ⟨naimarkV_isometry Λ e, ?_, ?_, ?_, ?_⟩
  · intro o; exact ⟨naimarkP_self D e o, naimarkP_mul_self e o⟩
  · intro o p h; exact naimarkP_mul_of_ne e h
  · exact naimarkP_sum e
  · intro o
    rw [Matrix.mul_assoc]
    exact naimarkV_P_V Λ e o

theorem instrumentProb_eq_effectStat {D : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    (Λ : POVM O (Fin D)) (ρ : Operator D) (o : O) :
    instrumentProb (Instrument.ofPOVM Λ) ρ o = EffectStat ((Λ.mats o).mat) ρ := by
  rw [instrumentProb_ofPOVM]
  rfl

theorem naimarkP_mulVec {D : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    (e : O ≃ Fin (Fintype.card O)) (o : O) (w : Fin D × Fin (Fintype.card O) → ℂ) :
    naimarkP e o *ᵥ w = fun x => if x.2 = e o then w (x.1, e o) else 0 := by
  classical
  funext x
  rcases x with ⟨xi, xk⟩
  show (∑ y : Fin D × Fin (Fintype.card O), naimarkP e o (xi, xk) y * w y)
    = if xk = e o then w (xi, e o) else 0
  simp only [naimarkP]
  simp only [Fintype.sum_prod_type]
  have hk : ∀ a : Fin D,
      (∑ k : Fin (Fintype.card O),
          (if xk = e o ∧ k = e o ∧ xi = a then (1 : ℂ) else 0) * w (a, k))
      = if xk = e o ∧ xi = a then w (a, e o) else 0 := by
    intro a
    rw [Finset.sum_eq_single (e o)]
    · by_cases h : xk = e o ∧ xi = a
      · obtain ⟨h1, h2⟩ := h
        rw [if_pos (by exact ⟨h1, rfl, h2⟩), if_pos ⟨h1, h2⟩, one_mul]
      · rw [if_neg (fun ⟨hh, _, hh'⟩ => h ⟨hh, hh'⟩), if_neg h, zero_mul]
    · intro k _ hk'
      rw [if_neg (fun ⟨_, hh, _⟩ => hk' hh), zero_mul]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  simp only [hk]
  rw [Finset.sum_eq_single xi]
  · by_cases h : xk = e o
    · rw [if_pos (by exact ⟨h, rfl⟩), if_pos h]
    · rw [if_neg (fun ⟨hh, _⟩ => h hh), if_neg h]
  · intro b _ hb
    rw [if_neg (fun ⟨_, hh⟩ => hb hh.symm)]
  · intro habs; exact absurd (Finset.mem_univ _) habs

theorem naimarkP_V_zero_of_effect {D : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    (Λ : POVM O (Fin D)) (e : O ≃ Fin (Fintype.card O)) {o : O}
    (ho : (Λ.mats o).mat = 0) (ψ : Fin D → ℂ) :
    normSqVec (naimarkP e o *ᵥ (naimarkV Λ e *ᵥ ψ)) = 0 := by
  classical
  have hs : ((Λ.mats o ^ (1 / 2 : ℝ)).mat) = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    rw [HermitianMat.conjTranspose_mat, HermitianMat.pow_half_mul (Λ.nonneg o), ho]
  have hval : ∀ x : Fin D × Fin (Fintype.card O),
      (if x.2 = e o then (naimarkV Λ e *ᵥ ψ) (x.1, e o) else 0) = 0 := by
    intro x
    by_cases hx : x.2 = e o
    · rw [if_pos hx]
      have h1 : (naimarkV Λ e *ᵥ ψ) (x.1, e o)
          = ∑ j : Fin D, ((Λ.mats o ^ (1 / 2 : ℝ)).mat) x.1 j * ψ j := by
        show (∑ j : Fin D, naimarkV Λ e (x.1, e o) j * ψ j) = _
        simp only [naimarkV]
        congr 1
        funext j
        rw [e.symm_apply_apply o]
      rw [h1, hs]
      simp
    · rw [if_neg hx]
  rw [naimarkP_mulVec]
  have hzero : (fun x : Fin D × Fin (Fintype.card O) =>
      if x.2 = e o then (naimarkV Λ e *ᵥ ψ) (x.1, e o) else 0) = 0 := by
    funext x
    exact hval x
  rw [hzero]
  simp [normSqVec]

theorem normSq_eq_re_conj_mul (z : ℂ) : ‖z‖ ^ (2 : ℕ) = (star z * z).re := by
  rw [Complex.sq_norm]
  have h := congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := z))
  simp only [Complex.ofReal_re] at h
  exact h

theorem normSqVec_eq_re_trace_outerProduct {n : ℕ} (φ : Fin n → ℂ) :
    normSqVec φ = (Matrix.trace (outerProduct φ)).re := by
  classical
  have htrace : Matrix.trace (outerProduct φ)
      = ∑ s : Fin n, star (φ s) * φ s := by
    show (∑ s : Fin n, φ s * starRingEnd ℂ (φ s))
      = ∑ s : Fin n, star (φ s) * φ s
    apply Finset.sum_congr rfl
    intro s _
    rw [starRingEnd_apply, mul_comm]
  rw [htrace, Complex.re_sum]
  unfold normSqVec
  apply Finset.sum_congr rfl
  intro s _
  exact normSq_eq_re_conj_mul (φ s)

theorem normSqVec_block_ite {n m : ℕ} (b : Fin m) (w : Fin n → ℂ) :
    normSqVec (fun x : Fin n × Fin m => if x.2 = b then w x.1 else 0) = normSqVec w := by
  classical
  unfold normSqVec
  simp only [Fintype.sum_prod_type]
  have hk : ∀ a : Fin n,
      (∑ k : Fin m, ‖if k = b then w a else 0‖ ^ (2 : ℕ)) = ‖w a‖ ^ (2 : ℕ) := by
    intro a
    rw [Finset.sum_eq_single b]
    · rw [if_pos rfl]
    · intro k _ hk
      rw [if_neg hk]
      simp
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  exact Finset.sum_congr rfl fun a _ => hk a

theorem naimark_born {D : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    (Λ : POVM O (Fin D)) (e : O ≃ Fin (Fintype.card O)) (ψ : Fin D → ℂ) (o : O) :
    normSqVec (naimarkP e o *ᵥ (naimarkV Λ e *ᵥ ψ))
      = EffectStat ((Λ.mats o).mat) (outerProduct ψ) := by
  classical
  have hvec : naimarkP e o *ᵥ (naimarkV Λ e *ᵥ ψ)
      = fun x : Fin D × Fin (Fintype.card O) =>
          if x.2 = e o then ((Λ.mats o ^ (1 / 2 : ℝ)).mat *ᵥ ψ) x.1 else 0 := by
    funext x
    rcases x with ⟨xi, xk⟩
    rw [naimarkP_mulVec]
    show (if xk = e o then (naimarkV Λ e *ᵥ ψ) (xi, e o) else 0)
      = if xk = e o then ((Λ.mats o ^ (1 / 2 : ℝ)).mat *ᵥ ψ) xi else 0
    by_cases hk : xk = e o
    · rw [if_pos hk, if_pos hk]
      have h1 : (naimarkV Λ e *ᵥ ψ) (xi, e o)
          = ∑ j : Fin D, ((Λ.mats o ^ (1 / 2 : ℝ)).mat) xi j * ψ j := by
        show (∑ j : Fin D, naimarkV Λ e (xi, e o) j * ψ j) = _
        simp only [naimarkV]
        congr 1
        funext j
        rw [e.symm_apply_apply o]
      show (naimarkV Λ e *ᵥ ψ) (xi, e o) = ((Λ.mats o ^ (1 / 2 : ℝ)).mat *ᵥ ψ) xi
      exact h1
    · rw [if_neg hk, if_neg hk]
  rw [hvec]
  rw [normSqVec_block_ite (e o) ((Λ.mats o ^ (1 / 2 : ℝ)).mat *ᵥ ψ)]
  have hS : ((Λ.mats o ^ (1 / 2 : ℝ)).mat).conjTranspose * (Λ.mats o ^ (1 / 2 : ℝ)).mat
      = (Λ.mats o).mat := by
    rw [HermitianMat.conjTranspose_mat, HermitianMat.pow_half_mul (Λ.nonneg o)]
  rw [normSqVec_eq_re_trace_outerProduct, outerProduct_mulVec, Matrix.trace_mul_cycle, hS]
  rfl

theorem sum4_swap {α β γ δ ε : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid ε] (f : α → β → γ → δ → ε) :
    ∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, f a b c d
      = ∑ c : γ, ∑ d : δ, ∑ a : α, ∑ b : β, f a b c d := by
  classical
  have h : (∑ x : α × β, ∑ y : γ × δ, f x.1 x.2 y.1 y.2)
      = (∑ y : γ × δ, ∑ x : α × β, f x.1 x.2 y.1 y.2) := Finset.sum_comm
  simp only [Fintype.sum_prod_type] at h ⊢
  exact h

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid in

theorem trace_refLeft_refIsometryImage {D E env R : ℕ}
    (V : Matrix (Fin E × Fin env) (Fin D) ℂ)
    (A : Matrix (Fin E × Fin env) (Fin E × Fin env) ℂ)
    (X : Matrix (Fin R × Fin D) (Fin R × Fin D) ℂ) :
    Matrix.trace (refLeft A R * refIsometryImage V R X)
      = Matrix.trace (refLeft ((V.conjTranspose * A * V) : Matrix (Fin D) (Fin D) ℂ) R * X) := by
  classical
  have hL : Matrix.trace (refLeft A R * refIsometryImage V R X)
      = ∑ r : Fin R, ∑ i : Fin D, ∑ j : Fin D,
          ∑ p : Fin E × Fin env, ∑ q : Fin E × Fin env,
            X (r, i) (r, j) * star (V p j) * A p q * V q i := by
    have step1 : Matrix.trace (refLeft A R * refIsometryImage V R X)
        = ∑ r : Fin R, ∑ p : Fin E × Fin env, ∑ q : Fin E × Fin env,
            A p q * (∑ i : Fin D, ∑ j : Fin D, V q i * X (r, i) (r, j) * star (V p j)) := by
      show (∑ x : Fin R × (Fin E × Fin env),
          (refLeft A R * refIsometryImage V R X) x x) = _
      conv_lhs => rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro p _
      have hz : (∑ z : Fin R × (Fin E × Fin env),
            refLeft A R (r, p) z * refIsometryImage V R X z (r, p))
          = ∑ q : Fin E × Fin env, A p q * refIsometryImage V R X (r, q) (r, p) := by
        conv_lhs => rw [Fintype.sum_prod_type]
        rw [Finset.sum_eq_single r]
        · apply Finset.sum_congr rfl
          intro q _
          simp [refLeft]
        · intro r' _ hr'
          apply Finset.sum_eq_zero
          intro q _
          simp [refLeft, Ne.symm hr']
        · intro habs
          exact absurd (Finset.mem_univ _) habs
      show (∑ z : Fin R × (Fin E × Fin env),
          refLeft A R (r, p) z * refIsometryImage V R X z (r, p))
        = ∑ q : Fin E × Fin env, A p q *
            (∑ i : Fin D, ∑ j : Fin D, V q i * X (r, i) (r, j) * star (V p j))
      rw [hz]
      apply Finset.sum_congr rfl
      intro q _
      rfl
    rw [step1]
    have step2 : (∑ r : Fin R, ∑ p : Fin E × Fin env, ∑ q : Fin E × Fin env,
          A p q * (∑ i : Fin D, ∑ j : Fin D, V q i * X (r, i) (r, j) * star (V p j)))
        = ∑ r : Fin R, ∑ p : Fin E × Fin env, ∑ q : Fin E × Fin env,
            ∑ i : Fin D, ∑ j : Fin D,
              A p q * (V q i * X (r, i) (r, j) * star (V p j)) := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      simp only [Finset.mul_sum]
    rw [step2]
    apply Finset.sum_congr rfl
    intro r _
    have hs := sum4_swap
      (fun (p : Fin E × Fin env) (q : Fin E × Fin env) (i : Fin D) (j : Fin D) =>
        A p q * (V q i * X (r, i) (r, j) * star (V p j)))
    rw [hs]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  have hR : Matrix.trace (refLeft ((V.conjTranspose * A * V) : Matrix (Fin D) (Fin D) ℂ) R * X)
      = ∑ r : Fin R, ∑ i : Fin D, ∑ j : Fin D,
          ∑ p : Fin E × Fin env, ∑ q : Fin E × Fin env,
            X (r, i) (r, j) * star (V p j) * A p q * V q i := by
    have hMexp : ∀ a b : Fin D,
        ((V.conjTranspose * A * V) : Matrix (Fin D) (Fin D) ℂ) a b
          = ∑ q : Fin E × Fin env, ∑ p : Fin E × Fin env, star (V p a) * A p q * V q b := by
      intro a b
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      simp only [Finset.sum_mul]
    have step1 : Matrix.trace (refLeft ((V.conjTranspose * A * V) : Matrix (Fin D) (Fin D) ℂ) R * X)
        = ∑ r : Fin R, ∑ a : Fin D, ∑ b : Fin D,
            ((V.conjTranspose * A * V) : Matrix (Fin D) (Fin D) ℂ) a b * X (r, b) (r, a) := by
      show (∑ x : Fin R × Fin D,
          (refLeft ((V.conjTranspose * A * V) : Matrix (Fin D) (Fin D) ℂ) R * X) x x) = _
      conv_lhs => rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro a _
      have hz : (∑ z : Fin R × Fin D,
            refLeft ((V.conjTranspose * A * V) : Matrix (Fin D) (Fin D) ℂ) R (r, a) z * X z (r, a))
          = ∑ b : Fin D,
              ((V.conjTranspose * A * V) : Matrix (Fin D) (Fin D) ℂ) a b * X (r, b) (r, a) := by
        conv_lhs => rw [Fintype.sum_prod_type]
        rw [Finset.sum_eq_single r]
        · apply Finset.sum_congr rfl
          intro b _
          simp [refLeft]
        · intro r' _ hr'
          apply Finset.sum_eq_zero
          intro b _
          simp [refLeft, Ne.symm hr']
        · intro habs
          exact absurd (Finset.mem_univ _) habs
      show (∑ z : Fin R × Fin D,
          refLeft ((V.conjTranspose * A * V) : Matrix (Fin D) (Fin D) ℂ) R (r, a) z * X z (r, a))
        = ∑ b : Fin D,
            ((V.conjTranspose * A * V) : Matrix (Fin D) (Fin D) ℂ) a b * X (r, b) (r, a)
      exact hz
    rw [step1]
    have step2 : (∑ r : Fin R, ∑ a : Fin D, ∑ b : Fin D,
          ((V.conjTranspose * A * V) : Matrix (Fin D) (Fin D) ℂ) a b * X (r, b) (r, a))
        = ∑ r : Fin R, ∑ i : Fin D, ∑ j : Fin D,
            ∑ p : Fin E × Fin env, ∑ q : Fin E × Fin env,
              X (r, i) (r, j) * star (V p j) * A p q * V q i := by
      apply Finset.sum_congr rfl
      intro r _
      have h0 : (∑ a : Fin D, ∑ b : Fin D,
            ((V.conjTranspose * A * V) : Matrix (Fin D) (Fin D) ℂ) a b * X (r, b) (r, a))
          = ∑ a : Fin D, ∑ b : Fin D,
              ∑ q : Fin E × Fin env, ∑ p : Fin E × Fin env,
                star (V p a) * A p q * V q b * X (r, b) (r, a) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [hMexp a b]
        simp only [Finset.sum_mul]
      rw [h0]
      have h1 : (∑ a : Fin D, ∑ b : Fin D,
            ∑ q : Fin E × Fin env, ∑ p : Fin E × Fin env,
              star (V p a) * A p q * V q b * X (r, b) (r, a))
          = (∑ b : Fin D, ∑ a : Fin D,
            ∑ q : Fin E × Fin env, ∑ p : Fin E × Fin env,
              star (V p a) * A p q * V q b * X (r, b) (r, a)) := Finset.sum_comm
      rw [h1]
      have h2 : (∑ b : Fin D, ∑ a : Fin D,
            ∑ q : Fin E × Fin env, ∑ p : Fin E × Fin env,
              star (V p a) * A p q * V q b * X (r, b) (r, a))
          = (∑ b : Fin D, ∑ a : Fin D,
            ∑ p : Fin E × Fin env, ∑ q : Fin E × Fin env,
              star (V p a) * A p q * V q b * X (r, b) (r, a)) := by
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_comm
      rw [h2]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      ring
    exact step2
  rw [hL, hR]

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid in

theorem naimark_reference {D : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    (Λ : POVM O (Fin D)) (e : O ≃ Fin (Fintype.card O)) (R : ℕ)
    (X : Matrix (Fin R × Fin D) (Fin R × Fin D) ℂ) (o : O) :
    Matrix.trace (refLeft (naimarkP e o) R * refIsometryImage (naimarkV Λ e) R X)
      = Matrix.trace (refLeft ((Λ.mats o).mat) R * X) := by
  rw [trace_refLeft_refIsometryImage]
  have hM : (((Matrix.conjTranspose (naimarkV Λ e)) :
        Matrix (Fin D) (Fin D × Fin (Fintype.card O)) ℂ)
      * (naimarkP e o : Matrix (Fin D × Fin (Fintype.card O)) (Fin D × Fin (Fintype.card O)) ℂ)
      * (naimarkV Λ e : Matrix (Fin D × Fin (Fintype.card O)) (Fin D) ℂ))
      = (Λ.mats o).mat := by
    rw [Matrix.mul_assoc]
    exact naimarkV_P_V Λ e o
  rw [hM]

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid in

theorem naimarkP_mul_apply {D : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    {ι : Type} (e : O ≃ Fin (Fintype.card O)) (o : O)
    (B : Matrix (Fin D × Fin (Fintype.card O)) ι ℂ)
    (x : Fin D × Fin (Fintype.card O)) (j : ι) :
    ((naimarkP e o * B) : Matrix (Fin D × Fin (Fintype.card O)) ι ℂ) x j
      = if x.2 = e o then B (x.1, e o) j else 0 := by
  classical
  rcases x with ⟨xi, xk⟩
  show (∑ z : Fin D × Fin (Fintype.card O), naimarkP e o (xi, xk) z * B z j)
    = if xk = e o then B (xi, e o) j else 0
  simp only [naimarkP]
  simp only [Fintype.sum_prod_type]
  have hk : ∀ a : Fin D,
      (∑ k : Fin (Fintype.card O),
          (if xk = e o ∧ k = e o ∧ xi = a then (1 : ℂ) else 0) * B (a, k) j)
      = if xk = e o ∧ xi = a then B (a, e o) j else 0 := by
    intro a
    rw [Finset.sum_eq_single (e o)]
    · by_cases h : xk = e o ∧ xi = a
      · obtain ⟨h1, h2⟩ := h
        rw [if_pos (by exact ⟨h1, rfl, h2⟩), if_pos ⟨h1, h2⟩, one_mul]
      · rw [if_neg (fun ⟨hh, _, hh'⟩ => h ⟨hh, hh'⟩), if_neg h, zero_mul]
    · intro k _ hk'
      rw [if_neg (fun ⟨_, hh, _⟩ => hk' hh), zero_mul]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  simp only [hk]
  rw [Finset.sum_eq_single xi]
  · by_cases h : xk = e o
    · rw [if_pos (by exact ⟨h, rfl⟩), if_pos h]
    · rw [if_neg (fun ⟨hh, _⟩ => h hh), if_neg h]
  · intro b _ hb
    rw [if_neg (fun ⟨_, hh⟩ => hb hh.symm)]
  · intro habs; exact absurd (Finset.mem_univ _) habs

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid in

theorem naimarkP_mul_right_apply {D : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    {ι : Type} (e : O ≃ Fin (Fintype.card O)) (o : O)
    (B : Matrix ι (Fin D × Fin (Fintype.card O)) ℂ)
    (i : ι) (x : Fin D × Fin (Fintype.card O)) :
    ((B * naimarkP e o) : Matrix ι (Fin D × Fin (Fintype.card O)) ℂ) i x
      = if x.2 = e o then B i (x.1, e o) else 0 := by
  classical
  rcases x with ⟨xi, xk⟩
  show (∑ z : Fin D × Fin (Fintype.card O), B i z * naimarkP e o z (xi, xk))
    = if xk = e o then B i (xi, e o) else 0
  simp only [naimarkP]
  simp only [Fintype.sum_prod_type]
  have hk : ∀ a : Fin D,
      (∑ k : Fin (Fintype.card O),
          B i (a, k) * (if k = e o ∧ xk = e o ∧ a = xi then (1 : ℂ) else 0))
      = if xk = e o ∧ a = xi then B i (a, e o) else 0 := by
    intro a
    rw [Finset.sum_eq_single (e o)]
    · by_cases h : xk = e o ∧ a = xi
      · obtain ⟨h1, h2⟩ := h
        rw [if_pos (by exact ⟨rfl, h1, h2⟩), if_pos ⟨h1, h2⟩, mul_one]
      · rw [if_neg (fun ⟨_, hh, hh'⟩ => h ⟨hh, hh'⟩), if_neg h, mul_zero]
    · intro k _ hk'
      rw [if_neg (fun ⟨hh, _, _⟩ => hk' hh), mul_zero]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  simp only [hk]
  rw [Finset.sum_eq_single xi]
  · by_cases h : xk = e o
    · rw [if_pos (by exact ⟨h, rfl⟩), if_pos h]
    · rw [if_neg (fun ⟨hh, _⟩ => h hh), if_neg h]
  · intro b _ hb
    rw [if_neg (fun ⟨_, hh⟩ => hb hh)]
  · intro habs; exact absurd (Finset.mem_univ _) habs

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid in

theorem naimarkP_sandwich_apply {D : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    (e : O ≃ Fin (Fintype.card O)) (o : O)
    (T : Matrix (Fin D × Fin (Fintype.card O)) (Fin D × Fin (Fintype.card O)) ℂ)
    (x y : Fin D × Fin (Fintype.card O)) :
    ((naimarkP e o * T * naimarkP e o) :
      Matrix (Fin D × Fin (Fintype.card O)) (Fin D × Fin (Fintype.card O)) ℂ) x y
      = if x.2 = e o ∧ y.2 = e o then T (x.1, e o) (y.1, e o) else 0 := by
  classical
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  have h1 : ((naimarkP e o * T * naimarkP e o) :
      Matrix (Fin D × Fin (Fintype.card O)) (Fin D × Fin (Fintype.card O)) ℂ) (xi, xk) (yi, yk)
      = if yk = e o then
          ((naimarkP e o * T) :
            Matrix (Fin D × Fin (Fintype.card O)) (Fin D × Fin (Fintype.card O)) ℂ) (xi, xk) (yi, e o)
        else 0 :=
    naimarkP_mul_right_apply e o (naimarkP e o * T) (xi, xk) (yi, yk)
  rw [h1]
  by_cases hy : yk = e o
  · rw [if_pos hy]
    have h2 : ((naimarkP e o * T) :
        Matrix (Fin D × Fin (Fintype.card O)) (Fin D × Fin (Fintype.card O)) ℂ) (xi, xk) (yi, e o)
        = if xk = e o then T (xi, e o) (yi, e o) else 0 :=
      naimarkP_mul_apply e o T (xi, xk) (yi, e o)
    rw [h2]
    by_cases hx : xk = e o
    · rw [if_pos hx, if_pos ⟨hx, hy⟩]
    · rw [if_neg hx, if_neg (fun ⟨hh, _⟩ => hx hh)]
  · rw [if_neg hy, if_neg (fun ⟨_, hh⟩ => hy hh)]

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid in

theorem naimark_ptrace {D : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    (Λ : POVM O (Fin D)) (e : O ≃ Fin (Fintype.card O)) (ρ : Operator D) (o : O) :
    PartialTrace (naimarkP e o * (naimarkV Λ e * ρ * Matrix.conjTranspose (naimarkV Λ e)) * naimarkP e o)
      = (Λ.mats o ^ (1 / 2 : ℝ)).mat * ρ * (Λ.mats o ^ (1 / 2 : ℝ)).mat := by
  classical
  set W : Matrix (Fin D × Fin (Fintype.card O)) (Fin D × Fin (Fintype.card O)) ℂ
      := naimarkV Λ e * ρ * Matrix.conjTranspose (naimarkV Λ e) with hW
  set S : Matrix (Fin D) (Fin D) ℂ := (Λ.mats o ^ (1 / 2 : ℝ)).mat with hS
  have hSc : S.conjTranspose = S := by
    rw [hS, HermitianMat.conjTranspose_mat]
  ext i j
  show (∑ k : Fin (Fintype.card O),
      ((naimarkP e o * W * naimarkP e o) :
        Matrix (Fin D × Fin (Fintype.card O)) (Fin D × Fin (Fintype.card O)) ℂ) (i, k) (j, k))
    = (S * ρ * S) i j
  have hsum : (∑ k : Fin (Fintype.card O),
      ((naimarkP e o * W * naimarkP e o) :
        Matrix (Fin D × Fin (Fintype.card O)) (Fin D × Fin (Fintype.card O)) ℂ) (i, k) (j, k))
      = W (i, e o) (j, e o) := by
    rw [Finset.sum_eq_single (e o)]
    · rw [naimarkP_sandwich_apply]
      rw [if_pos ⟨rfl, rfl⟩]
    · intro k _ hk
      rw [naimarkP_sandwich_apply]
      rw [if_neg (fun ⟨hh, _⟩ => hk hh)]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  rw [hsum]
  have hV : ∀ a b : Fin D,
      naimarkV Λ e (a, e o) b = S a b := by
    intro a b
    simp only [naimarkV, hS]
    rw [e.symm_apply_apply o]
  have hT : W (i, e o) (j, e o) = (S * ρ * S.conjTranspose) i j := by
    rw [hW]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro w _
    rw [hV i w, hV j z]
  rw [hT, hSc]

theorem naimark_zero_effect_map {D : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    (Λ : POVM O (Fin D)) {o : O} (ho : (Λ.mats o).mat = 0) :
    (Instrument.ofPOVM Λ).branch o = 0 := by
  apply Instrument.ofPOVM_zero_effect_map
  apply HermitianMat.ext
  rw [ho, HermitianMat.mat_zero]

theorem g3 :
  (∀ (D : ℕ) (O : Type) (_ : Fintype O) (_ : DecidableEq O) (Λ : POVM O (Fin D)),
    ∃ (m : ℕ) (V : Matrix (Fin D × Fin m) (Fin D) ℂ)
      (P : O → Matrix (Fin D × Fin m) (Fin D × Fin m) ℂ),
      m ≤ Fintype.card O ∧
      NaimarkDilation Λ m V P ∧
      (∀ ψ : Fin D → ℂ, Normalized ψ → ∀ o : O,
        normSqVec (P o *ᵥ (V *ᵥ ψ)) = EffectStat ((Λ.mats o).mat) (outerProduct ψ)) ∧
      (∀ (R : ℕ) (X : Matrix (Fin R × Fin D) (Fin R × Fin D) ℂ) (o : O),
        Matrix.trace (refLeft (P o) R * refIsometryImage V R X)
          = Matrix.trace (refLeft ((Λ.mats o).mat) R * X)) ∧
      (∀ (ρ : Operator D) (o : O),
        PartialTrace (P o * (V * ρ * V.conjTranspose) * P o)
          = (Instrument.ofPOVM Λ).branch o ρ) ∧
      (∀ (ρ : Operator D) (o : O),
        instrumentProb (Instrument.ofPOVM Λ) ρ o = EffectStat ((Λ.mats o).mat) ρ) ∧
      (∀ o : O, (Λ.mats o).mat = 0 →
        (Instrument.ofPOVM Λ).branch o = 0 ∧
        ∀ ψ : Fin D → ℂ, normSqVec (P o *ᵥ (V *ᵥ ψ)) = 0)) ∧
  (∀ (D : ℕ) (S : Finset (Fin D)) (ψ : QState (Fin D)),
      0 < MeasureProb ψ S →
        outerProduct (PostMeasure ψ S)
          = (((MeasureProb ψ S : ℝ) : ℂ)⁻¹) • (Projector S * outerProduct ψ * Projector S)) ∧
  (∀ (D : ℕ) (S : Finset (Fin D)) (ψ : QState (Fin D)),
      MeasureProb ψ S = 0 →
        PostMeasure ψ S = 0 ∧ Projector S * outerProduct ψ * Projector S = 0) ∧
  (∃ (I₁ I₂ : Instrument (Fin 1) 2 2) (ρ : Operator 2) (o : Fin 1),
      (∀ (ρ' : Operator 2) (o' : Fin 1),
        instrumentProb I₁ ρ' o' = instrumentProb I₂ ρ' o') ∧
      I₁.branch o ρ ≠ I₂.branch o ρ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro D O _ _ Λ
    classical
    let e : O ≃ Fin (Fintype.card O) := Fintype.equivFin O
    refine ⟨Fintype.card O, naimarkV Λ e, naimarkP e, le_refl _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact naimark_dilation Λ e
    · intro ψ _ o
      exact naimark_born Λ e ψ o
    · intro R X o
      exact naimark_reference Λ e R X o
    · intro ρ o
      rw [Instrument.ofPOVM_branch]
      exact naimark_ptrace Λ e ρ o
    · intro ρ o
      exact instrumentProb_eq_effectStat Λ ρ o
    · intro o ho
      exact ⟨naimark_zero_effect_map Λ ho, naimarkP_V_zero_of_effect Λ e ho⟩
  · exact fun D S ψ h => postMeasure_outerProduct S ψ h
  · exact fun D S ψ h => postMeasure_zero_mass S ψ h
  · exact instrument_pair_same_stats
end Qatlib.Concepts.ChannelTheory.Naimark
