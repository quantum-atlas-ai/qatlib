/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.Fermion
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Concepts.MpsAdaptation.MpsTransfer.Fermion

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionExt

open Matrix
open scoped BigOperators
open Qatlib
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib

private theorem sum_single' {ι : Type} [Fintype ι] {β : Type} [AddCommMonoid β]
    (f : ι → β) (a : ι) (h : ∀ z, z ≠ a → f z = 0) :
    ∑ z : ι, f z = f a := by
  refine Finset.sum_eq_single a ?_ ?_
  · intro z _ hz
    exact h z hz
  · intro hcon
    exact (hcon (Finset.mem_univ a)).elim

def frameExtend {n : ℕ} (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  Matrix.of fun a b =>
    if isLocalMajorana i j a ∧ isLocalMajorana i j b then
      R (localSlot i j a) (localSlot i j b)
    else if a = b then 1 else 0

theorem frameExtend_apply_local {n : ℕ} (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ)
    (a b : Fin (2 * n)) (ha : isLocalMajorana i j a) (hb : isLocalMajorana i j b) :
    frameExtend i j R a b = R (localSlot i j a) (localSlot i j b) := by
  simp [frameExtend, ha, hb]

theorem frameExtend_apply_away {n : ℕ} (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ)
    (a b : Fin (2 * n)) (ha : ¬ isLocalMajorana i j a) (hb : ¬ isLocalMajorana i j b) :
    frameExtend i j R a b = if a = b then 1 else 0 := by
  simp [frameExtend, ha, hb]

theorem frameExtend_apply_left_local_right_away {n : ℕ} (i j : Fin n)
    (R : Matrix (Fin 4) (Fin 4) ℝ) (a c : Fin (2 * n))
    (ha : isLocalMajorana i j a) (hc : ¬ isLocalMajorana i j c) :
    frameExtend i j R a c = 0 := by
  have hne : a ≠ c := fun h => hc (h ▸ ha)
  simp [frameExtend, ha, hc, hne]

theorem frameExtend_apply_right_local_left_away {n : ℕ} (i j : Fin n)
    (R : Matrix (Fin 4) (Fin 4) ℝ) (a c : Fin (2 * n))
    (ha : ¬ isLocalMajorana i j a) (hc : isLocalMajorana i j c) :
    frameExtend i j R a c = 0 := by
  have hne : a ≠ c := fun h => ha (h ▸ hc)
  simp [frameExtend, ha, hc, hne]

theorem frameExtend_apply_away_neq {n : ℕ} (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ)
    (a b : Fin (2 * n)) (ha : ¬ isLocalMajorana i j a) (hb : ¬ isLocalMajorana i j b)
    (hne : a ≠ b) :
    frameExtend i j R a b = 0 := by
  simp [frameExtend, ha, hb, hne]

theorem frameExtend_apply_away_eq {n : ℕ} (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ)
    (a : Fin (2 * n)) (ha : ¬ isLocalMajorana i j a) :
    frameExtend i j R a a = 1 := by
  simp [frameExtend, ha]

theorem frameExtend_one {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    frameExtend i j (1 : Matrix (Fin 4) (Fin 4) ℝ) = 1 := by
  ext a b
  rw [Matrix.one_apply]
  by_cases hlab : isLocalMajorana i j a ∧ isLocalMajorana i j b
  · obtain ⟨ha, hb⟩ := hlab
    obtain ⟨p, rfl⟩ := exists_localIndices i j a ha
    obtain ⟨q, rfl⟩ := exists_localIndices i j b hb
    rw [frameExtend_apply_local i j 1 (localIndices i j p) (localIndices i j q)
      (isLocalMajorana_localIndices i j p) (isLocalMajorana_localIndices i j q),
      localSlot_localIndices i j hij p, localSlot_localIndices i j hij q,
      Matrix.one_apply]
    by_cases hpq : p = q
    · simp [hpq]
    · have hne : localIndices i j p ≠ localIndices i j q := fun h =>
        hpq (localIndices_inj i j hij p q h)
      simp [hpq, hne]
  · rcases not_and_or.mp hlab with ha | hb
    · by_cases hbb : isLocalMajorana i j b
      · rw [frameExtend_apply_right_local_left_away i j 1 a b ha hbb]
        have hne : a ≠ b := fun h => ha (h ▸ hbb)
        rw [if_neg hne]
      · rw [frameExtend_apply_away i j 1 a b ha hbb]
    · by_cases haa : isLocalMajorana i j a
      · rw [frameExtend_apply_left_local_right_away i j 1 a b haa hb]
        have hne : a ≠ b := fun h => hb (h ▸ haa)
        rw [if_neg hne]
      · rw [frameExtend_apply_away i j 1 a b haa hb]

def covarianceUpdateComplete {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  frameExtend i j R * Γ * (frameExtend i j R).transpose

theorem covarianceUpdateComplete_apply {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ) (a b : Fin (2 * n)) :
    covarianceUpdateComplete Γ i j R a b
      = ∑ c : Fin (2 * n), ∑ d : Fin (2 * n),
          frameExtend i j R a c * Γ c d * frameExtend i j R b d := by
  rw [covarianceUpdateComplete]
  calc (frameExtend i j R * Γ * (frameExtend i j R).transpose) a b
      = ∑ c : Fin (2 * n), (frameExtend i j R * Γ) a c * (frameExtend i j R).transpose c b :=
        Matrix.mul_apply ..
    _ = ∑ c : Fin (2 * n),
          (∑ d : Fin (2 * n), frameExtend i j R a d * Γ d c) * frameExtend i j R b c := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Matrix.mul_apply, Matrix.transpose_apply]
    _ = ∑ c : Fin (2 * n), ∑ d : Fin (2 * n),
          frameExtend i j R a d * Γ d c * frameExtend i j R b c := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ c : Fin (2 * n), ∑ d : Fin (2 * n),
          frameExtend i j R a c * Γ c d * frameExtend i j R b d := Finset.sum_comm

private theorem sum_inner_away {n : ℕ} (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ)
    (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (c b : Fin (2 * n))
    (hb : ¬ isLocalMajorana i j b) :
    ∑ d : Fin (2 * n), Γ c d * frameExtend i j R b d = Γ c b := by
  have h : ∀ d : Fin (2 * n), d ≠ b → Γ c d * frameExtend i j R b d = 0 := by
    intro d hdb
    by_cases hd : isLocalMajorana i j d
    · rw [frameExtend_apply_right_local_left_away i j R b d hb hd]
      simp
    · rw [frameExtend_apply_away_neq i j R b d hb hd (Ne.symm hdb)]
      simp
  calc ∑ d : Fin (2 * n), Γ c d * frameExtend i j R b d
      = Γ c b * frameExtend i j R b b := sum_single' _ b h
    _ = Γ c b := by rw [frameExtend_apply_away_eq i j R b hb, mul_one]

private theorem sum_inner_local {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (R : Matrix (Fin 4) (Fin 4) ℝ) (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (a : Fin (2 * n)) (q : Fin 4) :
    ∑ d : Fin (2 * n), Γ a d * frameExtend i j R (localIndices i j q) d
      = ∑ p : Fin 4, Γ a (localIndices i j p) * R q p := by
  have hzero : ∀ d : Fin (2 * n), ¬ isLocalMajorana i j d →
      Γ a d * frameExtend i j R (localIndices i j q) d = 0 := by
    intro d hd
    rw [frameExtend_apply_left_local_right_away i j R (localIndices i j q) d
      (isLocalMajorana_localIndices i j q) hd]
    simp
  rw [sum_localMajorana i j hij
    (fun d : Fin (2 * n) => Γ a d * frameExtend i j R (localIndices i j q) d) hzero]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [frameExtend_apply_local i j R (localIndices i j q) (localIndices i j p)
    (isLocalMajorana_localIndices i j q) (isLocalMajorana_localIndices i j p),
    localSlot_localIndices i j hij q, localSlot_localIndices i j hij p]

theorem covarianceUpdateComplete_cross {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (i j : Fin n) (hij : i ≠ j) (R : Matrix (Fin 4) (Fin 4) ℝ) (p : Fin 4)
    (b : Fin (2 * n)) (hb : ¬ isLocalMajorana i j b) :
    covarianceUpdateComplete Γ i j R (localIndices i j p) b
      = ∑ q : Fin 4, R p q * Γ (localIndices i j q) b := by
  have hstep : ∀ c : Fin (2 * n),
      (∑ d : Fin (2 * n),
          frameExtend i j R (localIndices i j p) c * Γ c d * frameExtend i j R b d)
        = frameExtend i j R (localIndices i j p) c * Γ c b := by
    intro c
    refine (sum_single' (fun d : Fin (2 * n) =>
      frameExtend i j R (localIndices i j p) c * Γ c d * frameExtend i j R b d) b ?_).trans ?_
    · intro d hdb
      have hS : frameExtend i j R b d = 0 := by
        by_cases hd : isLocalMajorana i j d
        · exact frameExtend_apply_right_local_left_away i j R b d hb hd
        · exact frameExtend_apply_away_neq i j R b d hb hd (Ne.symm hdb)
      simp only [hS]
      ring
    · rw [frameExtend_apply_away_eq i j R b hb]
      ring
  rw [covarianceUpdateComplete_apply Γ i j R (localIndices i j p) b,
    Finset.sum_congr rfl (fun c _ => hstep c)]
  have hzero : ∀ c : Fin (2 * n), ¬ isLocalMajorana i j c →
      frameExtend i j R (localIndices i j p) c * Γ c b = 0 := by
    intro c hc
    rw [frameExtend_apply_left_local_right_away i j R (localIndices i j p) c
      (isLocalMajorana_localIndices i j p) hc]
    simp
  rw [sum_localMajorana i j hij
    (fun c : Fin (2 * n) => frameExtend i j R (localIndices i j p) c * Γ c b) hzero]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [frameExtend_apply_local i j R (localIndices i j p) (localIndices i j q)
    (isLocalMajorana_localIndices i j p) (isLocalMajorana_localIndices i j q),
    localSlot_localIndices i j hij p, localSlot_localIndices i j hij q]

theorem covarianceUpdateComplete_cross' {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (i j : Fin n) (hij : i ≠ j) (R : Matrix (Fin 4) (Fin 4) ℝ)
    (a : Fin (2 * n)) (ha : ¬ isLocalMajorana i j a) (q : Fin 4) :
    covarianceUpdateComplete Γ i j R a (localIndices i j q)
      = ∑ p : Fin 4, Γ a (localIndices i j p) * R q p := by
  have h : ∀ c : Fin (2 * n), c ≠ a →
      (∑ d : Fin (2 * n),
          frameExtend i j R a c * Γ c d * frameExtend i j R (localIndices i j q) d) = 0 := by
    intro c hca
    by_cases hc : isLocalMajorana i j c
    · rw [frameExtend_apply_right_local_left_away i j R a c ha hc]
      simp
    · rw [frameExtend_apply_away_neq i j R a c ha hc (Ne.symm hca)]
      simp
  rw [covarianceUpdateComplete_apply Γ i j R a (localIndices i j q)]
  calc ∑ c : Fin (2 * n), ∑ d : Fin (2 * n),
        frameExtend i j R a c * Γ c d * frameExtend i j R (localIndices i j q) d
      = (∑ d : Fin (2 * n),
          frameExtend i j R a a * Γ a d * frameExtend i j R (localIndices i j q) d) :=
        sum_single' _ a h
    _ = ∑ d : Fin (2 * n), Γ a d * frameExtend i j R (localIndices i j q) d := by
        simp only [frameExtend_apply_away_eq i j R a ha, one_mul]
    _ = ∑ p : Fin 4, Γ a (localIndices i j p) * R q p := sum_inner_local i j hij R Γ a q

theorem covarianceUpdateComplete_away {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (i j : Fin n) (R : Matrix (Fin 4) (Fin 4) ℝ) (a b : Fin (2 * n))
    (ha : ¬ isLocalMajorana i j a) (hb : ¬ isLocalMajorana i j b) :
    covarianceUpdateComplete Γ i j R a b = Γ a b := by
  have h : ∀ c : Fin (2 * n), c ≠ a →
      (∑ d : Fin (2 * n),
          frameExtend i j R a c * Γ c d * frameExtend i j R b d) = 0 := by
    intro c hca
    by_cases hc : isLocalMajorana i j c
    · rw [frameExtend_apply_right_local_left_away i j R a c ha hc]
      simp
    · rw [frameExtend_apply_away_neq i j R a c ha hc (Ne.symm hca)]
      simp
  rw [covarianceUpdateComplete_apply Γ i j R a b]
  calc ∑ c : Fin (2 * n), ∑ d : Fin (2 * n),
        frameExtend i j R a c * Γ c d * frameExtend i j R b d
      = (∑ d : Fin (2 * n), frameExtend i j R a a * Γ a d * frameExtend i j R b d) :=
        sum_single' _ a h
    _ = ∑ d : Fin (2 * n), Γ a d * frameExtend i j R b d := by
        simp only [frameExtend_apply_away_eq i j R a ha, one_mul]
    _ = Γ a b := sum_inner_away i j R Γ a b hb

theorem covarianceUpdateComplete_local {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (i j : Fin n) (hij : i ≠ j) (R : Matrix (Fin 4) (Fin 4) ℝ) (p q : Fin 4) :
    covarianceUpdateComplete Γ i j R (localIndices i j p) (localIndices i j q)
      = (R * localBlock Γ i j * R.transpose) p q := by
  rw [covarianceUpdateComplete_apply Γ i j R (localIndices i j p) (localIndices i j q),
    mul_congruence_apply R (localBlock Γ i j) p q]
  have hstep : ∀ c : Fin (2 * n),
      (∑ d : Fin (2 * n),
          frameExtend i j R (localIndices i j p) c * Γ c d
            * frameExtend i j R (localIndices i j q) d)
        = frameExtend i j R (localIndices i j p) c
          * ∑ d' : Fin 4, Γ c (localIndices i j d') * R q d' := by
    intro c
    have hassoc : ∀ d : Fin (2 * n),
        (frameExtend i j R (localIndices i j p) c * Γ c d
            * frameExtend i j R (localIndices i j q) d)
          = frameExtend i j R (localIndices i j p) c
            * (Γ c d * frameExtend i j R (localIndices i j q) d) := fun d => by ring
    rw [Finset.sum_congr rfl (fun d _ => hassoc d), ← Finset.mul_sum,
      sum_inner_local i j hij R Γ c q]
  rw [Finset.sum_congr rfl (fun c _ => hstep c)]
  have hzero : ∀ c : Fin (2 * n), ¬ isLocalMajorana i j c →
      (frameExtend i j R (localIndices i j p) c
        * ∑ d' : Fin 4, Γ c (localIndices i j d') * R q d') = 0 := by
    intro c hc
    rw [frameExtend_apply_left_local_right_away i j R (localIndices i j p) c
      (isLocalMajorana_localIndices i j p) hc]
    simp
  rw [sum_localMajorana i j hij
    (fun c : Fin (2 * n) => frameExtend i j R (localIndices i j p) c
      * ∑ d' : Fin 4, Γ c (localIndices i j d') * R q d') hzero]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [frameExtend_apply_local i j R (localIndices i j p) (localIndices i j c')
    (isLocalMajorana_localIndices i j p) (isLocalMajorana_localIndices i j c'),
    localSlot_localIndices i j hij p, localSlot_localIndices i j hij c',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [localBlock, Matrix.of_apply]
  ring

theorem localBlock_covarianceUpdateComplete {n : ℕ}
    (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (i j : Fin n) (hij : i ≠ j)
    (R : Matrix (Fin 4) (Fin 4) ℝ) :
    localBlock (covarianceUpdateComplete Γ i j R) i j
      = R * localBlock Γ i j * R.transpose := by
  ext p q
  simpa only [localBlock, Matrix.of_apply] using!
    covarianceUpdateComplete_local Γ i j hij R p q

theorem covarianceUpdateComplete_antisymm {n : ℕ}
    (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (i j : Fin n)
    (R : Matrix (Fin 4) (Fin 4) ℝ) (hΓ : ∀ a b : Fin (2 * n), Γ b a = -Γ a b)
    (a b : Fin (2 * n)) :
    covarianceUpdateComplete Γ i j R b a = -covarianceUpdateComplete Γ i j R a b :=
  mul_congruence_antisymm (frameExtend i j R) Γ hΓ a b

theorem covarianceUpdateComplete_one {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (i j : Fin n) (hij : i ≠ j) :
    covarianceUpdateComplete Γ i j (1 : Matrix (Fin 4) (Fin 4) ℝ) = Γ := by
  rw [covarianceUpdateComplete, frameExtend_one i j hij, Matrix.one_mul,
    Matrix.transpose_one, Matrix.mul_one]

theorem frameExtend_localRotation {n : ℕ} (i j : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    frameExtend i j (localRotation A) = frameRotation i j A := by
  ext a b
  by_cases ha : isLocalMajorana i j a
  · by_cases hb : isLocalMajorana i j b
    · rw [frameExtend_apply_local i j (localRotation A) a b ha hb,
        frameRotation_apply_local i j A a b ha hb]
    · rw [frameExtend_apply_left_local_right_away i j (localRotation A) a b ha hb]
      exact (frameRotation_apply_left_local_right_away i j A a b ha hb).symm
  · by_cases hb : isLocalMajorana i j b
    · rw [frameExtend_apply_right_local_left_away i j (localRotation A) a b ha hb]
      exact (frameRotation_apply_right_local_left_away i j A a b ha hb).symm
    · rw [frameExtend_apply_away i j (localRotation A) a b ha hb]
      exact (frameRotation_apply_away i j A a b ha hb).symm

theorem covarianceMatrix_matchGate_eq_complete {n : ℕ} (i j : Fin n)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : Aᴴ = -A) (M : Matrix (Reg n) (Reg n) ℂ)
    (hS : ∀ a : Fin (2 * n),
      (matchGate i j A)ᴴ * majorana a * (matchGate i j A)
        = majoranaInBasis (frameRotation i j A) a) :
    covarianceMatrix (matchGate i j A * M)
      = covarianceUpdateComplete (covarianceMatrix M) i j (localRotation A) := by
  rw [covarianceUpdateComplete, frameExtend_localRotation]
  exact matchGate_covariance_congruence i j A hA M (frameRotation i j A) hS

def matchGateBridged {n : ℕ} (g : Fin n × Fin n × Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  g.2.2ᴴ = -(g.2.2) ∧ ∀ a : Fin (2 * n),
    (matchGate g.1 g.2.1 g.2.2)ᴴ * majorana a * (matchGate g.1 g.2.1 g.2.2)
      = majoranaInBasis (frameRotation g.1 g.2.1 g.2.2) a

def covarianceRun {n : ℕ} : MatchGateCircuit n
    → Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ → Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ
  | [], Γ => Γ
  | (i, j, A) :: rest, Γ =>
      covarianceUpdateComplete (covarianceRun rest Γ) i j (localRotation A)

theorem covarianceMatrix_matchGateCircuit_of_bridged {n : ℕ} (gl : MatchGateCircuit n)
    (h : ∀ g ∈ gl, matchGateBridged g) (M : Matrix (Reg n) (Reg n) ℂ) :
    covarianceMatrix (matchGateCircuitOp gl * M)
      = covarianceRun gl (covarianceMatrix M) := by
  induction gl generalizing M with
  | nil =>
      show covarianceMatrix ((1 : Matrix (Reg n) (Reg n) ℂ) * M) = covarianceMatrix M
      rw [Matrix.one_mul]
  | cons g rest ih =>
      obtain ⟨i, j, A⟩ := g
      have hg := h (i, j, A) (List.mem_cons_self)
      have hrest : ∀ q ∈ rest, matchGateBridged q := fun q hq =>
        h q (List.mem_cons_of_mem _ hq)
      show covarianceMatrix (matchGate i j A * matchGateCircuitOp rest * M) = _
      rw [Matrix.mul_assoc,
        covarianceMatrix_matchGate_eq_complete i j A hg.1 _ hg.2, ih hrest, covarianceRun]

def covarianceUpdateCompleteOps (n : ℕ) : ℕ := 16 * n + 64

def covarianceRunOps {n : ℕ} (gl : MatchGateCircuit n) : ℕ :=
  matchGateCount gl * covarianceUpdateCompleteOps n

theorem covarianceRunOps_le {n : ℕ} (gl : MatchGateCircuit n) :
    covarianceRunOps gl ≤ (16 * n + 64) * matchGateCount gl := by
  rw [covarianceRunOps,
    Nat.mul_comm (matchGateCount gl) (covarianceUpdateCompleteOps n)]
  exact Nat.le_refl _

def isModeMajorana {n : ℕ} (k : Fin n) (a : Fin (2 * n)) : Prop :=
  a = majoranaIndices k 0 ∨ a = majoranaIndices k 1

instance isModeMajoranaDecidable {n : ℕ} (k : Fin n) (a : Fin (2 * n)) :
    Decidable (isModeMajorana k a) := by
  unfold isModeMajorana
  infer_instance

def measurementProjector {n : ℕ} (k : Fin n) (b : Bool) : Matrix (Reg n) (Reg n) ℂ :=
  if b then numberOp k else 1 - numberOp k

def bornWeight {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ) (k : Fin n) (b : Bool) : ℝ :=
  (Matrix.trace ((measurementProjector k b * M)ᴴ * (measurementProjector k b * M))).re

def measurementUpdate {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (k : Fin n)
    (b : Bool) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  Matrix.of fun a c =>
    if a = majoranaIndices k 0 ∧ c = majoranaIndices k 1 then (if b then -1 else 1)
    else if a = majoranaIndices k 1 ∧ c = majoranaIndices k 0 then (if b then 1 else -1)
    else if isModeMajorana k a ∨ isModeMajorana k c then 0
    else Γ a c

theorem numberOp_mul_numberOp {n : ℕ} (k : Fin n) :
    numberOp k * numberOp k = numberOp k := by
  rw [numberOp_eq_diagonal k, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  by_cases hx : x k <;> simp [hx]

theorem measurementProjector_idem {n : ℕ} (k : Fin n) (b : Bool) :
    measurementProjector k b * measurementProjector k b = measurementProjector k b := by
  cases b with
  | false =>
      show (1 - numberOp k) * (1 - numberOp k) = 1 - numberOp k
      calc (1 - numberOp k) * (1 - numberOp k)
          = 1 * (1 - numberOp k) - numberOp k * (1 - numberOp k) := sub_mul _ _ _
        _ = (1 * 1 - 1 * numberOp k) - (numberOp k * 1 - numberOp k * numberOp k) := by
            rw [mul_sub, mul_sub]
        _ = 1 - numberOp k := by
            rw [one_mul, one_mul, mul_one, numberOp_mul_numberOp k, sub_self, sub_zero]
  | true =>
      show numberOp k * numberOp k = numberOp k
      exact numberOp_mul_numberOp k

theorem measurementProjector_hermitian {n : ℕ} (k : Fin n) (b : Bool) :
    (measurementProjector k b)ᴴ = measurementProjector k b := by
  cases b with
  | false =>
      show (1 - numberOp k)ᴴ = 1 - numberOp k
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, numberOp_hermitian]
  | true =>
      show (numberOp k)ᴴ = numberOp k
      exact numberOp_hermitian k

theorem measurementProjector_add {n : ℕ} (k : Fin n) :
    measurementProjector k false + measurementProjector k true = 1 := by
  show (1 - numberOp k) + numberOp k = 1
  rw [sub_add_cancel]

theorem measurementProjector_apply {n : ℕ} (k : Fin n) (b : Bool) (y x : Reg n) :
    measurementProjector k b y x = if x = y ∧ x k = b then 1 else 0 := by
  cases b with
  | false =>
      show (1 - numberOp k) y x = if x = y ∧ x k = false then 1 else 0
      rw [Matrix.sub_apply, Matrix.one_apply, numberOp, Matrix.of_apply]
      by_cases hxy : x = y
      · subst hxy
        by_cases hx : x k <;> simp [hx]
      · simp [hxy, Ne.symm hxy]
  | true =>
      show numberOp k y x = if x = y ∧ x k = true then 1 else 0
      rfl

theorem measurementProjector_eq_diagonal {n : ℕ} (k : Fin n) (b : Bool) :
    measurementProjector k b
      = Matrix.diagonal (fun x : Reg n => if x k = b then (1 : ℂ) else 0) := by
  ext y x
  rw [measurementProjector_apply k b y x]
  by_cases hxy : x = y
  · subst hxy
    rw [Matrix.diagonal_apply_eq]
    by_cases hx : x k = b <;> simp [hx]
  · rw [Matrix.diagonal_apply_ne _ (fun h => hxy h.symm)]
    have : ¬ (x = y ∧ x k = b) := by intro hh; exact hxy hh.1
    rw [if_neg this]

theorem annihilation_apply_of_bit_eq {n : ℕ} (k : Fin n) {y x : Reg n} (h : y k = x k) :
    annihilation k y x = 0 := by
  rw [annihilation, Matrix.of_apply]
  by_cases hcond : x k ∧ y = Function.update x k false
  · exfalso
    rw [hcond.2] at h
    rw [Function.update_self] at h
    exact Bool.noConfusion (h.trans hcond.1)
  · rw [if_neg hcond]

theorem creation_apply_of_bit_eq {n : ℕ} (k : Fin n) {y x : Reg n} (h : y k = x k) :
    creation k y x = 0 := by
  rw [creation, Matrix.of_apply]
  by_cases hcond : ¬ x k ∧ y = Function.update x k true
  · exfalso
    rw [hcond.2] at h
    rw [Function.update_self] at h
    exact hcond.1 h.symm
  · rw [if_neg hcond]

theorem majoranaEven_apply_ne_zero {n : ℕ} (k : Fin n) {y x : Reg n}
    (h : majoranaEven k y x ≠ 0) : y k ≠ x k := by
  intro heq
  rw [majoranaEven, Matrix.add_apply, annihilation_apply_of_bit_eq k heq,
      creation_apply_of_bit_eq k heq] at h
  simp at h

theorem majoranaOdd_apply_ne_zero {n : ℕ} (k : Fin n) {y x : Reg n}
    (h : majoranaOdd k y x ≠ 0) : y k ≠ x k := by
  intro heq
  rw [majoranaOdd, Matrix.smul_apply, Matrix.sub_apply,
      annihilation_apply_of_bit_eq k heq, creation_apply_of_bit_eq k heq] at h
  simp at h

theorem numberOp_mul_annihilation_of_ne {n : ℕ} (k m : Fin n) (hkm : k ≠ m) :
    numberOp k * annihilation m = annihilation m * numberOp k := by
  have h1 : annihilation k * annihilation m = -(annihilation m * annihilation k) :=
    eq_neg_of_add_eq_zero_left (car_ann n k m)
  have h2 : creation k * annihilation m = -(annihilation m * creation k) := by
    have haa := car_aa n m k
    rw [if_neg (Ne.symm hkm)] at haa
    exact eq_neg_of_add_eq_zero_right haa
  calc numberOp k * annihilation m
      = creation k * annihilation k * annihilation m := by
          rw [creation_mul_annihilation_eq_numberOp k]
    _ = creation k * (annihilation k * annihilation m) := by rw [Matrix.mul_assoc]
    _ = creation k * (-(annihilation m * annihilation k)) := by rw [h1]
    _ = -(creation k * (annihilation m * annihilation k)) := by rw [mul_neg]
    _ = -(creation k * annihilation m * annihilation k) := by rw [← Matrix.mul_assoc]
    _ = -(-(annihilation m * creation k) * annihilation k) := by rw [← h2]
    _ = annihilation m * numberOp k := by
        rw [neg_mul, neg_neg, Matrix.mul_assoc, ← creation_mul_annihilation_eq_numberOp k]

theorem numberOp_mul_creation_of_ne {n : ℕ} (k m : Fin n) (hkm : k ≠ m) :
    numberOp k * creation m = creation m * numberOp k := by
  have h1 : annihilation k * creation m = -(creation m * annihilation k) := by
    have haa := car_aa n k m
    rw [if_neg hkm] at haa
    exact eq_neg_of_add_eq_zero_left haa
  have h2 : creation k * creation m = -(creation m * creation k) :=
    eq_neg_of_add_eq_zero_left (car_cre n k m)
  calc numberOp k * creation m
      = creation k * annihilation k * creation m := by
          rw [creation_mul_annihilation_eq_numberOp k]
    _ = creation k * (annihilation k * creation m) := by rw [Matrix.mul_assoc]
    _ = creation k * (-(creation m * annihilation k)) := by rw [h1]
    _ = -(creation k * (creation m * annihilation k)) := by rw [mul_neg]
    _ = -(creation k * creation m * annihilation k) := by rw [← Matrix.mul_assoc]
    _ = -(-(creation m * creation k) * annihilation k) := by rw [← h2]
    _ = creation m * numberOp k := by
        rw [neg_mul, neg_neg, Matrix.mul_assoc, ← creation_mul_annihilation_eq_numberOp k]

theorem measurementProjector_mul_creation_of_ne {n : ℕ} (k m : Fin n) (hkm : k ≠ m)
    (b : Bool) :
    measurementProjector k b * creation m = creation m * measurementProjector k b := by
  cases b with
  | true =>
      show numberOp k * creation m = creation m * numberOp k
      exact numberOp_mul_creation_of_ne k m hkm
  | false =>
      show (1 - numberOp k) * creation m = creation m * (1 - numberOp k)
      rw [one_sub_mul, mul_one_sub, numberOp_mul_creation_of_ne k m hkm]

theorem measurementProjector_mul_annihilation_of_ne {n : ℕ} (k m : Fin n) (hkm : k ≠ m)
    (b : Bool) :
    measurementProjector k b * annihilation m = annihilation m * measurementProjector k b := by
  cases b with
  | true =>
      show numberOp k * annihilation m = annihilation m * numberOp k
      exact numberOp_mul_annihilation_of_ne k m hkm
  | false =>
      show (1 - numberOp k) * annihilation m = annihilation m * (1 - numberOp k)
      rw [one_sub_mul, mul_one_sub, numberOp_mul_annihilation_of_ne k m hkm]

theorem measurementProjector_mul_majoranaEven_of_ne {n : ℕ} (k m : Fin n) (hkm : k ≠ m)
    (b : Bool) :
    measurementProjector k b * majoranaEven m
      = majoranaEven m * measurementProjector k b := by
  show measurementProjector k b * (creation m + annihilation m)
      = (creation m + annihilation m) * measurementProjector k b
  rw [mul_add, add_mul, measurementProjector_mul_creation_of_ne k m hkm,
      measurementProjector_mul_annihilation_of_ne k m hkm]

theorem measurementProjector_mul_majoranaOdd_of_ne {n : ℕ} (k m : Fin n) (hkm : k ≠ m)
    (b : Bool) :
    measurementProjector k b * majoranaOdd m
      = majoranaOdd m * measurementProjector k b := by
  show measurementProjector k b * (Complex.I • (annihilation m - creation m))
      = (Complex.I • (annihilation m - creation m)) * measurementProjector k b
  rw [Matrix.mul_smul, mul_sub, Matrix.smul_mul, sub_mul,
      measurementProjector_mul_annihilation_of_ne k m hkm,
      measurementProjector_mul_creation_of_ne k m hkm]

theorem majoranaIndices_val {n : ℕ} (k : Fin n) (b : Fin 2) :
    (majoranaIndices k b).val = 2 * k.val + b.val := rfl

private theorem isModeMajorana_of_val {n : ℕ} {k : Fin n} {c : Fin (2 * n)}
    (hdv : c.val / 2 = k.val) (hpar : c.val % 2 = 0 ∨ c.val % 2 = 1) :
    isModeMajorana k c := by
  obtain hpar | hpar := hpar
  · left
    apply Fin.ext
    simp only [majoranaIndices_val, Fin.val_zero]
    omega
  · right
    apply Fin.ext
    simp only [majoranaIndices_val]
    have h1v : (1 : Fin 2).val = 1 := by decide
    rw [h1v]
    omega

theorem measurementProjector_mul_majorana_of_not_mode {n : ℕ} (k : Fin n) (b : Bool)
    {c : Fin (2 * n)} (hc : ¬ isModeMajorana k c) :
    measurementProjector k b * majorana c = majorana c * measurementProjector k b := by
  rw [majorana_eq_flavour n c]
  by_cases hpar : c.val % 2 = 0
  · rw [if_pos hpar]
    refine measurementProjector_mul_majoranaEven_of_ne k ⟨c.val / 2, by omega⟩ ?_ b
    intro heq
    exact hc (isModeMajorana_of_val (by simpa using! (congrArg Fin.val heq).symm)
      (Or.inl hpar))
  · rw [if_neg hpar]
    refine measurementProjector_mul_majoranaOdd_of_ne k ⟨c.val / 2, by omega⟩ ?_ b
    intro heq
    exact hc (isModeMajorana_of_val (by simpa using! (congrArg Fin.val heq).symm)
      (Or.inr (by omega)))

theorem trace_sandwich_projector {n : ℕ} (P M X : Matrix (Reg n) (Reg n) ℂ)
    (hP : Pᴴ = P) :
    Matrix.trace ((P * M)ᴴ * X * (P * M))
      = Matrix.trace (Mᴴ * (P * X * P) * M) := by
  rw [Matrix.conjTranspose_mul, hP]
  simp only [Matrix.mul_assoc]

theorem covarianceMatrix_projector_apply {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ)
    (P : Matrix (Reg n) (Reg n) ℂ) (hP : Pᴴ = P) (a b : Fin (2 * n)) :
    covarianceMatrix (P * M) a b
      = Complex.re ((Complex.I / 2) * Matrix.trace
          (Mᴴ * (P * (majorana a * majorana b - majorana b * majorana a) * P) * M)) := by
  show Complex.re ((Complex.I / 2) * Matrix.trace
      ((P * M)ᴴ * (majorana a * majorana b - majorana b * majorana a) * (P * M))) = _
  rw [trace_sandwich_projector P M _ hP]

theorem measurementProjector_mul_majoranaMul {n : ℕ} (k : Fin n) (b : Bool)
    {γ : Matrix (Reg n) (Reg n) ℂ}
    (hsupp : ∀ y x : Reg n, γ y x ≠ 0 → y k ≠ x k) :
    measurementProjector k b * γ * measurementProjector k b = 0 := by
  rw [measurementProjector_eq_diagonal k b]
  ext y x
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
    mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.zero_apply]
  by_cases hyx : y k = x k
  · have h0 : γ y x = 0 := by
      by_contra h
      exact hsupp y x h hyx
    simp [h0]
  · by_cases hy : y k = b
    · have hx : ¬ (x k = b) := fun h => hyx (hy.trans h.symm)
      simp [hx]
    · simp [hy]

theorem measurementProjector_mul_majoranaEven_mul {n : ℕ} (k : Fin n) (b : Bool) :
    measurementProjector k b * majoranaEven k * measurementProjector k b = 0 :=
  measurementProjector_mul_majoranaMul k b
    (fun _ _ h => majoranaEven_apply_ne_zero k h)

theorem measurementProjector_mul_majoranaOdd_mul {n : ℕ} (k : Fin n) (b : Bool) :
    measurementProjector k b * majoranaOdd k * measurementProjector k b = 0 :=
  measurementProjector_mul_majoranaMul k b
    (fun _ _ h => majoranaOdd_apply_ne_zero k h)

theorem majorana_commutator_mode {n : ℕ} (k : Fin n) :
    majorana (majoranaIndices k 0) * majorana (majoranaIndices k 1)
      - majorana (majoranaIndices k 1) * majorana (majoranaIndices k 0)
      = (2 : ℂ) • (Complex.I • (numberOp k + numberOp k - 1)) := by
  rw [majorana_even_index, majorana_odd_index,
    majoranaEven_majoranaOdd, majoranaOdd_majoranaEven, ← smul_sub]
  have hz : (numberOp k + numberOp k - 1) - (1 - numberOp k - numberOp k)
      = (numberOp k + numberOp k - 1) + (numberOp k + numberOp k - 1) := by
    noncomm_ring
  rw [hz, smul_add, ← two_smul (ℂ) (Complex.I • (numberOp k + numberOp k - 1))]

theorem numberOp_mul_twoSubOne {n : ℕ} (k : Fin n) :
    numberOp k * (numberOp k + numberOp k - 1) = numberOp k
      ∧ (numberOp k + numberOp k - 1) * numberOp k = numberOp k := by
  constructor
  · rw [mul_sub, mul_add, numberOp_mul_numberOp k, mul_one]
    abel
  · rw [sub_mul, add_mul, numberOp_mul_numberOp k, one_mul]
    abel

theorem measurementProjector_mul_numberPoly {n : ℕ} (k : Fin n) (b : Bool) :
    measurementProjector k b * (numberOp k + numberOp k - 1)
      = (numberOp k + numberOp k - 1) * measurementProjector k b := by
  have h1 := (numberOp_mul_twoSubOne k).1
  have h2 := (numberOp_mul_twoSubOne k).2
  cases b with
  | true =>
      show numberOp k * (numberOp k + numberOp k - 1)
          = (numberOp k + numberOp k - 1) * numberOp k
      rw [h1, h2]
  | false =>
      show (1 - numberOp k) * (numberOp k + numberOp k - 1)
          = (numberOp k + numberOp k - 1) * (1 - numberOp k)
      rw [one_sub_mul, mul_one_sub, h1, h2]

theorem measurementProjector_commutator_sandwich {n : ℕ} (k : Fin n) (b : Bool) :
    measurementProjector k b * ((2 : ℂ) • (Complex.I • (numberOp k + numberOp k - 1)))
        * measurementProjector k b
      = (2 : ℂ) • (Complex.I • ((numberOp k + numberOp k - 1) * measurementProjector k b)) := by
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    measurementProjector_mul_numberPoly k b, Matrix.mul_assoc,
    measurementProjector_idem k b]

private theorem half_two_I_mul (T : ℂ) :
    (Complex.I / 2) * (2 * (Complex.I * T)) = -T := by
  have hI : (Complex.I / 2) * 2 = Complex.I := by norm_num
  rw [← mul_assoc, ← mul_assoc, hI, Complex.I_mul_I, neg_one_mul]

theorem measurementProjector_mul_mode_majorana_mul {n : ℕ} (k : Fin n) (b : Bool)
    {a : Fin (2 * n)} (ha : isModeMajorana k a) :
    measurementProjector k b * majorana a * measurementProjector k b = 0 := by
  obtain ha | ha := ha
  · rw [ha, majorana_even_index]
    exact measurementProjector_mul_majoranaEven_mul k b
  · rw [ha, majorana_odd_index]
    exact measurementProjector_mul_majoranaOdd_mul k b

theorem covarianceMatrix_measurement_cross {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ)
    (k : Fin n) (b : Bool) {a c : Fin (2 * n)}
    (ha : isModeMajorana k a) (hc : ¬ isModeMajorana k c) :
    covarianceMatrix (measurementProjector k b * M) a c = 0 := by
  rw [covarianceMatrix_projector_apply M (measurementProjector k b)
    (measurementProjector_hermitian k b) a c]
  have hcomm : measurementProjector k b * majorana c
      = majorana c * measurementProjector k b :=
    measurementProjector_mul_majorana_of_not_mode k b hc
  have h1 : measurementProjector k b * majorana a * measurementProjector k b = 0 :=
    measurementProjector_mul_mode_majorana_mul k b ha
  have e1 : measurementProjector k b * (majorana a * majorana c)
      * measurementProjector k b = 0 := by
    simp only [Matrix.mul_assoc]
    rw [← hcomm,
      ← Matrix.mul_assoc (measurementProjector k b) (majorana a)
        (measurementProjector k b * majorana c),
      ← Matrix.mul_assoc (measurementProjector k b * majorana a)
        (measurementProjector k b) (majorana c),
      h1, zero_mul]
  have e2 : measurementProjector k b * (majorana c * majorana a)
      * measurementProjector k b = 0 := by
    rw [← Matrix.mul_assoc (measurementProjector k b) (majorana c) (majorana a), hcomm]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (measurementProjector k b) (majorana a)
      (measurementProjector k b), h1, mul_zero]
  rw [mul_sub, sub_mul, e1, e2, sub_zero, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.trace_zero, mul_zero, Complex.zero_re]

theorem bornWeight_true {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ) (k : Fin n) :
    bornWeight M k true = (Matrix.trace (Mᴴ * numberOp k * M)).re := by
  show (Matrix.trace ((numberOp k * M)ᴴ * (numberOp k * M))).re = _
  have h : (numberOp k * M)ᴴ * (numberOp k * M) = Mᴴ * numberOp k * M := by
    rw [Matrix.conjTranspose_mul, numberOp_hermitian]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (numberOp k) (numberOp k) M, numberOp_mul_numberOp k]
  rw [h]

theorem bornWeight_false {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ) (k : Fin n) :
    bornWeight M k false
      = (Matrix.trace (Mᴴ * ((1 : Matrix (Reg n) (Reg n) ℂ) - numberOp k) * M)).re := by
  show (Matrix.trace ((((1 : Matrix (Reg n) (Reg n) ℂ) - numberOp k) * M)ᴴ
      * (((1 : Matrix (Reg n) (Reg n) ℂ) - numberOp k) * M))).re = _
  have h : (((1 : Matrix (Reg n) (Reg n) ℂ) - numberOp k) * M)ᴴ
      * (((1 : Matrix (Reg n) (Reg n) ℂ) - numberOp k) * M)
      = Mᴴ * ((1 : Matrix (Reg n) (Reg n) ℂ) - numberOp k) * M := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      numberOp_hermitian]
    simp only [Matrix.mul_assoc]
    have hidem : ((1 : Matrix (Reg n) (Reg n) ℂ) - numberOp k)
        * ((1 : Matrix (Reg n) (Reg n) ℂ) - numberOp k)
        = (1 : Matrix (Reg n) (Reg n) ℂ) - numberOp k :=
      measurementProjector_idem k false
    rw [← Matrix.mul_assoc ((1 : Matrix (Reg n) (Reg n) ℂ) - numberOp k)
        ((1 : Matrix (Reg n) (Reg n) ℂ) - numberOp k) M, hidem]
  rw [h]

theorem bornWeight_split {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ) (k : Fin n) :
    bornWeight M k false + bornWeight M k true
      = (Matrix.trace (Mᴴ * M)).re := by
  rw [bornWeight_false, bornWeight_true, ← Complex.add_re, ← Matrix.trace_add,
    ← add_mul, ← mul_add, sub_add_cancel, mul_one]

theorem bornWeight_from_covariance {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ) (k : Fin n) :
    2 * bornWeight M k true
      = (Matrix.trace (Mᴴ * M)).re
        - covarianceMatrix M (majoranaIndices k 0) (majoranaIndices k 1) := by
  rw [bornWeight_true, covarianceMatrix_occupation M k]
  linarith

theorem covarianceMatrix_measurement_local {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ)
    (k : Fin n) (b : Bool) :
    covarianceMatrix (measurementProjector k b * M) (majoranaIndices k 0) (majoranaIndices k 1)
      = (if b then (-1 : ℝ) else 1) * bornWeight M k b := by
  cases b with
  | true =>
      show covarianceMatrix (measurementProjector k true * M) (majoranaIndices k 0)
          (majoranaIndices k 1) = (-1 : ℝ) * bornWeight M k true
      rw [covarianceMatrix_projector_apply M (measurementProjector k true)
        (measurementProjector_hermitian k true) (majoranaIndices k 0) (majoranaIndices k 1),
        majorana_commutator_mode k, measurementProjector_commutator_sandwich k true,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul,
        half_two_I_mul, Complex.neg_re]
      have hPP : (numberOp k + numberOp k - 1) * measurementProjector k true
          = numberOp k := (numberOp_mul_twoSubOne k).2
      rw [hPP, bornWeight_true, neg_one_mul]
  | false =>
      show covarianceMatrix (measurementProjector k false * M) (majoranaIndices k 0)
          (majoranaIndices k 1) = (1 : ℝ) * bornWeight M k false
      rw [covarianceMatrix_projector_apply M (measurementProjector k false)
        (measurementProjector_hermitian k false) (majoranaIndices k 0) (majoranaIndices k 1),
        majorana_commutator_mode k, measurementProjector_commutator_sandwich k false,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul,
        half_two_I_mul, Complex.neg_re]
      have hPP : (numberOp k + numberOp k - 1) * measurementProjector k false
          = numberOp k - 1 := by
        show (numberOp k + numberOp k - 1)
            * ((1 : Matrix (Reg n) (Reg n) ℂ) - numberOp k) = numberOp k - 1
        rw [mul_one_sub, (numberOp_mul_twoSubOne k).2]
        abel
      have hneg : numberOp k - 1
          = -((1 : Matrix (Reg n) (Reg n) ℂ) - numberOp k) := by rw [neg_sub]
      rw [hPP, hneg, Matrix.mul_neg, Matrix.neg_mul, Matrix.trace_neg, Complex.neg_re,
        neg_neg, bornWeight_false, one_mul]

private theorem commute_P_product {n : ℕ} (P γa γc : Matrix (Reg n) (Reg n) ℂ)
    (hca : P * γa = γa * P) (hcc : P * γc = γc * P) :
    P * (γa * γc) = (γa * γc) * P := by
  rw [← Matrix.mul_assoc P γa γc, hca, Matrix.mul_assoc γa P γc, hcc,
    ← Matrix.mul_assoc γa γc P]

theorem measurementProjector_mul_majoranaCommutator {n : ℕ} (k : Fin n) (b : Bool)
    {a c : Fin (2 * n)} (ha : ¬ isModeMajorana k a) (hc : ¬ isModeMajorana k c) :
    measurementProjector k b * (majorana a * majorana c - majorana c * majorana a)
      = (majorana a * majorana c - majorana c * majorana a)
        * measurementProjector k b := by
  have h1 := commute_P_product (measurementProjector k b) (majorana a) (majorana c)
    (measurementProjector_mul_majorana_of_not_mode k b ha)
    (measurementProjector_mul_majorana_of_not_mode k b hc)
  have h2 := commute_P_product (measurementProjector k b) (majorana c) (majorana a)
    (measurementProjector_mul_majorana_of_not_mode k b hc)
    (measurementProjector_mul_majorana_of_not_mode k b ha)
  rw [mul_sub, sub_mul, h1, h2]

private theorem projector_sandwich_of_commute {n : ℕ} (P X : Matrix (Reg n) (Reg n) ℂ)
    (hPX : P * X = X * P) (hPP : P * P = P) :
    P * X * P = X * P := by
  rw [hPX, Matrix.mul_assoc, hPP]

theorem covarianceMatrix_measurement_mixture_away {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ)
    (k : Fin n) {a c : Fin (2 * n)}
    (ha : ¬ isModeMajorana k a) (hc : ¬ isModeMajorana k c) :
    covarianceMatrix (measurementProjector k false * M) a c
      + covarianceMatrix (measurementProjector k true * M) a c
      = covarianceMatrix M a c := by
  have h₀ := projector_sandwich_of_commute (measurementProjector k false)
    (majorana a * majorana c - majorana c * majorana a)
    (measurementProjector_mul_majoranaCommutator k false ha hc)
    (measurementProjector_idem k false)
  have h₁ := projector_sandwich_of_commute (measurementProjector k true)
    (majorana a * majorana c - majorana c * majorana a)
    (measurementProjector_mul_majoranaCommutator k true ha hc)
    (measurementProjector_idem k true)
  rw [covarianceMatrix_projector_apply M (measurementProjector k false)
    (measurementProjector_hermitian k false) a c,
    covarianceMatrix_projector_apply M (measurementProjector k true)
    (measurementProjector_hermitian k true) a c, h₀, h₁,
    ← Complex.add_re, ← mul_add, ← Matrix.trace_add, ← add_mul,
    ← mul_add, ← mul_add, measurementProjector_add k, Matrix.mul_one]
  rfl

theorem measurementUpdate_entry_main {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (k : Fin n) (b : Bool) :
    measurementUpdate Γ k b (majoranaIndices k 0) (majoranaIndices k 1)
      = if b then (-1 : ℝ) else 1 := by
  unfold measurementUpdate
  rw [Matrix.of_apply, if_pos ⟨rfl, rfl⟩]

theorem measurementUpdate_entry_anti {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (k : Fin n) (b : Bool) :
    measurementUpdate Γ k b (majoranaIndices k 1) (majoranaIndices k 0)
      = if b then (1 : ℝ) else -1 := by
  unfold measurementUpdate
  rw [Matrix.of_apply,
    if_neg (fun h => majoranaIndices_ne k 1 0 (by decide) h.1),
    if_pos ⟨rfl, rfl⟩]

theorem measurementUpdate_entry_diag {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (k : Fin n) (b : Bool) {a : Fin (2 * n)} (ha : isModeMajorana k a) :
    measurementUpdate Γ k b a a = 0 := by
  obtain rfl | rfl := ha
  · unfold measurementUpdate
    have him : isModeMajorana k (majoranaIndices k 0) := Or.inl rfl
    rw [Matrix.of_apply,
      if_neg (fun h => majoranaIndices_ne k 0 1 (by decide) h.2),
      if_neg (fun h => majoranaIndices_ne k 0 1 (by decide) h.1),
      if_pos (Or.inl him)]
  · unfold measurementUpdate
    have him : isModeMajorana k (majoranaIndices k 1) := Or.inr rfl
    rw [Matrix.of_apply,
      if_neg (fun h => majoranaIndices_ne k 1 0 (by decide) h.1),
      if_neg (fun h => majoranaIndices_ne k 1 0 (by decide) h.2),
      if_pos (Or.inl him)]

theorem measurementUpdate_entry_cross_left {n : ℕ}
    (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (k : Fin n) (b : Bool)
    {a c : Fin (2 * n)} (ha : isModeMajorana k a) (hc : ¬ isModeMajorana k c) :
    measurementUpdate Γ k b a c = 0 := by
  obtain rfl | rfl := ha
  · unfold measurementUpdate
    have him : isModeMajorana k (majoranaIndices k 0) := Or.inl rfl
    rw [Matrix.of_apply,
      if_neg (fun h => hc (Or.inr h.2)),
      if_neg (fun h => hc (Or.inl h.2)),
      if_pos (Or.inl him)]
  · unfold measurementUpdate
    have him : isModeMajorana k (majoranaIndices k 1) := Or.inr rfl
    rw [Matrix.of_apply,
      if_neg (fun h => majoranaIndices_ne k 1 0 (by decide) h.1),
      if_neg (fun h => hc (Or.inl h.2)),
      if_pos (Or.inl him)]

theorem measurementUpdate_entry_cross_right {n : ℕ}
    (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (k : Fin n) (b : Bool)
    {a c : Fin (2 * n)} (ha : ¬ isModeMajorana k a) (hc : isModeMajorana k c) :
    measurementUpdate Γ k b a c = 0 := by
  obtain rfl | rfl := hc
  · unfold measurementUpdate
    have him : isModeMajorana k (majoranaIndices k 0) := Or.inl rfl
    rw [Matrix.of_apply,
      if_neg (fun h => ha (Or.inl h.1)),
      if_neg (fun h => ha (Or.inr h.1)),
      if_pos (Or.inr him)]
  · unfold measurementUpdate
    have him : isModeMajorana k (majoranaIndices k 1) := Or.inr rfl
    rw [Matrix.of_apply,
      if_neg (fun h => ha (Or.inl h.1)),
      if_neg (fun h => ha (Or.inr h.1)),
      if_pos (Or.inr him)]

theorem measurementUpdate_entry_away {n : ℕ} (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (k : Fin n) (b : Bool) {a c : Fin (2 * n)}
    (ha : ¬ isModeMajorana k a) (hc : ¬ isModeMajorana k c) :
    measurementUpdate Γ k b a c = Γ a c := by
  unfold measurementUpdate
  rw [Matrix.of_apply,
    if_neg (fun h => hc (Or.inr h.2)),
    if_neg (fun h => hc (Or.inl h.2)),
    if_neg (fun h => h.elim ha hc)]

theorem covarianceMatrix_measurement_eq_update {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ)
    (k : Fin n) (b : Bool)
    (hAway : ∀ a c : Fin (2 * n), ¬ isModeMajorana k a → ¬ isModeMajorana k c →
      covarianceMatrix (measurementProjector k b * M) a c
        = bornWeight M k b * covarianceMatrix M a c) :
    covarianceMatrix (measurementProjector k b * M)
      = bornWeight M k b • measurementUpdate (covarianceMatrix M) k b := by
  ext a c
  rw [Matrix.smul_apply, smul_eq_mul]
  have hdiag : ∀ x : Fin (2 * n),
      covarianceMatrix (measurementProjector k b * M) x x = 0 := by
    intro x
    have h := covarianceMatrix_antisymm (measurementProjector k b * M) x x
    linarith
  by_cases ha : isModeMajorana k a
  · by_cases hc : isModeMajorana k c
    · obtain rfl | rfl := ha <;> obtain rfl | rfl := hc
      · rw [hdiag _, measurementUpdate_entry_diag (covarianceMatrix M) k b (Or.inl rfl),
          mul_zero]
      · rw [covarianceMatrix_measurement_local M k b,
          measurementUpdate_entry_main (covarianceMatrix M) k b, mul_comm]
      · rw [covarianceMatrix_antisymm (measurementProjector k b * M)
            (majoranaIndices k 0) (majoranaIndices k 1),
          covarianceMatrix_measurement_local M k b,
          measurementUpdate_entry_anti (covarianceMatrix M) k b]
        cases b <;> norm_num
      · rw [hdiag _, measurementUpdate_entry_diag (covarianceMatrix M) k b (Or.inr rfl),
          mul_zero]
    · rw [covarianceMatrix_measurement_cross M k b ha hc,
        measurementUpdate_entry_cross_left (covarianceMatrix M) k b ha hc, mul_zero]
  · by_cases hc : isModeMajorana k c
    · rw [covarianceMatrix_antisymm (measurementProjector k b * M) c a,
        covarianceMatrix_measurement_cross M k b hc ha, neg_zero,
        measurementUpdate_entry_cross_right (covarianceMatrix M) k b ha hc, mul_zero]
    · rw [hAway a c ha hc, measurementUpdate_entry_away (covarianceMatrix M) k b ha hc]

private def counterexampleΓ : Matrix (Fin (2 * 3)) (Fin (2 * 3)) ℝ :=
  Matrix.of fun a c =>
    if a = majoranaIndices 0 0 ∧ c = majoranaIndices 1 0 then (1 : ℝ) else 0

private def counterexampleR : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun p q =>
    if p = 0 ∧ q = 1 then (1 : ℝ) else if p = 1 ∧ q = 0 then 1
    else if p = 2 ∧ q = 2 then 1 else if p = 3 ∧ q = 3 then 1 else 0

theorem covarianceUpdate_ne_covarianceUpdateComplete_entry :
    covarianceUpdate counterexampleΓ 0 2 counterexampleR (majoranaIndices 0 0)
        (majoranaIndices 1 0)
      ≠ covarianceUpdateComplete counterexampleΓ 0 2 counterexampleR
        (majoranaIndices 0 0) (majoranaIndices 1 0) := by
  have hc : ¬ isLocalMajorana (0 : Fin 3) (2 : Fin 3) (majoranaIndices 1 0) := by decide
  have hold : covarianceUpdate counterexampleΓ 0 2 counterexampleR (majoranaIndices 0 0)
      (majoranaIndices 1 0) = 1 := by
    unfold covarianceUpdate
    simp [hc, counterexampleΓ]
  have hnew : covarianceUpdateComplete counterexampleΓ 0 2 counterexampleR
      (majoranaIndices 0 0) (majoranaIndices 1 0) = 0 := by
    rw [show majoranaIndices (0 : Fin 3) 0 = localIndices (0 : Fin 3) (2 : Fin 3) (0 : Fin 4)
          from rfl,
      covarianceUpdateComplete_cross counterexampleΓ 0 2 (by decide) counterexampleR 0
        (majoranaIndices 1 0) hc, Fin.sum_univ_four]
    have hR : counterexampleR (0 : Fin 4) (0 : Fin 4) = 0
        ∧ counterexampleR (0 : Fin 4) (1 : Fin 4) = 1
        ∧ counterexampleR (0 : Fin 4) (2 : Fin 4) = 0
        ∧ counterexampleR (0 : Fin 4) (3 : Fin 4) = 0 :=
      ⟨rfl, rfl, rfl, rfl⟩
    obtain ⟨hR00, hR01, hR02, hR03⟩ := hR
    have hG1 : counterexampleΓ (localIndices (0 : Fin 3) (2 : Fin 3) (1 : Fin 4))
        (majoranaIndices 1 0) = 0 := rfl
    rw [hR00, zero_mul, hR01, one_mul, hG1, hR02, zero_mul, hR03, zero_mul]
    ring
  rw [hold, hnew]
  exact one_ne_zero

theorem covarianceUpdate_ne_covarianceUpdateComplete :
    covarianceUpdate counterexampleΓ 0 2 counterexampleR
      ≠ covarianceUpdateComplete counterexampleΓ 0 2 counterexampleR := by
  intro h
  exact covarianceUpdate_ne_covarianceUpdateComplete_entry
    (congrArg (fun X => X (majoranaIndices 0 0) (majoranaIndices 1 0)) h)

theorem frontier1 :
    (∀ (n : ℕ) (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (i j : Fin n) (_hij : i ≠ j)
        (R : Matrix (Fin 4) (Fin 4) ℝ) (p : Fin 4) (b : Fin (2 * n))
        (_hb : ¬ isLocalMajorana i j b),
        covarianceUpdateComplete Γ i j R (localIndices i j p) b
          = ∑ q : Fin 4, R p q * Γ (localIndices i j q) b)
    ∧ (∀ (n : ℕ) (Γ : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (i j : Fin n) (_hij : i ≠ j)
        (R : Matrix (Fin 4) (Fin 4) ℝ),
        localBlock (covarianceUpdateComplete Γ i j R) i j = R * localBlock Γ i j * R.transpose)
    ∧ (∀ (n : ℕ) (gl : MatchGateCircuit n) (_h : ∀ g ∈ gl, matchGateBridged g)
        (M : Matrix (Reg n) (Reg n) ℂ),
        covarianceMatrix (matchGateCircuitOp gl * M) = covarianceRun gl (covarianceMatrix M))
    ∧ (∀ (n : ℕ) (M : Matrix (Reg n) (Reg n) ℂ) (k : Fin n) (β : Bool) (a : Fin (2 * n))
        (_ha : isModeMajorana k a) (c : Fin (2 * n)) (_hc : ¬ isModeMajorana k c),
        covarianceMatrix (measurementProjector k β * M) a c = 0)
    ∧ (∀ (n : ℕ) (M : Matrix (Reg n) (Reg n) ℂ) (k : Fin n) (β : Bool),
        covarianceMatrix (measurementProjector k β * M) (majoranaIndices k 0)
            (majoranaIndices k 1)
          = (if β then (-1 : ℝ) else 1) * bornWeight M k β)
    ∧ (∀ (n : ℕ) (M : Matrix (Reg n) (Reg n) ℂ) (k : Fin n) (a c : Fin (2 * n))
        (_ha : ¬ isModeMajorana k a) (_hc : ¬ isModeMajorana k c),
        covarianceMatrix (measurementProjector k false * M) a c
          + covarianceMatrix (measurementProjector k true * M) a c
          = covarianceMatrix M a c)
    ∧ (∀ (n : ℕ) (M : Matrix (Reg n) (Reg n) ℂ) (k : Fin n),
        bornWeight M k false + bornWeight M k true = (Matrix.trace (Mᴴ * M)).re)
    ∧ (∀ (n : ℕ) (M : Matrix (Reg n) (Reg n) ℂ) (k : Fin n) (β : Bool)
        (_hAway : ∀ a c : Fin (2 * n), ¬ isModeMajorana k a → ¬ isModeMajorana k c →
          covarianceMatrix (measurementProjector k β * M) a c
            = bornWeight M k β * covarianceMatrix M a c),
        covarianceMatrix (measurementProjector k β * M)
          = bornWeight M k β • measurementUpdate (covarianceMatrix M) k β)
    ∧ covarianceUpdate counterexampleΓ 0 2 counterexampleR
        ≠ covarianceUpdateComplete counterexampleΓ 0 2 counterexampleR :=
  ⟨fun _ Γ i j hij R p c hb => covarianceUpdateComplete_cross Γ i j hij R p c hb,
    fun _ Γ i j hij R => localBlock_covarianceUpdateComplete Γ i j hij R,
    fun _ gl h M => covarianceMatrix_matchGateCircuit_of_bridged gl h M,
    fun _ M k β _ ha _ hc => covarianceMatrix_measurement_cross M k β ha hc,
    fun _ M k β => covarianceMatrix_measurement_local M k β,
    fun _ M k _ _ ha hc => covarianceMatrix_measurement_mixture_away M k ha hc,
    fun _ M k => bornWeight_split M k,
    fun _ M k β hAway => covarianceMatrix_measurement_eq_update M k β hAway,
    covarianceUpdate_ne_covarianceUpdateComplete⟩

end Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionExt
