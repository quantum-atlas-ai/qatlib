/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ReferenceError.RefTraceError.ChannelMixture
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Concepts.ReferenceError.RefTraceError

open Matrix
open scoped ComplexOrder
open scoped Kronecker

set_option autoImplicit false

private lemma star_real (r : ℝ) : star (r : ℂ) = (r : ℂ) := by
  simp [RCLike.star_def, Complex.conj_ofReal]

private lemma smul_smul' {α : Type*} [Fintype α] (c d : ℂ) (M : Matrix α α ℂ) :
    c • (d • M) = (c * d) • M := by
  ext i j
  show c * (d * M i j) = c * d * M i j
  ring

private lemma smul_conj' {α : Type*} [Fintype α] (c : ℂ) (V Y : Matrix α α ℂ) :
    V * (c • Y) * Vᴴ = c • (V * Y * Vᴴ) := by
  simp only [Matrix.mul_smul, Matrix.smul_mul]

private lemma smul_conj {α : Type*} [Fintype α] (c : ℂ) (V Y : Matrix α α ℂ) :
    c • (V * Y * Vᴴ) = V * (c • Y) * Vᴴ :=
  (smul_conj' c V Y).symm

private lemma fintype_smul_sum {J : Type*} [Fintype J] {α : Type*} [Fintype α] (c : ℂ)
    (f : J → Matrix α α ℂ) : (∑ j, c • f j) = c • (∑ j, f j) :=
  (Finset.smul_sum (s := Finset.univ)).symm

private lemma fintype_sum_pair_swap {J K : Type*} [Fintype J] [Fintype K] {D : ℕ}
    (f : J → K → Operator D) : (∑ x : J × K, f x.1 x.2) = ∑ k, ∑ j, f j k := by
  calc (∑ x : J × K, f x.1 x.2) = ∑ y : K × J, f y.2 y.1 :=
          Equiv.sum_comp (Equiv.prodComm J K) (fun y : K × J => f y.2 y.1)
    _ = ∑ k, ∑ j, f j k := Fintype.sum_prod_type' (fun k j => f j k)

theorem sum_weight_smul_one {J : Type*} [Fintype J] (d : FinDist J) {D : ℕ} (M : Operator D) :
    (∑ j, (d.prob j : ℂ) • M) = M := by
  have hsum : (∑ j, (d.prob j : ℂ)) = (1 : ℂ) := by
    rw [← Complex.ofReal_sum, d.sum_one, Complex.ofReal_one]
  ext i k
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  calc (∑ x, ((d.prob x : ℂ) : ℂ) * M i k) = (∑ x, ((d.prob x : ℂ) : ℂ)) * M i k :=
          (Finset.sum_mul _ _ _).symm
    _ = 1 * M i k := by rw [hsum]
    _ = M i k := one_mul _

private lemma ofReal_smul {α : Type*} [Fintype α] (p q : ℝ) (M : Matrix α α ℂ) :
    ((p * q : ℝ) : ℂ) • M = (q : ℂ) • ((p : ℂ) • M) := by
  rw [Complex.ofReal_mul, mul_comm, (smul_smul' _ _ _).symm]

private lemma real_sqrt_sq {J : Type*} [Fintype J] (d : FinDist J) (j : J) :
    (Real.sqrt (d.prob j) : ℂ) * (Real.sqrt (d.prob j) : ℂ) = (d.prob j : ℂ) := by
  rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt (d.nonneg j)]

theorem trace_conjBranch {J : Type*} [Fintype J] [DecidableEq J] (d : FinDist J) {D : ℕ}
    (M : Operator D) (hM : M ∈ Matrix.unitaryGroup (Fin D) ℂ) (ρ : Operator D) :
    Matrix.trace (M * ρ * Mᴴ) = Matrix.trace ρ := by
  have h := trace_channelMixture d (fun _ => M) (fun _ => hM) ρ
  unfold ChannelMixture at h
  rwa [sum_weight_smul_one d] at h

noncomputable def unitaryMixtureKraus {J : Type*} [Fintype J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D) (j : J) : Operator D :=
  (Real.sqrt (d.prob j) : ℂ) • U j

theorem unitaryMixtureKraus_conj {J : Type*} [Fintype J] {D : ℕ} (d : FinDist J)
    (U : J → Operator D) (ρ : Operator D) (j : J) :
    unitaryMixtureKraus d U j * ρ * (unitaryMixtureKraus d U j)ᴴ
      = (d.prob j : ℂ) • (U j * ρ * (U j)ᴴ) := by
  show (Real.sqrt (d.prob j) : ℂ) • (U j) * ρ * ((Real.sqrt (d.prob j) : ℂ) • (U j))ᴴ = _
  simp only [Matrix.conjTranspose_smul, star_real, smul_mul, Matrix.mul_smul, smul_mul,
    smul_smul']
  rw [mul_assoc, real_sqrt_sq]

theorem unitaryMixtureKraus_complete {J : Type*} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (∑ j, (unitaryMixtureKraus d U j).conjTranspose * unitaryMixtureKraus d U j) = 1 := by
  have hU' : ∀ j, (U j)ᴴ * U j = 1 := fun j => by
    have h := (Matrix.mem_unitaryGroup_iff').mp (hU j)
    rwa [Matrix.star_eq_conjTranspose] at h
  have hterm (j : J) :
      (unitaryMixtureKraus d U j).conjTranspose * unitaryMixtureKraus d U j
        = (d.prob j : ℂ) • ((U j)ᴴ * U j) := by
    show ((Real.sqrt (d.prob j) : ℂ) • (U j))ᴴ * ((Real.sqrt (d.prob j) : ℂ) • (U j)) = _
    simp only [Matrix.conjTranspose_smul, star_real, smul_mul, Matrix.mul_smul, smul_mul,
      smul_smul']
    rw [real_sqrt_sq]
  calc (∑ j, (unitaryMixtureKraus d U j).conjTranspose * unitaryMixtureKraus d U j)
      = ∑ j, (d.prob j : ℂ) • ((U j)ᴴ * U j) := Finset.sum_congr rfl fun j _ => hterm j
    _ = ∑ j, (d.prob j : ℂ) • 1 := Finset.sum_congr rfl fun j _ => by rw [hU' j]
    _ = 1 := sum_weight_smul_one d (1 : Operator D)

noncomputable def unitaryMixtureInstrument {J : Type*} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ) : Instrument J D D :=
  Instrument.ofKraus (unitaryMixtureKraus d U) (unitaryMixtureKraus_complete d U hU)

theorem unitaryMixture_forget {J : Type*} [Fintype J] [DecidableEq J] {D : ℕ} (d : FinDist J)
    (U : J → Operator D) (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ) (ρ : Operator D) :
    (unitaryMixtureInstrument d U hU).forget.map ρ = ChannelMixture d U ρ := by
  rw [Instrument.forget_apply]
  simp only [unitaryMixtureInstrument, Instrument.ofKraus, Instrument.ofBranches,
    conjBranch_apply]
  exact Finset.sum_congr rfl fun j _ => unitaryMixtureKraus_conj d U ρ j

theorem unitaryMixtureInstrument_spec {J : Type*} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ) (ρ : Operator D) (j : J) :
    (unitaryMixtureInstrument d U hU).branch j ρ
      = (d.prob j : ℂ) • (U j * ρ * (U j)ᴴ) ∧
    (unitaryMixtureInstrument d U hU).forget.map ρ = ChannelMixture d U ρ ∧
    instrumentProb (unitaryMixtureInstrument d U hU) ρ j
      = d.prob j * (Matrix.trace ρ).re := by
  refine ⟨unitaryMixtureKraus_conj d U ρ j, unitaryMixture_forget d U hU ρ, ?_⟩
  show (Matrix.trace ((unitaryMixtureInstrument d U hU).branch j ρ)).re = _
  simp only [unitaryMixtureInstrument, Instrument.ofKraus, Instrument.ofBranches,
    conjBranch_apply]
  rw [unitaryMixtureKraus_conj d U ρ j, Matrix.trace_smul, trace_conjBranch d (U j) (hU j) ρ]
  rw [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

private lemma rebracket {D : ℕ} (V U ρ : Operator D) :
    (V * U) * ρ * (V * U)ᴴ = V * (U * ρ * Uᴴ) * Vᴴ := by
  simp only [Matrix.mul_assoc, Matrix.conjTranspose_mul]

private lemma mixture_pair {J K : Type*} [Fintype J] [DecidableEq J] [Fintype K]
    [DecidableEq K] {D : ℕ} (d : FinDist J) (e : FinDist K) (U : J → Operator D)
    (V : K → Operator D) (ρ : Operator D) :
    ChannelMixture (FinDist.independentPair d e) (fun jk => V jk.2 * U jk.1) ρ
      = ChannelMixture e V (ChannelMixture d U ρ) := by
  simp only [ChannelMixture]
  have hcoef (j : J) (k : K) (M : Operator D) :
      ((d.prob j * e.prob k : ℝ) : ℂ) • M
        = (e.prob k : ℂ) • ((d.prob j : ℂ) • M) := ofReal_smul _ _ _
  have hreb (j : J) (k : K) :
      (V k * U j) * ρ * (V k * U j)ᴴ = V k * (U j * ρ * (U j)ᴴ) * (V k)ᴴ := rebracket _ _ _
  calc (∑ jk : J × K, ((d.prob jk.1 * e.prob jk.2 : ℝ) : ℂ) •
          ((V jk.2 * U jk.1) * ρ * (V jk.2 * U jk.1)ᴴ))
      = ∑ k, ∑ j, ((d.prob j * e.prob k : ℝ) : ℂ) •
          ((V k * U j) * ρ * (V k * U j)ᴴ) :=
        fintype_sum_pair_swap
          (fun j k => ((d.prob j * e.prob k : ℝ) : ℂ) • ((V k * U j) * ρ * (V k * U j)ᴴ))
    _ = ∑ k, ∑ j, (e.prob k : ℂ) • ((d.prob j : ℂ) • ((V k * U j) * ρ * (V k * U j)ᴴ)) := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => hcoef j k _
    _ = ∑ k, ∑ j, (e.prob k : ℂ) •
          ((d.prob j : ℂ) • (V k * (U j * ρ * (U j)ᴴ) * (V k)ᴴ)) := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hreb j k]
    _ = ∑ k, (e.prob k : ℂ) •
          (V k * (∑ j, (d.prob j : ℂ) • (U j * ρ * (U j)ᴴ)) * (V k)ᴴ) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have hsmul : (∑ j, (e.prob k : ℂ) • ((d.prob j : ℂ) • (V k * (U j * ρ * (U j)ᴴ) * (V k)ᴴ)))
            = (e.prob k : ℂ) • (∑ j, (d.prob j : ℂ) • (V k * (U j * ρ * (U j)ᴴ) * (V k)ᴴ)) :=
          fintype_smul_sum _ _
        have hmul : (∑ j, V k * ((d.prob j : ℂ) • (U j * ρ * (U j)ᴴ)))
            = V k * (∑ j, (d.prob j : ℂ) • (U j * ρ * (U j)ᴴ)) :=
          (Finset.mul_sum (Finset.univ : Finset J)
            (fun j => (d.prob j : ℂ) • (U j * ρ * (U j)ᴴ)) (V k)).symm
        have hsum : (∑ j, (d.prob j : ℂ) • (U j * ρ * (U j)ᴴ) * (V k)ᴴ)
            = (∑ j, (d.prob j : ℂ) • (U j * ρ * (U j)ᴴ)) * (V k)ᴴ :=
          (Finset.sum_mul (Finset.univ : Finset J)
            (fun j => (d.prob j : ℂ) • (U j * ρ * (U j)ᴴ)) (V k)ᴴ).symm
        have hpush : (∑ j, (d.prob j : ℂ) • (V k * (U j * ρ * (U j)ᴴ) * (V k)ᴴ))
            = V k * (∑ j, (d.prob j : ℂ) • (U j * ρ * (U j)ᴴ)) * (V k)ᴴ := by
          calc (∑ j, (d.prob j : ℂ) • (V k * (U j * ρ * (U j)ᴴ) * (V k)ᴴ))
              = ∑ j, V k * ((d.prob j : ℂ) • (U j * ρ * (U j)ᴴ)) * (V k)ᴴ := by
                refine Finset.sum_congr rfl fun j _ => (smul_conj' _ _ _).symm
            _ = (∑ j, V k * ((d.prob j : ℂ) • (U j * ρ * (U j)ᴴ))) * (V k)ᴴ := by
                rw [Finset.sum_mul]
            _ = V k * (∑ j, (d.prob j : ℂ) • (U j * ρ * (U j)ᴴ)) * (V k)ᴴ := by
                rw [hmul]
        calc (∑ j, (e.prob k : ℂ) • ((d.prob j : ℂ) • (V k * (U j * ρ * (U j)ᴴ) * (V k)ᴴ)))
            = (e.prob k : ℂ) • (∑ j, (d.prob j : ℂ) • (V k * (U j * ρ * (U j)ᴴ) * (V k)ᴴ)) :=
              hsmul
          _ = (e.prob k : ℂ) • (V k * (∑ j, (d.prob j : ℂ) • (U j * ρ * (U j)ᴴ)) * (V k)ᴴ) := by
                rw [hpush]

theorem unitaryMixture_composition {J K : Type*} [Fintype J] [DecidableEq J] [Fintype K]
    [DecidableEq K] {D : ℕ} (d : FinDist J) (e : FinDist K) (U : J → Operator D)
    (V : K → Operator D) (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hV : ∀ k, V k ∈ Matrix.unitaryGroup (Fin D) ℂ) (ρ : Operator D) :
    ChannelMixture (FinDist.independentPair d e) (fun jk => V jk.2 * U jk.1) ρ
      = ChannelMixture e V (ChannelMixture d U ρ) ∧
    (((unitaryMixtureInstrument e V hV).forget).comp
      (unitaryMixtureInstrument d U hU).forget).map ρ
      = ChannelMixture (FinDist.independentPair d e) (fun jk => V jk.2 * U jk.1) ρ := by
  have h1 : ChannelMixture (FinDist.independentPair d e) (fun jk => V jk.2 * U jk.1) ρ
      = ChannelMixture e V (ChannelMixture d U ρ) := mixture_pair d e U V ρ
  refine ⟨h1, ?_⟩
  simp only [QuantumChannel.comp, LinearMap.comp_apply, Instrument.forget_apply]
  have hinter : (∑ o, (unitaryMixtureInstrument d U hU).branch o ρ) = ChannelMixture d U ρ :=
    (Instrument.forget_apply _ _).symm.trans (unitaryMixture_forget d U hU ρ)
  rw [hinter]
  calc (∑ k, (unitaryMixtureInstrument e V hV).branch k (ChannelMixture d U ρ))
      = ∑ k, unitaryMixtureKraus e V k * ChannelMixture d U ρ *
          (unitaryMixtureKraus e V k)ᴴ := by
        simp only [unitaryMixtureInstrument, Instrument.ofKraus, Instrument.ofBranches,
          conjBranch_apply]
    _ = ∑ k, (e.prob k : ℂ) • (V k * ChannelMixture d U ρ * (V k)ᴴ) :=
        Finset.sum_congr rfl fun k _ => unitaryMixtureKraus_conj e V _ k
    _ = ChannelMixture e V (ChannelMixture d U ρ) := rfl
    _ = ChannelMixture (FinDist.independentPair d e) (fun jk => V jk.2 * U jk.1) ρ :=
        h1.symm

theorem Instrument.seq_branch_apply {O P : Type*} [Fintype O] [Fintype P] {D E F : ℕ}
    (I : Instrument O D E) (J : Instrument P E F) (o : O) (p : P) (ρ : Operator D) :
    (I.seq J).branch (o, p) ρ = J.branch p (I.branch o ρ) := rfl

private lemma unitary_mul {D : ℕ} {M N : Operator D}
    (hM : M ∈ Matrix.unitaryGroup (Fin D) ℂ) (hN : N ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    M * N ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  have hM' : Mᴴ * M = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp hM
    rwa [Matrix.star_eq_conjTranspose] at h
  have hN' : Nᴴ * N = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp hN
    rwa [Matrix.star_eq_conjTranspose] at h
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.mul_assoc (N)ᴴ (M)ᴴ (M * N), (Matrix.mul_assoc (M)ᴴ M N).symm, hM',
    Matrix.one_mul, hN']

theorem unitaryMixtureInstrument_seq_spec {J K : Type*} [Fintype J] [DecidableEq J] [Fintype K]
    [DecidableEq K] {D : ℕ} (d : FinDist J) (e : FinDist K) (U : J → Operator D)
    (V : K → Operator D) (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hV : ∀ k, V k ∈ Matrix.unitaryGroup (Fin D) ℂ) (ρ : Operator D) (j : J) (k : K) :
    ((unitaryMixtureInstrument d U hU).seq (unitaryMixtureInstrument e V hV)).branch (j, k) ρ
      = ((d.prob j * e.prob k : ℝ) : ℂ) • ((V k * U j) * ρ * (V k * U j)ᴴ) ∧
    instrumentProb ((unitaryMixtureInstrument d U hU).seq
      (unitaryMixtureInstrument e V hV)) ρ (j, k)
      = d.prob j * e.prob k * (Matrix.trace ρ).re := by
  have hmem : V k * U j ∈ Matrix.unitaryGroup (Fin D) ℂ := unitary_mul (hV k) (hU j)
  have hbranch :
      (unitaryMixtureInstrument e V hV).branch k
          ((unitaryMixtureInstrument d U hU).branch j ρ)
        = ((d.prob j * e.prob k : ℝ) : ℂ) • ((V k * U j) * ρ * (V k * U j)ᴴ) := by
    simp only [unitaryMixtureInstrument, Instrument.ofKraus, Instrument.ofBranches,
      conjBranch_apply]
    rw [unitaryMixtureKraus_conj, unitaryMixtureKraus_conj]
    show (e.prob k : ℂ) • (V k * ((d.prob j : ℂ) • (U j * ρ * (U j)ᴴ)) * (V k)ᴴ) = _
    rw [smul_conj', smul_smul', mul_comm, Complex.ofReal_mul, rebracket]
  refine ⟨hbranch, ?_⟩
  show (Matrix.trace (((unitaryMixtureInstrument d U hU).seq
    (unitaryMixtureInstrument e V hV)).branch (j, k) ρ)).re = _
  rw [Instrument.seq_branch_apply, hbranch, Matrix.trace_smul,
    trace_conjBranch d (V k * U j) hmem ρ]
  rw [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem unitaryMixtureInstrument_seq_outerProduct {J K : Type*} [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K] {D : ℕ} (d : FinDist J) (e : FinDist K)
    (U : J → Operator D) (V : K → Operator D) (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hV : ∀ k, V k ∈ Matrix.unitaryGroup (Fin D) ℂ) (ψ : QState (Fin D)) (j : J) (k : K) :
    ((unitaryMixtureInstrument d U hU).seq (unitaryMixtureInstrument e V hV)).branch (j, k)
        (outerProduct ψ)
      = ((d.prob j * e.prob k : ℝ) : ℂ) • outerProduct ((V k * U j) *ᵥ ψ) := by
  refine (unitaryMixtureInstrument_seq_spec d e U V hU hV (outerProduct ψ) j k).1.trans ?_
  show ((d.prob j * e.prob k : ℝ) : ℂ) •
      ((V k * U j) * (outerProduct ψ) * (V k * U j)ᴴ) = _
  rw [← conjBranch_outerProduct]
  rfl

private lemma kron_smul {R D : ℕ} (c : ℂ) (M : Matrix (Fin D) (Fin D) ℂ) :
    (1 : Operator R) ⊗ₖ (c • M) = c • ((1 : Operator R) ⊗ₖ M) := by
  show Matrix.kroneckerMap (· * ·) (1 : Operator R) (c • M)
    = c • Matrix.kroneckerMap (· * ·) (1 : Operator R) M
  exact Matrix.kroneckerMap_smul_right (· * · : ℂ → ℂ → ℂ) c (fun _ _ => by ring) _ _

private lemma conjMap_smul {α : Type*} [Fintype α] (c : ℝ) (M : Matrix α α ℂ)
    (A : Matrix α α ℂ) :
    MatrixMap.conj ((c : ℂ) • M) A = ((c : ℂ) * (c : ℂ)) • (M * A * Mᴴ) := by
  show (c : ℂ) • M * A * ((c : ℂ) • M)ᴴ = _
  simp only [Matrix.conjTranspose_smul, star_real, smul_mul, Matrix.mul_smul, smul_mul,
    smul_smul']

theorem channelAmplification_unitaryMixture {J : Type*} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (U : J → Operator D)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ) (R : ℕ)
    (A : Matrix (Fin R × Fin D) (Fin R × Fin D) ℂ) :
    ChannelAmplification (unitaryMixtureInstrument d U hU).forget.map R A
      = ∑ j, (d.prob j : ℂ) •
        (TensorGate (1 : Operator R) (U j) * A * (TensorGate (1 : Operator R) (U j))ᴴ) := by
  have hforget : (unitaryMixtureInstrument d U hU).forget.map
      = ∑ j, conjBranch (unitaryMixtureKraus d U j) := by
    show (∑ j, (unitaryMixtureInstrument d U hU).branch j) = _
    simp only [unitaryMixtureInstrument, Instrument.ofKraus, Instrument.ofBranches]
  calc ChannelAmplification (unitaryMixtureInstrument d U hU).forget.map R A
      = ∑ j, ChannelAmplification (conjBranch (unitaryMixtureKraus d U j)) R A := by
        rw [hforget]
        ext ⟨x, y⟩
        simp only [ChannelAmplification, Matrix.sum_apply, LinearMap.sum_apply]
    _ = ∑ j, MatrixMap.conj ((1 : Operator R) ⊗ₖ unitaryMixtureKraus d U j) A :=
          Finset.sum_congr rfl fun j _ => channelAmplification_conjBranch _ _ _
    _ = ∑ j, (d.prob j : ℂ) • (MatrixMap.conj ((1 : Operator R) ⊗ₖ U j) A) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        show MatrixMap.conj ((1 : Operator R) ⊗ₖ ((Real.sqrt (d.prob j) : ℂ) • (U j))) A
          = (d.prob j : ℂ) • (MatrixMap.conj ((1 : Operator R) ⊗ₖ U j) A)
        rw [kron_smul, conjMap_smul, real_sqrt_sq]
        simp only [MatrixMap.conj, LinearMap.coe_mk, AddHom.coe_mk]
    _ = ∑ j, (d.prob j : ℂ) •
        (TensorGate (1 : Operator R) (U j) * A * (TensorGate (1 : Operator R) (U j))ᴴ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [MatrixMap.conj, LinearMap.coe_mk, AddHom.coe_mk, TensorGate]

end Qatlib.Concepts.ReferenceError.RefTraceError
