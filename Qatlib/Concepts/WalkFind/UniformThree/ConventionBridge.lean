/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform
import Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelianState
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.WalshMoment.Forrelation

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.WalkFind.UniformThree

open Matrix
open scoped ComplexConjugate

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem fourierMatrix_eq_abelianQFTMatrix_neg (χ : AddChar G ℂ) (x : G) :
    Qatlib.Concepts.WalshMoment.Forrelation.fourierMatrix G χ x = abelianQFTMatrix (G := G) (-χ) x := by
  simp [Qatlib.Concepts.WalshMoment.Forrelation.fourierMatrix, abelianQFTMatrix, Qatlib.Concepts.WalshMoment.Forrelation.fourierScale,
    AddChar.map_neg_eq_conj]

theorem fourierMatrix_eq_abelianQFTMatrix_submatrix_neg :
    Qatlib.Concepts.WalshMoment.Forrelation.fourierMatrix G =
      (abelianQFTMatrix (G := G)).submatrix (Equiv.neg (AddChar G ℂ)) id := by
  ext χ x
  simp [fourierMatrix_eq_abelianQFTMatrix_neg]

theorem fourier_eq_abelianQFT_neg (ψ : G → ℂ) (χ : AddChar G ℂ) :
    Qatlib.Concepts.WalshMoment.Forrelation.fourier ψ χ = abelianQFT ψ (-χ) := by
  simp only [Qatlib.Concepts.WalshMoment.Forrelation.fourier, abelianQFT, Matrix.mulVec,
      dotProduct]
  exact Finset.sum_congr rfl fun x _ => by rw [fourierMatrix_eq_abelianQFTMatrix_neg]

theorem fourier_abelianCharacterState (χ : AddChar G ℂ) :
    Qatlib.Concepts.WalshMoment.Forrelation.fourier (abelianCharacterState χ) = Ket χ := by
  funext η
  rw [fourier_eq_abelianQFT_neg, abelianQFT_characterState]
  by_cases h : η = χ
  · subst h; simp
  · have hne : -η ≠ -χ := by simpa using neg_injective.ne h
    simp [Ket, h, hne]

theorem fourierInv_eq_abelianQFTInv_neg (φ : AddChar G ℂ → ℂ) (x : G) :
    Qatlib.Concepts.WalshMoment.Forrelation.fourierInv φ x = abelianQFTInv (fun χ => φ (-χ)) x := by
  classical
  have hs : (starRingEnd ℂ) ((Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹) =
      (Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹ := by
    simp [Complex.conj_ofReal]
  rw [Qatlib.Concepts.WalshMoment.Forrelation.fourierInv_apply]
  simp only [abelianQFTInv, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    abelianQFTMatrix, RCLike.star_def, map_mul, hs, Qatlib.Concepts.WalshMoment.Forrelation.fourierScale,
    mul_assoc, ← Finset.mul_sum]
  congr 1
  rw [← Equiv.sum_comp (Equiv.neg (AddChar G ℂ)) (fun χ => conj (χ x) * φ (-χ))]
  apply Finset.sum_congr rfl
  intro χ _
  simp [AddChar.map_neg_eq_conj]

end Qatlib.Concepts.WalkFind.UniformThree

namespace Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian

open Matrix
open scoped ComplexConjugate Classical

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem fourierMatrix_eq_abelianQFTMatrix_neg :
    fourierMatrix G = (abelianQFTMatrix (G := G)).submatrix Neg.neg id :=
  Qatlib.Concepts.WalkFind.UniformThree.fourierMatrix_eq_abelianQFTMatrix_submatrix_neg

theorem fourier_eq_abelianQFT_neg (ψ : QState G) (χ : AddChar G ℂ) :
    fourier ψ χ = abelianQFT ψ (-χ) :=
  Qatlib.Concepts.WalkFind.UniformThree.fourier_eq_abelianQFT_neg ψ χ

theorem abelianQFT_eq_fourier_neg (ψ : QState G) (χ : AddChar G ℂ) :
    abelianQFT ψ χ = fourier ψ (-χ) := by
  rw [fourier_eq_abelianQFT_neg, neg_neg]

theorem fourierInv_eq_abelianQFTInv_neg [DecidableEq G]
    (φ : QState (AddChar G ℂ)) :
    fourierInv φ = abelianQFTInv (fun χ => φ (-χ)) := by
  funext x
  exact Qatlib.Concepts.WalkFind.UniformThree.fourierInv_eq_abelianQFTInv_neg φ x

theorem characterState_eq_abelianCharacterState (χ : AddChar G ℂ) :
    characterState χ = abelianCharacterState χ := rfl

theorem bornProb_fourier_eq_abelianQFT_neg (ψ : QState G) (χ : AddChar G ℂ) :
    BornProb (fourier ψ) χ = BornProb (abelianQFT ψ) (-χ) := by
  simp only [BornProb, fourier_eq_abelianQFT_neg]

theorem measureProb_fourier_eq_abelianQFT_neg (ψ : QState G)
    (S : Finset (AddChar G ℂ)) :
    MeasureProb (fourier ψ) S =
      MeasureProb (abelianQFT ψ) (S.map (Equiv.neg _).toEmbedding) := by
  simp only [MeasureProb, Finset.sum_map, Equiv.toEmbedding_apply, Equiv.neg_apply,
    bornProb_fourier_eq_abelianQFT_neg]

theorem bornDistribution_fourier_eq_abelianQFT_neg [DecidableEq G]
    (ψ : QState G) (hψ : Normalized ψ) (χ : AddChar G ℂ) :
    bornDistribution (fourier ψ) (normalized_fourier hψ) χ =
      bornDistribution (abelianQFT ψ) (normalized_abelianQFT hψ) (-χ) := by
  simp only [bornDistribution_apply, bornProb_fourier_eq_abelianQFT_neg]

theorem fourierGate_eq_abelianQFTMatrix_neg (e : G ≃ AddChar G ℂ) :
    fourierGate e = (abelianQFTMatrix (G := G)).submatrix (fun x => -(e x)) id := by
  ext x y
  exact congrArg (fun M : Matrix (AddChar G ℂ) G ℂ => M (e x) y)
    fourierMatrix_eq_abelianQFTMatrix_neg

theorem run_fourierCircuit_eq_abelianQFT_neg [DecidableEq G]
    (e : G ≃ AddChar G ℂ) (oracle : Matrix G G ℂ) (ψ : QState G) (χ : AddChar G ℂ) :
    Run oracle (fourierCircuit e) ψ (e.symm χ) = abelianQFT ψ (-χ) := by
  rw [run_fourierCircuit, fourier_eq_abelianQFT_neg]

theorem fourier_abelianCosetState (H : AddSubgroup G) (s : G) (χ : AddChar G ℂ) :
    fourier (abelianCosetState H s) χ =
      if χ ∈ characterAnnihilator H then
        conj (χ s) * ((Real.sqrt (Fintype.card H : ℝ) : ℂ) *
          (Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹) else 0 := by
  rw [fourier_eq_abelianQFT_neg, abelianQFT_cosetState]
  simp only [AddSubgroup.neg_mem_iff, AddChar.neg_apply, AddChar.map_neg_eq_conj]

theorem subgroup_card_ratio_eq_inv_annihilator (H : AddSubgroup G) :
    (Fintype.card H : ℝ) / (Fintype.card G : ℝ) =
      1 / (Fintype.card (characterAnnihilator H) : ℝ) := by
  have hcard : (Fintype.card (characterAnnihilator H) : ℝ) * Fintype.card H =
      (Fintype.card G : ℝ) := by exact_mod_cast card_characterAnnihilator H
  have hH : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := H)
  rw [← hcard, mul_comm, div_mul_eq_div_div, div_self hH]

theorem bornProb_fourier_abelianCosetState (H : AddSubgroup G) (s : G)
    (χ : AddChar G ℂ) :
    BornProb (fourier (abelianCosetState H s)) χ =
      if χ ∈ characterAnnihilator H then
        1 / (Fintype.card (characterAnnihilator H) : ℝ) else 0 := by
  rw [bornProb_fourier_eq_abelianQFT_neg, bornProb_abelianQFT_cosetState]
  simp only [AddSubgroup.neg_mem_iff, subgroup_card_ratio_eq_inv_annihilator]

theorem bornProb_fourier_abelianCosetState_shift (H : AddSubgroup G)
    (s t : G) (χ : AddChar G ℂ) :
    BornProb (fourier (abelianCosetState H s)) χ =
      BornProb (fourier (abelianCosetState H t)) χ := by
  rw [bornProb_fourier_abelianCosetState, bornProb_fourier_abelianCosetState]

theorem bornProb_run_fourierCircuit_abelianCosetState [DecidableEq G]
    (e : G ≃ AddChar G ℂ) (oracle : Matrix G G ℂ) (H : AddSubgroup G)
    (s : G) (χ : AddChar G ℂ) :
    BornProb (Run oracle (fourierCircuit e) (abelianCosetState H s)) (e.symm χ) =
      if χ ∈ characterAnnihilator H then
        1 / (Fintype.card (characterAnnihilator H) : ℝ) else 0 := by
  rw [bornProb_run_fourierCircuit, bornProb_fourier_abelianCosetState]

theorem fourier_zmodAddEquiv {N : ℕ} [NeZero N]
    (ψ : QState (ZMod N)) (k : ZMod N) :
    fourier ψ (AddChar.zmodAddEquiv k) = zmodQFT ψ (-k) := by
  rw [fourier_eq_abelianQFT_neg, ← map_neg AddChar.zmodAddEquiv,
    abelianQFT_zmodAddEquiv]

end Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
