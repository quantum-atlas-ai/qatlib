/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerExt
import Qatlib.Concepts.HspRecovery.Reduction.BooleanRecoveryRank
import Qatlib.Concepts.HspRecovery.Reduction.BooleanGaussianDecoder
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.HspRecovery.Distinguisher

noncomputable section

namespace Qatlib.Concepts.PauliClifford.PauliAlgebra

open Qatlib
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
open Qatlib
open Qatlib.Concepts.PauliClifford.ExactRank.StabilizerRank
open Qatlib.Concepts.PauliClifford.ExactRank (BooleanVec booleanDot booleanCharacter)
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Matrix
open scoped Classical BigOperators

def IsPhysicalStabilizerState {n : ℕ} (ψ : QState (Reg n)) : Prop :=
  ∃ t : Tableau n n, ConsistentTableau t ∧
    IndependentGenerators (tableauGenerators t) ∧ ψ ∈ codeSpace t

def IsNormalizedPhysicalStabilizerState {n : ℕ} (ψ : QState (Reg n)) : Prop :=
  Normalized ψ ∧ IsPhysicalStabilizerState ψ

def IsStabilizerFunUpToPhase {n : ℕ} (φ : BooleanVec n → ℂ) : Prop :=
  ∃ (lam : ℂ) (χ : BooleanVec n → ℂ), lam ≠ 0 ∧ IsStabilizerFun χ ∧
    φ = fun x => lam * χ x

theorem isStabilizerFunUpToPhase_self {n : ℕ} {φ : BooleanVec n → ℂ}
    (hφ : IsStabilizerFun φ) : IsStabilizerFunUpToPhase φ := by
  refine ⟨1, φ, one_ne_zero, hφ, ?_⟩
  funext x
  simp

theorem isStabilizerFunUpToPhase_smul {n : ℕ} {φ : BooleanVec n → ℂ}
    (hφ : IsStabilizerFunUpToPhase φ) (mu : ℂ) (hmu : mu ≠ 0) :
    IsStabilizerFunUpToPhase (fun x => mu * φ x) := by
  obtain ⟨lam, χ, hlam, hχ, rfl⟩ := hφ
  refine ⟨mu * lam, χ, mul_ne_zero hmu hlam, hχ, ?_⟩
  funext x
  simp only
  ring

theorem IsPhysicalStabilizerState.smul {n : ℕ} {ψ : QState (Reg n)}
    (hψ : IsPhysicalStabilizerState ψ) (lam : ℂ) :
    IsPhysicalStabilizerState (lam • ψ) := by
  obtain ⟨t, ht, hind, hmem⟩ := hψ
  exact ⟨t, ht, hind, (codeSpace t).smul_mem lam hmem⟩

theorem normalized_smul_of_norm_eq_one {n : ℕ} {ψ : QState (Reg n)}
    (hn : Normalized ψ) {lam : ℂ} (hlam : ‖lam‖ = 1) : Normalized (lam • ψ) := by
  change (∑ i, ‖ψ i‖ ^ 2) = 1 at hn
  change (∑ i, ‖(lam • ψ) i‖ ^ 2) = 1
  simp_rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, hlam, one_pow, one_mul]
  exact hn

theorem IsNormalizedPhysicalStabilizerState.smul {n : ℕ} {ψ : QState (Reg n)}
    (hψ : IsNormalizedPhysicalStabilizerState ψ) {lam : ℂ} (hlam : ‖lam‖ = 1) :
    IsNormalizedPhysicalStabilizerState (lam • ψ) :=
  ⟨normalized_smul_of_norm_eq_one hψ.1 hlam, hψ.2.smul lam⟩

def translationRow {n : ℕ} (x : BooleanVec n) : Row n :=
  ⟨vecToReg x, fun _ => false, 0⟩

def diagonalRow {n : ℕ} (z : BooleanVec n) (sign : ZMod 2) : Row n :=
  ⟨fun _ => false, vecToReg z, if sign = 0 then 0 else 2⟩

theorem vecToReg_add {n : ℕ} (x y : BooleanVec n) :
    vecToReg (x + y) = Qatlib.Concepts.HspRecovery.ReductionCore.regXor (vecToReg x) (vecToReg y) := by
  apply (Qatlib.Concepts.WalshMoment.Forrelation.regBooleanEquiv n).injective
  change (Qatlib.Concepts.WalshMoment.Forrelation.regBooleanEquiv n) ((Qatlib.Concepts.WalshMoment.Forrelation.regBooleanEquiv n).symm (x + y)) =
    (Qatlib.Concepts.WalshMoment.Forrelation.regBooleanEquiv n) (Qatlib.Concepts.HspRecovery.ReductionCore.regXor
      ((Qatlib.Concepts.WalshMoment.Forrelation.regBooleanEquiv n).symm x) ((Qatlib.Concepts.WalshMoment.Forrelation.regBooleanEquiv n).symm y))
  rw [Qatlib.Concepts.HspRecovery.ReductionCore.regBooleanEquiv_xor]
  simp

theorem regXor_cancel {n : ℕ} (r : Reg n) (x : Reg n) :
    Qatlib.Concepts.HspRecovery.ReductionCore.regXor (Qatlib.Concepts.HspRecovery.ReductionCore.regXor r x) x = r := by
  rw [Qatlib.Concepts.HspRecovery.ReductionCore.regXor_assoc, Qatlib.Concepts.HspRecovery.ReductionCore.regXor_self,
    Qatlib.Concepts.HspRecovery.ReductionCore.regXor_zeroStr]

theorem vecToReg_apply_of_eq_zero {n : ℕ} (x : BooleanVec n) (i : Fin n)
    (h : x i = 0) : vecToReg x i = false := by
  apply Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv.injective
  change Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv (Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv.symm (x i)) =
    Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv false
  rw [Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv.apply_symm_apply, h,
    Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv_false]

theorem vecToReg_apply_of_eq_one {n : ℕ} (x : BooleanVec n) (i : Fin n)
    (h : x i = 1) : vecToReg x i = true := by
  apply Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv.injective
  change Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv (Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv.symm (x i)) =
    Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv true
  rw [Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv.apply_symm_apply, h,
    Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv_true]

theorem symplecticVec_translationRow {n : ℕ} (x : BooleanVec n) :
    symplecticVec (translationRow x).decode.word = (x, 0) := by
  apply Prod.ext
  · funext i
    rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one
        (x i) with h | h
    · have hr := vecToReg_apply_of_eq_zero x i h
      simp [symplecticVec, translationRow, Row.decode, letter,
        symplecticX, hr, h]
    · have hr := vecToReg_apply_of_eq_one x i h
      simp [symplecticVec, translationRow, Row.decode, letter,
        symplecticX, hr, h]
  · funext i
    cases hr : vecToReg x i <;>
      simp [symplecticVec, translationRow, Row.decode, letter, symplecticZ, hr]

theorem symplecticVec_diagonalRow {n : ℕ} (z : BooleanVec n) (sign : ZMod 2) :
    symplecticVec (diagonalRow z sign).decode.word = (0, z) := by
  apply Prod.ext
  · funext i
    cases hr : vecToReg z i <;>
      simp [symplecticVec, diagonalRow, Row.decode, letter, symplecticX, hr]
  · funext i
    rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one
        (z i) with h | h
    · have hr := vecToReg_apply_of_eq_zero z i h
      simp [symplecticVec, diagonalRow, Row.decode, letter,
        symplecticZ, hr, h]
    · have hr := vecToReg_apply_of_eq_one z i h
      simp [symplecticVec, diagonalRow, Row.decode, letter,
        symplecticZ, hr, h]

theorem diagonalRow_hermitian {n : ℕ} (z : BooleanVec n) (sign : ZMod 2) :
    IsHermitianPauli (diagonalRow z sign).decode := by
  by_cases h : sign = 0
  · left
    simp [diagonalRow, Row.decode, h]
  · right
    simp [diagonalRow, Row.decode, h]

theorem translationRow_op {n : ℕ} (x : BooleanVec n) :
    op (translationRow x).decode = fun r s =>
      if s = Qatlib.Concepts.HspRecovery.ReductionCore.regXor r (vecToReg x) then (1 : ℂ) else 0 := by
  ext r s
  rw [op_apply]
  simp only [translationRow, Row.decode, ZMod.val_zero, pow_zero, one_mul]
  by_cases hs : s = Qatlib.Concepts.HspRecovery.ReductionCore.regXor r (vecToReg x)
  · subst s
    rw [if_pos rfl]
    have hf : ∀ k, P1 (letter (vecToReg x k) false) (r k)
        (Qatlib.Concepts.HspRecovery.ReductionCore.regXor r (vecToReg x) k) = (1 : ℂ) := by
      intro k
      cases hx : vecToReg x k <;> cases hr : r k <;>
        simp [letter, P1, Qatlib.Concepts.HspRecovery.ReductionCore.regXor, hx, hr]
    simp_rw [hf]
    simp
  · rw [if_neg hs]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hs
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    cases hx : vecToReg x k <;> cases hr : r k <;> cases hs' : s k <;>
      simp_all [letter, P1, Qatlib.Concepts.HspRecovery.ReductionCore.regXor]

theorem translationRow_mulVec {n : ℕ} (x : BooleanVec n)
    (ψ : QState (Reg n)) (r : Reg n) :
    (op (translationRow x).decode *ᵥ ψ) r =
      ψ (Qatlib.Concepts.HspRecovery.ReductionCore.regXor r (vecToReg x)) := by
  simp [Matrix.mulVec, dotProduct, translationRow_op]

theorem diagonalRow_op {n : ℕ} (z : BooleanVec n) (sign : ZMod 2) :
    op (diagonalRow z sign).decode = Matrix.diagonal (fun r =>
      (if sign = 0 then (1 : ℂ) else -1) * booleanCharacter z (regToVec r)) := by
  ext r s
  rw [op_apply]
  simp only [diagonalRow, Row.decode, Matrix.diagonal_apply]
  by_cases hrs : r = s
  · subst s
    rw [if_pos rfl]
    have hchar :=
        Qatlib.Concepts.WalshMoment.Forrelation.booleanCharacter_regBooleanEquiv_sign
        (vecToReg z) r
    have hz : Qatlib.Concepts.WalshMoment.Forrelation.regBooleanEquiv n (vecToReg z) = z :=
      (Qatlib.Concepts.WalshMoment.Forrelation.regBooleanEquiv n).apply_symm_apply z
    rw [hz] at hchar
    change booleanCharacter z (regToVec r) = _ at hchar
    have hf : ∀ k, P1 (letter false (vecToReg z k)) (r k) (r k) =
        if vecToReg z k && r k then (-1 : ℂ) else 1 := by
      intro k
      cases hzr : vecToReg z k <;> cases hr : r k <;>
        simp [letter, P1]
    simp_rw [hf]
    rw [← hchar]
    by_cases h : sign = 0 <;> simp [h, zmod4_val_two]
  · rw [if_neg hrs]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hrs
    have hzero : (∏ k, P1 (letter false (vecToReg z k)) (r k) (s k)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      cases hzr : vecToReg z k <;> cases hr : r k <;> cases hs : s k <;>
        simp_all [letter, P1]
    rw [hzero, mul_zero]

theorem diagonalRow_mulVec {n : ℕ} (z : BooleanVec n) (sign : ZMod 2)
    (ψ : QState (Reg n)) (r : Reg n) :
    (op (diagonalRow z sign).decode *ᵥ ψ) r =
      ((if sign = 0 then (1 : ℂ) else -1) * booleanCharacter z (regToVec r)) * ψ r := by
  rw [diagonalRow_op]
  exact Matrix.mulVec_diagonal _ _ _

def rawDiagonalRow {n : ℕ} (z : BooleanVec n) (phase : Phase4) : Row n :=
  ⟨fun _ => false, vecToReg z, phase⟩

theorem rawDiagonalRow_op {n : ℕ} (z : BooleanVec n) (phase : Phase4) :
    op (rawDiagonalRow z phase).decode = Matrix.diagonal (fun r =>
      (Complex.I ^ phase.val : ℂ) * booleanCharacter z (regToVec r)) := by
  ext r s
  rw [op_apply]
  simp only [rawDiagonalRow, Row.decode, Matrix.diagonal_apply]
  by_cases hrs : r = s
  · subst s
    rw [if_pos rfl]
    have hchar :=
        Qatlib.Concepts.WalshMoment.Forrelation.booleanCharacter_regBooleanEquiv_sign
        (vecToReg z) r
    have hz : Qatlib.Concepts.WalshMoment.Forrelation.regBooleanEquiv n (vecToReg z) = z :=
      (Qatlib.Concepts.WalshMoment.Forrelation.regBooleanEquiv n).apply_symm_apply z
    rw [hz] at hchar
    change booleanCharacter z (regToVec r) = _ at hchar
    have hf : ∀ k, P1 (letter false (vecToReg z k)) (r k) (r k) =
        if vecToReg z k && r k then (-1 : ℂ) else 1 := by
      intro k
      cases hzr : vecToReg z k <;> cases hr : r k <;>
        simp [letter, P1]
    simp_rw [hf]
    rw [← hchar]
  · rw [if_neg hrs]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hrs
    have hzero : (∏ k, P1 (letter false (vecToReg z k)) (r k) (s k)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      cases hzr : vecToReg z k <;> cases hr : r k <;> cases hs : s k <;>
        simp_all [letter, P1]
    rw [hzero, mul_zero]

theorem rawDiagonalRow_mulVec {n : ℕ} (z : BooleanVec n) (phase : Phase4)
    (ψ : QState (Reg n)) (r : Reg n) :
    (op (rawDiagonalRow z phase).decode *ᵥ ψ) r =
      ((Complex.I ^ phase.val : ℂ) * booleanCharacter z (regToVec r)) * ψ r := by
  rw [rawDiagonalRow_op]
  exact Matrix.mulVec_diagonal _ _ _

def phase4Sign (sign : ZMod 2) : Phase4 := if sign = 0 then 0 else 2

def yCount {n : ℕ} (x z : BooleanVec n) : Phase4 :=
  ∑ k, if x k = 1 ∧ z k = 1 then 1 else 0

def pauliRow {n : ℕ} (x z : BooleanVec n) (phase : Phase4) : Row n :=
  ⟨vecToReg x, vecToReg z, phase⟩

def affinePauliRow {n : ℕ} (x z : BooleanVec n) (sign : ZMod 2) : Row n :=
  pauliRow x z (phase4Sign sign)

theorem symplecticVec_pauliRow {n : ℕ} (x z : BooleanVec n) (phase : Phase4) :
    symplecticVec (pauliRow x z phase).decode.word = (x, z) := by
  apply Prod.ext
  · funext i
    rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one (x i) with hx | hx <;>
      rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one
          (z i) with hz | hz <;>
      simp [symplecticVec, pauliRow, Row.decode, letter, symplecticX,
        vecToReg_apply_of_eq_zero, vecToReg_apply_of_eq_one, hx, hz]
  · funext i
    rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one (x i) with hx | hx <;>
      rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one
          (z i) with hz | hz <;>
      simp [symplecticVec, pauliRow, Row.decode, letter, symplecticZ,
        vecToReg_apply_of_eq_zero, vecToReg_apply_of_eq_one, hx, hz]

theorem affinePauliRow_hermitian {n : ℕ} (x z : BooleanVec n) (sign : ZMod 2) :
    IsHermitianPauli (affinePauliRow x z sign).decode := by
  by_cases h : sign = 0
  · left
    simp [affinePauliRow, pauliRow, Row.decode, phase4Sign, h]
  · right
    simp [affinePauliRow, pauliRow, Row.decode, phase4Sign, h]

theorem rawDiagonal_mul_translation_eq_affinePauliRow {n : ℕ}
    (x z : BooleanVec n) (sign : ZMod 2) :
    (rawDiagonalRow z (3 * yCount x z + phase4Sign sign)).mul (translationRow x) =
      affinePauliRow x z sign := by
  apply Row.ext
  · funext k
    simp [rawDiagonalRow, translationRow, affinePauliRow, pauliRow, Row.mul]
  · funext k
    simp [rawDiagonalRow, translationRow, affinePauliRow, pauliRow, Row.mul]
  · change 3 * yCount x z + phase4Sign sign + 0 +
      (∑ k, pauliMulPhase (letter false (vecToReg z k))
        (letter (vecToReg x k) false)) = phase4Sign sign
    have hf : ∀ k, pauliMulPhase (letter false (vecToReg z k))
        (letter (vecToReg x k) false) =
          1 * (if x k = 1 ∧ z k = 1 then (1 : Phase4) else 0) := by
      intro k
      rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one (x k) with hx | hx <;>
        rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one
            (z k) with hz | hz <;>
        simp [letter, pauliMulPhase, vecToReg_apply_of_eq_zero, vecToReg_apply_of_eq_one, hx, hz]
    simp_rw [hf]
    rw [← Finset.mul_sum]
    change 3 * yCount x z + phase4Sign sign + 0 + 1 * yCount x z = phase4Sign sign
    ring_nf
    simp [show (4 : Phase4) = 0 by decide]

theorem affinePauliRow_op {n : ℕ} (x z : BooleanVec n) (sign : ZMod 2) :
    op (affinePauliRow x z sign).decode =
      op (rawDiagonalRow z (3 * yCount x z + phase4Sign sign)).decode *
        op (translationRow x).decode := by
  rw [← row_mul_op, rawDiagonal_mul_translation_eq_affinePauliRow]

theorem affinePauliRow_mulVec {n : ℕ} (x z : BooleanVec n) (sign : ZMod 2)
    (ψ : QState (Reg n)) (r : Reg n) :
    (op (affinePauliRow x z sign).decode *ᵥ ψ) r =
      ((Complex.I ^ (3 * yCount x z + phase4Sign sign).val : ℂ) *
        booleanCharacter z (regToVec r)) * ψ (Qatlib.Concepts.HspRecovery.ReductionCore.regXor r (vecToReg x)) := by
  rw [affinePauliRow_op, ← Matrix.mulVec_mulVec, rawDiagonalRow_mulVec,
    translationRow_mulVec]

def affineOrthogonal {n : ℕ} (D : Submodule (ZMod 2) (BooleanVec n)) :
    Submodule (ZMod 2) (BooleanVec n) :=
  Qatlib.Concepts.HspRecovery.ReductionCore.booleanOrthogonalSubmodule D.toAddSubgroup

theorem finrank_add_finrank_affineOrthogonal {n : ℕ}
    (D : Submodule (ZMod 2) (BooleanVec n)) :
    Module.finrank (ZMod 2) D + Module.finrank (ZMod 2) (affineOrthogonal D) = n := by
  have h := Qatlib.Concepts.QuditTeleport.TeleportCore.card_characterAnnihilator D.toAddSubgroup
  rw [Qatlib.Concepts.HspRecovery.ReductionCore.card_characterAnnihilator_eq_two_pow_booleanOrthogonalRank] at h
  have hD : Fintype.card D.toAddSubgroup = 2 ^ Module.finrank (ZMod 2) D := by
    change Fintype.card D = 2 ^ Module.finrank (ZMod 2) D
    simpa using! (Module.card_eq_pow_finrank (K := ZMod 2) (V := D))
  have hV : Fintype.card (BooleanVec n) = 2 ^ n := by
    simp [BooleanVec]
  rw [hD, hV, ← pow_add] at h
  have heq : Qatlib.Concepts.HspRecovery.ReductionCore.booleanOrthogonalRank D.toAddSubgroup +
      Module.finrank (ZMod 2) D = n :=
    Nat.pow_right_injective (by decide : 2 ≤ 2) h
  change Module.finrank (ZMod 2) (affineOrthogonal D) +
    Module.finrank (ZMod 2) D = n at heq
  omega

noncomputable def affineIndexEquiv {n : ℕ} (D : Submodule (ZMod 2) (BooleanVec n)) :
    (Fin (Module.finrank (ZMod 2) D) ⊕
      Fin (Module.finrank (ZMod 2) (affineOrthogonal D))) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (finrank_add_finrank_affineOrthogonal D))

noncomputable def affineRowFamily {n : ℕ} (D : Submodule (ZMod 2) (BooleanVec n))
    (p : BooleanVec n) :
    (Fin (Module.finrank (ZMod 2) D) ⊕
      Fin (Module.finrank (ZMod 2) (affineOrthogonal D))) → Row n
  | Sum.inl i => translationRow (Module.finBasis (ZMod 2) D i : BooleanVec n)
  | Sum.inr j =>
      diagonalRow (Module.finBasis (ZMod 2) (affineOrthogonal D) j : BooleanVec n)
        (booleanDot (Module.finBasis (ZMod 2) (affineOrthogonal D) j : BooleanVec n) p)

noncomputable def affineSympFamily {n : ℕ} (D : Submodule (ZMod 2) (BooleanVec n)) :
    (Fin (Module.finrank (ZMod 2) D) ⊕
      Fin (Module.finrank (ZMod 2) (affineOrthogonal D))) → BooleanVec n × BooleanVec n
  | Sum.inl i => ((Module.finBasis (ZMod 2) D i : BooleanVec n), 0)
  | Sum.inr j => (0, (Module.finBasis (ZMod 2) (affineOrthogonal D) j : BooleanVec n))

noncomputable def affineTableau {n : ℕ} (D : Submodule (ZMod 2) (BooleanVec n))
    (p : BooleanVec n) : Tableau n n :=
  fun i => affineRowFamily D p ((affineIndexEquiv D).symm i)

theorem rowSympVec_affineTableau {n : ℕ} (D : Submodule (ZMod 2) (BooleanVec n))
    (p : BooleanVec n) (i : Fin n) :
    rowSympVec (affineTableau D p) i = affineSympFamily D ((affineIndexEquiv D).symm i) := by
  change symplecticVec (affineRowFamily D p ((affineIndexEquiv D).symm i)).decode.word = _
  cases h : (affineIndexEquiv D).symm i with
  | inl j =>
      simp [affineRowFamily, affineSympFamily, symplecticVec_translationRow]
  | inr j =>
      simp [affineRowFamily, affineSympFamily, symplecticVec_diagonalRow]

theorem affineSympFamily_linearIndependent {n : ℕ}
    (D : Submodule (ZMod 2) (BooleanVec n)) :
    LinearIndependent (ZMod 2) (affineSympFamily D) := by
  have hD : LinearIndependent (ZMod 2)
      (fun i => (Module.finBasis (ZMod 2) D i : BooleanVec n)) := by
    simpa [Function.comp_def] using!
      (Module.finBasis (ZMod 2) D).linearIndependent.map' D.subtype (Submodule.ker_subtype D)
  have hO : LinearIndependent (ZMod 2)
      (fun j => (Module.finBasis (ZMod 2) (affineOrthogonal D) j : BooleanVec n)) := by
    simpa [Function.comp_def] using!
      (Module.finBasis (ZMod 2) (affineOrthogonal D)).linearIndependent.map'
        (affineOrthogonal D).subtype (Submodule.ker_subtype (affineOrthogonal D))
  have heq : affineSympFamily D = Sum.elim
      (fun i => ((Module.finBasis (ZMod 2) D i : BooleanVec n), 0))
      (fun j => (0, (Module.finBasis (ZMod 2) (affineOrthogonal D) j : BooleanVec n))) := by
    funext x
    cases x <;> rfl
  rw [heq]
  simpa [Function.comp_def] using! linearIndependent_inl_union_inr' hD hO

theorem affineTableau_independent {n : ℕ} (D : Submodule (ZMod 2) (BooleanVec n))
    (p : BooleanVec n) : IndependentGenerators (tableauGenerators (affineTableau D p)) := by
  apply independent_of_row_linearIndependent
  have h := (affineSympFamily_linearIndependent D).comp
    (affineIndexEquiv D).symm (affineIndexEquiv D).symm.injective
  have heq : rowSympVec (affineTableau D p) =
      fun i => affineSympFamily D ((affineIndexEquiv D).symm i) := by
    funext i
    exact rowSympVec_affineTableau D p i
  rw [heq]
  simpa [Function.comp_def] using! h

theorem booleanDot_comm_affine {n : ℕ} (x y : BooleanVec n) :
    booleanDot x y = booleanDot y x := by
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm (x i) (y i)

theorem affineOrthogonal_dot {n : ℕ} {D : Submodule (ZMod 2) (BooleanVec n)}
    {z x : BooleanVec n} (hz : z ∈ affineOrthogonal D) (hx : x ∈ D) :
    booleanDot z x = 0 := by
  exact hz ⟨x, hx⟩

theorem affineTableau_consistent {n : ℕ} (D : Submodule (ZMod 2) (BooleanVec n))
    (p : BooleanVec n) : ConsistentTableau (affineTableau D p) := by
  constructor
  · intro i
    cases h : (affineIndexEquiv D).symm i with
    | inl j =>
        left
        simp [affineTableau, affineRowFamily, h, translationRow, Row.decode]
    | inr j =>
        simpa [affineTableau, affineRowFamily, h] using!
          (diagonalRow_hermitian
            (Module.finBasis (ZMod 2) (affineOrthogonal D) j : BooleanVec n)
            (booleanDot (Module.finBasis (ZMod 2) (affineOrthogonal D) j : BooleanVec n) p))
  · intro i j
    apply (op_commute_iff_symplecticVec_form_zero _ _).mpr
    change symplecticForm (rowSympVec (affineTableau D p) i)
      (rowSympVec (affineTableau D p) j) = 0
    rw [rowSympVec_affineTableau, rowSympVec_affineTableau]
    cases hi : (affineIndexEquiv D).symm i with
    | inl di =>
        cases hj : (affineIndexEquiv D).symm j with
        | inl dj => simp [affineSympFamily, symplecticForm, booleanDot]
        | inr oj =>
            have hz := affineOrthogonal_dot (D := D)
              (Module.finBasis (ZMod 2) (affineOrthogonal D) oj).property
              (Module.finBasis (ZMod 2) D di).property
            simp only [affineSympFamily, symplecticForm]
            rw [booleanDot_comm_affine, hz]
            simp [booleanDot]
    | inr oi =>
        cases hj : (affineIndexEquiv D).symm j with
        | inl dj =>
            have hz := affineOrthogonal_dot (D := D)
              (Module.finBasis (ZMod 2) (affineOrthogonal D) oi).property
              (Module.finBasis (ZMod 2) D dj).property
            simp only [affineSympFamily, symplecticForm]
            rw [hz]
            simp [booleanDot]
        | inr oj => simp [affineSympFamily, symplecticForm, booleanDot]

def uniformAffineFun {n : ℕ} (D : Submodule (ZMod 2) (BooleanVec n))
    (p : BooleanVec n) : BooleanVec n → ℂ :=
  fun x => if x ∈ AffineSubspace.mk' p D then (1 : ℂ) else 0

def uniformAffineState {n : ℕ} (D : Submodule (ZMod 2) (BooleanVec n))
    (p : BooleanVec n) : QState (Reg n) :=
  stateOfFn (uniformAffineFun D p)

theorem regToVec_regXor {n : ℕ} (r x : Reg n) :
    regToVec (Qatlib.Concepts.HspRecovery.ReductionCore.regXor r x) = regToVec r + regToVec x :=
  Qatlib.Concepts.HspRecovery.ReductionCore.regBooleanEquiv_xor r x

theorem regToVec_regXor_vecToReg {n : ℕ} (r : Reg n) (d : BooleanVec n) :
    regToVec (Qatlib.Concepts.HspRecovery.ReductionCore.regXor r (vecToReg d)) = d + regToVec r := by
  rw [regToVec_regXor]
  have hd : regToVec (vecToReg d) = d := regVecEquiv.apply_symm_apply d
  rw [hd, add_comm]

theorem mem_mk'_regXor_translation {n : ℕ} {D : Submodule (ZMod 2) (BooleanVec n)}
    {d : BooleanVec n} (hd : d ∈ D) (p : BooleanVec n) (r : Reg n) :
    regToVec (Qatlib.Concepts.HspRecovery.ReductionCore.regXor r (vecToReg d)) ∈ AffineSubspace.mk' p D ↔
      regToVec r ∈ AffineSubspace.mk' p D := by
  rw [regToVec_regXor_vecToReg]
  exact AffineSubspace.vadd_mem_iff_mem_of_mem_direction (by simpa using! hd)

theorem translationRow_uniformAffineState {n : ℕ} {D : Submodule (ZMod 2) (BooleanVec n)}
    {p d : BooleanVec n} (hd : d ∈ D) :
    op (translationRow d).decode *ᵥ uniformAffineState D p = uniformAffineState D p := by
  funext r
  rw [translationRow_mulVec]
  simp only [uniformAffineState, uniformAffineFun, stateOfFn]
  rw [mem_mk'_regXor_translation hd]

theorem diagonalRow_uniformAffineState {n : ℕ} {D : Submodule (ZMod 2) (BooleanVec n)}
    {p z : BooleanVec n} (hz : z ∈ affineOrthogonal D) :
    op (diagonalRow z (booleanDot z p)).decode *ᵥ uniformAffineState D p =
      uniformAffineState D p := by
  funext r
  rw [diagonalRow_mulVec]
  by_cases hr : regToVec r ∈ AffineSubspace.mk' p D
  · have hdir : regToVec r - p ∈ D := by
      simpa using! AffineSubspace.vsub_mem_direction hr (AffineSubspace.self_mem_mk' p D)
    have hzdir := affineOrthogonal_dot hz hdir
    have hdot : booleanDot z (regToVec r) = booleanDot z p := by
      have hadd :=
          (Qatlib.Concepts.PauliClifford.ExactRank.booleanDotHom z).map_add (regToVec r - p) p
      rw [sub_add_cancel] at hadd
      change booleanDot z (regToVec r) = booleanDot z (regToVec r - p) + booleanDot z p at hadd
      rw [hadd, hzdir, zero_add]
    have hchar : booleanCharacter z (regToVec r) = booleanCharacter z p := by
      simp only [Qatlib.Concepts.PauliClifford.ExactRank.booleanCharacter_apply, hdot]
    have hsign : (if booleanDot z p = 0 then (1 : ℂ) else -1) *
        booleanCharacter z p = 1 := by
      rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one (booleanDot z p) with h | h <;>
        simp [h, Qatlib.Concepts.PauliClifford.ExactRank.booleanCharacter_apply]
    simp only [uniformAffineState, uniformAffineFun, stateOfFn, hr, if_pos, mul_one]
    rw [hchar]
    exact hsign
  · simp [uniformAffineState, uniformAffineFun, stateOfFn, hr]

theorem uniformAffineState_mem_codeSpace {n : ℕ} (D : Submodule (ZMod 2) (BooleanVec n))
    (p : BooleanVec n) : uniformAffineState D p ∈ codeSpace (affineTableau D p) := by
  intro i
  cases h : (affineIndexEquiv D).symm i with
  | inl j =>
      simpa [affineTableau, affineRowFamily, h] using!
        (translationRow_uniformAffineState (D := D) (p := p)
          (Module.finBasis (ZMod 2) D j).property)
  | inr j =>
      simpa [affineTableau, affineRowFamily, h] using!
        (diagonalRow_uniformAffineState (D := D) (p := p)
          (Module.finBasis (ZMod 2) (affineOrthogonal D) j).property)

theorem uniformAffineFun_ne_zero {n : ℕ} (D : Submodule (ZMod 2) (BooleanVec n))
    (p : BooleanVec n) : uniformAffineFun D p ≠ 0 := by
  intro hzero
  have h := congrFun hzero p
  simp [uniformAffineFun] at h

theorem normalizedStabilizerState_uniform_physical {n : ℕ}
    (D : Submodule (ZMod 2) (BooleanVec n)) (p : BooleanVec n) :
    IsNormalizedPhysicalStabilizerState
      (normalizedStabilizerState (uniformAffineFun D p)) := by
  have hmass : 0 < stabilizerFunMass (uniformAffineFun D p) := by
    unfold stabilizerFunMass
    apply Finset.sum_pos' (fun x _ => sq_nonneg ‖uniformAffineFun D p x‖)
    refine ⟨p, Finset.mem_univ _, ?_⟩
    simp [uniformAffineFun]
  refine ⟨normalizedStabilizerState_normalized _ hmass,
    affineTableau D p, affineTableau_consistent D p, affineTableau_independent D p, ?_⟩
  have hum := uniformAffineState_mem_codeSpace D p
  change stateOfFn (fun x => uniformAffineFun D p x *
    (Real.sqrt (stabilizerFunMass (uniformAffineFun D p)) : ℂ)⁻¹) ∈ codeSpace (affineTableau D p)
  have heq : (fun x => uniformAffineFun D p x *
      (Real.sqrt (stabilizerFunMass (uniformAffineFun D p)) : ℂ)⁻¹) =
      fun x => (Real.sqrt (stabilizerFunMass (uniformAffineFun D p)) : ℂ)⁻¹ *
        uniformAffineFun D p x := by
    funext x
    ring
  rw [heq, stateOfFn_smul]
  exact (codeSpace (affineTableau D p)).smul_mem _ hum

theorem isStabilizerFun_uniformAffineFun {n : ℕ} (D : Submodule (ZMod 2) (BooleanVec n))
    (p : BooleanVec n) : IsStabilizerFun (uniformAffineFun D p) := by
  refine ⟨0, 0, 0, 0, AffineSubspace.mk' p D, ?_⟩
  funext x
  simp [uniformAffineFun, booleanDot, quadFun]

theorem normalizedStabilizerState_affine_uniform_physical {n : ℕ}
    {A : AffineSubspace (ZMod 2) (BooleanVec n)} {p : BooleanVec n} (hp : p ∈ A) :
    IsNormalizedPhysicalStabilizerState
      (normalizedStabilizerState (fun x => if x ∈ A then (1 : ℂ) else 0)) := by
  rw [← AffineSubspace.mk'_eq hp]
  exact normalizedStabilizerState_uniform_physical A.direction p

def basisTableau {n : ℕ} (p : Reg n) : Tableau n n :=
  fun i => ⟨fun _ => false, fun k => decide (k = i), if p i then 2 else 0⟩

theorem basis_row_symp {n : ℕ} (p : Reg n) (i : Fin n) :
    rowSympVec (basisTableau p) i = (0, Pi.single i (1 : ZMod 2)) := by
  apply Prod.ext
  · funext j
    by_cases h : j = i <;>
      simp [rowSympVec, symplecticVec, basisTableau, Row.decode, letter, symplecticX, h]
  · funext j
    by_cases h : j = i <;>
      simp [rowSympVec, symplecticVec, basisTableau, Row.decode, letter, symplecticZ,
        Pi.single_apply, h]

theorem basisTableau_consistent {n : ℕ} (p : Reg n) :
    ConsistentTableau (basisTableau p) := by
  constructor
  · intro i
    by_cases h : p i <;> simp [IsHermitianPauli, basisTableau, Row.decode, h]
  · intro i j
    apply (op_commute_iff_symplecticVec_form_zero _ _).mpr
    change symplecticForm (rowSympVec (basisTableau p) i)
      (rowSympVec (basisTableau p) j) = 0
    rw [basis_row_symp, basis_row_symp]
    simp [symplecticForm, booleanDot]

theorem basisTableau_linearIndependent {n : ℕ} (p : Reg n) :
    LinearIndependent (ZMod 2) (rowSympVec (basisTableau p)) := by
  simpa only [basis_row_symp, zero_row_symp] using! zero_tableau_linearIndependent n

theorem basisTableau_independent {n : ℕ} (p : Reg n) :
    IndependentGenerators (tableauGenerators (basisTableau p)) :=
  independent_of_row_linearIndependent _ (basisTableau_linearIndependent p)

theorem basis_row_op {n : ℕ} (p : Reg n) (i : Fin n) :
    op (basisTableau p i).decode = Matrix.diagonal (fun b : Reg n =>
      if b i = p i then (1 : ℂ) else -1) := by
  ext b c
  rw [op_apply]
  simp only [basisTableau, Row.decode, Matrix.diagonal_apply]
  by_cases hbc : b = c
  · subst c
    rw [if_pos rfl]
    have hf : ∀ k, P1 (letter false (decide (k = i))) (b k) (b k) =
        if k = i then (if b k then (-1 : ℂ) else 1) else 1 := by
      intro k
      by_cases hk : k = i
      · subst k
        cases b i <;> simp [letter, P1]
      · cases b k <;> simp [hk, letter, P1]
    simp_rw [hf]
    by_cases hb : b i <;> by_cases hp : p i <;>
      simp [hb, hp, zmod4_val_two]
  · rw [if_neg hbc]
    have hzero : (∏ k, P1 (letter false (decide (k = i))) (b k) (c k)) = 0 := by
      obtain ⟨k, hk⟩ := Function.ne_iff.mp hbc
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      by_cases hki : k = i <;> cases hb : b k <;> cases hc : c k <;>
        simp_all [letter, P1]
    rw [hzero, mul_zero]

theorem basis_row_mulVec {n : ℕ} (p : Reg n) (i : Fin n)
    (ψ : QState (Reg n)) (b : Reg n) :
    (op (basisTableau p i).decode *ᵥ ψ) b =
      (if b i = p i then (1 : ℂ) else -1) * ψ b := by
  rw [basis_row_op]
  exact Matrix.mulVec_diagonal _ _ _

theorem mem_basis_code_iff {n : ℕ} (p : Reg n) (ψ : QState (Reg n)) :
    ψ ∈ codeSpace (basisTableau p) ↔ ∃ c : ℂ, ψ = c • Qatlib.Foundations.PureStateMath.Ket p := by
  constructor
  · intro hψ
    refine ⟨ψ p, ?_⟩
    funext b
    by_cases hb : b = p
    · subst b
      simp [Qatlib.Foundations.PureStateMath.Ket]
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hb
      have h := congrFun (hψ i) b
      rw [basis_row_mulVec, if_neg hi] at h
      have hz : ψ b = 0 := by linear_combination (-(1 / 2 : ℂ)) * h
      simp [Qatlib.Foundations.PureStateMath.Ket, hb, hz]
  · rintro ⟨c, rfl⟩ i
    rw [Matrix.mulVec_smul]
    congr 1
    funext b
    rw [basis_row_mulVec]
    by_cases hb : b = p
    · subst b
      simp [Qatlib.Foundations.PureStateMath.Ket]
    · simp [Qatlib.Foundations.PureStateMath.Ket, hb]

theorem basis_isNormalizedPhysicalStabilizerState {n : ℕ} (p : Reg n) :
    IsNormalizedPhysicalStabilizerState (Qatlib.Foundations.PureStateMath.Ket p) := by
  refine ⟨normalized_ket p, basisTableau p, basisTableau_consistent p,
    basisTableau_independent p, ?_⟩
  exact (mem_basis_code_iff p (Qatlib.Foundations.PureStateMath.Ket p)).mpr ⟨1,
      (one_smul ℂ _).symm⟩

theorem amplitudeFn_ket {n : ℕ} (p : Reg n) :
    amplitudeFn (Qatlib.Foundations.PureStateMath.Ket p) = fun x => if x = regToVec p then (1 : ℂ) else 0 := by
  funext x
  by_cases h : x = regToVec p
  · subst x
    have hround : vecToReg (regToVec p) = p := regVecEquiv.symm_apply_apply p
    simp [amplitudeFn, Qatlib.Foundations.PureStateMath.Ket, hround]
  · have hr : vecToReg x ≠ p := by
      intro hp
      apply h
      rw [← hp]
      exact (regVecEquiv.apply_symm_apply x).symm
    simp [amplitudeFn, Qatlib.Foundations.PureStateMath.Ket, h, hr]

theorem amplitudeFn_smul {n : ℕ} (lam : ℂ) (ψ : QState (Reg n)) :
    amplitudeFn (lam • ψ) = fun x => lam * amplitudeFn ψ x := rfl

theorem isStabilizerFunUpToPhase_of_normalized_codeState {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t))
    (ψ φ : QState (Reg n)) (hψ : ψ ∈ codeSpace t) (hφ : φ ∈ codeSpace t)
    (hnψ : Normalized ψ) (hnφ : Normalized φ)
    (hextract : IsStabilizerFunUpToPhase (amplitudeFn ψ)) :
    IsStabilizerFunUpToPhase (amplitudeFn φ) := by
  obtain ⟨lam, hlam, hrel⟩ := unique_stabilizerState_unitPhase t ht hind ψ φ hψ hφ hnψ hnφ
  have hne : lam ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hlam
    exact zero_ne_one hlam
  rw [hrel, amplitudeFn_smul]
  exact isStabilizerFunUpToPhase_smul hextract lam hne

theorem stabilizerFunMass_delta {n : ℕ} (p : BooleanVec n) :
    stabilizerFunMass (fun x => if x = p then (1 : ℂ) else 0) = 1 := by
  have h : ∀ x : BooleanVec n, ‖if x = p then (1 : ℂ) else 0‖ ^ 2 =
      if x = p then (1 : ℝ) else 0 := by
    intro x
    by_cases hx : x = p <;> simp [hx]
  rw [stabilizerFunMass]
  simp_rw [h]
  simp

theorem normalizedStabilizerState_delta {n : ℕ} (p : Reg n) :
    normalizedStabilizerState (fun x => if x = regToVec p then (1 : ℂ) else 0) =
      Qatlib.Foundations.PureStateMath.Ket p := by
  unfold normalizedStabilizerState
  rw [stabilizerFunMass_delta]
  simp only [Real.sqrt_one, Complex.ofReal_one, inv_one, mul_one]
  rw [← amplitudeFn_ket p]
  exact stateOfFn_amplitudeFn (Qatlib.Foundations.PureStateMath.Ket p)

theorem normalizedStabilizerState_delta_physical {n : ℕ} (p : Reg n) :
    IsNormalizedPhysicalStabilizerState
      (normalizedStabilizerState (fun x => if x = regToVec p then (1 : ℂ) else 0)) := by
  rw [normalizedStabilizerState_delta]
  exact basis_isNormalizedPhysicalStabilizerState p

theorem normalizedStabilizerState_delta_smul {n : ℕ} (p : Reg n)
    (lam : ℂ) (hlam : lam ≠ 0) (r : Reg n) :
    normalizedStabilizerState
        (fun x => lam * (if x = regToVec p then (1 : ℂ) else 0)) r =
      (lam * ((‖lam‖ : ℝ) : ℂ)⁻¹) * Qatlib.Foundations.PureStateMath.Ket p r := by
  rw [normalizedStabilizerState_smul _ lam hlam (by simp [stabilizerFunMass_delta]) r,
    normalizedStabilizerState_delta]

theorem basis_extract_upToPhase {n : ℕ} (p : Reg n) (ψ : QState (Reg n))
    (hψ : ψ ∈ codeSpace (basisTableau p)) (hn : Normalized ψ) :
    ∃ lam : ℂ, ‖lam‖ = 1 ∧ ψ = lam • Qatlib.Foundations.PureStateMath.Ket p ∧
      IsStabilizerFunUpToPhase (amplitudeFn ψ) := by
  obtain ⟨lam, hlam, hrel⟩ := unique_stabilizerState_unitPhase (basisTableau p)
    (basisTableau_consistent p) (basisTableau_independent p) (Qatlib.Foundations.PureStateMath.Ket p) ψ
    ((mem_basis_code_iff p (Qatlib.Foundations.PureStateMath.Ket p)).mpr ⟨1, (one_smul ℂ _).symm⟩) hψ
    (normalized_ket p) hn
  have hne : lam ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hlam
    exact zero_ne_one hlam
  refine ⟨lam, hlam, hrel, lam, fun x => if x = regToVec p then (1 : ℂ) else 0,
    hne, isStabilizerFun_delta (regToVec p), ?_⟩
  rw [hrel, amplitudeFn_smul, amplitudeFn_ket]

theorem isStabilizerFun_zero {n : ℕ} :
    IsStabilizerFun (0 : BooleanVec n → ℂ) := by
  refine ⟨0, 0, 0, 0, ⊥, ?_⟩
  funext x
  simp [booleanDot, quadFun, AffineSubspace.notMem_bot]

theorem stabilizerFunMass_eq_zero_iff {n : ℕ} (φ : BooleanVec n → ℂ) :
    stabilizerFunMass φ = 0 ↔ φ = 0 := by
  constructor
  · intro h
    funext x
    have hx := (Finset.sum_eq_zero_iff_of_nonneg
      (fun y (_ : y ∈ (Finset.univ : Finset (BooleanVec n))) => sq_nonneg ‖φ y‖)).mp h
      x (Finset.mem_univ x)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)
  · rintro rfl
    simp [stabilizerFunMass]

theorem stabilizerFunMass_pos_of_ne_zero {n : ℕ} {φ : BooleanVec n → ℂ}
    (hφ : φ ≠ 0) : 0 < stabilizerFunMass φ := by
  have hnonneg : 0 ≤ stabilizerFunMass φ := by
    unfold stabilizerFunMass
    positivity
  have hne : stabilizerFunMass φ ≠ 0 := by
    intro hzero
    exact hφ ((stabilizerFunMass_eq_zero_iff φ).mp hzero)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

theorem normalizedStabilizerState_zero {n : ℕ} :
    normalizedStabilizerState (0 : BooleanVec n → ℂ) = 0 := by
  funext r
  simp [normalizedStabilizerState, stateOfFn, stabilizerFunMass]

theorem zero_isPhysicalStabilizerState {n : ℕ} :
    IsPhysicalStabilizerState (0 : QState (Reg n)) := by
  exact ⟨zeroTableau n, zero_tableau_consistent n, zero_tableau_independent n,
    (codeSpace (zeroTableau n)).zero_mem⟩

theorem normalizedStabilizerState_zero_physical {n : ℕ} :
    IsPhysicalStabilizerState (normalizedStabilizerState (0 : BooleanVec n → ℂ)) := by
  rw [normalizedStabilizerState_zero]
  exact zero_isPhysicalStabilizerState

theorem normalizedStabilizerState_normalized_of_ne_zero {n : ℕ} {φ : BooleanVec n → ℂ}
    (hφ : φ ≠ 0) : Normalized (normalizedStabilizerState φ) :=
  normalizedStabilizerState_normalized φ (stabilizerFunMass_pos_of_ne_zero hφ)

theorem isStabilizerFunUpToPhase_amplitude_normalized {n : ℕ} (φ : BooleanVec n → ℂ)
    (hφ : IsStabilizerFun φ) :
    IsStabilizerFunUpToPhase (amplitudeFn (normalizedStabilizerState φ)) := by
  by_cases hzero : φ = 0
  · subst φ
    refine ⟨1, 0, one_ne_zero, isStabilizerFun_zero, ?_⟩
    rw [normalizedStabilizerState_zero]
    funext x
    simp [amplitudeFn]
  · have hmass : 0 < stabilizerFunMass φ := stabilizerFunMass_pos_of_ne_zero hzero
    have hsqrt : (Real.sqrt (stabilizerFunMass φ) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos_of_pos hmass))
    refine ⟨(Real.sqrt (stabilizerFunMass φ) : ℂ)⁻¹, φ, inv_ne_zero hsqrt, hφ, ?_⟩
    funext x
    rw [normalizedStabilizerState, amplitudeFn, stateOfFn]
    have hrt : regToVec (vecToReg x) = x := regVecEquiv.apply_symm_apply x
    rw [hrt]
    exact mul_comm (φ x) ((Real.sqrt (stabilizerFunMass φ) : ℂ)⁻¹)

theorem exact_rank_collision_of_amplitude_rank {n r : ℕ} (φ : BooleanVec n → ℂ)
    (hn : 1 ≤ n) (hrn : 100 * r ≤ n) (hF : stabilizerRank φ ≤ r) :
    ∃ y z : BooleanVec n, cubeWeight y ≠ cubeWeight z ∧
      amplitudeFn (normalizedStabilizerState φ) y =
        amplitudeFn (normalizedStabilizerState φ) z := by
  apply exact_rank_collision_normalizedStabilizerState φ hn hrn
  rwa [stabilizerRank_normalizedStabilizerState]

def phase4OfBit (x : ZMod 2) : Phase4 := x.val

def quadDirection {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (d : BooleanVec n) : BooleanVec n :=
  fun i => ∑ j, (Q i j + Q j i) * d j

def stabilizerPhaseDirection {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (d : BooleanVec n) : BooleanVec n :=
  (booleanDot a d) • a + quadDirection Q d

def stabilizerPhaseTarget {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n) (d : BooleanVec n) : Phase4 :=
  -phase4OfBit (booleanDot a d) + phase4Sign (quadFun Q b 0 d)

def stabilizerPhaseSign {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n) (d : BooleanVec n) : ZMod 2 :=
  if 3 * yCount d (stabilizerPhaseDirection a Q d) = stabilizerPhaseTarget a Q b d then 0 else 1

theorem yCount_val_mod_two {n : ℕ} (x z : BooleanVec n) :
    (yCount x z).val % 2 = (booleanDot x z).val := by
  let f : Phase4 →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)
  have hsum : f (yCount x z) = booleanDot x z := by
    simp only [yCount, map_sum, booleanDot]
    apply Finset.sum_congr rfl
    intro k _
    rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one (x k) with hx | hx <;>
      rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one
          (z k) with hz | hz <;>
      simp [f, hx, hz]
  have hcast (y : Phase4) : f y = (y.val : ZMod 2) := by
    simp [f, ZMod.castHom_apply]
  have hval := congrArg ZMod.val (hcast (yCount x z))
  rw [hsum] at hval
  simpa [ZMod.val_natCast] using! hval.symm

theorem negOnePowZ2_add (u v : ZMod 2) :
    ((-1 : ℂ) ^ (u + v).val) = (-1 : ℂ) ^ u.val * (-1 : ℂ) ^ v.val := by
  rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one u with rfl | rfl <;>
    rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one v with rfl | rfl <;>
    simp [StabilizerDesign.zmod2_val_one, StabilizerDesign.zmod2_val_one_add_one]

theorem iPowZ2_add (u v : ZMod 2) :
    (Complex.I ^ (u + v).val : ℂ) = (-1 : ℂ) ^ (u * v).val *
      Complex.I ^ u.val * Complex.I ^ v.val := by
  rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one u with rfl | rfl <;>
    rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one v with rfl | rfl <;>
    simp [StabilizerDesign.zmod2_val_one, StabilizerDesign.zmod2_val_one_add_one]

theorem booleanCharacter_eq_negOnePow {n : ℕ} (z x : BooleanVec n) :
    booleanCharacter z x = (-1 : ℂ) ^ (booleanDot z x).val := by
  rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one (booleanDot z x) with h | h <;>
    simp [h, Qatlib.Concepts.PauliClifford.ExactRank.booleanCharacter_apply,
        StabilizerDesign.zmod2_val_one]

theorem booleanDot_quadDirection_self {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (d : BooleanVec n) :
    booleanDot d (quadDirection Q d) = 0 := by
  have hswap : (∑ i, ∑ j, d i * Q j i * d j) = ∑ i, ∑ j, d i * Q i j * d j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    booleanDot d (quadDirection Q d) =
        (∑ i, ∑ j, d i * Q i j * d j) + (∑ i, ∑ j, d i * Q j i * d j) := by
      simp only [booleanDot, quadDirection, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ i, ∑ j, d i * Q i j * d j) + (∑ i, ∑ j, d i * Q i j * d j) := by rw [hswap]
    _ = 0 := by
      have htwo : (∑ i, ∑ j, d i * Q i j * d j) + (∑ i, ∑ j, d i * Q i j * d j) =
          (∑ i, ∑ j, d i * Q i j * d j) * 2 := by ring
      rw [htwo, show (2 : ZMod 2) = 0 by decide, mul_zero]

theorem booleanDot_stabilizerPhaseDirection {n : ℕ} (a d x : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) :
    booleanDot (stabilizerPhaseDirection a Q d) x =
      booleanDot a d * booleanDot a x + booleanDot (quadDirection Q d) x := by
  rw [stabilizerPhaseDirection, Qatlib.Concepts.HspRecovery.ReductionCore.booleanDot_add_left]
  congr 1
  simp only [Pi.smul_apply, booleanDot, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem booleanDot_direction_stabilizerPhaseDirection {n : ℕ} (a d : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) :
    booleanDot d (stabilizerPhaseDirection a Q d) = booleanDot a d := by
  rw [stabilizerPhaseDirection, Qatlib.Concepts.HspRecovery.ReductionCore.booleanDot_add_right,
    booleanDot_quadDirection_self, add_zero]
  rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one
      (booleanDot a d) with h | h
  · rw [h]
    simp [booleanDot]
  · rw [h]
    simp only [one_smul]
    exact (booleanDot_comm_affine d a).trans h

theorem phase4_adjust_of_parity (y : Phase4) (u k : ZMod 2)
    (h : y.val % 2 = u.val) :
    3 * y + phase4Sign
        (if 3 * y = -phase4OfBit u + phase4Sign k then 0 else 1) =
      -phase4OfBit u + phase4Sign k := by
  fin_cases y <;>
    rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one u with rfl | rfl <;>
    rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one k with rfl | rfl <;>
    revert h <;> decide

theorem stabilizerPhaseSign_adjust {n : ℕ} (a d : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n) :
    3 * yCount d (stabilizerPhaseDirection a Q d) +
        phase4Sign (stabilizerPhaseSign a Q b d) = stabilizerPhaseTarget a Q b d := by
  apply phase4_adjust_of_parity
  rw [yCount_val_mod_two, booleanDot_direction_stabilizerPhaseDirection]

def stabilizerPhase {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n) (c : ZMod 2)
    (x : BooleanVec n) : ℂ :=
  Complex.I ^ (booleanDot a x).val * (-1 : ℂ) ^ (quadFun Q b c x).val

def stabilizerAffineFun {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n) (c : ZMod 2)
    (A : AffineSubspace (ZMod 2) (BooleanVec n)) : BooleanVec n → ℂ :=
  fun x => stabilizerPhase a Q b c x * (if x ∈ A then (1 : ℂ) else 0)

def stabilizerAffineState {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n) (c : ZMod 2)
    (A : AffineSubspace (ZMod 2) (BooleanVec n)) : QState (Reg n) :=
  stateOfFn (stabilizerAffineFun a Q b c A)

theorem quadFun_add_direction {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (b d x : BooleanVec n) (c : ZMod 2) :
    quadFun Q b c (d + x) = quadFun Q b c x + booleanDot (quadDirection Q d) x +
      quadFun Q b 0 d := by
  have hQ : (∑ i, ∑ j, Q i j * (d i + x i) * (d j + x j)) =
      (∑ i, ∑ j, Q i j * x i * x j) + (∑ i, ∑ j, Q i j * x i * d j) +
        (∑ i, ∑ j, Q i j * d i * x j) + (∑ i, ∑ j, Q i j * d i * d j) := by
    simp only [mul_add, add_mul, Finset.sum_add_distrib]
    ring
  have hswap : (∑ i, ∑ j, Q i j * d i * x j) = ∑ i, ∑ j, Q j i * d j * x i := by
    rw [Finset.sum_comm]
  have hD : booleanDot (quadDirection Q d) x =
      (∑ i, ∑ j, Q i j * x i * d j) + (∑ i, ∑ j, Q i j * d i * x j) := by
    rw [hswap]
    calc
      booleanDot (quadDirection Q d) x =
          (∑ i, ∑ j, Q i j * d j * x i) + (∑ i, ∑ j, Q j i * d j * x i) := by
        simp only [booleanDot, quadDirection, Finset.sum_mul, add_mul,
          Finset.sum_add_distrib]
      _ = (∑ i, ∑ j, Q i j * x i * d j) + (∑ i, ∑ j, Q j i * d j * x i) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hB : (∑ i, b i * (d i + x i)) = (∑ i, b i * d i) + ∑ i, b i * x i := by
    simp only [mul_add, Finset.sum_add_distrib]
  simp only [quadFun, Pi.add_apply]
  rw [hQ, hD, hB]
  ring

theorem stabilizerPhase_add {n : ℕ} (a d x : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n) (c : ZMod 2) :
    stabilizerPhase a Q b c (d + x) =
      (Complex.I ^ (booleanDot a d).val * (-1 : ℂ) ^ (quadFun Q b 0 d).val) *
        booleanCharacter (stabilizerPhaseDirection a Q d) x * stabilizerPhase a Q b c x := by
  simp only [stabilizerPhase]
  rw [Qatlib.Concepts.HspRecovery.ReductionCore.booleanDot_add_right, quadFun_add_direction,
    iPowZ2_add, negOnePowZ2_add, negOnePowZ2_add,
    booleanCharacter_eq_negOnePow, booleanDot_stabilizerPhaseDirection,
    negOnePowZ2_add]
  ring

theorem phase4Target_cancel (u k : ZMod 2) :
    (Complex.I ^ (-phase4OfBit u + phase4Sign k).val : ℂ) *
      Complex.I ^ u.val * (-1 : ℂ) ^ k.val = 1 := by
  rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one u with rfl | rfl <;>
    rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one k with rfl | rfl <;>
    norm_num [phase4OfBit, phase4Sign, ZMod.val_one, zmod4_val_two,
      show (1 : Phase4).val = 1 by decide, pow_succ, Complex.I_mul_I]

theorem booleanCharacter_mul_self {n : ℕ} (z x : BooleanVec n) :
    booleanCharacter z x * booleanCharacter z x = 1 := by
  rw [booleanCharacter_eq_negOnePow, ← pow_add]
  rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one (booleanDot z x) with h | h <;>
    simp [h, StabilizerDesign.zmod2_val_one]

theorem quadDirection_zero {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2)) :
    quadDirection Q 0 = 0 := by
  funext i
  simp [quadDirection]

def stabilizerPhaseDirectionLinearMap {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) : BooleanVec n →ₗ[ZMod 2] BooleanVec n where
  toFun d := stabilizerPhaseDirection a Q d
  map_add' d e := by
    funext i
    simp only [stabilizerPhaseDirection, quadDirection, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Qatlib.Concepts.HspRecovery.ReductionCore.booleanDot_add_right, add_mul, mul_add,
      Finset.sum_add_distrib]
    ring
  map_smul' k d := by
    rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one k with rfl | rfl
    · funext i
      simp [stabilizerPhaseDirection, quadDirection_zero, booleanDot]
    · simp [stabilizerPhaseDirection, booleanDot]

def quadraticSympShear {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (BooleanVec n × BooleanVec n) →ₗ[ZMod 2] (BooleanVec n × BooleanVec n) where
  toFun v := (v.1, v.2 + stabilizerPhaseDirectionLinearMap a Q v.1)
  map_add' u v := by
    apply Prod.ext
    · rfl
    · change u.2 + v.2 + stabilizerPhaseDirectionLinearMap a Q (u.1 + v.1) =
        u.2 + stabilizerPhaseDirectionLinearMap a Q u.1 +
          (v.2 + stabilizerPhaseDirectionLinearMap a Q v.1)
      rw [map_add]
      abel
  map_smul' k v := by
    apply Prod.ext
    · rfl
    · change k • v.2 + stabilizerPhaseDirectionLinearMap a Q (k • v.1) =
        k • (v.2 + stabilizerPhaseDirectionLinearMap a Q v.1)
      rw [map_smul, smul_add]

theorem quadraticSympShear_injective {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Function.Injective (quadraticSympShear a Q) := by
  intro u v h
  have hfst := congrArg (fun w : BooleanVec n × BooleanVec n => w.1) h
  change u.1 = v.1 at hfst
  apply Prod.ext hfst
  have hsnd := congrArg (fun w : BooleanVec n × BooleanVec n => w.2) h
  change u.2 + stabilizerPhaseDirectionLinearMap a Q u.1 =
    v.2 + stabilizerPhaseDirectionLinearMap a Q v.1 at hsnd
  rw [hfst] at hsnd
  exact add_right_cancel hsnd

noncomputable def quadraticSympFamily {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (D : Submodule (ZMod 2) (BooleanVec n)) :
    (Fin (Module.finrank (ZMod 2) D) ⊕
      Fin (Module.finrank (ZMod 2) (affineOrthogonal D))) → BooleanVec n × BooleanVec n
  | Sum.inl i =>
      let d : BooleanVec n := Module.finBasis (ZMod 2) D i
      (d, stabilizerPhaseDirection a Q d)
  | Sum.inr j => (0, (Module.finBasis (ZMod 2) (affineOrthogonal D) j : BooleanVec n))

theorem quadraticSympFamily_eq_shear {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (D : Submodule (ZMod 2) (BooleanVec n)) :
    quadraticSympFamily a Q D = (quadraticSympShear a Q) ∘ affineSympFamily D := by
  funext i
  cases i <;>
    simp [quadraticSympFamily, quadraticSympShear, affineSympFamily,
      stabilizerPhaseDirectionLinearMap, stabilizerPhaseDirection, quadDirection_zero,
      booleanDot]

theorem quadraticSympFamily_linearIndependent {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (D : Submodule (ZMod 2) (BooleanVec n)) :
    LinearIndependent (ZMod 2) (quadraticSympFamily a Q D) := by
  have hker : LinearMap.ker (quadraticSympShear a Q) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (quadraticSympShear_injective a Q)
  have h := (affineSympFamily_linearIndependent D).map' (quadraticSympShear a Q) hker
  rw [quadraticSympFamily_eq_shear]
  simpa [Function.comp_def] using! h

theorem booleanDot_quadDirection_comm {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (d e : BooleanVec n) :
    booleanDot (quadDirection Q d) e = booleanDot (quadDirection Q e) d := by
  simp only [booleanDot, quadDirection, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem stabilizerPhaseDirection_symplectic {n : ℕ} (a d e : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) :
    symplecticForm (d, stabilizerPhaseDirection a Q d)
      (e, stabilizerPhaseDirection a Q e) = 0 := by
  simp only [symplecticForm]
  rw [booleanDot_comm_affine d (stabilizerPhaseDirection a Q e),
    booleanDot_stabilizerPhaseDirection, booleanDot_stabilizerPhaseDirection,
    booleanDot_quadDirection_comm Q e d]
  ring_nf
  simp [show (2 : ZMod 2) = 0 by decide]

noncomputable def quadraticAffineRowFamily {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n)
    (D : Submodule (ZMod 2) (BooleanVec n)) (p : BooleanVec n) :
    (Fin (Module.finrank (ZMod 2) D) ⊕
      Fin (Module.finrank (ZMod 2) (affineOrthogonal D))) → Row n
  | Sum.inl i =>
      let d : BooleanVec n := Module.finBasis (ZMod 2) D i
      affinePauliRow d (stabilizerPhaseDirection a Q d) (stabilizerPhaseSign a Q b d)
  | Sum.inr j =>
      diagonalRow (Module.finBasis (ZMod 2) (affineOrthogonal D) j : BooleanVec n)
        (booleanDot (Module.finBasis (ZMod 2) (affineOrthogonal D) j : BooleanVec n) p)

noncomputable def quadraticAffineTableau {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n)
    (D : Submodule (ZMod 2) (BooleanVec n)) (p : BooleanVec n) : Tableau n n :=
  fun i => quadraticAffineRowFamily a Q b D p ((affineIndexEquiv D).symm i)

theorem rowSympVec_quadraticAffineTableau {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n)
    (D : Submodule (ZMod 2) (BooleanVec n)) (p : BooleanVec n) (i : Fin n) :
    rowSympVec (quadraticAffineTableau a Q b D p) i =
      quadraticSympFamily a Q D ((affineIndexEquiv D).symm i) := by
  change symplecticVec
    (quadraticAffineRowFamily a Q b D p ((affineIndexEquiv D).symm i)).decode.word = _
  cases h : (affineIndexEquiv D).symm i with
  | inl j =>
      simp [quadraticAffineRowFamily, quadraticSympFamily, affinePauliRow,
        symplecticVec_pauliRow]
  | inr j =>
      simp [quadraticAffineRowFamily, quadraticSympFamily, symplecticVec_diagonalRow]

theorem quadraticAffineTableau_independent {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n)
    (D : Submodule (ZMod 2) (BooleanVec n)) (p : BooleanVec n) :
    IndependentGenerators (tableauGenerators (quadraticAffineTableau a Q b D p)) := by
  apply independent_of_row_linearIndependent
  have h := (quadraticSympFamily_linearIndependent a Q D).comp
    (affineIndexEquiv D).symm (affineIndexEquiv D).symm.injective
  have heq : rowSympVec (quadraticAffineTableau a Q b D p) =
      fun i => quadraticSympFamily a Q D ((affineIndexEquiv D).symm i) := by
    funext i
    exact rowSympVec_quadraticAffineTableau a Q b D p i
  rw [heq]
  simpa [Function.comp_def] using! h

theorem quadraticAffineTableau_consistent {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n)
    (D : Submodule (ZMod 2) (BooleanVec n)) (p : BooleanVec n) :
    ConsistentTableau (quadraticAffineTableau a Q b D p) := by
  constructor
  · intro i
    cases h : (affineIndexEquiv D).symm i with
    | inl j =>
        simpa [quadraticAffineTableau, quadraticAffineRowFamily, h] using!
          (affinePauliRow_hermitian
            (Module.finBasis (ZMod 2) D j : BooleanVec n)
            (stabilizerPhaseDirection a Q (Module.finBasis (ZMod 2) D j : BooleanVec n))
            (stabilizerPhaseSign a Q b (Module.finBasis (ZMod 2) D j : BooleanVec n)))
    | inr j =>
        simpa [quadraticAffineTableau, quadraticAffineRowFamily, h] using!
          (diagonalRow_hermitian
            (Module.finBasis (ZMod 2) (affineOrthogonal D) j : BooleanVec n)
            (booleanDot (Module.finBasis (ZMod 2) (affineOrthogonal D) j : BooleanVec n) p))
  · intro i j
    apply (op_commute_iff_symplecticVec_form_zero _ _).mpr
    change symplecticForm (rowSympVec (quadraticAffineTableau a Q b D p) i)
      (rowSympVec (quadraticAffineTableau a Q b D p) j) = 0
    rw [rowSympVec_quadraticAffineTableau, rowSympVec_quadraticAffineTableau]
    cases hi : (affineIndexEquiv D).symm i with
    | inl di =>
        cases hj : (affineIndexEquiv D).symm j with
        | inl dj =>
            simpa [quadraticSympFamily] using!
              (stabilizerPhaseDirection_symplectic a
                (Module.finBasis (ZMod 2) D di : BooleanVec n)
                (Module.finBasis (ZMod 2) D dj : BooleanVec n) Q)
        | inr oj =>
            have hz := affineOrthogonal_dot (D := D)
              (Module.finBasis (ZMod 2) (affineOrthogonal D) oj).property
              (Module.finBasis (ZMod 2) D di).property
            simp only [quadraticSympFamily, symplecticForm]
            rw [booleanDot_comm_affine, hz]
            simp [booleanDot]
    | inr oi =>
        cases hj : (affineIndexEquiv D).symm j with
        | inl dj =>
            have hz := affineOrthogonal_dot (D := D)
              (Module.finBasis (ZMod 2) (affineOrthogonal D) oi).property
              (Module.finBasis (ZMod 2) D dj).property
            simp only [quadraticSympFamily, symplecticForm]
            rw [hz]
            simp [booleanDot]
        | inr oj => simp [quadraticSympFamily, symplecticForm, booleanDot]

theorem affinePauliRow_stabilizerAffineState {n : ℕ} {D : Submodule (ZMod 2) (BooleanVec n)}
    {p d : BooleanVec n} (hd : d ∈ D) (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n) (c : ZMod 2) :
    op (affinePauliRow d (stabilizerPhaseDirection a Q d)
      (stabilizerPhaseSign a Q b d)).decode *ᵥ
        stabilizerAffineState a Q b c (AffineSubspace.mk' p D) =
      stabilizerAffineState a Q b c (AffineSubspace.mk' p D) := by
  have htarget :
      (Complex.I ^ (stabilizerPhaseTarget a Q b d).val : ℂ) *
        Complex.I ^ (booleanDot a d).val * (-1 : ℂ) ^ (quadFun Q b 0 d).val = 1 := by
    simpa [stabilizerPhaseTarget, phase4OfBit] using!
      (phase4Target_cancel (booleanDot a d) (quadFun Q b 0 d))
  funext r
  rw [affinePauliRow_mulVec]
  simp only [stabilizerAffineState, stabilizerAffineFun, stateOfFn]
  rw [mem_mk'_regXor_translation hd, regToVec_regXor_vecToReg,
    stabilizerPhase_add, stabilizerPhaseSign_adjust]
  by_cases hr : regToVec r ∈ AffineSubspace.mk' p D
  · simp only [hr, if_pos, mul_one]
    calc
      _ = ((Complex.I ^ (stabilizerPhaseTarget a Q b d).val : ℂ) *
            Complex.I ^ (booleanDot a d).val * (-1 : ℂ) ^ (quadFun Q b 0 d).val) *
          (booleanCharacter (stabilizerPhaseDirection a Q d) (regToVec r) *
            booleanCharacter (stabilizerPhaseDirection a Q d) (regToVec r)) *
          stabilizerPhase a Q b c (regToVec r) := by ring
      _ = stabilizerPhase a Q b c (regToVec r) := by
        rw [htarget, booleanCharacter_mul_self]
        simp
  · simp [hr]

theorem diagonalRow_stabilizerAffineState {n : ℕ} {D : Submodule (ZMod 2) (BooleanVec n)}
    {p z : BooleanVec n} (hz : z ∈ affineOrthogonal D) (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n) (c : ZMod 2) :
    op (diagonalRow z (booleanDot z p)).decode *ᵥ
        stabilizerAffineState a Q b c (AffineSubspace.mk' p D) =
      stabilizerAffineState a Q b c (AffineSubspace.mk' p D) := by
  funext r
  rw [diagonalRow_mulVec]
  by_cases hr : regToVec r ∈ AffineSubspace.mk' p D
  · have hdir : regToVec r - p ∈ D := by
      simpa using! AffineSubspace.vsub_mem_direction hr (AffineSubspace.self_mem_mk' p D)
    have hzdir := affineOrthogonal_dot hz hdir
    have hdot : booleanDot z (regToVec r) = booleanDot z p := by
      have hadd :=
          (Qatlib.Concepts.PauliClifford.ExactRank.booleanDotHom z).map_add (regToVec r - p) p
      rw [sub_add_cancel] at hadd
      change booleanDot z (regToVec r) = booleanDot z (regToVec r - p) + booleanDot z p at hadd
      rw [hadd, hzdir, zero_add]
    have hchar : booleanCharacter z (regToVec r) = booleanCharacter z p := by
      simp only [Qatlib.Concepts.PauliClifford.ExactRank.booleanCharacter_apply, hdot]
    have hsign : (if booleanDot z p = 0 then (1 : ℂ) else -1) *
        booleanCharacter z p = 1 := by
      rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one (booleanDot z p) with h | h <;>
        simp [h, Qatlib.Concepts.PauliClifford.ExactRank.booleanCharacter_apply]
    simp only [stabilizerAffineState, stabilizerAffineFun, stateOfFn, hr, if_pos, mul_one]
    rw [hchar, hsign, one_mul]
  · simp [stabilizerAffineState, stabilizerAffineFun, stateOfFn, hr]

theorem quadraticAffineState_mem_codeSpace {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n) (c : ZMod 2)
    (D : Submodule (ZMod 2) (BooleanVec n)) (p : BooleanVec n) :
    stabilizerAffineState a Q b c (AffineSubspace.mk' p D) ∈
      codeSpace (quadraticAffineTableau a Q b D p) := by
  intro i
  cases h : (affineIndexEquiv D).symm i with
  | inl j =>
      simpa [quadraticAffineTableau, quadraticAffineRowFamily, h] using!
        (affinePauliRow_stabilizerAffineState (D := D) (p := p)
          (Module.finBasis (ZMod 2) D j).property a Q b c)
  | inr j =>
      simpa [quadraticAffineTableau, quadraticAffineRowFamily, h] using!
        (diagonalRow_stabilizerAffineState (D := D) (p := p)
          (Module.finBasis (ZMod 2) (affineOrthogonal D) j).property a Q b c)

theorem normalizedStabilizerState_quadraticAffine_mem_codeSpace {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n) (c : ZMod 2)
    (D : Submodule (ZMod 2) (BooleanVec n)) (p : BooleanVec n) :
    normalizedStabilizerState (stabilizerAffineFun a Q b c (AffineSubspace.mk' p D)) ∈
      codeSpace (quadraticAffineTableau a Q b D p) := by
  have hum := quadraticAffineState_mem_codeSpace a Q b c D p
  change stateOfFn (fun x => stabilizerAffineFun a Q b c (AffineSubspace.mk' p D) x *
    (Real.sqrt (stabilizerFunMass
      (stabilizerAffineFun a Q b c (AffineSubspace.mk' p D))) : ℂ)⁻¹) ∈
        codeSpace (quadraticAffineTableau a Q b D p)
  have heq : (fun x => stabilizerAffineFun a Q b c (AffineSubspace.mk' p D) x *
      (Real.sqrt (stabilizerFunMass
        (stabilizerAffineFun a Q b c (AffineSubspace.mk' p D))) : ℂ)⁻¹) =
      fun x => (Real.sqrt (stabilizerFunMass
        (stabilizerAffineFun a Q b c (AffineSubspace.mk' p D))) : ℂ)⁻¹ *
          stabilizerAffineFun a Q b c (AffineSubspace.mk' p D) x := by
    funext x
    ring
  rw [heq, stateOfFn_smul]
  exact (codeSpace (quadraticAffineTableau a Q b D p)).smul_mem _ hum

theorem normalizedStabilizerState_quadraticAffine_physical {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n) (c : ZMod 2)
    (D : Submodule (ZMod 2) (BooleanVec n)) (p : BooleanVec n) :
    IsNormalizedPhysicalStabilizerState
      (normalizedStabilizerState
        (stabilizerAffineFun a Q b c (AffineSubspace.mk' p D))) := by
  have hmass : 0 < stabilizerFunMass
      (stabilizerAffineFun a Q b c (AffineSubspace.mk' p D)) := by
    unfold stabilizerFunMass
    apply Finset.sum_pos'
      (fun x _ => sq_nonneg ‖stabilizerAffineFun a Q b c (AffineSubspace.mk' p D) x‖)
    refine ⟨p, Finset.mem_univ _, ?_⟩
    have hnorm' : ‖stabilizerAffineFun a Q b c (AffineSubspace.mk' p D) p‖ ^ 2 = 1 := by
      simp [stabilizerAffineFun, stabilizerPhase, norm_pow]
    rw [hnorm']
    norm_num
  exact ⟨normalizedStabilizerState_normalized _ hmass,
    quadraticAffineTableau a Q b D p, quadraticAffineTableau_consistent a Q b D p,
    quadraticAffineTableau_independent a Q b D p,
    normalizedStabilizerState_quadraticAffine_mem_codeSpace a Q b c D p⟩

theorem normalizedStabilizerState_quadratic_physical {n : ℕ}
    {A : AffineSubspace (ZMod 2) (BooleanVec n)} {p : BooleanVec n} (hp : p ∈ A)
    (a : BooleanVec n) (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (b : BooleanVec n) (c : ZMod 2) :
    IsNormalizedPhysicalStabilizerState
      (normalizedStabilizerState (stabilizerAffineFun a Q b c A)) := by
  rw [← AffineSubspace.mk'_eq hp]
  exact normalizedStabilizerState_quadraticAffine_physical a Q b c A.direction p

theorem isStabilizerFun_stabilizerAffineFun {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n) (c : ZMod 2)
    (A : AffineSubspace (ZMod 2) (BooleanVec n)) :
    IsStabilizerFun (stabilizerAffineFun a Q b c A) := by
  exact ⟨a, Q, b, c, A, rfl⟩

theorem normalizedStabilizerState_isStabilizerFun_physical {n : ℕ} {φ : BooleanVec n → ℂ}
    (hφ : IsStabilizerFun φ) :
    IsPhysicalStabilizerState (normalizedStabilizerState φ) := by
  obtain ⟨a, Q, b, c, A, rfl⟩ := hφ
  change IsPhysicalStabilizerState
    (normalizedStabilizerState (stabilizerAffineFun a Q b c A))
  by_cases hzero : stabilizerAffineFun a Q b c A = 0
  · rw [hzero]
    exact normalizedStabilizerState_zero_physical
  · have hA : ∃ p, p ∈ A := by
      by_contra h
      push Not at h
      apply hzero
      funext x
      simp [stabilizerAffineFun, h x]
    obtain ⟨p, hp⟩ := hA
    exact (normalizedStabilizerState_quadratic_physical hp a Q b c).2

theorem normalizedStabilizerState_isStabilizerFun_normalized_physical {n : ℕ}
    {φ : BooleanVec n → ℂ} (hφ : IsStabilizerFun φ) (hne : φ ≠ 0) :
    IsNormalizedPhysicalStabilizerState (normalizedStabilizerState φ) :=
  ⟨normalizedStabilizerState_normalized_of_ne_zero hne,
    normalizedStabilizerState_isStabilizerFun_physical hφ⟩

theorem quadraticAffine_extract_upToPhase {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n) (c : ZMod 2)
    (D : Submodule (ZMod 2) (BooleanVec n)) (p : BooleanVec n)
    (ψ : QState (Reg n)) (hψ : ψ ∈ codeSpace (quadraticAffineTableau a Q b D p))
    (hn : Normalized ψ) : IsStabilizerFunUpToPhase (amplitudeFn ψ) := by
  let χ : QState (Reg n) := normalizedStabilizerState
    (stabilizerAffineFun a Q b c (AffineSubspace.mk' p D))
  have hχnorm : Normalized χ :=
    (normalizedStabilizerState_quadraticAffine_physical a Q b c D p).1
  have hχmem : χ ∈ codeSpace (quadraticAffineTableau a Q b D p) :=
    normalizedStabilizerState_quadraticAffine_mem_codeSpace a Q b c D p
  have hχamp : IsStabilizerFunUpToPhase (amplitudeFn χ) :=
    isStabilizerFunUpToPhase_amplitude_normalized _
      (isStabilizerFun_stabilizerAffineFun a Q b c (AffineSubspace.mk' p D))
  exact isStabilizerFunUpToPhase_of_normalized_codeState
    (quadraticAffineTableau a Q b D p) (quadraticAffineTableau_consistent a Q b D p)
    (quadraticAffineTableau_independent a Q b D p) χ ψ hχmem hψ hχnorm hn hχamp

def zmod2Mask {k : ℕ} (c : Fin k → ZMod 2) : Mask :=
  List.ofFn (fun i => decide (c i = 1))

theorem maskXor_ofFn {k : ℕ} (b c : Fin k → Bool) :
    maskXor (List.ofFn b) (List.ofFn c) = List.ofFn (fun i => xor (b i) (c i)) := by
  induction k with
  | zero => simp [maskXor]
  | succ k ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
      simp only [maskXor]
      congr 1
      exact ih (fun i => b i.succ) (fun i => c i.succ)

theorem zmod2Mask_add {k : ℕ} (b c : Fin k → ZMod 2) :
    maskXor (zmod2Mask b) (zmod2Mask c) = zmod2Mask (b + c) := by
  unfold zmod2Mask
  rw [maskXor_ofFn]
  congr 1
  funext i
  rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one (b i) with hb | hb <;>
    rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one (c i) with hc | hc <;>
      simp [hb, hc]

def tableauRowSpace {n m : ℕ} (t : Tableau n m) :
    Submodule (ZMod 2) (BooleanVec n × BooleanVec n) :=
  Submodule.span (ZMod 2) (Set.range (symplecticVecOfFn (tableauGenerators t)))

noncomputable def tableauRowBasis {n m : ℕ} (t : Tableau n m)
    (hind : IndependentGenerators (tableauGenerators t)) :
    Module.Basis (Fin (tableauGenerators t).length) (ZMod 2) (tableauRowSpace t) :=
  Module.Basis.span (symplecticVecOfFn_linearIndependent _ hind)

noncomputable def tableauLift {n m : ℕ} (t : Tableau n m)
    (hind : IndependentGenerators (tableauGenerators t)) (v : tableauRowSpace t) : PauliElem n :=
  maskProduct (tableauGenerators t) (zmod2Mask ((tableauRowBasis t hind).repr v))

theorem tableauLift_symplecticVec {n m : ℕ} (t : Tableau n m)
    (hind : IndependentGenerators (tableauGenerators t)) (v : tableauRowSpace t) :
    symplecticVec (tableauLift t hind v).word = (v : BooleanVec n × BooleanVec n) := by
  unfold tableauLift
  rw [maskProduct_word, symplecticVec_maskWordProduct]
  change maskVecSum (tableauGenerators t)
    (List.ofFn (fun i => decide (((tableauRowBasis t hind).repr v) i = 1))) = _
  rw [maskVecSum_eq_sum]
  have h := congrArg Subtype.val ((tableauRowBasis t hind).sum_repr v)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h
  have hb (i : Fin (tableauGenerators t).length) :
      ((tableauRowBasis t hind i : tableauRowSpace t) : BooleanVec n × BooleanVec n) =
        symplecticVecOfFn (tableauGenerators t) i :=
    Module.Basis.coe_span_apply (symplecticVecOfFn_linearIndependent _ hind) i
  simp_rw [hb] at h
  exact h

theorem tableauLift_hermitian {n m : ℕ} (t : Tableau n m) (ht : ConsistentTableau t)
    (hind : IndependentGenerators (tableauGenerators t)) (v : tableauRowSpace t) :
    IsHermitianPauli (tableauLift t hind v) := by
  apply maskProduct_herm _ (generators_commuting t ht)
  simp [zmod2Mask]

theorem tableauLift_fixes {n m : ℕ} (t : Tableau n m)
    (hind : IndependentGenerators (tableauGenerators t)) (ψ : QState (Reg n))
    (hψ : ψ ∈ codeSpace t) (v : tableauRowSpace t) :
    op (tableauLift t hind v) *ᵥ ψ = ψ := by
  apply op_maskProduct_fixes_codeSpace t ψ hψ
  simp [zmod2Mask]

theorem tableauLift_add {n m : ℕ} (t : Tableau n m) (ht : ConsistentTableau t)
    (hind : IndependentGenerators (tableauGenerators t)) (v w : tableauRowSpace t) :
    tableauLift t hind (v + w) = tableauLift t hind v * tableauLift t hind w := by
  have hmasks : maskXor (zmod2Mask ((tableauRowBasis t hind).repr v))
      (zmod2Mask ((tableauRowBasis t hind).repr w)) =
      zmod2Mask ((tableauRowBasis t hind).repr (v + w)) := by
    rw [zmod2Mask_add]
    congr 1
    ext i
    simp
  unfold tableauLift
  rw [← hmasks]
  exact (maskProduct_xor (tableauGenerators t) (generators_commuting t ht)
    (zmod2Mask ((tableauRowBasis t hind).repr v))
    (zmod2Mask ((tableauRowBasis t hind).repr w)) (by simp [zmod2Mask])
    (by simp [zmod2Mask]))

theorem symplecticForm_smul_right {n : ℕ} (c : ZMod 2)
    (v w : BooleanVec n × BooleanVec n) :
    symplecticForm v (c • w) = c • symplecticForm v w := by
  rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one c with rfl | rfl <;>
    simp [symplecticForm, booleanDot]

theorem tableauRowSpace_isotropic {n m : ℕ} (t : Tableau n m)
    (ht : ConsistentTableau t) (v w : tableauRowSpace t) :
    symplecticForm (v : BooleanVec n × BooleanVec n) w = 0 := by
  let s : Set (BooleanVec n × BooleanVec n) := Set.range (symplecticVecOfFn (tableauGenerators t))
  let p : (x y : BooleanVec n × BooleanVec n) →
      x ∈ Submodule.span (ZMod 2) s → y ∈ Submodule.span (ZMod 2) s → Prop :=
    fun x y _ _ => symplecticForm x y = 0
  have hgen : ∀ (x y : BooleanVec n × BooleanVec n) (hx : x ∈ s) (hy : y ∈ s), p x y
      (Submodule.subset_span hx) (Submodule.subset_span hy) := by
    intro x y hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    have h := (op_commute_iff_symplecticVec_form_zero
      (t ((rowEquiv t).symm i)).decode (t ((rowEquiv t).symm j)).decode).mp
      (ht.2 ((rowEquiv t).symm i) ((rowEquiv t).symm j))
    have hi := symplecticVecOfFn_rowEquiv t ((rowEquiv t).symm i)
    have hj := symplecticVecOfFn_rowEquiv t ((rowEquiv t).symm j)
    rw [Equiv.apply_symm_apply] at hi hj
    change symplecticForm (symplecticVecOfFn (tableauGenerators t) i)
      (symplecticVecOfFn (tableauGenerators t) j) = 0
    rw [hi, hj]
    exact h
  have hzero_left : ∀ y hy, p 0 y (Submodule.zero_mem _) hy := by
    intro y hy
    simp [p, symplecticForm, booleanDot]
  have hzero_right : ∀ x hx, p x 0 hx (Submodule.zero_mem _) := by
    intro x hx
    simp [p, symplecticForm, booleanDot]
  have hadd_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz →
      p (x + y) z (Submodule.add_mem _ hx hy) hz := by
    intro x y z hx hy hz hxz hyz
    simp only [p] at hxz hyz ⊢
    rw [symplecticForm_add_left, hxz, hyz, add_zero]
  have hadd_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz →
      p x (y + z) hx (Submodule.add_mem _ hy hz) := by
    intro x y z hx hy hz hxy hxz
    simp only [p] at hxy hxz ⊢
    rw [symplecticForm_add_right, hxy, hxz, add_zero]
  have hsmul_left : ∀ (r : ZMod 2) x y hx hy, p x y hx hy →
      p (r • x) y (Submodule.smul_mem _ r hx) hy := by
    intro r x y hx hy hxy
    simp only [p] at hxy ⊢
    rw [symplecticForm_smul_left, hxy, smul_zero]
  have hsmul_right : ∀ (r : ZMod 2) x y hx hy, p x y hx hy →
      p x (r • y) hx (Submodule.smul_mem _ r hy) := by
    intro r x y hx hy hxy
    simp only [p] at hxy ⊢
    rw [symplecticForm_smul_right, hxy, smul_zero]
  exact Submodule.span_induction₂ hgen hzero_left hzero_right hadd_left hadd_right
    hsmul_left hsmul_right v.property w.property

def tableauDirectionProjection {n m : ℕ} (t : Tableau n m) :
    tableauRowSpace t →ₗ[ZMod 2] BooleanVec n :=
  (LinearMap.fst (ZMod 2) (BooleanVec n) (BooleanVec n)).comp (tableauRowSpace t).subtype

def tableauDirection {n m : ℕ} (t : Tableau n m) : Submodule (ZMod 2) (BooleanVec n) :=
  LinearMap.range (tableauDirectionProjection t)

noncomputable def tableauDirectionSection {n m : ℕ} (t : Tableau n m) :
    tableauDirection t →ₗ[ZMod 2] tableauRowSpace t :=
  Classical.choose ((tableauDirectionProjection t).rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_rangeRestrict (tableauDirectionProjection t)))

theorem tableauDirectionProjection_section {n m : ℕ} (t : Tableau n m)
    (d : tableauDirection t) : tableauDirectionProjection t (tableauDirectionSection t d) = d := by
  have h := Classical.choose_spec
    ((tableauDirectionProjection t).rangeRestrict.exists_rightInverse_of_surjective
      (LinearMap.range_rangeRestrict (tableauDirectionProjection t)))
  have h' := LinearMap.ext_iff.mp h d
  exact congrArg (fun x : tableauDirection t => (x : BooleanVec n)) h'

noncomputable def tableauPhaseSection {n m : ℕ} (t : Tableau n m) :
    tableauDirection t →ₗ[ZMod 2] BooleanVec n :=
  (LinearMap.snd (ZMod 2) (BooleanVec n) (BooleanVec n)).comp
    ((tableauRowSpace t).subtype.comp (tableauDirectionSection t))

theorem tableauDirectionSection_fst {n m : ℕ} (t : Tableau n m) (d : tableauDirection t) :
    ((tableauDirectionSection t d : tableauRowSpace t) : BooleanVec n × BooleanVec n).1 = d :=
  tableauDirectionProjection_section t d

theorem tableauDirectionSection_snd {n m : ℕ} (t : Tableau n m) (d : tableauDirection t) :
    ((tableauDirectionSection t d : tableauRowSpace t) : BooleanVec n × BooleanVec n).2 =
      tableauPhaseSection t d := rfl

theorem tableauPhaseSection_symmetric {n m : ℕ} (t : Tableau n m)
    (ht : ConsistentTableau t) (d e : tableauDirection t) :
    booleanDot (d : BooleanVec n) (tableauPhaseSection t e) =
      booleanDot (e : BooleanVec n) (tableauPhaseSection t d) := by
  have h := tableauRowSpace_isotropic t ht (tableauDirectionSection t d)
    (tableauDirectionSection t e)
  rw [symplecticForm, tableauDirectionSection_fst, tableauDirectionSection_fst,
    tableauDirectionSection_snd, tableauDirectionSection_snd] at h
  rw [booleanDot_comm_affine (tableauPhaseSection t d) (e : BooleanVec n)] at h
  exact Qatlib.Concepts.HspRecovery.ReductionCore.zmod2_eq_of_add_eq_zero h

def tableauPhaseDiagonal {n m : ℕ} (t : Tableau n m) (ht : ConsistentTableau t) :
    tableauDirection t →ₗ[ZMod 2] ZMod 2 where
  toFun d := booleanDot (d : BooleanVec n) (tableauPhaseSection t d)
  map_add' d e := by
    simp only [Submodule.coe_add, map_add, Qatlib.Concepts.HspRecovery.ReductionCore.booleanDot_add_left,
      Qatlib.Concepts.HspRecovery.ReductionCore.booleanDot_add_right]
    have h := tableauPhaseSection_symmetric t ht d e
    rw [h]
    calc
      _ = booleanDot (d : BooleanVec n) (tableauPhaseSection t d) +
          booleanDot (e : BooleanVec n) (tableauPhaseSection t e) +
          (booleanDot (e : BooleanVec n) (tableauPhaseSection t d) +
            booleanDot (e : BooleanVec n) (tableauPhaseSection t d)) := by abel
      _ = _ := by rw [Qatlib.Concepts.HspRecovery.ReductionCore.zmod2_add_self, add_zero]
  map_smul' c d := by
    rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one c with rfl | rfl <;> simp [booleanDot]

theorem finrank_tableauRowSpace {n : ℕ} (t : Tableau n n)
    (hind : IndependentGenerators (tableauGenerators t)) :
    Module.finrank (ZMod 2) (tableauRowSpace t) = n := by
  have h := finrank_span_eq_card (symplecticVecOfFn_linearIndependent (tableauGenerators t) hind)
  simpa only [tableauRowSpace, tableauGenerators_length, Fintype.card_fin] using! h

theorem finrank_direction_add_finrank_projectionKer {n : ℕ} (t : Tableau n n)
    (hind : IndependentGenerators (tableauGenerators t)) :
    Module.finrank (ZMod 2) (tableauDirection t) +
      Module.finrank (ZMod 2) (LinearMap.ker (tableauDirectionProjection t)) = n := by
  calc
    Module.finrank (ZMod 2) (tableauDirection t) +
        Module.finrank (ZMod 2) (LinearMap.ker (tableauDirectionProjection t)) =
        Module.finrank (ZMod 2) (tableauRowSpace t) :=
      LinearMap.finrank_range_add_finrank_ker (tableauDirectionProjection t)
    _ = n := finrank_tableauRowSpace t hind

def tableauKernelToOrthogonal {n : ℕ} (t : Tableau n n) (ht : ConsistentTableau t) :
    LinearMap.ker (tableauDirectionProjection t) →ₗ[ZMod 2]
      affineOrthogonal (tableauDirection t) where
  toFun v := ⟨((v.1 : tableauRowSpace t) : BooleanVec n × BooleanVec n).2, by
    intro d
    obtain ⟨w, hw⟩ := d.property
    have hv0 : ((v.1 : tableauRowSpace t) : BooleanVec n × BooleanVec n).1 = 0 := v.property
    have hform : booleanDot ((w : tableauRowSpace t) : BooleanVec n × BooleanVec n).1
        ((v.1 : tableauRowSpace t) : BooleanVec n × BooleanVec n).2 = 0 := by
      have h := tableauRowSpace_isotropic t ht w v.1
      rw [symplecticForm, hv0] at h
      simpa [booleanDot] using! h
    have hw' : ((w : tableauRowSpace t) : BooleanVec n × BooleanVec n).1 =
        (d : BooleanVec n) := hw
    rw [← hw']
    exact (booleanDot_comm_affine _ _).trans hform⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tableauKernelToOrthogonal_injective {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) : Function.Injective (tableauKernelToOrthogonal t ht) := by
  intro v w h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · have hv0 : ((v.1 : tableauRowSpace t) : BooleanVec n × BooleanVec n).1 = 0 := v.property
    have hw0 : ((w.1 : tableauRowSpace t) : BooleanVec n × BooleanVec n).1 = 0 := w.property
    rw [hv0, hw0]
  · exact congrArg (fun z : affineOrthogonal (tableauDirection t) => (z : BooleanVec n)) h

theorem finrank_projectionKer_eq_orthogonal {n : ℕ} (t : Tableau n n)
    (hind : IndependentGenerators (tableauGenerators t)) :
    Module.finrank (ZMod 2) (LinearMap.ker (tableauDirectionProjection t)) =
      Module.finrank (ZMod 2) (affineOrthogonal (tableauDirection t)) := by
  have hk := finrank_direction_add_finrank_projectionKer t hind
  have ho := finrank_add_finrank_affineOrthogonal (tableauDirection t)
  omega

set_option backward.isDefEq.respectTransparency false in

theorem zero_diagonal_mem_tableauRowSpace {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t))
    (z : BooleanVec n) (hz : z ∈ affineOrthogonal (tableauDirection t)) :
    (0, z) ∈ tableauRowSpace t := by
  have hdim : @Module.finrank (ZMod 2) (LinearMap.ker (tableauDirectionProjection t)) _ _
      (LinearMap.ker (tableauDirectionProjection t)).module =
      @Module.finrank (ZMod 2) (affineOrthogonal (tableauDirection t)) _ _
      (affineOrthogonal (tableauDirection t)).module :=
    finrank_projectionKer_eq_orthogonal t hind
  have hsurj : Function.Surjective (tableauKernelToOrthogonal t ht) :=
    (@LinearMap.injective_iff_surjective_of_finrank_eq_finrank (ZMod 2)
      (LinearMap.ker (tableauDirectionProjection t)) _ _
      (LinearMap.ker (tableauDirectionProjection t)).module
      (affineOrthogonal (tableauDirection t)) _
      (affineOrthogonal (tableauDirection t)).module
      inferInstance inferInstance hdim (tableauKernelToOrthogonal t ht)).mp
      (tableauKernelToOrthogonal_injective t ht)
  obtain ⟨v, hv⟩ := hsurj ⟨z, hz⟩
  have hv0 : ((v.1 : tableauRowSpace t) : BooleanVec n × BooleanVec n).1 = 0 := v.property
  have hv2 : ((v.1 : tableauRowSpace t) : BooleanVec n × BooleanVec n).2 = z :=
    congrArg (fun y : affineOrthogonal (tableauDirection t) => (y : BooleanVec n)) hv
  have hpair : ((v.1 : tableauRowSpace t) : BooleanVec n × BooleanVec n) = (0, z) := by
    apply Prod.ext <;> assumption
  rw [← hpair]
  exact v.1.property

def booleanDotLinearMap {n : ℕ} (a : BooleanVec n) : BooleanVec n →ₗ[ZMod 2] ZMod 2 where
  toFun x := booleanDot a x
  map_add' x y := Qatlib.Concepts.HspRecovery.ReductionCore.booleanDot_add_right a x y
  map_smul' c x := by
    rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one c with rfl | rfl <;> simp [booleanDot]

theorem exists_booleanDot_eq {n : ℕ} (f : BooleanVec n →ₗ[ZMod 2] ZMod 2) :
    ∃ a : BooleanVec n, ∀ x, booleanDot a x = f x := by
  let a : BooleanVec n := fun i => f (Pi.single i 1)
  refine ⟨a, fun x => ?_⟩
  have h : booleanDotLinearMap a = f := by
    apply (Pi.basisFun (ZMod 2) (Fin n)).ext
    intro i
    simp [booleanDotLinearMap, a, booleanDot, Pi.single_apply]
  exact LinearMap.ext_iff.mp h x

noncomputable def submoduleRetraction {n : ℕ} (D : Submodule (ZMod 2) (BooleanVec n)) :
    BooleanVec n →ₗ[ZMod 2] D :=
  Classical.choose (D.subtype.exists_leftInverse_of_injective D.ker_subtype)

theorem submoduleRetraction_coe {n : ℕ} (D : Submodule (ZMod 2) (BooleanVec n))
    (d : D) : submoduleRetraction D (d : BooleanVec n) = d := by
  have h := Classical.choose_spec (D.subtype.exists_leftInverse_of_injective D.ker_subtype)
  have h' := LinearMap.ext_iff.mp h d
  exact h'

def upperTriangular {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => if i < j then M i j else 0

theorem upperTriangular_add_swap {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hsym : ∀ i j, M i j = M j i) (hdiag : ∀ i, M i i = 0) (i j : Fin n) :
    upperTriangular M i j + upperTriangular M j i = M i j := by
  by_cases hij : i = j
  · subst j
    simp [upperTriangular, hdiag]
  · rcases lt_or_gt_of_ne hij with h | h
    · have hji : ¬ j < i := by omega
      simp [upperTriangular, h, hji]
    · have hji : ¬ i < j := by omega
      simp [upperTriangular, h, hji, hsym]

theorem quadDirection_upperTriangular {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hsym : ∀ i j, M i j = M j i) (hdiag : ∀ i, M i i = 0) (d : BooleanVec n) :
    quadDirection (upperTriangular M) d = M *ᵥ d := by
  funext i
  simp only [quadDirection, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  rw [upperTriangular_add_swap M hsym hdiag]

theorem booleanDot_quadDirection_upperTriangular {n : ℕ}
    (B : BooleanVec n →ₗ[ZMod 2] (BooleanVec n →ₗ[ZMod 2] ZMod 2))
    (hsym : ∀ x y, B x y = B y x) (hdiag : ∀ x, B x x = 0) (x y : BooleanVec n) :
    booleanDot x (quadDirection (upperTriangular (LinearMap.toMatrix₂' (ZMod 2) B)) y) =
      B x y := by
  have hm : ∀ i j, LinearMap.toMatrix₂' (ZMod 2) B i j =
      LinearMap.toMatrix₂' (ZMod 2) B j i := by
    intro i j
    simp only [LinearMap.toMatrix₂'_apply]
    exact hsym _ _
  have hd : ∀ i, LinearMap.toMatrix₂' (ZMod 2) B i i = 0 := by
    intro i
    simp only [LinearMap.toMatrix₂'_apply]
    exact hdiag _
  rw [quadDirection_upperTriangular _ hm hd]
  have h := congrArg (fun f : BooleanVec n →ₗ[ZMod 2] (BooleanVec n →ₗ[ZMod 2] ZMod 2) =>
    f x y) (Matrix.toLinearMap₂'_toMatrix' (R := ZMod 2) B)
  change Matrix.toLinearMap₂' (ZMod 2) (LinearMap.toMatrix₂' (ZMod 2) B) x y = B x y at h
  rw [Matrix.toLinearMap₂'_apply'] at h
  exact h

noncomputable def tableauPhaseAFunctional {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) : BooleanVec n →ₗ[ZMod 2] ZMod 2 :=
  (tableauPhaseDiagonal t ht).comp (submoduleRetraction (tableauDirection t))

noncomputable def tableauPhaseA {n : ℕ} (t : Tableau n n) (ht : ConsistentTableau t) :
    BooleanVec n :=
  Classical.choose (exists_booleanDot_eq (tableauPhaseAFunctional t ht))

theorem booleanDot_tableauPhaseA {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) (x : BooleanVec n) :
    booleanDot (tableauPhaseA t ht) x = tableauPhaseAFunctional t ht x :=
  Classical.choose_spec (exists_booleanDot_eq (tableauPhaseAFunctional t ht)) x

theorem booleanDot_tableauPhaseA_eq {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) (x : BooleanVec n) :
    booleanDot (tableauPhaseA t ht) x =
      booleanDot (submoduleRetraction (tableauDirection t) x : BooleanVec n)
        (tableauPhaseSection t (submoduleRetraction (tableauDirection t) x)) := by
  rw [booleanDot_tableauPhaseA]
  rfl

def tableauAlternatingBilinear {n : ℕ} (t : Tableau n n) (ht : ConsistentTableau t) :
    BooleanVec n →ₗ[ZMod 2] (BooleanVec n →ₗ[ZMod 2] ZMod 2) where
  toFun x :=
    { toFun y :=
        booleanDot (submoduleRetraction (tableauDirection t) x : BooleanVec n)
            (tableauPhaseSection t (submoduleRetraction (tableauDirection t) y)) +
          booleanDot (tableauPhaseA t ht) x * booleanDot (tableauPhaseA t ht) y
      map_add' y z := by
        simp only [map_add, Qatlib.Concepts.HspRecovery.ReductionCore.booleanDot_add_right, booleanDot_tableauPhaseA,
          tableauPhaseAFunctional, LinearMap.comp_apply]
        ring
      map_smul' c y := by
        rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one c with rfl | rfl <;>
          simp [booleanDot] }
  map_add' x y := by
    ext z
    simp only [map_add, Submodule.coe_add, LinearMap.add_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Qatlib.Concepts.HspRecovery.ReductionCore.booleanDot_add_left, booleanDot_tableauPhaseA,
      tableauPhaseAFunctional, LinearMap.comp_apply]
    ring
  map_smul' c x := by
    rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one c with rfl | rfl <;>
      ext y <;> simp [booleanDot]

theorem tableauAlternatingBilinear_symmetric {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) (x y : BooleanVec n) :
    tableauAlternatingBilinear t ht x y = tableauAlternatingBilinear t ht y x := by
  change booleanDot (submoduleRetraction (tableauDirection t) x : BooleanVec n)
      (tableauPhaseSection t (submoduleRetraction (tableauDirection t) y)) +
    booleanDot (tableauPhaseA t ht) x * booleanDot (tableauPhaseA t ht) y = _
  rw [tableauPhaseSection_symmetric t ht]
  change _ + _ = booleanDot (submoduleRetraction (tableauDirection t) y : BooleanVec n)
      (tableauPhaseSection t (submoduleRetraction (tableauDirection t) x)) +
    booleanDot (tableauPhaseA t ht) y * booleanDot (tableauPhaseA t ht) x
  rw [mul_comm (booleanDot (tableauPhaseA t ht) x)]

theorem tableauAlternatingBilinear_self {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) (x : BooleanVec n) :
    tableauAlternatingBilinear t ht x x = 0 := by
  change booleanDot (submoduleRetraction (tableauDirection t) x : BooleanVec n)
      (tableauPhaseSection t (submoduleRetraction (tableauDirection t) x)) +
    booleanDot (tableauPhaseA t ht) x * booleanDot (tableauPhaseA t ht) x = 0
  have hsq : booleanDot (tableauPhaseA t ht) x * booleanDot (tableauPhaseA t ht) x =
      booleanDot (tableauPhaseA t ht) x := by
    rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one (booleanDot (tableauPhaseA t ht) x) with h | h <;>
      simp [h]
  rw [hsq, booleanDot_tableauPhaseA_eq, Qatlib.Concepts.HspRecovery.ReductionCore.zmod2_add_self]

noncomputable def tableauQuadraticMatrix {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  upperTriangular (LinearMap.toMatrix₂' (ZMod 2) (tableauAlternatingBilinear t ht))

theorem booleanDot_quadDirection_tableauQuadraticMatrix {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) (x y : BooleanVec n) :
    booleanDot x (quadDirection (tableauQuadraticMatrix t ht) y) =
      tableauAlternatingBilinear t ht x y := by
  exact booleanDot_quadDirection_upperTriangular _ (tableauAlternatingBilinear_symmetric t ht)
    (tableauAlternatingBilinear_self t ht) x y

theorem tableauAlternatingBilinear_on_direction {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) (d e : tableauDirection t) :
    tableauAlternatingBilinear t ht (d : BooleanVec n) (e : BooleanVec n) =
      booleanDot (d : BooleanVec n) (tableauPhaseSection t e) +
        (booleanDot (d : BooleanVec n) (tableauPhaseSection t d)) *
          (booleanDot (e : BooleanVec n) (tableauPhaseSection t e)) := by
  change booleanDot (submoduleRetraction (tableauDirection t) (d : BooleanVec n) : BooleanVec n)
      (tableauPhaseSection t (submoduleRetraction (tableauDirection t) (e : BooleanVec n))) +
    booleanDot (tableauPhaseA t ht) (d : BooleanVec n) *
      booleanDot (tableauPhaseA t ht) (e : BooleanVec n) = _
  rw [submoduleRetraction_coe, submoduleRetraction_coe,
    booleanDot_tableauPhaseA_eq, booleanDot_tableauPhaseA_eq,
    submoduleRetraction_coe, submoduleRetraction_coe]

theorem tableauPhaseDirection_error_orthogonal {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) (d : tableauDirection t) :
    tableauPhaseSection t d +
      stabilizerPhaseDirection (tableauPhaseA t ht) (tableauQuadraticMatrix t ht) (d : BooleanVec n) ∈
        affineOrthogonal (tableauDirection t) := by
  intro e
  let e' : tableauDirection t := ⟨e, e.property⟩
  change booleanDot (tableauPhaseSection t d +
    stabilizerPhaseDirection (tableauPhaseA t ht) (tableauQuadraticMatrix t ht)
      (d : BooleanVec n)) (e' : BooleanVec n) = 0
  rw [Qatlib.Concepts.HspRecovery.ReductionCore.booleanDot_add_left, booleanDot_stabilizerPhaseDirection,
    booleanDot_comm_affine
      (quadDirection (tableauQuadraticMatrix t ht) (d : BooleanVec n)) (e' : BooleanVec n),
    booleanDot_quadDirection_tableauQuadraticMatrix t ht (e' : BooleanVec n) (d : BooleanVec n),
    tableauAlternatingBilinear_on_direction t ht e' d, booleanDot_tableauPhaseA_eq,
    booleanDot_tableauPhaseA_eq, submoduleRetraction_coe, submoduleRetraction_coe,
    booleanDot_comm_affine (tableauPhaseSection t d) (e' : BooleanVec n)]
  ring_nf
  simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, add_zero]

theorem quadraticDirection_mem_tableauRowSpace {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t))
    (d : tableauDirection t) :
    ((d : BooleanVec n),
      stabilizerPhaseDirection (tableauPhaseA t ht) (tableauQuadraticMatrix t ht)
        (d : BooleanVec n)) ∈ tableauRowSpace t := by
  let z : BooleanVec n := tableauPhaseSection t d +
    stabilizerPhaseDirection (tableauPhaseA t ht) (tableauQuadraticMatrix t ht) (d : BooleanVec n)
  have hz : z ∈ affineOrthogonal (tableauDirection t) :=
      tableauPhaseDirection_error_orthogonal t ht d
  have hzmem : (0, z) ∈ tableauRowSpace t := zero_diagonal_mem_tableauRowSpace t ht hind z hz
  have hpair : ((tableauDirectionSection t d : tableauRowSpace t) :
      BooleanVec n × BooleanVec n) + (0, z) =
      ((d : BooleanVec n),
        stabilizerPhaseDirection (tableauPhaseA t ht) (tableauQuadraticMatrix t ht)
          (d : BooleanVec n)) := by
    apply Prod.ext
    · simp only [Prod.fst_add, add_zero]
      exact tableauDirectionSection_fst t d
    · simp only [Prod.snd_add]
      change tableauPhaseSection t d + (tableauPhaseSection t d +
        stabilizerPhaseDirection (tableauPhaseA t ht) (tableauQuadraticMatrix t ht)
          (d : BooleanVec n)) = _
      rw [← add_assoc]
      have hself : tableauPhaseSection t d + tableauPhaseSection t d = 0 := by
        funext i
        exact Qatlib.Concepts.HspRecovery.ReductionCore.zmod2_add_self _
      rw [hself, zero_add]
  rw [← hpair]
  exact (tableauRowSpace t).add_mem (tableauDirectionSection t d).property hzmem

theorem quadraticSympFamily_mem_tableauRowSpace {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t))
    (i : Fin (Module.finrank (ZMod 2) (tableauDirection t)) ⊕
      Fin (Module.finrank (ZMod 2) (affineOrthogonal (tableauDirection t)))) :
    quadraticSympFamily (tableauPhaseA t ht) (tableauQuadraticMatrix t ht)
      (tableauDirection t) i ∈ tableauRowSpace t := by
  cases i with
  | inl j =>
      exact quadraticDirection_mem_tableauRowSpace t ht hind
        (Module.finBasis (ZMod 2) (tableauDirection t) j)
  | inr j =>
      exact zero_diagonal_mem_tableauRowSpace t ht hind _
        (Module.finBasis (ZMod 2) (affineOrthogonal (tableauDirection t)) j).property

theorem maskProduct_single {n : ℕ} : ∀ (gs : List (PauliElem n)) (i : Fin gs.length),
    maskProduct gs (List.ofFn (fun j => decide (i = j))) = generatorAt gs i := by
  intro gs
  induction gs with
  | nil => intro i; exact Fin.elim0 i
  | cons g rest ih =>
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [List.ofFn_succ]
        have htail : maskProduct rest
            (List.ofFn (fun j => decide ((0 : Fin (rest.length + 1)) = j.succ))) = 1 := by
          apply maskProduct_eq_one
          · simp
          · intro b hb
            obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
            apply decide_eq_false
            exact (Fin.succ_ne_zero j).symm
        simp [maskProduct, htail, generatorAt, pauliElem_mul_one]
      · rw [List.ofFn_succ]
        simp [maskProduct, ih, generatorAt]

theorem tableauLift_basis {n m : ℕ} (t : Tableau n m)
    (hind : IndependentGenerators (tableauGenerators t)) (i : Fin m) :
    tableauLift t hind (tableauRowBasis t hind (rowEquiv t i)) = (t i).decode := by
  have h := maskProduct_single (tableauGenerators t) (rowEquiv t i)
  rw [generatorAt_rowEquiv] at h
  simpa [tableauLift, tableauRowBasis, zmod2Mask, Module.Basis.repr_self,
    Finsupp.single_apply] using! h

theorem quadraticAffine_rowSpace_eq {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t))
    (b : BooleanVec n) (p : BooleanVec n) :
    tableauRowSpace (quadraticAffineTableau (tableauPhaseA t ht) (tableauQuadraticMatrix t ht)
      b (tableauDirection t) p) = tableauRowSpace t := by
  let q := quadraticAffineTableau (tableauPhaseA t ht) (tableauQuadraticMatrix t ht)
    b (tableauDirection t) p
  have hle : tableauRowSpace q ≤ tableauRowSpace t := by
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    have hi := symplecticVecOfFn_rowEquiv q ((rowEquiv q).symm i)
    rw [Equiv.apply_symm_apply] at hi
    rw [hi, rowSympVec_quadraticAffineTableau]
    exact quadraticSympFamily_mem_tableauRowSpace t ht hind _
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hqind : IndependentGenerators (tableauGenerators q) :=
    quadraticAffineTableau_independent _ _ _ _ _
  exact (finrank_tableauRowSpace q hqind).trans (finrank_tableauRowSpace t hind).symm

def tableauRowSpaceCast {n : ℕ} {q t : Tableau n n}
    (hspace : tableauRowSpace q = tableauRowSpace t) (v : tableauRowSpace t) : tableauRowSpace q :=
  ⟨v, by rw [hspace]; exact v.property⟩

def pauliSignDifference {n : ℕ} (p q : PauliElem n) : ZMod 2 :=
  if p.phase = q.phase then 0 else 1

theorem pauli_phase_eq_add_signDifference {n : ℕ} {p q : PauliElem n}
    (hp : IsHermitianPauli p) (hq : IsHermitianPauli q) :
    p.phase = q.phase + phase4Sign (pauliSignDifference p q) := by
  rcases hp with hp | hp <;> rcases hq with hq | hq <;>
    simp_all [pauliSignDifference, phase4Sign, zmod4_two_add_two]

theorem pauliSignDifference_add {n : ℕ} {ι : Type*} [AddCommGroup ι]
    (p q : ι → PauliElem n)
    (hpherm : ∀ v, IsHermitianPauli (p v)) (hqherm : ∀ v, IsHermitianPauli (q v))
    (hword : ∀ v, (p v).word = (q v).word)
    (hpadd : ∀ v w, p (v + w) = p v * p w) (hqadd : ∀ v w, q (v + w) = q v * q w)
    (v w : ι) :
    pauliSignDifference (p (v + w)) (q (v + w)) =
      pauliSignDifference (p v) (q v) + pauliSignDifference (p w) (q w) := by
  have htadd := congrArg PauliElem.phase (hpadd v w)
  have hqadd' := congrArg PauliElem.phase (hqadd v w)
  change (p (v + w)).phase = (p v).phase + (p w).phase +
    ∑ i, pauliMulPhase ((p v).word i) ((p w).word i) at htadd
  change (q (v + w)).phase = (q v).phase + (q w).phase +
    ∑ i, pauliMulPhase ((q v).word i) ((q w).word i) at hqadd'
  have hvw := pauli_phase_eq_add_signDifference (hpherm (v + w)) (hqherm (v + w))
  have hv := pauli_phase_eq_add_signDifference (hpherm v) (hqherm v)
  have hw := pauli_phase_eq_add_signDifference (hpherm w) (hqherm w)
  rw [hvw, hv, hw, hword v, hword w, hqadd'] at htadd
  have hs : phase4Sign (pauliSignDifference (p (v + w)) (q (v + w))) =
      phase4Sign (pauliSignDifference (p v) (q v)) +
        phase4Sign (pauliSignDifference (p w) (q w)) := by
    linear_combination htadd
  rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one (pauliSignDifference (p (v + w)) (q (v + w))) with h0 | h0 <;>
    rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one (pauliSignDifference (p v) (q v)) with h1 | h1 <;>
      rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one (pauliSignDifference (p w) (q w)) with h2 | h2 <;>
        (rw [h0, h1, h2] at hs ⊢; revert hs; decide)

def zmod2LinearMapOfAdd {ι : Type*} [AddCommGroup ι] [Module (ZMod 2) ι]
    (f : ι → ZMod 2) (hadd : ∀ v w, f (v + w) = f v + f w) : ι →ₗ[ZMod 2] ZMod 2 where
  toFun := f
  map_add' := hadd
  map_smul' c v := by
    rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one c with rfl | rfl
    · simp only [zero_smul, RingHom.id_apply]
      have h := hadd 0 0
      simp only [add_zero] at h
      have hz : 0 = f 0 := by linear_combination h
      exact hz.symm
    · simp

def tableauSignCharacter {n : ℕ} (t q : Tableau n n)
    (ht : ConsistentTableau t) (hq : ConsistentTableau q)
    (hindt : IndependentGenerators (tableauGenerators t))
    (hindq : IndependentGenerators (tableauGenerators q))
    (hspace : tableauRowSpace q = tableauRowSpace t) : tableauRowSpace t →ₗ[ZMod 2] ZMod 2 :=
  zmod2LinearMapOfAdd
    (fun v => pauliSignDifference (tableauLift t hindt v)
      (tableauLift q hindq (tableauRowSpaceCast hspace v))) (by
      intro v w
      let p : tableauRowSpace t → PauliElem n := fun v => tableauLift t hindt v
      let r : tableauRowSpace t → PauliElem n := fun v =>
        tableauLift q hindq (tableauRowSpaceCast hspace v)
      apply pauliSignDifference_add p r
      · intro u; exact tableauLift_hermitian t ht hindt u
      · intro u; exact tableauLift_hermitian q hq hindq _
      · intro u
        apply symplecticVec_injective
        rw [tableauLift_symplecticVec, tableauLift_symplecticVec]
        rfl
      · exact tableauLift_add t ht hindt
      · intro u z
        have hcast : tableauRowSpaceCast hspace (u + z) =
            tableauRowSpaceCast hspace u + tableauRowSpaceCast hspace z := by
          apply Subtype.ext
          rfl
        dsimp only [r]
        rw [hcast]
        exact tableauLift_add q hq hindq _ _)

theorem tableauSignCharacter_phase {n : ℕ} (t q : Tableau n n)
    (ht : ConsistentTableau t) (hq : ConsistentTableau q)
    (hindt : IndependentGenerators (tableauGenerators t))
    (hindq : IndependentGenerators (tableauGenerators q))
    (hspace : tableauRowSpace q = tableauRowSpace t) (v : tableauRowSpace t) :
    (tableauLift t hindt v).phase =
      (tableauLift q hindq (tableauRowSpaceCast hspace v)).phase +
        phase4Sign (tableauSignCharacter t q ht hq hindt hindq hspace v) := by
  exact pauli_phase_eq_add_signDifference (tableauLift_hermitian t ht hindt v)
    (tableauLift_hermitian q hq hindq _)

theorem quadFun_add_linear {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (b u d : BooleanVec n) :
    quadFun Q (b + u) 0 d = quadFun Q b 0 d + booleanDot u d := by
  simp only [quadFun, Pi.add_apply, booleanDot, add_mul, Finset.sum_add_distrib, add_zero]
  ring

theorem phase4Sign_add (x y : ZMod 2) :
    phase4Sign (x + y) = phase4Sign x + phase4Sign y := by
  rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one x with rfl | rfl <;>
    rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one y with rfl | rfl <;> decide

theorem stabilizerPhaseSign_add_linear {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b u d : BooleanVec n) :
    stabilizerPhaseSign a Q (b + u) d =
      stabilizerPhaseSign a Q b d + booleanDot u d := by
  have h0 := stabilizerPhaseSign_adjust a d Q b
  have h1 := stabilizerPhaseSign_adjust a d Q (b + u)
  rw [stabilizerPhaseTarget] at h0
  rw [stabilizerPhaseTarget, quadFun_add_linear, phase4Sign_add] at h1
  have hs : phase4Sign (stabilizerPhaseSign a Q (b + u) d) =
      phase4Sign (stabilizerPhaseSign a Q b d) + phase4Sign (booleanDot u d) := by
    linear_combination h1 - h0
  rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one (stabilizerPhaseSign a Q (b + u) d) with hnew | hnew <;>
    rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one
        (stabilizerPhaseSign a Q b d) with hold | hold <;>
    rcases Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.zmod2_eq_zero_or_one
        (booleanDot u d) with hu | hu <;>
    (rw [hnew, hold, hu] at hs ⊢; revert hs; decide)

def quadraticDirectionMap {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t)) :
    tableauDirection t →ₗ[ZMod 2] tableauRowSpace t where
  toFun d := ⟨((d : BooleanVec n),
      stabilizerPhaseDirectionLinearMap (tableauPhaseA t ht) (tableauQuadraticMatrix t ht)
        (d : BooleanVec n)),
    quadraticDirection_mem_tableauRowSpace t ht hind d⟩
  map_add' d e := by
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add, Prod.mk_add_mk]
  map_smul' c d := by
    apply Subtype.ext
    simp

def quadraticDiagonalMap {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t)) :
    affineOrthogonal (tableauDirection t) →ₗ[ZMod 2] tableauRowSpace t where
  toFun z := ⟨((0 : BooleanVec n), (z : BooleanVec n)),
    zero_diagonal_mem_tableauRowSpace t ht hind z z.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def tableauDirectionSign {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t))
    (tau : tableauRowSpace t →ₗ[ZMod 2] ZMod 2) : BooleanVec n :=
  Classical.choose (exists_booleanDot_eq
    (tau.comp ((quadraticDirectionMap t ht hind).comp
      (submoduleRetraction (tableauDirection t)))))

theorem booleanDot_tableauDirectionSign {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t))
    (tau : tableauRowSpace t →ₗ[ZMod 2] ZMod 2) (d : tableauDirection t) :
    booleanDot (tableauDirectionSign t ht hind tau) (d : BooleanVec n) =
      tau (quadraticDirectionMap t ht hind d) := by
  have h := Classical.choose_spec (exists_booleanDot_eq
    (tau.comp ((quadraticDirectionMap t ht hind).comp
      (submoduleRetraction (tableauDirection t))))) (d : BooleanVec n)
  change booleanDot (tableauDirectionSign t ht hind tau) (d : BooleanVec n) =
    tau (quadraticDirectionMap t ht hind
      (submoduleRetraction (tableauDirection t) (d : BooleanVec n))) at h
  rwa [submoduleRetraction_coe] at h

noncomputable def tableauDiagonalSign {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t))
    (tau : tableauRowSpace t →ₗ[ZMod 2] ZMod 2) : BooleanVec n :=
  Classical.choose (exists_booleanDot_eq
    (tau.comp ((quadraticDiagonalMap t ht hind).comp
      (submoduleRetraction (affineOrthogonal (tableauDirection t))))))

theorem booleanDot_tableauDiagonalSign {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t))
    (tau : tableauRowSpace t →ₗ[ZMod 2] ZMod 2)
    (z : affineOrthogonal (tableauDirection t)) :
    booleanDot (tableauDiagonalSign t ht hind tau) (z : BooleanVec n) =
      tau (quadraticDiagonalMap t ht hind z) := by
  have h := Classical.choose_spec (exists_booleanDot_eq
    (tau.comp ((quadraticDiagonalMap t ht hind).comp
      (submoduleRetraction (affineOrthogonal (tableauDirection t)))))) (z : BooleanVec n)
  change booleanDot (tableauDiagonalSign t ht hind tau) (z : BooleanVec n) =
    tau (quadraticDiagonalMap t ht hind
      (submoduleRetraction (affineOrthogonal (tableauDirection t)) (z : BooleanVec n))) at h
  rwa [submoduleRetraction_coe] at h

theorem tableauRowBasis_rowSympVec {n m : ℕ} (t : Tableau n m)
    (hind : IndependentGenerators (tableauGenerators t)) (i : Fin m) :
    ((tableauRowBasis t hind (rowEquiv t i) : tableauRowSpace t) :
      BooleanVec n × BooleanVec n) = rowSympVec t i := by
  exact (Module.Basis.coe_span_apply (symplecticVecOfFn_linearIndependent _ hind) _).trans
    (symplecticVecOfFn_rowEquiv t i)

theorem quadraticAffineTableau_direction_phase {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n)
    (D : Submodule (ZMod 2) (BooleanVec n)) (p : BooleanVec n) (i : Fin n)
    (j : Fin (Module.finrank (ZMod 2) D))
    (h : (affineIndexEquiv D).symm i = Sum.inl j) :
    (quadraticAffineTableau a Q b D p i).decode.phase =
      phase4Sign (stabilizerPhaseSign a Q b (Module.finBasis (ZMod 2) D j)) := by
  simp [quadraticAffineTableau, quadraticAffineRowFamily, h, affinePauliRow, pauliRow,
    Row.decode]

theorem quadraticAffineTableau_diagonal_phase {n : ℕ} (a : BooleanVec n)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (b : BooleanVec n)
    (D : Submodule (ZMod 2) (BooleanVec n)) (p : BooleanVec n) (i : Fin n)
    (j : Fin (Module.finrank (ZMod 2) (affineOrthogonal D)))
    (h : (affineIndexEquiv D).symm i = Sum.inr j) :
    (quadraticAffineTableau a Q b D p i).decode.phase =
      phase4Sign (booleanDot (Module.finBasis (ZMod 2) (affineOrthogonal D) j) p) := by
  simp [quadraticAffineTableau, quadraticAffineRowFamily, h, diagonalRow, Row.decode,
    phase4Sign]

theorem tableauRowSpaceCast_basis_of_rowSympVec_eq {n : ℕ} {q0 q1 t : Tableau n n}
    (hq0ind : IndependentGenerators (tableauGenerators q0))
    (hq1ind : IndependentGenerators (tableauGenerators q1))
    (hspace0 : tableauRowSpace q0 = tableauRowSpace t)
    (hspace1 : tableauRowSpace q1 = tableauRowSpace t) (i : Fin n)
    (hrow : rowSympVec q0 i = rowSympVec q1 i) :
    tableauRowSpaceCast hspace0 (tableauRowSpaceCast hspace1.symm
      (tableauRowBasis q1 hq1ind (rowEquiv q1 i))) =
        tableauRowBasis q0 hq0ind (rowEquiv q0 i) := by
  apply Subtype.ext
  change ((tableauRowBasis q1 hq1ind (rowEquiv q1 i) : tableauRowSpace q1) :
    BooleanVec n × BooleanVec n) = _
  rw [tableauRowBasis_rowSympVec, tableauRowBasis_rowSympVec, hrow]

theorem tableau_extract_upToPhase {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t)
    (hind : IndependentGenerators (tableauGenerators t))
    (ψ : QState (Reg n)) (hψ : ψ ∈ codeSpace t) (hn : Normalized ψ) :
    IsStabilizerFunUpToPhase (amplitudeFn ψ) := by
  let a := tableauPhaseA t ht
  let Q := tableauQuadraticMatrix t ht
  let D := tableauDirection t
  let q0 : Tableau n n := quadraticAffineTableau a Q 0 D 0
  have hq0 : ConsistentTableau q0 := by
    dsimp only [q0]
    exact quadraticAffineTableau_consistent a Q 0 D 0
  have hq0ind : IndependentGenerators (tableauGenerators q0) := by
    dsimp only [q0]
    exact quadraticAffineTableau_independent a Q 0 D 0
  have hspace0 : tableauRowSpace q0 = tableauRowSpace t := by
    dsimp only [q0, a, Q, D]
    exact quadraticAffine_rowSpace_eq t ht hind 0 0
  let tau : tableauRowSpace t →ₗ[ZMod 2] ZMod 2 :=
    tableauSignCharacter t q0 ht hq0 hind hq0ind hspace0
  let signB := tableauDirectionSign t ht hind tau
  let signP := tableauDiagonalSign t ht hind tau
  let q1 : Tableau n n := quadraticAffineTableau a Q signB D signP
  have hq1ind : IndependentGenerators (tableauGenerators q1) := by
    dsimp only [q1]
    exact quadraticAffineTableau_independent a Q signB D signP
  have hspace1 : tableauRowSpace q1 = tableauRowSpace t := by
    dsimp only [q1, a, Q, D]
    exact quadraticAffine_rowSpace_eq t ht hind signB signP
  apply quadraticAffine_extract_upToPhase a Q signB 0 D signP ψ _ hn
  intro i
  let vq : tableauRowSpace q1 := tableauRowBasis q1 hq1ind (rowEquiv q1 i)
  let v : tableauRowSpace t := tableauRowSpaceCast hspace1.symm vq
  have hrow : rowSympVec q0 i = rowSympVec q1 i := by
    dsimp only [q0, q1]
    rw [rowSympVec_quadraticAffineTableau, rowSympVec_quadraticAffineTableau]
  have hv0 : tableauRowSpaceCast hspace0 v = tableauRowBasis q0 hq0ind (rowEquiv q0 i) :=
    tableauRowSpaceCast_basis_of_rowSympVec_eq hq0ind hq1ind hspace0 hspace1 i hrow
  have hword : symplecticVec (tableauLift t hind v).word =
      symplecticVec (q1 i).decode.word := by
    rw [tableauLift_symplecticVec]
    change (v : BooleanVec n × BooleanVec n) = rowSympVec q1 i
    change (vq : BooleanVec n × BooleanVec n) = rowSympVec q1 i
    exact tableauRowBasis_rowSympVec q1 hq1ind i
  have heq : tableauLift t hind v = (q1 i).decode := by
    apply pauliElem_eq_of_symplecticVec_phase hword
    have hphase := tableauSignCharacter_phase t q0 ht hq0 hind hq0ind hspace0 v
    rw [hv0, tableauLift_basis] at hphase
    change (tableauLift t hind v).phase = (q1 i).decode.phase
    rw [hphase]
    cases h : (affineIndexEquiv D).symm i with
    | inl j =>
        let d : D := Module.finBasis (ZMod 2) D j
        have hvdir : v = quadraticDirectionMap t ht hind d := by
          apply Subtype.ext
          change (vq : BooleanVec n × BooleanVec n) = ((d : BooleanVec n),
            stabilizerPhaseDirectionLinearMap a Q (d : BooleanVec n))
          rw [tableauRowBasis_rowSympVec]
          dsimp only [q1]
          rw [rowSympVec_quadraticAffineTableau, h]
          rfl
        have hsign : stabilizerPhaseSign a Q signB (d : BooleanVec n) =
            stabilizerPhaseSign a Q 0 (d : BooleanVec n) + tau v := by
          calc
            stabilizerPhaseSign a Q signB (d : BooleanVec n) =
                stabilizerPhaseSign a Q (0 + signB) (d : BooleanVec n) := by rw [zero_add]
            _ = stabilizerPhaseSign a Q 0 (d : BooleanVec n) +
                booleanDot signB (d : BooleanVec n) :=
              stabilizerPhaseSign_add_linear a Q 0 signB (d : BooleanVec n)
            _ = stabilizerPhaseSign a Q 0 (d : BooleanVec n) +
                tau (quadraticDirectionMap t ht hind d) := by
              rw [booleanDot_tableauDirectionSign]
            _ = stabilizerPhaseSign a Q 0 (d : BooleanVec n) + tau v := by rw [hvdir]
        change (quadraticAffineTableau a Q 0 D 0 i).decode.phase + phase4Sign (tau v) =
          (quadraticAffineTableau a Q signB D signP i).decode.phase
        rw [quadraticAffineTableau_direction_phase a Q 0 D 0 i j h,
          quadraticAffineTableau_direction_phase a Q signB D signP i j h,
          hsign, phase4Sign_add]
    | inr j =>
        let z : affineOrthogonal D := Module.finBasis (ZMod 2) (affineOrthogonal D) j
        have hvdiag : v = quadraticDiagonalMap t ht hind z := by
          apply Subtype.ext
          change (vq : BooleanVec n × BooleanVec n) = (0, (z : BooleanVec n))
          rw [tableauRowBasis_rowSympVec]
          dsimp only [q1]
          rw [rowSympVec_quadraticAffineTableau, h]
          rfl
        have hsign : booleanDot (z : BooleanVec n) signP = tau v := by
          rw [booleanDot_comm_affine, booleanDot_tableauDiagonalSign, ← hvdiag]
        change (quadraticAffineTableau a Q 0 D 0 i).decode.phase + phase4Sign (tau v) =
          (quadraticAffineTableau a Q signB D signP i).decode.phase
        rw [quadraticAffineTableau_diagonal_phase a Q 0 D 0 i j h,
          quadraticAffineTableau_diagonal_phase a Q signB D signP i j h, hsign]
        simp [booleanDot, phase4Sign]
  change op (q1 i).decode *ᵥ ψ = ψ
  rw [← heq]
  exact tableauLift_fixes t hind ψ hψ v

end Qatlib.Concepts.PauliClifford.PauliAlgebra
