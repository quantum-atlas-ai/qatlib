/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AbelianStabil95.AbelianStabil.QFTAlgorithm.CharacterTarget
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.HspRecovery.AbelianSampling
open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.QFTAlgorithm

variable {E : Type} [AddCommGroup E] [Fintype E] [DecidableEq E]

theorem characterQFT_mulVec_ket (labels : E ≃ AddChar E ℂ) (a : E) :
    characterQFT E labels *ᵥ Ket a = orbitFourierVec E (labels a) := by
  funext x
  simp only [Matrix.mulVec, dotProduct, Ket, characterQFT]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem characterQFT_conjTranspose_mulVec (labels : E ≃ AddChar E ℂ) (a : E) :
    (characterQFT E labels)ᴴ *ᵥ orbitFourierVec E (labels a) = Ket a := by
  rw [← characterQFT_mulVec_ket labels a, Matrix.mulVec_mulVec]
  have hunit : (characterQFT E labels)ᴴ * characterQFT E labels = 1 := by
    have h := characterQFT_unitary E labels
    rwa [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
  rw [hunit, Matrix.one_mulVec]

def uqMat (labels : E ≃ AddChar E ℂ) : Matrix (E × E) (E × E) ℂ :=
  Matrix.diagonal (fun p : E × E => labels p.1 p.2)

theorem uqMat_mulVec_ket (labels : E ≃ AddChar E ℂ) (a b : E) :
    uqMat labels *ᵥ Ket (a, b) = (labels a b) • Ket (a, b) := by
  funext p
  unfold uqMat
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  simp only [Ket]
  by_cases h : p = (a, b)
  · subst h; simp
  · simp [h]

def tqMat (labels : E ≃ AddChar E ℂ) : Matrix (E × E) (E × E) ℂ :=
  Matrix.of fun p q =>
    if q.2 = 0 then (if p.1 = q.1 then characterQFT E labels p.2 q.1 else 0)
    else if p = q then 1 else 0

theorem tqMat_mulVec_ket (labels : E ≃ AddChar E ℂ) (a : E) :
    tqMat labels *ᵥ Ket (a, (0 : E)) =
      TensorState (Ket a) (orbitFourierVec E (labels a)) := by
  funext p
  obtain ⟨p1, p2⟩ := p
  simp only [Matrix.mulVec, dotProduct, Ket, tqMat, Matrix.of_apply, TensorState,
    characterQFT]
  rw [Finset.sum_eq_single (a, (0 : E))]
  · simp only [characterQFT]
    by_cases hp : (p1 = a)
    · simp [hp]
    · simp [hp]
  · intro q _ hq
    simp [hq]
  · intro h
    exact absurd (Finset.mem_univ (a, (0 : E))) h

def copyMat : Matrix (E × E) (E × E) ℂ :=
  Matrix.of fun p q => if p = (q.1, q.2 + q.1) then 1 else 0

theorem copyMat_mulVec_ket (x : E) :
    copyMat (E := E) *ᵥ Ket (x, (0 : E)) = Ket (x, x) := by
  funext p
  obtain ⟨p1, p2⟩ := p
  simp only [Matrix.mulVec, dotProduct, Ket, copyMat, Matrix.of_apply]
  rw [Finset.sum_eq_single (x, (0 : E))]
  · simp
  · intro q _ hq
    simp [hq]
  · intro h
    exact absurd (Finset.mem_univ (x, (0 : E))) h

def QqMat (labels : E ≃ AddChar E ℂ) : Matrix (E × E) (E × E) ℂ :=
  TensorGate (characterQFT E labels) (1 : Matrix E E ℂ) * copyMat (E := E) *
    TensorGate ((characterQFT E labels)ᴴ) (1 : Matrix E E ℂ)

theorem QqMat_mulVec (labels : E ≃ AddChar E ℂ) (a : E) :
    QqMat labels *ᵥ TensorState (orbitFourierVec E (labels a)) (Ket (0 : E)) =
      TensorState (orbitFourierVec E (labels a)) (Ket a) := by
  unfold QqMat
  rw [← ApplyGate, applyGate_mul, applyGate_mul]
  rw [applyGate_tensorGate]
  simp only [applyGate_one]
  rw [show ApplyGate (characterQFT E labels)ᴴ (orbitFourierVec E (labels a)) = Ket a
      from characterQFT_conjTranspose_mulVec labels a]
  rw [tensorState_ket_ket]
  rw [show ApplyGate copyMat (Ket (a, (0 : E))) = Ket (a, a) from copyMat_mulVec_ket a]
  rw [← tensorState_ket_ket]
  rw [applyGate_tensorGate]
  simp only [applyGate_one]
  rw [show ApplyGate (characterQFT E labels) (Ket a) = orbitFourierVec E (labels a)
      from characterQFT_mulVec_ket labels a]

end Qatlib.Papers.AbelianStabil95.AbelianStabil.QFTAlgorithm
