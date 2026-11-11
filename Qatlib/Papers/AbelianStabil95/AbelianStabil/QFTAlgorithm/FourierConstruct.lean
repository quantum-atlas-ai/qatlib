/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AbelianStabil95.AbelianStabil.QFTAlgorithm.CharacterTarget

/-!
# Matrix constructions for character Fourier readout

This module computes the action of the character Fourier matrix and its adjoint on basis and
character states. It also defines the diagonal character interaction `uqMat`, the preparation
matrix `tqMat`, the addition permutation `copyMat`, and the Fourier-conjugated copying operation
`QqMat`. The development follows [Kitaev1995].

## Main statements

* `tqMat_mulVec_ket`: prepares a labeled character state from a zero second register.
* `QqMat_mulVec`: extracts a character label while preserving its Fourier state.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.HspRecovery.AbelianSampling
open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.QFTAlgorithm

variable {E : Type} [AddCommGroup E] [Fintype E] [DecidableEq E]

/-- Applying the character Fourier matrix to basis state `a` yields the normalized character
vector labeled by `a`, as used in [Kitaev1995]. -/
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

/-- The adjoint character Fourier matrix sends the character vector labeled by `a` to basis
state `a`, as used in [Kitaev1995]. -/
theorem characterQFT_conjTranspose_mulVec (labels : E ≃ AddChar E ℂ) (a : E) :
    (characterQFT E labels)ᴴ *ᵥ orbitFourierVec E (labels a) = Ket a := by
  rw [← characterQFT_mulVec_ket labels a, Matrix.mulVec_mulVec]
  have hunit : (characterQFT E labels)ᴴ * characterQFT E labels = 1 := by
    have h := characterQFT_unitary E labels
    rwa [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
  rw [hunit, Matrix.one_mulVec]

/-- The diagonal two-register matrix with diagonal value `labels a b` at the pair `(a, b)`. -/
def uqMat (labels : E ≃ AddChar E ℂ) : Matrix (E × E) (E × E) ℂ :=
  Matrix.diagonal (fun p : E × E => labels p.1 p.2)

/-- The interaction matrix `uqMat` multiplies basis state `(a, b)` by the character value
`labels a b`, as used in [Kitaev1995]. -/
theorem uqMat_mulVec_ket (labels : E ≃ AddChar E ℂ) (a b : E) :
    uqMat labels *ᵥ Ket (a, b) = (labels a b) • Ket (a, b) := by
  funext p
  unfold uqMat
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  simp only [Ket]
  by_cases h : p = (a, b)
  · subst h; simp
  · simp [h]

/-- The matrix mapping zero-second-register basis inputs to the corresponding labeled Fourier
state and using identity columns for nonzero second-register inputs. -/
def tqMat (labels : E ≃ AddChar E ℂ) : Matrix (E × E) (E × E) ℂ :=
  Matrix.of fun p q =>
    if q.2 = 0 then (if p.1 = q.1 then characterQFT E labels p.2 q.1 else 0)
    else if p = q then 1 else 0

/-- On basis input `(a, 0)`, `tqMat` preserves the first register and prepares the normalized
character vector labeled by `a` in the second, as used in [Kitaev1995]. -/
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

/-- The permutation matrix of the map `(a, b) ↦ (a, b + a)` on two group registers. -/
def copyMat : Matrix (E × E) (E × E) ℂ :=
  Matrix.of fun p q => if p = (q.1, q.2 + q.1) then 1 else 0

/-- The addition permutation maps basis state `(x, 0)` to `(x, x)`, as used in [Kitaev1995]. -/
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

/-- The copying permutation conjugated by the character Fourier transform on the first register. -/
def QqMat (labels : E ≃ AddChar E ℂ) : Matrix (E × E) (E × E) ℂ :=
  TensorGate (characterQFT E labels) (1 : Matrix E E ℂ) * copyMat (E := E) *
    TensorGate ((characterQFT E labels)ᴴ) (1 : Matrix E E ℂ)

/-- On a labeled character vector and a zero second register, `QqMat` preserves the character
vector and writes its label in the second register, as used in [Kitaev1995]. -/
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
