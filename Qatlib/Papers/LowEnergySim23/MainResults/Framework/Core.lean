/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Foundations.PureStateMath.Qubit

set_option backward.isDefEq.respectTransparency false

/-!
# Framework: low-energy spectral projectors and symmetry groups

Fixed paper version: arXiv:2312.08867v3 (Quantum **8**, 1409 (2024)).
Local original text: `prove/assets/2312.08867.pdf`
(extracted text `2312.08867.txt`).

This module fixes the paper's basic objects that the MainResults claim files
consume:

* `Op D` — the finite `D`-dimensional complex operator algebra (the paper's
  finite-dimensional `2^n` Hilbert space, with `D = 2^n`);
* `imaginaryConjugate s H A = e^{sH} A e^{-sH}` (used by Lemma 5/6, §3.3);
* `lowEnergyProjector H hH Δ` — the spectral projector `Π_{≤Δ}` onto the
  eigenspaces of a Hermitian `H` with eigenvalue `≤ Δ`, implemented by
  diagonalizing `H` with `Matrix.IsHermitian.eigenvectorUnitary` and keeping
  exactly the eigenspace directions selected by the threshold;
* `highEnergyProjector H hH Λ = 1 - lowEnergyProjector H hH Λ` — `Π_{>Λ}`;
* `symmetryGroup H` — the unitaries commuting with `H` (the paper's symmetry
  group `S` in Proposition 1, p.24).

The central proved fact here is that a symmetry of `H` is automatically a
symmetry of the projected Hamiltonian `Π_{≤Δ'} H Π_{≤Δ'}`.  In the eigenbasis
of `H`, a matrix commuting with `H` has no entries between distinct
eigenvalues; it therefore commutes with every spectral indicator, and in
particular with `Π_{≤Δ'}`.  This proves Proposition 1 (p.24) with no extra
assumption on `C`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.LowEnergySim23.MainResults.Framework

/-- Finite `D`-dimensional complex operators (`D = 2^n` for an `n`-qubit
system).  This is the paper's ambient Hilbert space in §2. -/
abbrev Op (D : ℕ) := Matrix (Fin D) (Fin D) ℂ

/-- §3.3 (p.27) imaginary-time conjugation `e^{sH} A e^{-sH}`, the object whose
growth controls the spectral leakage in Lemma 5. -/
def imaginaryConjugate {D : ℕ} (s : ℝ) (H A : Op D) : Op D :=
  NormedSpace.exp (s • H) * A * NormedSpace.exp (-(s • H))

/-- The paper's low-energy projector `Π_{≤Δ}` (§2, p.10): the orthogonal
spectral projector of a Hermitian `H` onto the eigenspaces with eigenvalue
`≤ Δ`, written in the eigenbasis furnished by
`Matrix.IsHermitian.eigenvectorUnitary`. -/
def lowEnergyProjector {D : ℕ} (H : Op D) (hH : H.IsHermitian) (Δ : ℝ) : Op D :=
  (hH.eigenvectorUnitary : Op D) *
    diagonal (fun i : Fin D => if hH.eigenvalues i ≤ Δ then (1 : ℂ) else 0) *
    star (hH.eigenvectorUnitary : Op D)

/-- The complementary projector `Π_{>Λ} = I - Π_{≤Λ}` (paper p.10). -/
def highEnergyProjector {D : ℕ} (H : Op D) (hH : H.IsHermitian) (Λ : ℝ) : Op D :=
  1 - lowEnergyProjector H hH Λ

/-- The paper's symmetry group `S` of a Hamiltonian: all unitaries commuting
with `H` (Proposition 1, p.24). -/
def symmetryGroup {D : ℕ} (H : Op D) : Set (Op D) :=
  { C | C ∈ Matrix.unitaryGroup (Fin D) ℂ ∧ C * H = H * C }

/-- The eigenvalue diagonal of a Hermitian matrix, in its eigenbasis. -/
def eigenvalueDiagonal {D : ℕ} (H : Op D) (hH : H.IsHermitian) : Op D :=
  diagonal (fun i : Fin D => ((hH.eigenvalues i : ℝ) : ℂ))

/-- The threshold indicator diagonal of a Hermitian matrix, in its eigenbasis. -/
def lowEnergyIndicator {D : ℕ} (H : Op D) (hH : H.IsHermitian) (Δ : ℝ) : Op D :=
  diagonal (fun i : Fin D => if hH.eigenvalues i ≤ Δ then (1 : ℂ) else 0)

/-- Spectral diagonalization `H = U · diag(λ) · Uᴴ` (Mathlib
`Matrix.IsHermitian.spectral_theorem`), packaged in this development's
notation. -/
theorem spectral_decomposition {D : ℕ} (H : Op D) (hH : H.IsHermitian) :
    H = (hH.eigenvectorUnitary : Op D) * eigenvalueDiagonal H hH *
      star (hH.eigenvectorUnitary : Op D) := by
  have h := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  simpa [eigenvalueDiagonal, Function.comp_def] using h

/-- The eigenvector matrix is unitary: `Uᴴ U = 1`. -/
theorem star_eigenvectorUnitary_mul {D : ℕ} (H : Op D) (hH : H.IsHermitian) :
    star (hH.eigenvectorUnitary : Op D) * (hH.eigenvectorUnitary : Op D) = 1 :=
  Unitary.coe_star_mul_self hH.eigenvectorUnitary

/-- The eigenvector matrix is unitary: `U Uᴴ = 1`. -/
theorem eigenvectorUnitary_mul_star {D : ℕ} (H : Op D) (hH : H.IsHermitian) :
    (hH.eigenvectorUnitary : Op D) * star (hH.eigenvectorUnitary : Op D) = 1 :=
  Unitary.coe_mul_star_self hH.eigenvectorUnitary

/-- The projector is exactly `U · diag(indicator) · Uᴴ`. -/
theorem lowEnergyProjector_eq {D : ℕ} (H : Op D) (hH : H.IsHermitian) (Δ : ℝ) :
    lowEnergyProjector H hH Δ =
      (hH.eigenvectorUnitary : Op D) * lowEnergyIndicator H hH Δ *
        star (hH.eigenvectorUnitary : Op D) := by
  simp [lowEnergyProjector, lowEnergyIndicator, Matrix.mul_assoc]

/-- Conjugation by the eigenvector unitary sends the eigenvalue diagonal to
`H` itself: `U · diag(λ) · Uᴴ = H`. -/
theorem conjugate_diagonal_eq {D : ℕ} (H : Op D) (hH : H.IsHermitian) :
    Unitary.conjStarAlgAut ℂ (Op D) hH.eigenvectorUnitary (eigenvalueDiagonal H hH) = H :=
  (spectral_decomposition H hH).symm

/-- Conjugation by `Uᴴ` sends `H` to the eigenvalue diagonal:
`Uᴴ · H · U = diag(λ)`. -/
theorem conjugate_hamiltonian_eq_diagonal {D : ℕ} (H : Op D) (hH : H.IsHermitian) :
    (star (hH.eigenvectorUnitary : Op D)) * H * (hH.eigenvectorUnitary : Op D) =
      eigenvalueDiagonal H hH := by
  have h := hH.conjStarAlgAut_star_eigenvectorUnitary (𝕜 := ℂ)
  rw [Unitary.conjStarAlgAut_star_apply] at h
  simpa [eigenvalueDiagonal, Function.comp_def] using h

/-- Entrywise statement in the eigenbasis: if `C H = H C`, then the conjugated
matrix `Uᴴ C U` has zero entries between eigenvalues that differ.  This is the
key step of Proposition 1 (p.24). -/
theorem conjugated_entry_eq_zero_of_ne {D : ℕ} (H C : Op D) (hH : H.IsHermitian)
    (hC : C * H = H * C) {i j : Fin D} (hij : hH.eigenvalues i ≠ hH.eigenvalues j) :
    (star (hH.eigenvectorUnitary : Op D) * C * (hH.eigenvectorUnitary : Op D)) i j = 0 := by
  let X : Op D := star (hH.eigenvectorUnitary : Op D) * C * (hH.eigenvectorUnitary : Op D)
  let Dg : Op D := eigenvalueDiagonal H hH
  have hCD : X * Dg = Dg * X := by
    have h := congrArg (Unitary.conjStarAlgAut ℂ (Op D) (star hH.eigenvectorUnitary)) hC
    simp only [map_mul] at h
    simpa [X, Dg, Unitary.conjStarAlgAut_star_apply, conjugate_hamiltonian_eq_diagonal]
      using h
  have hdiag : X i j * ((hH.eigenvalues j : ℝ) : ℂ) =
      ((hH.eigenvalues i : ℝ) : ℂ) * X i j := by
    have h := congrArg (fun M : Op D => M i j) hCD
    simpa [X, Dg, eigenvalueDiagonal] using h
  have h0 : X i j * ((hH.eigenvalues j : ℝ) : ℂ) -
      ((hH.eigenvalues i : ℝ) : ℂ) * X i j = 0 := sub_eq_zero.mpr hdiag
  have hsub : (((hH.eigenvalues j : ℝ) : ℂ) - ((hH.eigenvalues i : ℝ) : ℂ)) * X i j = 0 := by
    calc (((hH.eigenvalues j : ℝ) : ℂ) - ((hH.eigenvalues i : ℝ) : ℂ)) * X i j
        = ((hH.eigenvalues j : ℝ) : ℂ) * X i j -
            ((hH.eigenvalues i : ℝ) : ℂ) * X i j := sub_mul _ _ _
      _ = X i j * ((hH.eigenvalues j : ℝ) : ℂ) -
            ((hH.eigenvalues i : ℝ) : ℂ) * X i j := by
          rw [mul_comm ((hH.eigenvalues j : ℝ) : ℂ) (X i j)]
      _ = 0 := h0
  have hcast : (((hH.eigenvalues j : ℝ) : ℂ) - ((hH.eigenvalues i : ℝ) : ℂ)) =
      (((hH.eigenvalues j - hH.eigenvalues i : ℝ)) : ℂ) := by
    push_cast
    ring
  have hne : (((hH.eigenvalues j - hH.eigenvalues i : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr (Ne.symm hij)
  rw [hcast] at hsub
  exact (mul_eq_zero.mp hsub).resolve_left hne

/-- **Proposition 1 (p.24), projection step.**  Every operator commuting with a
Hermitian `H` commutes with the spectral projector `Π_{≤Δ}`.  In the eigenbasis
the conjugated operator is block diagonal across distinct eigenvalues, hence it
commutes with the threshold indicator. -/
theorem commute_lowEnergyProjector_of_commute {D : ℕ} (H C : Op D) (hH : H.IsHermitian)
    (Δ : ℝ) (hC : C * H = H * C) :
    C * lowEnergyProjector H hH Δ = lowEnergyProjector H hH Δ * C := by
  classical
  let φ : Op D ≃⋆ₐ[ℂ] Op D := Unitary.conjStarAlgAut ℂ (Op D) hH.eigenvectorUnitary
  let E : Op D := lowEnergyIndicator H hH Δ
  have hP : lowEnergyProjector H hH Δ = φ E := by
    simp [φ, E, lowEnergyProjector_eq, Unitary.conjStarAlgAut_apply]
  have hsymm : φ.symm C = star (hH.eigenvectorUnitary : Op D) * C *
      (hH.eigenvectorUnitary : Op D) := by
    have hs : φ.symm = Unitary.conjStarAlgAut ℂ (Op D) (star hH.eigenvectorUnitary) :=
      Unitary.conjStarAlgAut_symm _
    rw [hs, Unitary.conjStarAlgAut_star_apply]
  have hCE : φ.symm C * E = E * φ.symm C := by
    rw [hsymm]
    let X : Op D := star (hH.eigenvectorUnitary : Op D) * C *
      (hH.eigenvectorUnitary : Op D)
    change X * E = E * X
    ext i j
    simp only [E, lowEnergyIndicator, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : hH.eigenvalues i = hH.eigenvalues j
    · rw [hij, mul_comm]
    · have hz : X i j = 0 := conjugated_entry_eq_zero_of_ne H C hH hC hij
      rw [hz, zero_mul, mul_zero]
  have hCeq : C = φ (φ.symm C) := (StarAlgEquiv.apply_symm_apply φ C).symm
  rw [hCeq, hP, ← map_mul, ← map_mul, hCE]

/-- **Proposition 1 (p.24).**  If `S` is the symmetry group of `H`, then `S`
is a subgroup of the symmetry group of `H̄ = Π_{≤Δ'} H Π_{≤Δ'}`. -/
theorem symmetry_group_le_projected_symmetry_group {D : ℕ} (H : Op D) (hH : H.IsHermitian)
    (Δ' : ℝ) :
    symmetryGroup H ⊆
      symmetryGroup (lowEnergyProjector H hH Δ' * H * lowEnergyProjector H hH Δ') := by
  intro C hC
  refine ⟨hC.1, ?_⟩
  let P : Op D := lowEnergyProjector H hH Δ'
  have hP : C * P = P * C :=
    commute_lowEnergyProjector_of_commute H C hH Δ' hC.2
  show C * (P * H * P) = (P * H * P) * C
  calc C * (P * H * P)
      = ((C * P) * H) * P := by simp only [Matrix.mul_assoc]
    _ = ((P * C) * H) * P := by rw [hP]
    _ = (P * (C * H)) * P := by simp only [Matrix.mul_assoc]
    _ = (P * (H * C)) * P := by rw [hC.2]
    _ = ((P * H) * C) * P := by simp only [Matrix.mul_assoc]
    _ = ((P * H) * P) * C := by simp only [Matrix.mul_assoc, hP]

end Qatlib.Papers.LowEnergySim23.MainResults.Framework
