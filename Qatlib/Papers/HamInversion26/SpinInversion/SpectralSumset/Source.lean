/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamInversion26.SpinInversion.SpectralSumset.Basic
public import Qatlib.Papers.HamInversion26.SpinInversion.Model.OracleWord
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.Matrix.Diagonal

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 1 / Theorem S2 / Corollary S3 — source statements

Fixed arXiv:2607.29382v2.
* Theorem 1, page 2 (Letter): one-parameter family `U(x) = e^{iHx}`, fixed eigenbasis,
  distinct spectrum `Λ`; the minimum number of forward calls to implement `U(x)†` up to
  a global phase is `κ(Λ)` of Eq. (2).
* Theorem S2, pages S4–S7: restatement with `κ(Λ) ≤ K − 1` and the note that the
  eigenspace multiplicities do not enter.
* Corollary S3, page S8: the multiparameter version with character vectors
  `λ_j ∈ ℝ^p` and the sumset `Σ_q(Λ)` of character vectors.

The spectral unitary is the diagonal family `U(t) = Σ_j e^{iλ_j t} Π_j` in the eigenbasis.
`InvertsIn q U` is the paper's "clean deterministic protocol with at most `q` forward
calls" (the query-word model of `Model.OracleWord`).
-/

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.HamInversion26.SpinInversion.SpectralSumset
open Qatlib.Papers.HamInversion26.SpinInversion
open Qatlib.Papers.HamInversion26.SpinInversion.SpectralSumset

set_option autoImplicit false
noncomputable section

/-- The spectral family `U(t) = Σ_j e^{iλ_j t} Π_j` in the eigenbasis, Eq. (S10),
page S4.  Written as a diagonal matrix on `Fin K`. -/
def spectralUnitary {K : ℕ} (lam : Fin K → ℝ) (t : ℝ) : Matrix (Fin K) (Fin K) ℂ :=
  diagonal fun j => Complex.exp (Complex.I * ((lam j * t : ℝ) : ℂ))

/-- The multiparameter family `U(x) = Σ_j e^{iλ_j·x} Π_j` of Eq. (S17), page S8. -/
def spectralUnitaryVec {K p : ℕ} (lam : Fin K → Fin p → ℝ) (x : Fin p → ℝ) :
    Matrix (Fin K) (Fin K) ℂ :=
  diagonal fun j => Complex.exp (Complex.I * ((∑ i, lam j i * x i : ℝ) : ℂ))

/-- **Theorem S2, multiplicity-free bound** (page S4): `κ(Λ) ≤ K − 1` independently of
the eigenspace multiplicities (`Λ` is the image of the distinct eigenvalues). -/
theorem source_theorem1_kappa_le {K : ℕ} (lam : Fin K → ℝ) (hK : 0 < K) :
    kappa (Finset.univ.image lam) ≤ K - 1 := by
  have hne : (Finset.univ.image lam).Nonempty := by
    obtain ⟨j⟩ : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
    exact ⟨lam j, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩
  have hcard : (Finset.univ.image lam).card ≤ K := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin K))) (f := lam)
  have := kappa_le_card_sub_one hne
  omega

/-- The multiparameter bound `κ(Λ) ≤ K − 1` (used implicitly in Corollary S3). -/
theorem source_corollaryS3_kappa_le {K p : ℕ} (lam : Fin K → Fin p → ℝ) (hK : 0 < K) :
    kappa (Finset.univ.image lam) ≤ K - 1 := by
  have hne : (Finset.univ.image lam).Nonempty := by
    obtain ⟨j⟩ : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
    exact ⟨lam j, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩
  have hcard : (Finset.univ.image lam).card ≤ K := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin K))) (f := lam)
  have := kappa_le_card_sub_one hne
  omega

end

end Qatlib.Papers.HamInversion26.SpinInversion.SpectralSumset
