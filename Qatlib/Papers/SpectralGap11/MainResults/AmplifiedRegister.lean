/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# The doubled oracle register for spectral-gap amplification

Fixed source: arXiv:1110.2494v3, printed p.4, Eq.(5) and the following
modification of the ancilla projection. Half of the doubled register applies
the original term reflection and half applies the identity. Its compression
is therefore `1-H/L`, avoiding the spurious endpoint at `lambda=L`.
-/

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Papers.SpectralGap11.MainResults.AmplifiedRegister

open Matrix
open scoped BigOperators

noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

/-- The register embedding with the same ancilla amplitude at each label. -/
def uniformEmbed (rho : ℂ) : Matrix (I × K) I ℂ :=
  fun row col => if row.1 = col then rho else 0

/-- Compressing a genuinely controlled gate along a uniform ancilla equals
the corresponding weighted sum of its blocks. -/
theorem embed_compression (rho : ℂ) (B : K → Matrix I I ℂ) :
    (uniformEmbed (K := K) rho)ᴴ * Matrix.blockDiagonal B * uniformEmbed rho =
      (star rho * rho) • ∑ k, B k := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.blockDiagonal_apply, Fintype.sum_prod_type, uniformEmbed,
    Matrix.smul_apply, smul_eq_mul]
  simp only [apply_ite]
  simp [mul_assoc]
  rw [Matrix.sum_apply]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The Gram matrix of the uniform-register embedding. -/
theorem uniformEmbed_gram (rho : ℂ) :
    (uniformEmbed (K := K) rho)ᴴ * uniformEmbed rho =
      (star rho * rho * (Fintype.card K : ℂ)) • (1 : Matrix I I ℂ) := by
  have h := embed_compression (I := I) (K := K) rho (fun _ => 1)
  have hdiag : Matrix.blockDiagonal (fun _ : K => (1 : Matrix I I ℂ)) = 1 :=
    Matrix.blockDiagonal_one
  rw [hdiag, Matrix.mul_one] at h
  simpa only [Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul] using h

/-- The reflection of a single input projector. -/
def termReflection (P : Matrix I I ℂ) : Matrix I I ℂ :=
  1 - (2 : ℂ) • P

/-- A term reflection is an involution when its input is a projector. -/
theorem termReflection_sq (P : Matrix I I ℂ) (hP : P * P = P) :
    termReflection P * termReflection P = 1 := by
  simp only [termReflection, sub_mul, mul_sub, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, hP]
  module

omit [Fintype I] in
/-- A term reflection is Hermitian for a Hermitian input projector. -/
theorem termReflection_hermitian (P : Matrix I I ℂ) (hP : P.IsHermitian) :
    (termReflection P).IsHermitian := by
  change (1 - (2 : ℂ) • P)ᴴ = 1 - (2 : ℂ) • P
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, hP.eq, star_ofNat]

/-- The two controlled branches: a term reflection and an idle branch. -/
def lazyBlocks (Proj : K → Matrix I I ℂ) (label : K × Bool) : Matrix I I ℂ :=
  if label.2 then 1 else termReflection (Proj label.1)

/-- The actual doubled-register oracle is a controlled block-diagonal gate. -/
def lazyOracle (Proj : K → Matrix I I ℂ) :
    Matrix (I × (K × Bool)) (I × (K × Bool)) ℂ :=
  Matrix.blockDiagonal (lazyBlocks Proj)

/-- All doubled-register oracle blocks square to the identity. -/
theorem lazyOracle_sq (Proj : K → Matrix I I ℂ)
    (hProj : ∀ k, Proj k * Proj k = Proj k) :
    lazyOracle Proj * lazyOracle Proj = 1 := by
  rw [lazyOracle, ← Matrix.blockDiagonal_mul]
  have hb : (fun kb => lazyBlocks Proj kb * lazyBlocks Proj kb) = fun _ =>
      (1 : Matrix I I ℂ) := by
    funext kb
    rcases kb with ⟨k, b⟩
    cases b <;> simp [lazyBlocks, termReflection_sq _ (hProj k)]
  rw [hb]
  exact Matrix.blockDiagonal_one

omit [Fintype I] [Fintype K] in
/-- The controlled reflection is Hermitian before any spectral decomposition. -/
theorem lazyOracle_hermitian (Proj : K → Matrix I I ℂ)
    (hProj : ∀ k, (Proj k).IsHermitian) :
    (lazyOracle Proj).IsHermitian := by
  change (Matrix.blockDiagonal (lazyBlocks Proj))ᴴ = _
  rw [Matrix.blockDiagonal_conjTranspose]
  congr 1
  funext kb
  rcases kb with ⟨k, b⟩
  cases b <;> simp [lazyBlocks, (termReflection_hermitian _ (hProj k)).eq]

omit [Fintype I] [DecidableEq K] in
/-- Summing the doubled oracle blocks gives `2|K| I - 2H` exactly. -/
theorem lazyBlocks_sum (Proj : K → Matrix I I ℂ) :
    ∑ kb, lazyBlocks Proj kb =
      (2 * Fintype.card K : ℂ) • (1 : Matrix I I ℂ) -
        (2 : ℂ) • ∑ k, Proj k := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, lazyBlocks,
    Bool.false_eq_true, ↓reduceIte, termReflection]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ,
    ← Finset.smul_sum]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  module

/-- The real nonnegative amplitude of the uniform doubled ancilla. -/
def ancAmplitude : ℂ :=
  (Real.sqrt ((1 : ℝ) / (2 * Fintype.card K)) : ℂ)

omit [Fintype I] [DecidableEq I] [DecidableEq K] in
/-- The squared amplitude equals `1/(2|K|)` exactly. -/
theorem ancAmplitude_norm :
    star (ancAmplitude (K := K)) * ancAmplitude (K := K) =
      1 / (2 * (Fintype.card K : ℂ)) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / (2 * Fintype.card K) by positivity)
  have hr : Real.sqrt ((1 : ℝ) / (2 * Fintype.card K)) *
      Real.sqrt ((1 : ℝ) / (2 * Fintype.card K)) =
        1 / (2 * Fintype.card K) := by nlinarith only [hs]
  simp only [ancAmplitude, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul]
  rw [hr]
  push_cast
  rfl

/-- The normalized doubled-register compression is the genuine operator
`1-H/L`; the matrix on the left is constructed from the controlled oracle. -/
theorem lazy_compression (Proj : K → Matrix I I ℂ)
    (hK : 0 < Fintype.card K) :
    (uniformEmbed (K := K × Bool) (ancAmplitude (K := K)))ᴴ * lazyOracle Proj *
        uniformEmbed (K := K × Bool) (ancAmplitude (K := K)) =
      1 - (Fintype.card K : ℂ)⁻¹ • ∑ k, Proj k := by
  rw [lazyOracle, embed_compression, ancAmplitude_norm, lazyBlocks_sum,
    smul_sub, smul_smul, smul_smul]
  have hne : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hK)
  have hfirst : 1 / (2 * (Fintype.card K : ℂ)) *
      (2 * (Fintype.card K : ℂ)) = 1 := by field_simp [hne]
  have hsecond : 1 / (2 * (Fintype.card K : ℂ)) * 2 =
      (Fintype.card K : ℂ)⁻¹ := by field_simp [hne]
  rw [hfirst, hsecond, one_smul]

/-- The doubled uniform embedding is an isometry for a nonempty term family. -/
theorem lazyEmbed_isometry (hK : 0 < Fintype.card K) :
    (uniformEmbed (I := I) (K := K × Bool) (ancAmplitude (K := K)))ᴴ *
      uniformEmbed (I := I) (K := K × Bool) (ancAmplitude (K := K)) = 1 := by
  rw [uniformEmbed_gram, ancAmplitude_norm]
  have hne : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hK)
  have hc : 1 / (2 * (Fintype.card K : ℂ)) *
      (Fintype.card (K × Bool) : ℂ) = 1 := by
    simp only [Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hne]
  rw [hc, one_smul]

/-- The original-register subspace is the range of the explicit embedding. -/
def lazyP : Matrix (I × (K × Bool)) (I × (K × Bool)) ℂ :=
  uniformEmbed (I := I) (K := K × Bool) (ancAmplitude (K := K)) *
    (uniformEmbed (I := I) (K := K × Bool) (ancAmplitude (K := K)))ᴴ

/-- The constructed register projection is idempotent. -/
theorem lazyP_sq (hK : 0 < Fintype.card K) :
    lazyP (I := I) (K := K) * lazyP = lazyP := by
  dsimp [lazyP]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc
    ((uniformEmbed (I := I) (K := K × Bool) (ancAmplitude (K := K)))ᴴ),
    lazyEmbed_isometry hK, Matrix.one_mul]

omit [DecidableEq K] in
/-- The constructed register projection is Hermitian. -/
theorem lazyP_hermitian : (lazyP (I := I) (K := K)).IsHermitian := by
  change (uniformEmbed (I := I) (K := K × Bool) (ancAmplitude (K := K)) *
    (uniformEmbed (I := I) (K := K × Bool) (ancAmplitude (K := K)))ᴴ)ᴴ = _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rfl

end

end Qatlib.Papers.SpectralGap11.MainResults.AmplifiedRegister
