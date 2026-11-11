/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContourMatFun21.MainResults.Common.BlockEncodingDefs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# ContourMatFun21 — §2.5 block-encoding of a diagonal matrix

Fixed arXiv:2106.08076v2 (Takahira–Ohashi–Sogabe–Usuda).

Proposition 12 (p. 12): the diagonal matrix `D = diag(d₀,…,d_{M−1})` with
`d_max = max_k |d_k|` is block-encoded *exactly* by

`U_D = Σ_k (R_z(φ_k) R_y(ϕ_k)) ⊗ |k⟩⟨k|`,

where `R_y(ϕ) = exp(i(ϕ/2)σ_y)` and `R_z(φ) = exp(i(φ/2)σ_z)`, provided
`cos(ϕ_k/2) = |d_k|/d_max` and `φ_k/2 = arg(d_k)`.

The gate is written out as the `2×2` block-diagonal `blockDiag2` over the system
index `M` (ancilla `Fin 2`), which is the matrix form of
`Σ_k (R_z R_y) ⊗ |k⟩⟨k|`.  The phase hypotheses are stated in division-free
form: `e^{iφ_k/2}·‖d_k‖ = d_k` is the paper's `φ_k/2 = arg(d_k)` together with
`|d_k| = e^{i arg d_k}·d_k`; this avoids a branch of `arg`/`sqrt` in the
statement while remaining equivalent for `d_k ≠ 0`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Foundations.PureStateMath
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.ContourMatFun21.MainResults

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- `R_y(ϕ) = e^{i(ϕ/2)σ_y} = [[cos(ϕ/2), sin(ϕ/2)], [−sin(ϕ/2), cos(ϕ/2)]]`. -/
def Ry (ϕ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos (ϕ / 2) : ℂ), (Real.sin (ϕ / 2) : ℂ);
     (-(Real.sin (ϕ / 2)) : ℂ), (Real.cos (ϕ / 2) : ℂ)]

/-- `R_z(φ) = e^{i(φ/2)σ_z} = diag(e^{iφ/2}, e^{−iφ/2})`. -/
def Rz (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (Complex.I * (φ / 2)), 0;
     0, Complex.exp (-(Complex.I * (φ / 2)))]

/-- The block-diagonal `Σ_k B_k ⊗ |k⟩⟨k|` of `2×2` blocks over the index `M`,
i.e. a matrix on `Fin 2 × M`. -/
def blockDiag2 (Bfam : M → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × M) (Fin 2 × M) ℂ :=
  Matrix.of fun p q => if p.2 = q.2 then Bfam p.2 p.1 q.1 else 0

/-- Auxiliary: half-angle cast identity `↑ϕ / 2 = ↑(ϕ / 2)` used to align the
arguments of the complex exponentials (Proposition 12, p. 12). -/
private lemma arg_half (ϕ : ℝ) : ((ϕ : ℂ) / 2) = ((ϕ / 2 : ℝ) : ℂ) := by
  push_cast; ring

/-- Auxiliary: `cos x · cos x + sin x · sin x = 1` in the `·`-rather than `^2`
form used by the entrywise `R_y` computation (Proposition 12, p. 12). -/
private lemma cos_mul_cos_add_sin_mul_sin (x : ℝ) :
    Real.cos x * Real.cos x + Real.sin x * Real.sin x = 1 := by
  rw [← sq, ← sq, Real.cos_sq_add_sin_sq]

/-- `R_y(ϕ)` is unitary: it is the real rotation matrix with orthogonal
half-angle `cos/sin` rows (Proposition 12, p. 12). -/
private lemma ry_unitary (ϕ : ℝ) : Ry ϕ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ry, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    rw [arg_half ϕ, ← Complex.ofReal_cos (ϕ / 2), ← Complex.ofReal_sin (ϕ / 2)]
    simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_neg,
      ← Complex.ofReal_add, ← Complex.ofReal_one, ← Complex.ofReal_zero]
    rw [Complex.ofReal_inj]
  · exact cos_mul_cos_add_sin_mul_sin (ϕ / 2)
  · ring
  · ring
  · rw [add_comm]; exact cos_mul_cos_add_sin_mul_sin (ϕ / 2)

/-- Auxiliary: `e^{it} · \overline{e^{it}} = 1` for real `t` (Proposition 12,
p. 12, unitarity of `R_z`). -/
private lemma expI_mul_conj (t : ℝ) :
    Complex.exp (Complex.I * (t : ℂ)) *
      (starRingEnd ℂ) (Complex.exp (Complex.I * (t : ℂ))) = 1 := by
  rw [← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_zero]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- `R_z(φ)` is unitary: it is the diagonal phase matrix
`diag(e^{iφ/2}, e^{-iφ/2})` (Proposition 12, p. 12). -/
private lemma rz_unitary (φ : ℝ) : Rz φ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rz, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [arg_half φ]
    exact expI_mul_conj (φ / 2)
  · have h := expI_mul_conj (-(φ / 2))
    rw [show Complex.I * ((-(φ / 2) : ℝ) : ℂ) = -(Complex.I * ((φ : ℂ) / 2)) by
      push_cast; ring] at h
    exact h

/-- `blockDiag2` is Mathlib's `Matrix.blockDiagonal` (Proposition 12, p. 12). -/
private lemma blockDiag2_eq_blockDiagonal (B : M → Matrix (Fin 2) (Fin 2) ℂ) :
    blockDiag2 B = Matrix.blockDiagonal B := rfl

/-- The `(0,0)` entry of `R_z(φ) R_y(ϕ)` is `e^{iφ/2} cos(ϕ/2)`
(Proposition 12, p. 12). -/
private lemma rzRy_zero_zero (φ ϕ : ℝ) :
    (Rz φ * Ry ϕ) (0 : Fin 2) 0
      = Complex.exp (Complex.I * ((φ : ℂ) / 2)) * (Real.cos (ϕ / 2) : ℂ) := by
  simp [Rz, Ry, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Proposition 12** (arXiv:2106.08076v2, p. 12).  Let `D = diagonal d` be an
`m`-qubit diagonal matrix and `d_max = max_k |d_k| > 0`.  If for each `k`
`cos(ϕ_k/2) = ‖d_k‖ / d_max` and `e^{iφ_k/2}·‖d_k‖ = d_k`, then the
block-diagonal `U_D = Σ_k (R_z(φ_k) R_y(ϕ_k)) ⊗ |k⟩⟨k|` is a
`(d_max, 1, 0)`-block-encoding of `D` (exact, one ancilla qubit).

The source states `φ_k/2 = arg(d_k)`; here it is the equivalent division-free
condition `e^{iφ_k/2}·‖d_k‖ = d_k`. -/
theorem proposition12
    (d : M → ℂ) (dmax : ℝ) (ϕ φ : M → ℝ)
    (hdmax : 0 < dmax)
    (hmax : ∀ k, ‖d k‖ ≤ dmax)
    (hcos : ∀ k, Real.cos (ϕ k / 2) = ‖d k‖ / dmax)
    (hexp : ∀ k, Complex.exp (Complex.I * (φ k / 2)) * ((‖d k‖ : ℝ) : ℂ) = d k) :
    IsApproxBlockEncoding (blockDiag2 (fun k => Rz (φ k) * Ry (ϕ k))) (0 : Fin 2)
      (Matrix.diagonal d) dmax 0 := by
  -- SOURCE: arXiv:2106.08076v2 Proposition 12, p. 12.
  -- KEY STEPS: `BlockCorner U_D 0 = diagonal (fun k => (R_z(φ_k)R_y(ϕ_k)) 0 0)`;
  --   `(R_z R_y) 0 0 = e^{iφ_k/2} cos(ϕ_k/2)`; using `cos(ϕ_k/2) = ‖d_k‖/dmax` and
  --   `e^{iφ_k/2}‖d_k‖ = d_k` this is `d_k/dmax`, so `dmax · corner = D`;
  --   unitarity of `U_D` is block-diagonal-of-unitaries (`R_z`, `R_y` unitary).
  have hunit : ∀ k, Rz (φ k) * Ry (ϕ k) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    fun k => Submonoid.mul_mem (Matrix.unitaryGroup (Fin 2) ℂ)
      (rz_unitary (φ k)) (ry_unitary (ϕ k))
  refine ⟨?_, hdmax, ?_⟩
  · -- Unitarity of the block-diagonal of unitaries.
    rw [blockDiag2_eq_blockDiagonal, Matrix.mem_unitaryGroup_iff,
      Matrix.star_eq_conjTranspose, Matrix.blockDiagonal_conjTranspose,
      ← Matrix.blockDiagonal_mul]
    have hpt : (fun k => Rz (φ k) * Ry (ϕ k) * (Rz (φ k) * Ry (ϕ k))ᴴ)
        = fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      funext k
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff.mp (hunit k)
    rw [hpt]
    exact Matrix.blockDiagonal_one
  · -- Exactness: the top-left `(0,0)` block is `D / dmax`.
    rw [norm_le_zero_iff]
    have hcorner : BlockCorner (blockDiag2 (fun k => Rz (φ k) * Ry (ϕ k))) (0 : Fin 2)
        = Matrix.diagonal (fun k => (Rz (φ k) * Ry (ϕ k)) 0 0) := by
      ext k k'
      simp [BlockCorner, blockDiag2, Matrix.diagonal]
    rw [hcorner]
    have hzero : Matrix.diagonal d
        - ((dmax : ℝ) : ℂ) • Matrix.diagonal (fun k => (Rz (φ k) * Ry (ϕ k)) 0 0) = 0 := by
      have hkey : ∀ k, ((dmax : ℝ) : ℂ) * ((Rz (φ k) * Ry (ϕ k)) 0 0) = d k := by
        intro k
        rw [rzRy_zero_zero, hcos k]
        calc ((dmax : ℝ) : ℂ)
              * (Complex.exp (Complex.I * ((φ k : ℂ) / 2))
                  * ((‖d k‖ / dmax : ℝ) : ℂ))
            = Complex.exp (Complex.I * ((φ k : ℂ) / 2))
                * (((dmax : ℝ) : ℂ) * ((‖d k‖ / dmax : ℝ) : ℂ)) := by ring
          _ = Complex.exp (Complex.I * ((φ k : ℂ) / 2))
                * ((‖d k‖ : ℝ) : ℂ) := by
              congr 1
              rw [← Complex.ofReal_mul]
              congr 1
              field_simp
          _ = d k := hexp k
      ext k k'
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply,
        Matrix.zero_apply, smul_eq_mul]
      by_cases h : k = k'
      · subst h
        simp only [↓reduceIte]
        rw [hkey k, sub_self]
      · simp [h]
    rw [hzero]

end Qatlib.Papers.ContourMatFun21.MainResults
