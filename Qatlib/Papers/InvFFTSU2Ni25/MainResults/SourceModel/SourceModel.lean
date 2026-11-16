/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.InvFFTSU2Ni25.NlfftPipeline.Algorithm1Inve
public import Qatlib.Concepts.NativeNumerics.NlfftPipeline.NonlinearFourierSU2
public import Qatlib.Papers.InvFFTSU2Ni25.NlfftPipeline.Algorithm1FiniteInve
public import Qatlib.Papers.InvFFTSU2Ni25.NlfftPipeline.Lemma22Inve

@[expose] public section


/-!
# InvFFTSU2Ni25 / MainResults — shared source model

Ni--Sarkar--Ying--Lin, *Inverse nonlinear fast Fourier transform on SU(2) with
applications to quantum signal processing*, fixed arXiv:2505.12615v1.

This file fixes the paper-layer vocabulary shared by all claim modules:

* the SU(2) rotation matrix `Θ(t)` of Lemma 4.1 / Lemma C.2 (Eq. (33));
* the `S` and `S_η` function classes of Eq. (10);
* the layer-stripping recurrence and its coefficient/`G_k` matrix form
  (Eqs. (23)--(34));
* the Frobenius and induced column-sum matrix norms used in Lemma C.2.

The NLFT itself (`nlftSU2`), the conjugate-reverse `conjRevN`, the layer
stripping step `layerStripStepSU2` and the actual `inverseNLFFTSU2` algorithm
are *not* redefined here: the paper-layer statements consume the shared
implementations from `Qatlib.Papers.InvFFTSU2Ni25.NlfftPipeline`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Polynomial
open scoped Matrix

namespace Qatlib.Papers.InvFFTSU2Ni25.MainResults

/-- Paper Eq. (4)-(6) notation: the NLFT of a coefficient sequence is the
polynomial pair `(A, B) = (a*, b)`, where the paper's `a*` is the
conjugate-reverse of the "a" polynomial. -/
abbrev NlftPair : Type := Polynomial ℂ × Polynomial ℂ

/-! ### The rotation matrix `Θ` -/

/-- Lemma 4.1 / Eq. (33), and Lemma C.2: the SU(2) matrix
`Θ(t) = (1/√(1+|t|²)) [[1, -t], [t, 1]]`. -/
def thetaMat (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt (1 + Complex.normSq t))⁻¹ : ℝ) • !![(1 : ℂ), -t; t, 1]

/-- The top-left entry is the reciprocal square-root normalization. -/
@[simp] theorem thetaMat_apply_zero_zero (t : ℂ) :
    thetaMat t 0 0 = ((Real.sqrt (1 + Complex.normSq t))⁻¹ : ℂ) := by
  simp [thetaMat, Matrix.cons_val_zero]

/-- The top-right entry is the negative normalized parameter. -/
@[simp] theorem thetaMat_apply_zero_one (t : ℂ) :
    thetaMat t 0 1 = -(((Real.sqrt (1 + Complex.normSq t))⁻¹ : ℝ) : ℂ) * t := by
  simp [thetaMat, Matrix.cons_val_one, Matrix.cons_val_zero]

/-- The bottom-left entry is the normalized parameter. -/
@[simp] theorem thetaMat_apply_one_zero (t : ℂ) :
    thetaMat t 1 0 = (((Real.sqrt (1 + Complex.normSq t))⁻¹ : ℝ) : ℂ) * t := by
  simp [thetaMat, Matrix.cons_val_one, Matrix.cons_val_zero]

/-- The bottom-right entry is the reciprocal square-root normalization. -/
@[simp] theorem thetaMat_apply_one_one (t : ℂ) :
    thetaMat t 1 1 = ((Real.sqrt (1 + Complex.normSq t))⁻¹ : ℂ) := by
  simp [thetaMat, Matrix.cons_val_one]

/-! ### Matrix norms used in Lemma C.2 -/

/-- Squared Frobenius norm `∑ᵢⱼ ‖Mᵢⱼ‖²` of a `2 × 2` matrix. -/
def frobSq (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ∑ i, ∑ j, ‖M i j‖ ^ 2

/-- Frobenius norm `‖M‖_F = √(∑ᵢⱼ ‖Mᵢⱼ‖²)` of a `2 × 2` matrix. -/
def frobNorm (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := Real.sqrt (frobSq M)

/-- Induced `1`-norm (maximum column sum of absolute values) of a `2 × 2`
matrix, the norm `‖·‖₁` of Lemma C.2. -/
def colSumNorm (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  max (‖M 0 0‖ + ‖M 1 0‖) (‖M 0 1‖ + ‖M 1 1‖)

/-! ### The function classes `S` and `S_η` (Eq. (10)) -/

/-- The SU(2) constraint `a a* + b b* = X^d` in the polynomial model
`(A, B) = (a*, b)`; this is the identity proved for the NLFT in the shared
library as `nlftSU2_identity`. -/
def SConstraint (d : ℕ) (A B : Polynomial ℂ) : Prop :=
  A * Qatlib.Concepts.NativeNumerics.NlfftPipeline.conjRevN d A
    + B * Qatlib.Concepts.NativeNumerics.NlfftPipeline.conjRevN d B
    = X ^ d

/-- `(a, b) ∈ S_n`: degree bounds, the SU(2) identity and the normalization
`a*(0)` real positive (paper Section 2, Eq. (3)-(6)). -/
def InS (d : ℕ) (A B : Polynomial ℂ) : Prop :=
  A.natDegree ≤ d ∧ B.natDegree ≤ d ∧ SConstraint d A B ∧
    (A.coeff 0).im = 0 ∧ 0 < (A.coeff 0).re

/-- Supremum bound on the unit circle `T`: `sup_{z∈T} ‖p(z)‖ ≤ s`. -/
def CircleSupLe (p : Polynomial ℂ) (s : ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ s

/-- `b` is not the zero polynomial on the unit circle (the paper's
`0 < sup_{z∈T} |b(z)|`). -/
def CircleSupPos (p : Polynomial ℂ) : Prop :=
  ∃ z : ℂ, ‖z‖ = 1 ∧ 0 < ‖p.eval z‖

/-- Eq. (10): `(a, b) ∈ S_η` for `η ∈ (0, 1)`: the pair lies in `S` and
`0 < sup_{z∈T} |b(z)| ≤ 1 - η`. -/
def InSη (d : ℕ) (A B : Polynomial ℂ) (η : ℝ) : Prop :=
  InS d A B ∧ CircleSupPos B ∧ CircleSupLe B (1 - η)

/-- Outer polynomial (paper Appendix B): no zeros in the closed unit disk. The
paper's `D` is the open unit disk and the boundary is handled separately; the
closed-disk version is what Lemma 2.3 concludes. -/
def NoZerosClosedDisk (p : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, ‖z‖ ≤ 1 → p.eval z ≠ 0

/-! ### Layer stripping recurrence (Eqs. (23)--(34)) -/

open Qatlib.Concepts.NativeNumerics.NlfftPipeline in
/-- One layer-stripping iteration `G_{k+1} = shift(G_k Θ(γ_k))` on the
polynomial pair model, using the shared step `layerStripStepSU2`. -/
def stripPair (A B : Polynomial ℂ) : ℕ → Polynomial ℂ × Polynomial ℂ
  | 0 => (A, B)
  | k + 1 =>
      let s := layerStripStepSU2 (stripPair A B k).1 (stripPair A B k).2
      (s.2.1, s.2.2)

open Qatlib.Concepts.NativeNumerics.NlfftPipeline in
/-- The reflection coefficient produced at step `k` of layer stripping. -/
def stripGamma (A B : Polynomial ℂ) (k : ℕ) : ℂ :=
  (layerStripStepSU2 (stripPair A B k).1 (stripPair A B k).2).1

/-- `a_{0,k}`: the constant coefficient of the `A` polynomial after `k`
layer-stripping steps (paper Lemma 4.1(a),(e)). -/
def a0k (A B : Polynomial ℂ) (k : ℕ) : ℂ := (stripPair A B k).1.coeff 0

/-- `a_{j,k}`: coefficient `j` of the `A` polynomial after `k` steps. -/
def ajk (A B : Polynomial ℂ) (j k : ℕ) : ℂ := (stripPair A B k).1.coeff j

/-- `b_{j,k}`: coefficient `j` of the `B` polynomial after `k` steps. -/
def bjk (A B : Polynomial ℂ) (j k : ℕ) : ℂ := (stripPair A B k).2.coeff j

/-- The layer-stripping matrix `G_k` of Eq. (33): row `j` holds
`(a_{j,k}, b_{j,k})`, zero-padded to `n` rows. The paper drops the last row of
the first column at each shift; padding with zeros below the valid range
matches this convention because higher coefficients vanish in the `S` model. -/
def Gmat (n : ℕ) (A B : Polynomial ℂ) (k : ℕ) : Matrix (Fin n) (Fin 2) ℂ :=
  fun j c =>
    if (j : ℕ) + k < n then
      (if c = 0 then ajk A B (j : ℕ) k else bjk A B (j : ℕ) k)
    else 0

/-- `G_0` is built from the input pair itself. -/
@[simp] theorem Gmat_zero (n : ℕ) (A B : Polynomial ℂ) :
    Gmat n A B 0 = fun (j : Fin n) (c : Fin 2) =>
      if c = 0 then A.coeff (j : ℕ) else B.coeff (j : ℕ) := by
  funext j c
  by_cases h : (j : ℕ) < n
  · simp [Gmat, h, ajk, bjk, stripPair]
  · exact False.elim (h j.isLt)

/-! ### Toeplitz scaffolding of Section 5.3 (Eqs. (46)--(53)) -/

/-- Lower-triangular Toeplitz matrix `T(v)` of Eq. (45): `T(v)_{ij} = v_{i-j}`
for `j ≤ i` and `0` otherwise. -/
def lowerToeplitz {n : ℕ} (v : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if h : (j : ℕ) ≤ (i : ℕ) then v ⟨(i : ℕ) - (j : ℕ), by omega⟩ else 0

/-- The vector `a₀` of Eq. (46): the constant coefficients `a_{0,0}, …,
a_{0,n-1}` produced by layer stripping. -/
def a0Vec (n : ℕ) (A B : Polynomial ℂ) : Fin n → ℂ := fun k => a0k A B (k : ℕ)

/-- The vector `b₀` of Eq. (46): `b_{0,0}, …, b_{0,n-1}`. -/
def b0Vec (n : ℕ) (A B : Polynomial ℂ) : Fin n → ℂ := fun k => bjk A B 0 (k : ℕ)

/-- The Toeplitz matrix `L = T(a₀)` of Lemma 5.2, Eq. (53). -/
def toeplitzL (n : ℕ) (A B : Polynomial ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  lowerToeplitz (a0Vec n A B)

/-- The displacement matrix `K = T(a₀) T(a₀)* + T(b₀) T(b₀)*` of Eq. (49). -/
def displacementK (n : ℕ) (A B : Polynomial ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  toeplitzL n A B * (toeplitzL n A B)ᴴ
    + lowerToeplitz (b0Vec n A B) * (lowerToeplitz (b0Vec n A B))ᴴ

/-- The vector of reflected coefficients `γ` computed by layer stripping
(paper Eq. (53), right-hand side `b₀`). -/
def gammaVec (n : ℕ) (A B : Polynomial ℂ) : Fin n → ℂ := fun k => stripGamma A B (k : ℕ)

end Qatlib.Papers.InvFFTSU2Ni25.MainResults
