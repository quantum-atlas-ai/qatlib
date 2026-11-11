/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# LatticeProd19, Block `MainResults` — source model

Childs--Su--Tran--Wiebe--Zhu, *Nearly optimal lattice simulation by product formulas*,
fixed arXiv:1901.00564v2 (PDF prefetched at `assets/1901.00564.pdf`; the qatlas markdown
API was unavailable, so the PDF/txt were used).

Notation of the paper (Sections III--V):

* `e^{tX}` is the matrix/operator exponential, Definition 1, Eq. (8), p.3;
* `Ad_X(Y) = X Y X⁻¹` and `ad_X(Y) = [X,Y] = XY - YX`, Eqs. (38)--(39), p.6;
* a canonical product formula is a product of stages `e^{-itb_j B} e^{-ita_j A}`, Eq. (8), p.3.

The operator statements are developed over an arbitrary complex Banach algebra
(`NormedRing`, `NormedAlgebra ℂ`, `CompleteSpace`), which is the paper's setting
(bounded operators on a finite-dimensional Hilbert space). The matrix model
`Op d = Matrix (Fin d) (Fin d) ℂ` below instantiates the same statements with the
`L2Operator` operator norm and is used for the formula-level results.

Because the paper writes `Ad_X(Y) = X Y X⁻¹` for *invertible* `X`, while matrix inverses
are awkward in Lean, we use the equivalent exponential form `Ad_{e^{tX}}(Y) = e^{tX} Y e^{-tX}`;
`expm_neg_mul` records that `e^{-tX}` is the inverse of `e^{tX}`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LatticeProd19.MainResults.SourceModel

open scoped Matrix.Norms.L2Operator

/-! ## Generic operator calculus -/

section Generic

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

/-- `expm X t = e^{tX}` (paper Eq. (8), p.3). -/
def expm (X : 𝔸) (t : ℝ) : 𝔸 := NormedSpace.exp ((t : ℂ) • X)

/-- The `expm_zero` result for the LatticeProd19 paper model. -/
@[simp] theorem expm_zero (X : 𝔸) : expm X 0 = 1 := by
  simp [expm]

/-- The commutator `ad_X(Y) = [X,Y] = XY - YX` (paper Eq. (39), p.6). -/
def ad (X Y : 𝔸) : 𝔸 := X * Y - Y * X

/-- Iterated commutator `ad_X^j(Y)` (paper Corollary 1, Eq. (41), p.6). -/
def adPow (X : 𝔸) (j : ℕ) (Y : 𝔸) : 𝔸 := (ad X)^[j] Y

/-- The `adPow_zero` result for the LatticeProd19 paper model. -/
@[simp] theorem adPow_zero (X Y : 𝔸) : adPow X 0 Y = Y := rfl

/-- The `adPow_succ` result for the LatticeProd19 paper model. -/
theorem adPow_succ (X : 𝔸) (j : ℕ) (Y : 𝔸) :
    adPow X (j + 1) Y = ad X (adPow X j Y) := by
  simp [adPow, Function.iterate_succ_apply']

/-- Conjugation by `e^{tX}`: `Ad_{e^{tX}}(Y) = e^{tX} Y e^{-tX}` (paper Eq. (38), p.6).
The paper writes `X Y X⁻¹` for invertible `X`; for `X = e^{tX}` this is the same object
because `e^{-tX}` is the inverse of `e^{tX}` (`expm_neg_mul`). -/
def AdExp (X : 𝔸) (t : ℝ) (Y : 𝔸) : 𝔸 := expm X t * Y * expm (-X) t

/-- The `AdExp_zero` result for the LatticeProd19 paper model. -/
@[simp] theorem AdExp_zero (X Y : 𝔸) : AdExp X 0 Y = Y := by
  simp [AdExp]

/-- The `expm_neg_mul` result for the LatticeProd19 paper model. -/
theorem expm_neg_mul (X : 𝔸) (t : ℝ) : expm X t * expm (-X) t = 1 := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ ℂ 𝔸
  have hc : Commute ((t : ℂ) • X) ((t : ℂ) • (-X)) :=
    (((Commute.refl X).neg_right).smul_left (t : ℂ)).smul_right (t : ℂ)
  have hsum : ((t : ℂ) • X) + ((t : ℂ) • (-X)) = 0 := by
    rw [← smul_add, add_neg_cancel, smul_zero]
  have h : expm X t * expm (-X) t = NormedSpace.exp 0 := by
    rw [expm, expm, ← NormedSpace.exp_add_of_commute hc, hsum]
  simpa using h

/-- The `expm_hasDerivAt` result for the LatticeProd19 paper model. -/
theorem expm_hasDerivAt (X : 𝔸) (t : ℝ) :
    HasDerivAt (fun s : ℝ => expm X s) (X * expm X t) t := by
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℂ) X (t : ℂ)).scomp
    (x := t) Complex.ofRealCLM.hasDerivAt
  simpa [expm, Function.comp_def] using h

/-- The `expm_neg_hasDerivAt` result for the LatticeProd19 paper model. -/
theorem expm_neg_hasDerivAt (X : 𝔸) (t : ℝ) :
    HasDerivAt (fun s : ℝ => expm (-X) s) ((-X) * expm (-X) t) t :=
  expm_hasDerivAt (-X) t

/-- The `AdExp_add` result for the LatticeProd19 paper model. -/
theorem AdExp_add (X : 𝔸) (t : ℝ) (Z W : 𝔸) :
    AdExp X t (Z + W) = AdExp X t Z + AdExp X t W := by
  unfold AdExp
  noncomm_ring

/-- The algebraic core of Proposition 1, Eq. (40), p.6. -/
theorem AdExp_deriv_formula (X : 𝔸) (t : ℝ) (Y Y' : 𝔸) :
    (X * expm X t * Y + expm X t * Y') * expm (-X) t
        + expm X t * Y * (-X * expm (-X) t)
      = AdExp X t (ad X Y + Y') := by
  have hU : X * expm X t = expm X t * X := (Commute.refl X).smul_right (t : ℂ) |>.exp_right |>.eq
  have hU2 : ∀ Z : 𝔸, X * (expm X t * Z) = expm X t * (X * Z) := fun Z => by
    rw [← mul_assoc, hU, mul_assoc]
  have hexp : (X * expm X t * Y + expm X t * Y') * expm (-X) t
        + expm X t * Y * (-X * expm (-X) t)
      = X * expm X t * Y * expm (-X) t + expm X t * Y' * expm (-X) t
        - expm X t * Y * (X * expm (-X) t) := by
    rw [neg_mul]
    noncomm_ring
  have hexpR : AdExp X t (ad X Y + Y')
      = expm X t * X * Y * expm (-X) t - expm X t * Y * X * expm (-X) t
        + expm X t * Y' * expm (-X) t := by
    unfold AdExp ad
    noncomm_ring
  rw [hexp, hexpR]
  simp only [mul_assoc]
  rw [hU2]
  abel

/-- Prop. 1 (p.6, Eq. (40)): the differentiation rule for the adjoint representation. -/
theorem AdExp_hasDerivAt (X : 𝔸) (Y : ℝ → 𝔸) (Y' : 𝔸) (t : ℝ)
    (hY : HasDerivAt Y Y' t) :
    HasDerivAt (fun s : ℝ => AdExp X s (Y s))
      (AdExp X t (ad X (Y t)) + AdExp X t Y') t := by
  have hU := expm_hasDerivAt X t
  have hV := expm_neg_hasDerivAt X t
  have h1 : HasDerivAt (fun s => expm X s * Y s) (X * expm X t * Y t + expm X t * Y') t :=
    hU.mul hY
  have h2 : HasDerivAt (fun s => expm X s * Y s * expm (-X) s)
      ((X * expm X t * Y t + expm X t * Y') * expm (-X) t
        + (expm X t * Y t) * (-X * expm (-X) t)) t :=
    h1.mul hV
  have h3 : AdExp X t (ad X (Y t)) + AdExp X t Y' = AdExp X t (ad X (Y t) + Y') :=
    (AdExp_add X t (ad X (Y t)) Y').symm
  rw [h3, ← AdExp_deriv_formula X t (Y t) Y']
  simpa [AdExp] using h2

end Generic

/-! ## Matrix model -/

/-- `d`-dimensional complex operators. -/
abbrev Op (d : ℕ) : Type := Matrix (Fin d) (Fin d) ℂ

/-- `Op d` as a real normed vector space, by restricting scalars from `ℂ`.  This is
needed to state real differentiability (`ContDiff ℝ`, `deriv`, `iteratedDeriv`) of
operator-valued functions of a real time parameter. -/
noncomputable instance instNormedSpaceRealOp (d : ℕ) : NormedSpace ℝ (Op d) :=
  NormedSpace.restrictScalars ℝ ℂ (Op d)

/-- Ideal evolution `E(t) = e^{-itH}` (paper Eq. (10), p.3). -/
def idealEvolution {d : ℕ} (H : Op d) (t : ℝ) : Op d :=
  expm ((-Complex.I) • H) t

/-- A single stage `e^{-itbB} e^{-itaA}` (paper Definition 1, Eq. (8), p.3). -/
def stage {d : ℕ} (A B : Op d) (a b : ℝ) (t : ℝ) : Op d :=
  expm ((-Complex.I) • B) (b * t) * expm ((-Complex.I) • A) (a * t)

/-- Canonical product formula with real coefficients `a, b : Fin s → ℝ`
(paper Definition 1, Eq. (8), p.3).  The index `j : Fin s` encodes the paper's
stage `j+1`; the list is reversed so that the product is `S_s ⋯ S_1`, exactly
as in the paper's Eq. (8). -/
def canonicalProduct {d s : ℕ} (A B : Op d) (a b : Fin s → ℝ) (t : ℝ) : Op d :=
  (List.ofFn (fun j : Fin s => stage A B (a j) (b j) t)).reverse.prod

/-- Ideal evolution for a sum Hamiltonian `H = A + B`. -/
def idealSum {d : ℕ} (A B : Op d) (t : ℝ) : Op d := idealEvolution (A + B) t

end Qatlib.Papers.LatticeProd19.MainResults.SourceModel
