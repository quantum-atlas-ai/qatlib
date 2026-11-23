/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# The actual two-dimensional invariant blocks of gap amplification

Fixed source: arXiv:1110.2494v3, Proof 2, Eqs. (5)-(8), printed pp. 4-5.
The lazy compression uses `gamma = 1-lambda/L`, keeping the endpoint
`lambda=L` away from the spurious `gamma=-1` of the undoubled register.
The matrices below are actual reflection, projection, and Hamiltonian blocks.
-/

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Papers.SpectralGap11.MainResults.InvariantBlocks

open Matrix

noncomputable section

/-- The reflection block in the span of a compressed eigenstate and its
orthogonal residual. -/
def blockU (gamma sine : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![gamma, sine; sine, -gamma]

/-- Projection onto the original eigenstate in its invariant block. -/
def blockP : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- The difference of the conjugated and original projections, Eq. (4). -/
def blockG (gamma sine : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  blockU gamma sine * blockP * blockU gamma sine - blockP

/-- The penalized amplification block `L G + delta (1-P)`, Eq. (7). -/
def blockH (L delta gamma sine : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  L • blockG gamma sine + delta • (1 - blockP)

/-- A normalized reflection block is an involution. -/
theorem blockU_sq (gamma sine : ℝ) (h : gamma ^ 2 + sine ^ 2 = 1) :
    blockU gamma sine * blockU gamma sine = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockU, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith

/-- The product construction gives exactly the source matrix in Eq. (6). -/
theorem blockG_eq (gamma sine : ℝ) (h : gamma ^ 2 + sine ^ 2 = 1) :
    blockG gamma sine = !![-sine ^ 2, sine * gamma;
      sine * gamma, sine ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockG, blockP, blockU] <;> nlinarith

/-- Adding the actual penalty produces Eq. (8). -/
theorem blockH_eq (L delta gamma sine : ℝ) (h : gamma ^ 2 + sine ^ 2 = 1) :
    blockH L delta gamma sine = !![-L * sine ^ 2, L * sine * gamma;
      L * sine * gamma, delta + L * sine ^ 2] := by
  rw [blockH, blockG_eq gamma sine h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockP] <;> ring

/-- Cosine of the lazy, doubled-register compression angle. -/
def lazyCos (lambda L : ℝ) : ℝ := 1 - lambda / L

/-- Nonnegative sine of the lazy compression angle. -/
noncomputable def lazySin (lambda L : ℝ) : ℝ :=
  Real.sqrt (1 - lazyCos lambda L ^ 2)

/-- Every input eigenvalue in `[0,L]` yields a compression cosine in `[0,1]`. -/
theorem lazyCos_bounds (lambda L : ℝ) (hL : 0 < L)
    (hlambda : 0 ≤ lambda) (hmax : lambda ≤ L) :
    0 ≤ lazyCos lambda L ∧ lazyCos lambda L ≤ 1 := by
  have hlo : 0 ≤ lambda / L := div_nonneg hlambda hL.le
  have hhi : lambda / L ≤ 1 := (div_le_one hL).2 hmax
  dsimp [lazyCos]
  constructor <;> linarith

/-- The lazy block has the exact trigonometric normalization used in Eq. (6). -/
theorem lazy_norm (lambda L : ℝ) (hL : 0 < L)
    (hlambda : 0 ≤ lambda) (hmax : lambda ≤ L) :
    lazyCos lambda L ^ 2 + lazySin lambda L ^ 2 = 1 := by
  obtain ⟨hlo, hhi⟩ := lazyCos_bounds lambda L hL hlambda hmax
  have hrad : 0 ≤ 1 - lazyCos lambda L ^ 2 := by nlinarith
  rw [lazySin, Real.sq_sqrt hrad]
  ring

/-- The squared sine is bounded below by the input eigenvalue divided by `L`.
This estimate remains positive at `lambda=L`. -/
theorem lazy_gain (lambda L : ℝ) (hL : 0 < L)
    (hlambda : 0 ≤ lambda) (hmax : lambda ≤ L) :
    lambda / L ≤ lazySin lambda L ^ 2 := by
  have hnorm := lazy_norm lambda L hL hlambda hmax
  have hlo : 0 ≤ lambda / L := div_nonneg hlambda hL.le
  have hhi : lambda / L ≤ 1 := (div_le_one hL).2 hmax
  dsimp [lazyCos] at hnorm
  nlinarith [mul_nonneg hlo (sub_nonneg.2 hhi)]

/-- The characteristic polynomial of the actual penalty block. -/
theorem blockH_det (L delta gamma sine z : ℝ)
    (h : gamma ^ 2 + sine ^ 2 = 1) :
    (blockH L delta gamma sine - z • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det =
      z ^ 2 - delta * z - L * (L + delta) * sine ^ 2 := by
  rw [blockH_eq L delta gamma sine h, Matrix.det_fin_two]
  simp
  have hmul := congrArg (fun x : ℝ => L ^ 2 * sine ^ 2 * x) h
  nlinarith only [hmul]

/-- Discriminant of the actual penalized two-dimensional block. -/
def blockDisc (L delta sine : ℝ) : ℝ :=
  delta ^ 2 + 4 * L * (L + delta) * sine ^ 2

/-- The larger root of the characteristic polynomial of the penalty block. -/
def rootPlus (L delta sine : ℝ) : ℝ :=
  (delta + Real.sqrt (blockDisc L delta sine)) / 2

/-- The smaller root of the characteristic polynomial of the penalty block. -/
def rootMinus (L delta sine : ℝ) : ℝ :=
  (delta - Real.sqrt (blockDisc L delta sine)) / 2

/-- The actual discriminant is nonnegative for nonnegative scale and penalty. -/
theorem blockDisc_nonneg (L delta sine : ℝ) (hL : 0 ≤ L) (hd : 0 ≤ delta) :
    0 ≤ blockDisc L delta sine := by
  dsimp [blockDisc]
  positivity

/-- Both explicit roots are characteristic values of the actual block. -/
theorem roots_characteristic (L delta gamma sine : ℝ)
    (hL : 0 ≤ L) (hd : 0 ≤ delta) (h : gamma ^ 2 + sine ^ 2 = 1) :
    (blockH L delta gamma sine - rootPlus L delta sine •
        (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 ∧
      (blockH L delta gamma sine - rootMinus L delta sine •
        (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 := by
  have hs := Real.sq_sqrt (blockDisc_nonneg L delta sine hL hd)
  rw [blockH_det L delta gamma sine _ h, blockH_det L delta gamma sine _ h]
  dsimp [rootPlus, rootMinus, blockDisc] at *
  constructor <;> nlinarith only [hs]

/-- A positive input eigenvalue gives a nonsingular amplification block,
so this block contributes no spurious zero eigenstate. -/
theorem positive_block_injective (lambda L delta : ℝ) (hL : 0 < L)
    (hlambda : 0 < lambda) (hmax : lambda ≤ L) (hd : 0 ≤ delta) :
    Function.Injective
      (blockH L delta (lazyCos lambda L) (lazySin lambda L)).mulVec := by
  have hg := lazy_gain lambda L hL hlambda.le hmax
  have hs : 0 < lazySin lambda L ^ 2 :=
    lt_of_lt_of_le (div_pos hlambda hL) hg
  have hdet : (blockH L delta (lazyCos lambda L) (lazySin lambda L)).det ≠ 0 := by
    have hpoly := blockH_det L delta (lazyCos lambda L) (lazySin lambda L) 0
      (lazy_norm lambda L hL hlambda.le hmax)
    simp only [zero_smul, sub_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
      zero_sub] at hpoly
    rw [hpoly]
    have : 0 < L * (L + delta) * lazySin lambda L ^ 2 := by positivity
    linarith
  exact Matrix.mulVec_injective_iff_isUnit.2
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))

/-- Every nonzero eigenvalue in a lazy block is separated from zero by at
least half the square-root scale, when the penalty uses a valid input-gap
lower bound. This is a gap around zero, including degenerate ground spaces. -/
theorem roots_gap (lambda L delta : ℝ) (hL : 0 < L)
    (hlambda : 0 ≤ lambda) (hmax : lambda ≤ L)
    (hd : 0 ≤ delta) (hsmall : delta ^ 2 ≤ lambda * L) :
    Real.sqrt (lambda * L) / 2 ≤
        |rootMinus L delta (lazySin lambda L)| ∧
      Real.sqrt (lambda * L) ≤ rootPlus L delta (lazySin lambda L) := by
  have hg := (div_le_iff₀ hL).1 (lazy_gain lambda L hL hlambda hmax)
  have hrad := blockDisc_nonneg L delta (lazySin lambda L) hL.le hd
  have hs := Real.sq_sqrt hrad
  have htarget := Real.sq_sqrt (mul_nonneg hlambda hL.le)
  have hsn := Real.sqrt_nonneg (blockDisc L delta (lazySin lambda L))
  have htn := Real.sqrt_nonneg (lambda * L)
  have hprod : 0 ≤ 4 * L * delta * lazySin lambda L ^ 2 := by positivity
  have hLg : lambda * L ≤ L ^ 2 * lazySin lambda L ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hg hL.le]
  have hdisc : 4 * (lambda * L) ≤ blockDisc L delta (lazySin lambda L) := by
    dsimp [blockDisc]
    nlinarith only [hLg, hprod, sq_nonneg delta]
  have htwice : 2 * Real.sqrt (lambda * L) ≤
      Real.sqrt (blockDisc L delta (lazySin lambda L)) := by
    nlinarith only [hs, htarget, hsn, htn, hdisc]
  have hdelta : delta ≤ Real.sqrt (lambda * L) := by
    nlinarith only [hsmall, htarget, hd, htn]
  have hm : rootMinus L delta (lazySin lambda L) ≤ 0 := by
    dsimp [rootMinus]
    linarith
  rw [abs_of_nonpos hm]
  dsimp [rootMinus, rootPlus]
  constructor <;> linarith

end

end Qatlib.Papers.SpectralGap11.MainResults.InvariantBlocks
