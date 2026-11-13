/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Module

/-!
# Block matrices for the adiabatic linear-system Hamiltonian

Defines the block-matrix Hamiltonians `H0`, `H1`, and `H` used in the linear-system construction
of [CostaEtAl2025]. Projection and reflection formulas connect their algebraic factorizations to
the selected block `selectBlock`.

The compressed expression `blockEncoding` is identified with a scalar multiple of `H`; the
scalar lies between `1 / sqrt 2` and one on the interpolation interval.

## Main statements

* `qGadget_compression`: Expresses `Qb` as the average of the identity and the reflection.
* `encodedCore_eq_H`: Identifies the selected block construction with the Hamiltonian.
* `blockEncoding_eq`: Gives the normalized Hamiltonian block.
* `prefactor_bounds`: Bounds the normalization factor on `[0, 1]`.

## References

* [Costa et al., 2025][CostaEtAl2025]
-/

set_option autoImplicit false

namespace Qatlib.Papers.AdiabaticQLS23.MainResults

open Matrix

noncomputable section

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The two-by-two block matrix with blocks `A`, `B`, `C`, and `D`, indexed using `Fin 2`. -/
def block2 {m n : Type*} [Fintype m] [Fintype n]
    (A B C D : Matrix m n ℂ) : Matrix (Fin 2 × m) (Fin 2 × n) ℂ :=
  fun i j => if i.1 = 0 then (if j.1 = 0 then A i.2 j.2 else B i.2 j.2)
             else (if j.1 = 0 then C i.2 j.2 else D i.2 j.2)

/-- Multiplies two two-by-two block matrices using the usual four block-product formulas. -/
theorem block2_mul {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (A B C D : Matrix m n ℂ) (A' B' C' D' : Matrix n p ℂ) :
    block2 A B C D * block2 A' B' C' D' =
      block2 (A * A' + B * C') (A * B' + B * D')
             (C * A' + D * C') (C * B' + D * D') := by
  ext i j
  rcases i with ⟨i, k⟩
  rcases j with ⟨j, l⟩
  fin_cases i <;> fin_cases j <;>
    simp [block2, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- The off-diagonal block matrix with `Q` in both off-diagonal positions. -/
def H0 (Q : Matrix N N ℂ) : Matrix (Fin 2 × N) (Fin 2 × N) ℂ := block2 0 Q Q 0

/-- The off-diagonal block matrix with upper block `A * Q` and lower block `Q * A`. -/
def H1 (A Q : Matrix N N ℂ) : Matrix (Fin 2 × N) (Fin 2 × N) ℂ :=
  block2 0 (A * Q) (Q * A) 0

/-- The interpolation `(1 - f) • H0 Q + f • H1 A Q`. -/
def H (f : ℝ) (A Q : Matrix N N ℂ) : Matrix (Fin 2 × N) (Fin 2 × N) ℂ :=
  (1 - f) • H0 Q + f • H1 A Q

/-- The block diagonal matrix with diagonal blocks the identity and `Q`. -/
def Qmat (Q : Matrix N N ℂ) : Matrix (Fin 2 × N) (Fin 2 × N) ℂ := block2 1 0 0 Q

/-- The block swap matrix with identity off-diagonal blocks. -/
def Smat : Matrix (Fin 2 × N) (Fin 2 × N) ℂ := block2 0 1 1 0

/-- The block diagonal matrix with `A` in both diagonal positions. -/
def DA (A : Matrix N N ℂ) : Matrix (Fin 2 × N) (Fin 2 × N) ℂ := block2 A 0 0 A

omit [DecidableEq N] in

/-- Expands the interpolating Hamiltonian into its two off-diagonal blocks. See [CostaEtAl2025]. -/
theorem H_eq (f : ℝ) (A Q : Matrix N N ℂ) :
    H f A Q = block2 0 ((1 - f) • Q + f • (A * Q))
      ((1 - f) • Q + f • (Q * A)) 0 := by
  ext i j
  rcases i with ⟨i, k⟩
  rcases j with ⟨j, l⟩
  fin_cases i <;> fin_cases j <;> simp [H, H0, H1, block2]

/-- Factors `H1 A Q` as `Qmat Q * Smat * DA A * Qmat Q`. See [CostaEtAl2025]. -/
theorem H1_eq (A Q : Matrix N N ℂ) :
    H1 A Q = Qmat Q * Smat * DA A * Qmat Q := by
  ext i j
  rcases i with ⟨i, k⟩
  rcases j with ⟨j, l⟩
  fin_cases i <;> fin_cases j <;>
    simp [H1, Qmat, Smat, DA, block2, block2_mul]

/-- Factors `H0 Q` as `Qmat Q * Smat * Qmat Q`. See [CostaEtAl2025]. -/
theorem H0_eq (Q : Matrix N N ℂ) :
    H0 Q = Qmat Q * Smat * Qmat Q := by
  ext i j
  rcases i with ⟨i, k⟩
  rcases j with ⟨j, l⟩
  fin_cases i <;> fin_cases j <;>
    simp [H0, Qmat, Smat, block2, block2_mul]

/-- The outer-product matrix with entries `b i * star (b j)`. -/
def rankOne (b : N → ℂ) : Matrix N N ℂ := Matrix.of fun i j => b i * star (b j)

/-- The matrix `1 - rankOne b`, which is the orthogonal complement projection when `b` is
normalized. -/
def Qb (b : N → ℂ) : Matrix N N ℂ := 1 - rankOne b

/-- The matrix `1 - 2 • rankOne b`, which is a reflection when `b` is normalized. -/
def reflection (b : N → ℂ) : Matrix N N ℂ := 1 - 2 • rankOne b

omit [DecidableEq N] in

/-- The outer-product matrix of a normalized vector is idempotent. -/
theorem rankOne_mul_self {b : N → ℂ} (hb : ∑ i, star (b i) * b i = 1) :
    rankOne b * rankOne b = rankOne b := by
  ext i j
  simp only [rankOne, Matrix.mul_apply, Matrix.of_apply]
  calc
    ∑ k, b i * star (b k) * (b k * star (b j))
        = b i * (∑ k, star (b k) * b k) * star (b j) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = b i * star (b j) := by rw [hb]; ring

/-- For normalized `b`, the complement matrix `Qb b` is idempotent. See [CostaEtAl2025]. -/
theorem Qb_mul_self {b : N → ℂ} (hb : ∑ i, star (b i) * b i = 1) :
    Qb b * Qb b = Qb b := by
  unfold Qb
  calc
    (1 - rankOne b) * (1 - rankOne b)
        = 1 - rankOne b - rankOne b + rankOne b * rankOne b := by noncomm_ring
    _ = 1 - rankOne b := by rw [rankOne_mul_self hb]; abel

omit [Fintype N] in

/-- The complement matrix `Qb b` is Hermitian for every vector `b`. See [CostaEtAl2025]. -/
theorem Qb_hermitian (b : N → ℂ) : (Qb b)ᴴ = Qb b := by
  unfold Qb rankOne
  ext i j
  simp [Matrix.conjTranspose_apply, star_sub, star_mul, Matrix.one_apply, eq_comm]

omit [Fintype N] in

/-- The average of the identity and `reflection b` equals `Qb b`. See [CostaEtAl2025]. -/
theorem qGadget_compression (b : N → ℂ) :
    (1 / 2 : ℂ) • (1 + reflection b) = Qb b := by
  unfold reflection Qb
  module

/-- The normalization `sqrt ((1 - f) ^ 2 + f ^ 2)` for the interpolation coefficients. -/
def rotNorm (f : ℝ) : ℝ := Real.sqrt ((1 - f) ^ 2 + f ^ 2)

/-- The two-dimensional matrix with rows `((1 - f) / rotNorm f, f / rotNorm f)` and `(f /
rotNorm f, -(1 - f) / rotNorm f)`. -/
def Rmat (f : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j =>
    if i = 0 then (if j = 0 then ((1 - f) / rotNorm f : ℝ) else (f / rotNorm f : ℝ))
    else (if j = 0 then (f / rotNorm f : ℝ) else (-(1 - f) / rotNorm f : ℝ))

/-- The two-dimensional Hadamard matrix with normalization `1 / Real.sqrt 2`. -/
def Hmat : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j =>
    if i = 0 then (if j = 0 then (1 / Real.sqrt 2 : ℝ) else (1 / Real.sqrt 2 : ℝ))
    else (if j = 0 then (1 / Real.sqrt 2 : ℝ) else (-(1 / Real.sqrt 2) : ℝ))

/-- The selected matrix block `(1 - f) • 1 + f • A`. -/
def selectBlock (f : ℝ) (A : Matrix N N ℂ) : Matrix N N ℂ :=
  (1 - f) • (1 : Matrix N N ℂ) + f • A

omit [Fintype N] in

/-- When `rotNorm f` is nonzero, the specified rotation and Hadamard coefficients produce
`selectBlock f A` scaled by `1 / (Real.sqrt 2 * rotNorm f)`. See [CostaEtAl2025]. -/
theorem select_rotation_eq (f : ℝ) (A : Matrix N N ℂ) (hn : rotNorm f ≠ 0) :
    (Rmat f 0 0 * Hmat 1 0) • (1 : Matrix N N ℂ) + (Rmat f 0 1 * Hmat 1 0) • A
      = (1 / (Real.sqrt 2 * rotNorm f)) • selectBlock f A := by
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    norm_num [Complex.ext_iff, Real.sqrt_eq_zero']
  have hnC : (rotNorm f : ℂ) ≠ 0 := by exact_mod_cast hn
  simp [Rmat, Hmat, selectBlock]
  field_simp [hnC, h2]
  module

/-- The off-diagonal block matrix formed from `selectBlock f A * Q` and `Q * selectBlock f A`. -/
def encodedCore (f : ℝ) (A Q : Matrix N N ℂ) : Matrix (Fin 2 × N) (Fin 2 × N) ℂ :=
  block2 0 (selectBlock f A * Q) (Q * selectBlock f A) 0

/-- The selected off-diagonal core equals the interpolating Hamiltonian `H f A Q`. See
[CostaEtAl2025]. -/
theorem encodedCore_eq_H (f : ℝ) (A Q : Matrix N N ℂ) :
    encodedCore f A Q = H f A Q := by
  rw [H_eq]
  ext i j
  rcases i with ⟨i, k⟩
  rcases j with ⟨j, l⟩
  fin_cases i <;> fin_cases j <;>
    simp [encodedCore, block2, selectBlock, Matrix.add_mul, Matrix.mul_add]

/-- The encoded core scaled by `1 / (Real.sqrt 2 * rotNorm f)`. -/
def blockEncoding (f : ℝ) (A Q : Matrix N N ℂ) : Matrix (Fin 2 × N) (Fin 2 × N) ℂ :=
  (1 / (Real.sqrt 2 * rotNorm f)) • encodedCore f A Q

/-- The normalized block expression equals `H f A Q` scaled by `1 / (Real.sqrt 2 * rotNorm f)`.
See [CostaEtAl2025]. -/
theorem blockEncoding_eq (f : ℝ) (A Q : Matrix N N ℂ) :
    blockEncoding f A Q
      = (1 / (Real.sqrt 2 * rotNorm f)) • H f A Q := by
  unfold blockEncoding
  rw [encodedCore_eq_H]

/-- For `f ∈ [0, 1]`, the Hamiltonian normalization factor lies between `1 / Real.sqrt 2` and
one. See [CostaEtAl2025]. -/
theorem prefactor_bounds {f : ℝ} (h0 : 0 ≤ f) (h1 : f ≤ 1) :
    1 / Real.sqrt 2 ≤ 1 / (Real.sqrt 2 * rotNorm f) ∧
    1 / (Real.sqrt 2 * rotNorm f) ≤ 1 := by
  have h2 : 0 < Real.sqrt 2 := by positivity
  have hpoly_lo : (1 / 2 : ℝ) ≤ (1 - f) ^ 2 + f ^ 2 := by
    nlinarith [sq_nonneg (f - 1 / 2)]
  have hpoly_hi : (1 - f) ^ 2 + f ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  have hnpos : 0 < rotNorm f := by
    unfold rotNorm
    apply Real.sqrt_pos.mpr
    nlinarith [sq_nonneg (1 - f), sq_nonneg f]
  have hn_lo : 1 / Real.sqrt 2 ≤ rotNorm f := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt 2)]
    apply Real.sqrt_le_sqrt
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
    exact hpoly_lo
  have hn_hi : rotNorm f ≤ 1 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1)]
    exact Real.sqrt_le_sqrt (by simpa using hpoly_hi)
  have hsqrt_inv : (Real.sqrt 2) * (1 / Real.sqrt 2) = 1 := by field_simp
  constructor
  · rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2)
      (by positivity : (0 : ℝ) < Real.sqrt 2 * rotNorm f)]
    nlinarith [hn_hi, h2, hnpos]
  · rw [div_le_one (by positivity : (0 : ℝ) < Real.sqrt 2 * rotNorm f)]
    nlinarith [hn_lo, h2, hnpos, hsqrt_inv]

end

end Qatlib.Papers.AdiabaticQLS23.MainResults
