/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Paper layer for *A New Quantum Algorithm for Linear Systems beyond the Condition Number*
(QLSBeyondCond25), fixed source version arXiv:2510.05588v3.

This file covers the condition-number claims of the paper:

* c012, Proposition 5.7 (page 30): the condition number of the weighted Boolean Macaulay matrix
  `AD` is `Ω(2^{h/2})`, where `h` is the Hamming weight of the Boolean solution, hence
  exponentially large when `h = Θ(n)`;
* c013, Theorem C.1 (Appendix C, page 47): for `‖A‖ = 1`, `‖b‖ ≤ 1`, `‖y‖ = 1` and
  `H = [A, -b]`, `(1/√2)·κ(A) ≤ κ(H) ≤ √2·κ(A)`.

`conditionNumber` is defined from `LinearMap.singularValues` (the paper's
`κ = σmax/σmin⁺`, Appendix C, page 47).  Mathlib has no condition-number API and no
Cauchy-interlacing lemma for singular values, so the two paper statements are recorded as
placeholders and documented; the quantitative cores of their proofs are proved:

* `proposition57_lower_bound` — the arithmetic core of Step 4 of the proof of Proposition 5.7:
  `dmax·c2/(dmin·c1) ≤ σmax/σmin` with `c1 ≤ P`, `1 ≤ c2`;
* `theoremC1_conditioning_core` — the arithmetic core of the proof of Theorem C.1:
  `1/√2 ≤ ... ` from `σmax(H) ≤ √2`, `1 ≤ σmax(H)`, `σmin(A) ≤ σmin(H)`.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Matrix
open scoped BigOperators InnerProductSpace
open Module

namespace Qatlib.Papers.QLSBeyondCond25.MainResults.Section5

/-! ## Condition number -/

/-- The condition number `κ(T) = σmax(T)/σmin⁺(T)` of a linear map between finite-dimensional
real inner product spaces: the largest singular value divided by the smallest positive singular
value (paper page 47, Appendix C; the singular values are indexed by `ℕ` in Mathlib and vanish
from `rank(T)` on, so the smallest positive one sits at index `rank(T) - 1`). -/
noncomputable def conditionNumber {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (T : E →ₗ[ℝ] F) : ℝ :=
  T.singularValues 0 / T.singularValues (finrank ℝ T.range - 1)

/-! ## c012 — Proposition 5.7 -/

/-- Arithmetic core of Step 4 of the proof of Proposition 5.7 (page 30): the condition number
`σmax/σmin` is bounded below by `dmax·c2/(dmin·c1)`, where `dmax, dmin` are the largest and
smallest diagonal weights of `D`, `c2` is the norm of the "large" column `AD e_jlarge = dmax·A e_j`
(so `c2 ≥ 1` after rescaling `‖A‖ = poly(n)`), and `c1 ≤ P` bounds the norm of the "small" column
`AD e_jsmall = dmin·A e_j` by a polynomial `P`.  Hence `κ(AD) ≥ dmax/(dmin·P)`. -/
theorem proposition57_lower_bound {smax smin dmax dmin c1 c2 P : ℝ}
    (hsmin : 0 < smin) (hdmax : 0 < dmax) (hdmin : 0 < dmin) (hc1 : 0 < c1)
    (hP : 0 < P) (hc1P : c1 ≤ P) (hc2 : 1 ≤ c2)
    (hsmax : dmax * c2 ≤ smax) (hsminle : smin ≤ dmin * c1) :
    dmax / (dmin * P) ≤ smax / smin := by
  have hc2' : dmax ≤ dmax * c2 := by nlinarith
  have hsmax0 : 0 ≤ smax := le_trans (mul_pos hdmax (by linarith)).le hsmax
  have hdet1 : (0 : ℝ) < dmin * c1 := by positivity
  have hkey : dmax * c2 * smin ≤ smax * (dmin * c1) := by
    have h1 : dmax * c2 * smin ≤ smax * smin := by nlinarith
    have h2 : smax * smin ≤ smax * (dmin * c1) := mul_le_mul_of_nonneg_left hsminle hsmax0
    linarith
  have h1 : dmax * c2 / (dmin * c1) ≤ smax / smin := by
    rw [div_le_div_iff₀ hdet1 hsmin]
    exact hkey
  have h2 : dmax / (dmin * P) ≤ dmax * c2 / (dmin * c1) := by
    have ha : dmax / (dmin * P) ≤ dmax / (dmin * c1) :=
      div_le_div_of_nonneg_left hdmax.le hdet1 (by nlinarith)
    have hb : dmax / (dmin * c1) ≤ dmax * c2 / (dmin * c1) :=
      div_le_div_of_nonneg_right hc2' (by positivity)
    linarith
  exact le_trans h2 h1

/-- Proposition 5.7 (page 30), *Exponential Condition Number of the Weighted Boolean Macaulay
Matrix*: let `A` be the matrix of the Boolean Macaulay system and `d` the diagonal weighting of
Definition 5.4 (entries `√C(h,k)` for monomials of degree `k ≤ h` and `1` for higher degree, so
`dmax = √C(h,⌊h/2⌋)` and `dmin = 1`), and assume the column norms of `A` are bounded by a
polynomial `P` and contain a column of norm at least `1`.  Then the condition number of `AD` is
`Ω(2^{h/2})`.

Gap: version arXiv:2510.05588v3, Proposition 5.7, page 30.  The paper's four steps: (1) all column
norms of `A` are `poly(n)`; (2) `dmax = max_{k≤h} √C(h,k) = Θ(2^{h/2})` and `dmin = 1`;
(3) the two test unit vectors `e_jsmall`, `e_jlarge` give `‖AD e_jsmall‖ = poly(n)` and
`‖AD e_jlarge‖ = dmax·poly(n)`; (4) `κ(AD) = σmax/σmin ≥ ‖AD e_jlarge‖/‖AD e_jsmall‖ = Ω(2^{h/2})`.
The arithmetic of Step 4 is proved in `proposition57_lower_bound`.  Missing formal ingredients:
(3) requires the singular-value inequality `σmax(T) ≥ ‖T v‖` for unit `v` and `σmin(T) ≤ ‖T v‖` (the
latter for any unit `v`), and the binomial asymptotics `√C(h,⌊h/2⌋) = Θ(2^{h/2})` (central binomial
coefficient, page 30).  Candidate reusable dependencies: `LinearMap.singularValues`,
`LinearMap.singularValues_antitone`, `LinearMap.singularValues_nonneg`,
`Nat.choose` estimates from `Mathlib.Analysis.SpecialFunctions.Stirling` (not yet used in the
library; `QuantumAlgorithm.Concepts.QlsReadoutSpec.PseudoInverse` covers the least-squares side).
Suggested next tactic: prove `σmax(T) ≥ ‖T v‖` from the spectral theorem for `T.adjoint ∘ₗ T`, then
instantiate `proposition57_lower_bound` with `c2 = ‖A e_jlarge‖`. -/
def proposition57_statement
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℝ) (h : ℕ)
    (hh : 0 < h) (hdpos : ∀ i, 0 < d i)
    (hdmax : ∃ i, d i = Real.sqrt ((Nat.choose h (h / 2) : ℝ)))
    (hdmin : ∃ i, d i = 1)
    (hcol : ∃ P : ℝ, 0 < P ∧ ∀ i, ‖A.toEuclideanLin (EuclideanSpace.single i (1 : ℝ))‖ ≤ P)
    (hcolpos : ∃ i, 1 ≤ ‖A.toEuclideanLin (EuclideanSpace.single i (1 : ℝ))‖) : Prop :=
  ∃ c : ℝ, 0 < c ∧ c * (2 : ℝ) ^ ((h : ℝ) / 2) ≤
    conditionNumber ((A * Matrix.diagonal d).toEuclideanLin)

/-! ## c013 — Theorem C.1 -/

/-- The augmented matrix `H = [A, -b]` of Appendix C (page 47): `A` with the extra last column
`-b`. -/
def augmentedMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Matrix (Fin m) (Fin (n + 1)) ℝ :=
  fun i j => if hj : (j : ℕ) < n then A i ⟨j, hj⟩ else -b i

/-- Arithmetic core of the proof of Theorem C.1 (page 47): with `σmax(A) = 1`, the two sandwich
inequalities `σmax(H) ≤ √2`, `1 ≤ σmax(H)`, `σmin(A) ≤ σmin(H)` and `σmin(H) ≤ √2·σmin(A)` give
`(1/√2)·κ(A) ≤ κ(H) ≤ √2·κ(A)`.

The lower bound uses `σmin(H) ≤ √2·σmin(A)` together with `σmax(H) ≥ 1`; the upper bound uses
`σmax(H) ≤ √2` and `σmin(A) ≤ σmin(H)`.  (`σmin(A) ≤ σmin(H)` is Cauchy interlacing, and
`σmin(H) ≤ √2·σmin(A)` follows because `Hᵀ H = Aᵀ A + b bᵀ` has no eigenvalue smaller than
`σmin(A)²`, together with `σmax(A) = 1`.) -/
theorem theoremC1_conditioning_core {κA κH sAmax sAmin sHmax sHmin : ℝ}
    (hsAmin : 0 < sAmin) (hsHmin : 0 < sHmin)
    (hAmax : sAmax = 1) (hkA : κA = sAmax / sAmin) (hkH : κH = sHmax / sHmin)
    (hHmax : sHmax ≤ Real.sqrt 2) (hHmax1 : 1 ≤ sHmax)
    (hmin : sAmin ≤ sHmin) (hmin2 : sHmin ≤ Real.sqrt 2 * sAmin) :
    (1 / Real.sqrt 2) * κA ≤ κH ∧ κH ≤ Real.sqrt 2 * κA := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2ge : 1 ≤ Real.sqrt 2 := by nlinarith
  constructor
  · rw [hkH, hkA, hAmax]
    have hden : sHmin ≤ Real.sqrt 2 * sAmin := hmin2
    have hstep : 1 / (Real.sqrt 2 * sAmin) ≤ 1 / sHmin :=
      one_div_le_one_div_of_le hsHmin hden
    have hstep2 : 1 / sHmin ≤ sHmax / sHmin :=
      div_le_div_of_nonneg_right hHmax1 hsHmin.le
    have heq : (1 / Real.sqrt 2) * (1 / sAmin) = 1 / (Real.sqrt 2 * sAmin) := by
      rw [div_mul_div_comm]
      norm_num
    rw [heq]
    exact le_trans hstep hstep2
  · rw [hkH, hkA, hAmax]
    have h1 : sHmax / sHmin ≤ Real.sqrt 2 / sHmin :=
      div_le_div_of_nonneg_right hHmax hsHmin.le
    have h2' : Real.sqrt 2 / sHmin ≤ Real.sqrt 2 / sAmin :=
      div_le_div_of_nonneg_left h2.le hsAmin hmin
    have heq : Real.sqrt 2 * (1 / sAmin) = Real.sqrt 2 / sAmin := by rw [mul_one_div]
    rw [heq]
    exact le_trans h1 h2'

/-- Theorem C.1 (Appendix C, page 47): let `‖A‖ = 1`, `‖b‖ ≤ 1`, `‖y‖ = 1`, `A y = b`, and
`H = [A, -b]`; then `(1/√2)·κ(A) ≤ κ(H) ≤ √2·κ(A)`.

Gap: version arXiv:2510.05588v3, Theorem C.1, page 47.  The paper's proof: (1) `σmax(H) ≤ √2` via
Weyl's inequality applied to `H Hᵀ = A Aᵀ + b bᵀ`; (2) `σmin⁺(H) ≥ σmin⁺(A)` by Cauchy interlacing
for `Hᵀ H = [[AᵀA, -Aᵀb], [-bᵀA, bᵀb]]` (using `b ∈ col(A)` so `rank H = rank A`); (3) combine
with `σmax(A) = 1`.  Missing formal ingredients: Weyl's inequality for singular values of a sum, the
Cauchy interlacing theorem for Hermitian matrices, and the identification of the nonzero spectrum
of `Hᵀ H` with that of `Aᵀ A` under `b ∈ col(A)`.  The arithmetic core (3) is proved in
`theoremC1_conditioning_core`.  Candidate reusable dependencies:
`LinearMap.singularValues`, `LinearMap.singularValues_antitone`,
`LinearMap.sq_singularValues_fin` (singular values as square roots of eigenvalues of
`T.adjoint ∘ₗ T`), `LinearMap.range_adjoint_comp_self`; Mathlib's `Matrix.IsHermitian` spectral
theorem provides the eigenbasis but not interlacing.  Suggested next tactic: prove
`σmax(T) = ‖T‖` for the upper bound and use `Submodule.finrank_mono` together with the
min-max characterisation of singular values for the lower bound. -/
def theoremC1_statement
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (y : EuclideanSpace ℝ (Fin n))
    (hAnorm : ∀ x, ‖A.toEuclideanLin x‖ ≤ ‖x‖)
    (hAnorm1 : ∃ v, ‖v‖ = 1 ∧ ‖A.toEuclideanLin v‖ = 1)
    (hb : ‖b‖ ≤ 1) (hy : ‖y‖ = 1)
    (hsol : A *ᵥ (WithLp.ofLp y) = WithLp.ofLp b) : Prop :=
    (1 / Real.sqrt 2) * conditionNumber A.toEuclideanLin
        ≤ conditionNumber (augmentedMatrix A (WithLp.ofLp b)).toEuclideanLin
      ∧ conditionNumber (augmentedMatrix A (WithLp.ofLp b)).toEuclideanLin
        ≤ Real.sqrt 2 * conditionNumber A.toEuclideanLin

end Qatlib.Papers.QLSBeyondCond25.MainResults.Section5
