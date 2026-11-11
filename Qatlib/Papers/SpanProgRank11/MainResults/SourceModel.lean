/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SpanProgRank11 — source model

Belovs, *Span-program-based quantum algorithm for the rank problem*,
arXiv:1103.0842v1 (4 March 2011, the only arXiv version).

This module fixes the paper's objects that the seven active claims talk about:

* real `n × m` matrices, their singular values and the quadratic mean `c_r(A)`
  of the reciprocals of the `r` largest singular values (Sec. 1, p. 2 and
  Sec. 4.2, p. 9; `c(A) = c_n(A)` in Eq. (1));
* the Gaussian matrix ensemble `G(n, n)` (Sec. 3.2, p. 6) as the `n`-fold
  product of standard-normal row/column measures;
* high-level span programs, their positive/negative witnesses and the witness
  size `wsize` (Sec. 4.1, p. 8);
* the cost profile of a matrix-loading subroutine (Sec. 5, p. 10–16), with the
  paper's geometric-mean bookkeeping of positive and negative witness sizes.

The measure-theoretic and span-program objects are definitions only. The
theorem layer of each claim lives in its own file.
-/

open Matrix MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpanProgRank11.MainResults

/-- The paper works over real matrices (Sec. 2.2: "we find real span programs
more convenient").  An `n × m` matrix is `Matrix (Fin n) (Fin m) ℝ`. -/
abbrev SourceMatrix (n m : ℕ) : Type := Matrix (Fin n) (Fin m) ℝ

/-! ## Singular values and the complexity measure `c_r(A)` -/

/-- The `i`-th singular value of `A` in descending order.  The paper is
1-indexed (`σ_1 ≥ σ_2 ≥ ⋯`); Mathlib's `LinearMap.singularValues` is 0-indexed,
antitone and nonnegative, so `sourceSingularValue A i` is the paper's `σ_{i+1}`. -/
def sourceSingularValue {n m : ℕ} (A : SourceMatrix n m) (i : ℕ) : ℝ :=
  (Matrix.toEuclideanLin A).singularValues i

/-- Singular values are nonnegative (paper Sec. 2.1, p. 3). -/
theorem sourceSingularValue_nonneg {n m : ℕ} (A : SourceMatrix n m) (i : ℕ) :
    0 ≤ sourceSingularValue A i :=
  LinearMap.singularValues_nonneg _ i

/-- Singular values are arranged in nonincreasing order (paper Sec. 2.1:
`σ_1 ≥ σ_2 ≥ ⋯`). -/
theorem sourceSingularValue_antitone {n m : ℕ} (A : SourceMatrix n m) :
    Antitone (sourceSingularValue A) :=
  LinearMap.singularValues_antitone _

/-- The paper's `c_r(A)^2 = (1/r) Σ_{i=1}^r 1/σ_i^2` (Sec. 1, p. 2).  It is
`⊤` when a singular value in the first `r` vanishes, matching the paper's
statement that `c_r` is infinitely large for matrices of rank `< r`. -/
def sourceCrSq {n m : ℕ} (A : SourceMatrix n m) (r : ℕ) : ℝ≥0∞ :=
  (r : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range r,
    ((ENNReal.ofReal (sourceSingularValue A i))⁻¹) ^ 2

/-- The paper's complexity measure `c_r(A)` (Sec. 1, p. 2, and Sec. 4.2, p. 9). -/
def sourceCr {n m : ℕ} (A : SourceMatrix n m) (r : ℕ) : ℝ≥0∞ :=
  ENNReal.rpow (sourceCrSq A r) (1 / 2 : ℝ)

/-- The paper's `c(A)` is `c_n(A)` for `n × n` matrices, Eq. (1). -/
abbrev sourceC {n : ℕ} (A : SourceMatrix n n) : ℝ≥0∞ := sourceCr A n

/-! ## The Gaussian matrix ensemble `G(n, n)` -/

/-- The law of the Gaussian matrix `G(n, n)` (Sec. 3.2, p. 6): all `n²` entries
are independent standard normal variables.  This is the `n`-fold product of the
standard normal measure on the rows, i.e. the product over the `n × n` index
set; `Matrix (Fin n) (Fin n) ℝ` is definitionally `Fin n → Fin n → ℝ`. -/
def gaussianMatrixMeasure (n : ℕ) : Measure (Fin n → Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1))

/-! ## High-level span programs (Sec. 4.1, p. 8) -/

/-- A high-level span program `𝒫` for `n × m` matrices (Sec. 4.1, p. 8): a
non-zero target vector `t ∈ ℝ^n`, a subspace `F` of free input vectors, and a
set `D` of valid input matrices.  The program asks whether the affine subspace
`t + F` intersects the column span of `A`. -/
structure HighLevelSpanProgram (n m : ℕ) where
  /-- The non-zero target vector `t`. -/
  target : Fin n → ℝ
  /-- The target is non-zero (`t ≠ 0`). -/
  target_ne_zero : target ≠ 0
  /-- The subspace `F` of free input vectors. -/
  freeSpace : Submodule ℝ (Fin n → ℝ)
  /-- The set `D` of valid input matrices. -/
  domain : Set (SourceMatrix n m)

/-- Positive inputs: `t + F` intersects `span(A)` (Sec. 4.1, p. 8). -/
def IsPositiveInput {n m : ℕ} (P : HighLevelSpanProgram n m)
    (A : SourceMatrix n m) : Prop :=
  ∃ w : Fin m → ℝ, A *ᵥ w - P.target ∈ P.freeSpace

/-- Negative inputs: `t + F` does not intersect `span(A)`. -/
def IsNegativeInput {n m : ℕ} (P : HighLevelSpanProgram n m)
    (A : SourceMatrix n m) : Prop :=
  ¬ IsPositiveInput P A

/-- Positive witnesses of `A` in `P`: vectors `w` with `A w ∈ t + F`
(Sec. 4.1, p. 8). -/
def positiveWitnessSet {n m : ℕ} (P : HighLevelSpanProgram n m)
    (A : SourceMatrix n m) : Set (Fin m → ℝ) :=
  {w | A *ᵥ w - P.target ∈ P.freeSpace}

/-- Negative witnesses of `A` in `P`: vectors `w'` with `⟨w', t⟩ = 1`, `w'` in
the orthogonal complement of the column span of `A`, and `w'` orthogonal to the
free space `F` (Sec. 4.1, p. 8). -/
def negativeWitnessSet {n m : ℕ} (P : HighLevelSpanProgram n m)
    (A : SourceMatrix n m) : Set (Fin n → ℝ) :=
  {w' | (∑ i, w' i * P.target i) = 1 ∧
        (∀ j, ∑ i, A i j * w' i = 0) ∧
        (∀ f ∈ P.freeSpace, ∑ i, w' i * f i = 0)}

/-- Size of a positive witness: `‖w‖²` (Sec. 4.1, p. 8). -/
def posWitnessSize {m : ℕ} (w : Fin m → ℝ) : ℝ :=
  ∑ j, (w j) ^ 2

/-- Size of a negative witness: `‖Aᵀ w'‖² = Σ_j (Σ_i A_{ij} w'_i)²`
(Sec. 4.1, p. 8). -/
def negWitnessSize {n m : ℕ} (A : SourceMatrix n m) (w' : Fin n → ℝ) : ℝ :=
  ∑ j, (∑ i, A i j * w' i) ^ 2

/-- The witness size `wsize(P, A)`: minimal size among positive witnesses for a
positive input, and among negative witnesses for a negative input
(Sec. 4.1, p. 8).  Valued in `ℝ≥0∞` so that an absent witness set has value
`⊤`. -/
def witnessSize {n m : ℕ} (P : HighLevelSpanProgram n m)
    (A : SourceMatrix n m) : ℝ≥0∞ := by
  classical
  exact if IsPositiveInput P A then
    ⨅ w : {w : Fin m → ℝ // w ∈ positiveWitnessSet P A},
      ENNReal.ofReal (posWitnessSize w.1)
  else
    ⨅ w : {w : Fin n → ℝ // w ∈ negativeWitnessSet P A},
      ENNReal.ofReal (negWitnessSize A w.1)

/-- Maximal positive-input witness size `wsize₁(P)` (Sec. 4.1, p. 8). -/
def wsize1 {n m : ℕ} (P : HighLevelSpanProgram n m) : ℝ≥0∞ :=
  ⨆ A : {A : SourceMatrix n m // A ∈ P.domain ∧ IsPositiveInput P A},
    witnessSize P A.1

/-- Maximal negative-input witness size `wsize₀(P)` (Sec. 4.1, p. 8). -/
def wsize0 {n m : ℕ} (P : HighLevelSpanProgram n m) : ℝ≥0∞ :=
  ⨆ A : {A : SourceMatrix n m // A ∈ P.domain ∧ IsNegativeInput P A},
    witnessSize P A.1

/-- The witness size `wsize(P) = √(wsize₀(P) · wsize₁(P))` (Sec. 4.1, p. 8). -/
def wsize {n m : ℕ} (P : HighLevelSpanProgram n m) : ℝ≥0∞ :=
  ENNReal.rpow (wsize1 P * wsize0 P) (1 / 2 : ℝ)

/-! ## Cost profiles of matrix-loading subroutines (Sec. 5, p. 10–16)

The loading subroutines of Sec. 5 have two independent cost contributions, one
from the positive witnesses and one from the negative witnesses.  The resulting
witness size is the geometric mean `√(pos · neg)` (Sec. 4.1, p. 8 / Eq. (2.8)
of Reichardt).  We record the bookkeeping in the real-valued profile below; the
per-subroutine factors (`n`, `m`, `k log n`, …) are the outputs of Subroutines
12 and 14.
-/

/-- The geometric mean `√(w1 · w0)` of a positive and a negative witness size;
this is the paper's `wsize` (Sec. 4.1). -/
def geometricWitnessSize (w1 w0 : ℝ) : ℝ := Real.sqrt (w1 * w0)

/-- A cost profile: a positive-witness-size bound and a negative-witness-size
bound produced by composing matrix-loading subroutines. -/
structure WitnessCostProfile where
  /-- Bound on the positive witness size `wsize₁`. -/
  pos : ℝ
  /-- Bound on the negative witness size `wsize₀`. -/
  neg : ℝ
  /-- The positive bound is nonnegative. -/
  pos_nonneg : 0 ≤ pos
  /-- The negative bound is nonnegative. -/
  neg_nonneg : 0 ≤ neg

/-- The witness size encoded by a cost profile, `√(pos · neg)`. -/
def WitnessCostProfile.total (b : WitnessCostProfile) : ℝ :=
  geometricWitnessSize b.pos b.neg

/-- Scaling both witness-size bounds by nonnegative factors scales the total
witness size by the geometric mean of the factors.  This is the algebraic core
of every matrix-loading subroutine: the composed positive witness size is the
source one scaled by the positive cost, the negative one by the negative cost,
and the total is their geometric mean. -/
theorem geometricWitnessSize_scale (a b w1 w0 : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : 0 ≤ w1) (h0 : 0 ≤ w0) :
    geometricWitnessSize (a * w1) (b * w0)
      = Real.sqrt a * Real.sqrt b * geometricWitnessSize w1 w0 := by
  unfold geometricWitnessSize
  rw [show a * w1 * (b * w0) = (a * b) * (w1 * w0) by ring]
  rw [Real.sqrt_mul (mul_nonneg ha hb) (w1 * w0),
      Real.sqrt_mul ha b, Real.sqrt_mul h1 w0]

/-- The source `wsize(P)` as a real number from the two component bounds. -/
def sourceWitnessSizeFromBounds (w1 w0 : ℝ) : ℝ := geometricWitnessSize w1 w0

end Qatlib.Papers.SpanProgRank11.MainResults
