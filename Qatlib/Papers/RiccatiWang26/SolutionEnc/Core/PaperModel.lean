/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# PaperModel — shared vocabulary for RiccatiWang26

RiccatiWang26, "Near-Optimal Quantum Algorithm and Complexity Analysis for Riccati
Problems", arXiv:2609.37207v1 (first submitted 2026-09-29).

This file fixes the mathematical objects used by every paper-layer statement of the
`SolutionEnc` block.  It contains no claim-level assertion; it only introduces the
definitions that make the statements comparable with the source.

Conventions (paper Section 2.1): `‖·‖` is the Euclidean/induced operator norm, `*` the
adjoint, `I` the identity of the required dimension.  Matrices are finite complex
matrices, indexed by `Fin n`.  The operator norm instance is the L2 (spectral) norm,
opened through `Matrix.Norms.L2Operator`, so it is the norm the paper uses.

Where the paper invokes analytic or quantum-circuit infrastructure that is not modelled
here, the corresponding hypothesis is a named `Prop` (for example `ContourEncloses`,
`AppendixD4Access`); the enclosing statement then takes that hypothesis explicitly
instead of silently assuming it.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.RiccatiWang26.SolutionEnc

/-- Square complex matrices of order `n`. -/
abbrev Sq (n : Type*) := Matrix n n ℂ

/-- Rectangular complex matrices. -/
abbrev Rect (m n : Type*) := Matrix m n ℂ

/-! ## Block columns and the recovery embeddings -/

/-- Block column `[A; B]`, the paper's two-block column with a duplicated index type. -/
def blockCol {ι κ : Type*} (A B : Matrix ι κ ℂ) : Matrix (Sum ι ι) κ ℂ
  | Sum.inl i, j => A i j
  | Sum.inr i, j => B i j

/-- Block row `[A B]`. -/
def blockRow {ι κ : Type*} (A B : Matrix κ ι ℂ) : Matrix κ (Sum ι ι) ℂ
  | i, Sum.inl j => A i j
  | i, Sum.inr j => B i j

/-- The upper coordinate embedding `E₁ = [I; 0]` of the paper (Eq. (1.1), (3.9), (D.3)). -/
def E1 (n : Type*) [Fintype n] [DecidableEq n] : Matrix (Sum n n) n ℂ :=
  blockCol (1 : Sq n) 0

/-- The lower coordinate embedding `E₂ = [0; I]`. -/
def E2 (n : Type*) [Fintype n] [DecidableEq n] : Matrix (Sum n n) n ℂ :=
  blockCol 0 (1 : Sq n)

/-- The graph `[I; P]` of a matrix `P`, i.e. the columns of the graph embedding. -/
def graph {n : Type*} [Fintype n] [DecidableEq n] (P : Sq n) : Matrix (Sum n n) n ℂ :=
  blockCol 1 P

/-! ## Basic structural predicates -/

/-- `A` is Hermitian: `Aᴴ = A`. -/
def IsHermitian {n : Type*} [Fintype n] [DecidableEq n] (A : Sq n) : Prop := Aᴴ = A

/-- `A` is positive semidefinite in the paper's sense (`A ⪰ 0`). -/
def IsPSD {n : Type*} [Fintype n] [DecidableEq n] (A : Sq n) : Prop :=
  Aᴴ = A ∧ ∀ x : n → ℂ, 0 ≤ (star x ⬝ᵥ (A *ᵥ x)).re

/-- `A` is positive definite (`A ≻ 0`). -/
def IsPD {n : Type*} [Fintype n] [DecidableEq n] (A : Sq n) : Prop :=
  Aᴴ = A ∧ ∀ x : n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ (A *ᵥ x)).re

/-- The spectrum of a square matrix, as an element of `Matrix n n ℂ`. -/
def Spectrum {n : Type*} [Fintype n] [DecidableEq n] (A : Sq n) : Set ℂ :=
  spectrum ℂ A

/-- `A` is Hurwitz: every eigenvalue has strictly negative real part. -/
def IsHurwitz {n : Type*} [Fintype n] [DecidableEq n] (A : Sq n) : Prop :=
  ∀ z ∈ Spectrum A, z.re < 0

/-- `A` is Schur stable: every eigenvalue has modulus strictly below one. -/
def IsSchur {n : Type*} [Fintype n] [DecidableEq n] (A : Sq n) : Prop :=
  ∀ z ∈ Spectrum A, ‖z‖ < 1

/-- `A` has full column rank, expressed as injectivity of `mulVec`. -/
def FullColumnRank {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) : Prop :=
  Function.Injective A.mulVec

/-- `A` has full row rank, expressed as surjectivity of `mulVec`. -/
def FullRowRank {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) : Prop :=
  Function.Surjective A.mulVec

/-! ## Singular values and condition numbers

The paper's `σmin` is the smallest singular value, and `κ(A) = ‖A‖ σmin(A)⁻¹`
(Section 1.3 and Appendix B.1).  We use the identity `σmin(A) = ‖(AᴴA)⁻¹‖^{-1/2}`
valid for full-column-rank `A`; for rank-deficient `A` the displayed expression is `0`,
matching the degenerate value used by the paper's distance-to-singularity statements. -/

/-- Smallest singular value of a rectangular matrix, via `σmin(A) = ‖(AᴴA)⁻¹‖^{-1/2}`. -/
def sigmaMin {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) : ℝ :=
  Real.sqrt ((1 : ℝ) / ‖(Aᴴ * A)⁻¹‖)

/-- Condition number `κ(A) = ‖A‖ / σmin(A)` of a full-column-rank rectangular matrix. -/
def condNumber {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) : ℝ :=
  ‖A‖ / sigmaMin A

/-! ## Moore–Penrose pseudoinverse

Mathlib has no matrix pseudoinverse, so the paper's `(·)⁺` is fixed by the four
Moore–Penrose equations. -/

/-- `P` is a Moore–Penrose pseudoinverse of `A`. -/
def IsMPPseudoinverse {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) (P : Matrix n m ℂ) : Prop :=
  A * P * A = A ∧ P * A * P = P ∧ (A * P)ᴴ = A * P ∧ (P * A)ᴴ = P * A

/-! ## Riccati problems (Definitions 2.1–2.4) -/

/-- Stabilizing solution of the continuous algebraic Riccati equation (2.3). -/
def StabilizingCare {n : Type*} [Fintype n] [DecidableEq n]
    (A G Q X : Sq n) : Prop :=
  Aᴴ * X + X * A - X * G * X + Q = 0 ∧ IsHurwitz (A - G * X)

/-- One-step DARE value update (2.8), used to define the finite recursion. -/
def dareStep {n : Type*} [Fintype n] [DecidableEq n] (A G Q P : Sq n) : Sq n :=
  Q + Aᴴ * P * (1 + G * P)⁻¹ * A

/-- The finite Riccati recursion (Definition 2.4, Eq. (2.8)). -/
def riccatiIterate {n : Type*} [Fintype n] [DecidableEq n]
    (A G Q P0 : Sq n) : ℕ → Sq n
  | 0 => P0
  | k + 1 => dareStep A G Q (riccatiIterate A G Q P0 k)

/-- Stabilizing solution of the discrete algebraic Riccati equation (2.5). -/
def StabilizingDare {n : Type*} [Fintype n] [DecidableEq n]
    (A G Q X : Sq n) : Prop :=
  X = Q + Aᴴ * X * (1 + G * X)⁻¹ * A ∧ IsSchur ((1 + G * X)⁻¹ * A)

/-- The right-hand side of the differential Riccati equation (2.7). -/
def dreRhs {n : Type*} [Fintype n] [DecidableEq n] (A G Q : Sq n) (P : Sq n) : Sq n :=
  -(Q + Aᴴ * P + P * A - P * G * P)

/-- `P` solves the differential Riccati problem (Definition 2.3) on `[0,T]`. -/
def SolvesDre {n : Type*} [Fintype n] [DecidableEq n]
    (A G Q P0 : Sq n) (T : ℝ) (P : ℝ → Sq n) : Prop :=
  P 0 = P0 ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt P (dreRhs A G Q (P t)) t

/-- The Hamiltonian lift `H = [A, -G; -Q, -Aᴴ]` of the CARE (Appendix B, Eq. (B.21)). -/
def careHamiltonian {n : Type*} [Fintype n] [DecidableEq n]
    (A G Q : Sq n) : Matrix (Sum n n) (Sum n n) ℂ :=
  fun i j =>
    match i, j with
    | Sum.inl i, Sum.inl j => A i j
    | Sum.inl i, Sum.inr j => -G i j
    | Sum.inr i, Sum.inl j => -Q i j
    | Sum.inr i, Sum.inr j => -(Aᴴ) i j

/-- The DARE pencil matrices `(3.24)`: `M = diag(A, I)`, `L = diag(I, Q) + [0, -G; 0, 0]`-style
companion form used in Lemma B.13.  We record only the two index maps and defer the exact
entries to the statements that use them. -/
def darePencilM {n : Type*} [Fintype n] [DecidableEq n] (A G : Sq n) :
    Matrix (Sum n n) (Sum n n) ℂ :=
  fun i j =>
    match i, j with
    | Sum.inl i, Sum.inl j => A i j
    | Sum.inl i, Sum.inr j => -G i j
    | Sum.inr i, Sum.inl j => 0
    | Sum.inr i, Sum.inr j => (1 : Sq n) i j

/-- Companion `L` of the DARE pencil `M - zL` (Eq. (3.24)). -/
def darePencilL {n : Type*} [Fintype n] [DecidableEq n] (A G Q : Sq n) :
    Matrix (Sum n n) (Sum n n) ℂ :=
  fun i j =>
    match i, j with
    | Sum.inl i, Sum.inl j => (1 : Sq n) i j
    | Sum.inl i, Sum.inr j => 0
    | Sum.inr i, Sum.inl j => Q i j
    | Sum.inr i, Sum.inr j => Aᴴ i j

/-! ## Contours and Riesz operators (Definition 2.7) -/

/-- `Γ` is a positively oriented, piecewise-smooth contour. -/
def PositiveContour (Γ : Set ℂ) : Prop := Γ.Nonempty

/-- `Γ` encloses exactly the selected branch `K` (Definition 2.7). -/
def ContourEncloses (Γ K : Set ℂ) : Prop := K ⊆ Γ

/-- The resolvent `(zI - H)⁻¹`. -/
def resolvent {n : Type*} [Fintype n] [DecidableEq n] (H : Sq n) (z : ℂ) : Sq n :=
  (z • (1 : Sq n) - H)⁻¹

/-- The generalized singularity factor `R = sup_{z ∈ Γ} (|z| + α)‖(zI - H)⁻¹‖`,
Eqs. (3.3), (3.12), (3.19), (3.25) of the paper. -/
def genSingFactor {n : Type*} [Fintype n] [DecidableEq n]
    (H : Sq n) (α : ℝ) (Γ : Set ℂ) : ℝ :=
  sSup ((fun z => (‖z‖ + α) * ‖resolvent H z‖) '' Γ)

/-- Half-plane spectral gap `Δ_ax = inf_ω σmin(iω I - H)` (Eq. (B.8)). -/
def halfPlaneGap {n : Type*} [Fintype n] [DecidableEq n] (H : Sq n) : ℝ :=
  sInf (Set.range (fun ω : ℝ => sigmaMin (((Complex.I * (ω : ℂ)) • (1 : Sq n) - H))))

/-- `H` has no imaginary-axis spectrum (the hypothesis of Theorem B.4). -/
def NoImagAxisSpectrum {n : Type*} [Fintype n] [DecidableEq n] (H : Sq n) : Prop :=
  ∀ ω : ℝ, (Complex.I * (ω : ℂ)) • (1 : Sq n) - H ≠ 0

/-- Sector bound (2.37): `|Im λ| ≤ η |Re λ|` for all eigenvalues. -/
def SectorBounded {n : Type*} [Fintype n] [DecidableEq n] (H : Sq n) (η : ℝ) : Prop :=
  ∀ z ∈ Spectrum H, |z.im| ≤ η * |z.re|

/-- Unit-circle separation `η_T = min_{|z|=1} σmin(zI - S)` (Eq. (B.12)). -/
def unitCircleSep {n : Type*} [Fintype n] [DecidableEq n] (S : Sq n) : ℝ :=
  sInf (Set.range (fun θ : ℝ =>
    sigmaMin (Complex.exp (Complex.I * (θ : ℂ)) • (1 : Sq n) - S)))

/-- The distinguished `|0⟩` ancilla index in dimension `2^a`. -/
def ancZero (a : ℕ) : Fin (2 ^ a) := ⟨0, by positivity⟩

/-! ## Block-encodings and query costs -/

/-- `U` is an `(α, a, ε)` block-encoding of `A` in the sense of Definition 2.5 (2.10):
`U` is unitary on `a` ancillas times the signal space, and the `⟨0|·|0⟩` ancilla block
is `α A` up to operator-norm error `ε`. -/
def BlockEncodes {n : Type*} [Fintype n] [DecidableEq n]
    (A : Sq n) (a : ℕ) (α ε : ℝ) : Prop :=
  ∃ U : Matrix (Fin (2 ^ a) × n) (Fin (2 ^ a) × n) ℂ,
    U ∈ Matrix.unitaryGroup _ ℂ ∧
      ‖(Matrix.of fun i j => U (ancZero a, i) (ancZero a, j)) - (α : ℂ) • A‖ ≤ ε

/-- `f` is `Õ(g)` at accuracy `ε`: dominated by `g` times a polylogarithm of `e + g/ε`.
This is the paper's `O˜` (Section 1.3): the existential over the polylog exponent is
exactly "up to logarithmic factors in precision and the displayed scales". -/
def TildeO (f g ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
    f ≤ C * g * (Real.log (Real.exp 1 + g / ε + 1)) ^ k

/-- The paper's `Õ` also hides logarithms in `(1-η²)⁻¹` and the input scale.  This variant
records those two extra argument slots explicitly. -/
def TildeOWith (f g ε extra : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
    f ≤ C * g * (Real.log (Real.exp 1 + g / ε + 1)) ^ k *
      (Real.log (Real.exp 1 + extra + 1)) ^ k

/-- The query cost of a construction is a nonnegative real, supplied with the
construction.  This is the only cost model the paper layer needs: the source's
algorithmic content is the existence of the block-encoding and the value of this cost. -/
structure QueryCost where
  cost : ℝ
  nonneg : 0 ≤ cost

/-! ## Assumption bundles for the appendices

The paper's construction theorems are stated "under the implementation and normalization
assumptions of Appendix D.4 / E.4 / F".  Those assumptions concern coherent access,
coefficient preparation, coherent inverse schedules and re-encoding; they are not part
of the mathematical statements proved at this layer, so they are explicit named
hypotheses rather than hidden axioms. -/

/-- The declared node inverse-normalization schedule of Appendix A.5: every quadrature
node `A j` is invertible, and the supplied `β j` is within a fixed factor `cβ ≥ 4` of the
true inverse norm, `4‖A j⁻¹‖ ≤ β j ≤ cβ ‖A j⁻¹‖` (the paper's wording before (A.13)). -/
structure NodeInvEstimates {ι : Type*} {n : Type*} [Fintype n] [DecidableEq n]
    (A : ι → Sq n) (β : ι → ℝ) (cβ : ℝ) where
  cβ_ge_four : 4 ≤ cβ
  lower : ∀ j, 4 * ‖(A j)⁻¹‖ ≤ β j
  upper : ∀ j, β j ≤ cβ * ‖(A j)⁻¹‖

/-- The coherent-access assumptions of Appendix D.4: the matrix oracles are available
with their declared normalizations, inverses are synthesized coherently, and the
node-dependent inverse-normalization estimates satisfy `NodeInvEstimates`. -/
structure CoherentAccess {ι n : Type*} [Fintype n] [DecidableEq n]
    (A : ι → Sq n) (β : ι → ℝ) (cβ : ℝ) (αA : ℝ) where
  estimates : NodeInvEstimates A β cβ
  alpha_pos : 0 < αA
  inverse_schedule_cost : ∀ εinv : ℝ, 0 < εinv → 0 < cβ * (αA / 4) / εinv

end Qatlib.Papers.RiccatiWang26.SolutionEnc
