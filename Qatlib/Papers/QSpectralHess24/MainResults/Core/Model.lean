/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Permutation

set_option backward.isDefEq.respectTransparency false

/-!
# QSpectralHess24 — shared paper-layer model

Paper: Yuxin Zhang, Changpeng Shao, *Quantum spectral method for gradient and
Hessian estimation*, arXiv:2407.03833v2 (fixed version, 5 May 2026).

This file fixes the shared vocabulary used by all claim modules of
`Qatlib.Papers.QSpectralHess24.MainResults`:

* the **costed query-algorithm certificate** used to state the "there is a quantum
  algorithm … with probability at least `1 - ρ` using `O(…)` queries" claims of the
  paper, grounded on the established fixed-space query model
  (`Qatlib.Concepts.QueryComplexity.DegreeMethod.FixedSpaceQueryUpperBound`);
* the **sampling grids** `G_n^d` (Definition 2.26) and `S_q` (Equation (4.2));
* the **polydisc** and `maps ℝ^d into ℝ` predicates for analytic functions
  (Definitions 2.19–2.22);
* the **matrix max-norm**, sparsity and symmetric/`S_q`-entry predicates;
* the **finite-difference coefficients** and the second-difference form
  `f_(2m)` of Definition 2.16 and the directional/partial derivatives of
  Definition 2.15;
* the **diagonal phase oracle** on a finite computational register.

The algorithmic certificates are deliberately *not* free-floating existence
statements: `HasEstimationAlgorithm` bundles one fixed unitary fixed-gate circuit,
one fixed normalized start state and one fixed decoder that succeed on **every**
instance of the promise family, with the probability taken over the measurement
in the computational basis. This is the shape of the paper's algorithmic claims
and cannot be discharged by setting the query count to zero.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QSpectralHess24.MainResults.Core

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Costed query-algorithm certificates -/

/-- **Estimation certificate.** One fixed unitary fixed-gate circuit `C`, one fixed
normalized start state `ψ₀` and one fixed decoder `decode : I → Answer` such that, for
every instance `i` of the promise family, measuring `Run (O i) C ψ₀` in the
computational basis lands in a state decoding to an `ε`-approximation of `target i`
with probability at least `1 - ρ`, and `C` makes at most `k` oracle queries.

`O` is the oracle family (Definition 2.1 binary oracle or Definition 2.4 phase oracle);
`dist` is the error metric (ℓ∞ for vectors, matrix max-norm for matrices). -/
noncomputable def HasEstimationAlgorithm {I Inst Answer : Type} [Fintype I]
    [DecidableEq I] (O : Inst → Matrix I I ℂ) (target : Inst → Answer)
    (dist : Answer → Answer → ℝ) (ε rho : ℝ) (k : ℕ) : Prop := by
  classical
  exact
    0 ≤ rho ∧ rho < 1 ∧ (∀ i, O i ∈ Matrix.unitaryGroup I ℂ) ∧
      ∃ (decode : I → Answer) (C : Circuit I) (ψ₀ : QState I),
        IsUnitaryCircuit C ∧ Normalized ψ₀ ∧ QueryCount C ≤ k ∧
          ∀ i, 1 - rho ≤
            MeasureProb (Run (O i) C ψ₀)
              (Finset.univ.filter fun s => dist (decode s) (target i) ≤ ε)

/-- **Asymptotic estimation bound.** There is a positive constant `C` and a concrete
query budget `k ≤ C * budget` for which the estimation certificate holds. This is the
formal counterpart of the `O(budget)` query bounds in the paper. -/
noncomputable def EstimationQueryBound {I Inst Answer : Type} [Fintype I]
    [DecidableEq I] (O : Inst → Matrix I I ℂ) (target : Inst → Answer)
    (dist : Answer → Answer → ℝ) (ε rho budget : ℝ) : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 < C ∧ (k : ℝ) ≤ C * budget ∧
    HasEstimationAlgorithm O target dist ε rho k

/-- **Asymptotic query lower bound.** Any fixed unitary fixed-gate circuit with any
decoder and any normalized start state that succeeds with probability at least
`1 - delta` on every instance must use at least `C * budget` queries, for some
positive constant `C`. This is the formal counterpart of the `Ω(budget)` lower
bounds (Propositions 6.2 and 6.6). -/
noncomputable def QueryLowerBound {I Inst Answer : Type} [Fintype I] [DecidableEq I]
    (O : Inst → Matrix I I ℂ) (target : Inst → Answer) (dist : Answer → Answer → ℝ)
    (ε delta budget : ℝ) : Prop := by
  classical
  exact
    ∃ (k : ℕ) (C : ℝ), 0 < C ∧ C * budget ≤ (k : ℝ) ∧
      ∀ (decode : I → Answer) (C' : Circuit I) (ψ₀ : QState I),
        IsUnitaryCircuit C' → Normalized ψ₀ →
          (∀ i, 1 - delta ≤
            MeasureProb (Run (O i) C' ψ₀)
              (Finset.univ.filter fun s => dist (decode s) (target i) ≤ ε)) →
          k ≤ QueryCount C'

/-- The diagonal (phase-oracle) matrix `|x⟩ ↦ e^{i φ(x)} |x⟩` on the computational
basis; all diagonal entries have modulus one, so this is a unitary (the unitarity
conjunct is part of `HasEstimationAlgorithm`). -/
noncomputable def phaseOracle {ι : Type} [Fintype ι] [DecidableEq ι] (φ : ι → ℝ) :
    Matrix ι ι ℂ :=
  Matrix.diagonal fun i => Complex.exp (Complex.I * (φ i : ℂ))

/-! ## Grids (Definition 2.26 and Equation (4.2)) -/

/-- The one-dimensional grid value `k/2^n + 1/2^{n+1}` of Definition 2.26, indexed by
`Fin (2^n)` so that `k` runs over the `2^n` grid positions. -/
noncomputable def gridVal (n : ℕ) (k : Fin (2 ^ n)) : ℝ :=
  ((k : ℕ) : ℝ) / ((2 ^ n : ℕ) : ℝ) - 1 / 2 + 1 / ((2 ^ (n + 1) : ℕ) : ℝ)

/-- The index type of the grid `G_n^d`. -/
abbrev gridIndex (d n : ℕ) := Fin d → Fin (2 ^ n)

/-- The grid `G_n^d` of Definition 2.26, as a point of `ℝ^d`. -/
noncomputable def gridPoint {d n : ℕ} (k : gridIndex d n) : Fin d → ℝ :=
  fun i => gridVal n (k i)

/-- The modular grid value `k/q` of Equation (4.2) (`S_q`). -/
noncomputable def sqVal (q : ℕ) (k : Fin q) : ℝ :=
  ((k : ℕ) : ℝ) / ((q : ℕ) : ℝ)

/-- The index type of the grid `S_q^d`. -/
abbrev sqIndex (d q : ℕ) := Fin d → Fin q

/-- The grid `S_q^d` of Equation (4.2), as a point of `ℝ^d`. -/
noncomputable def sqPoint {d q : ℕ} (k : sqIndex d q) : Fin d → ℝ :=
  fun i => sqVal q (k i)

/-! ## Norms, sparsity, symmetric and `S_q`-entry predicates -/

/-- The matrix max-norm `‖A‖_max = max_{i,j} |A_{ij}|` (Section 2 notation). -/
noncomputable def maxNorm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ⨆ i, ⨆ j, |A i j|

/-- The ℓ∞ distance used for gradient estimates. -/
noncomputable def linfDist {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  ⨆ i, |x i - y i|

/-- The matrix max-norm distance used for Hessian estimates. -/
noncomputable def matMaxDist {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  maxNorm (A - B)

/-- Number of nonzero entries of a matrix. -/
noncomputable def nnz {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun p : Fin d × Fin d => A p.1 p.2 ≠ 0).card

/-- `s`-sparse in the sense of Section 4.2: at most `s` nonzero entries in each row
(and, since the matrices are symmetric, in each column too). -/
def IsSparse {d : ℕ} (s : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) : Prop := by
  classical
  exact ∀ i, (Finset.univ.filter fun j : Fin d => A i j ≠ 0).card ≤ s

/-- Symmetry of a real matrix. -/
def IsSymmetric {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : Prop := Aᵀ = A

/-- The matrix has all entries in `S_q = {k/q : k ∈ Z_q}` (Equation (4.2)). -/
def HasSQEntries {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (q : ℕ) : Prop :=
  ∀ i j, ∃ k : Fin q, A i j = sqVal q k

/-- The `(j,k)` elementary `(0,1)`-matrix `E_{jk}` of Lemma 6.5. -/
noncomputable def elementaryMatrix (d : ℕ) (j k : Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  fun a b => if a = j ∧ b = k then 1 else 0

/-! ## Polydiscs and real-analytic functions (Definitions 2.19–2.22) -/

/-- The closed polydisc `D̄(0, r)`. -/
def closedPolydisc {d : ℕ} (r : Fin d → ℝ) : Set (Fin d → ℂ) :=
  {z | ∀ i, ‖z i‖ ≤ r i}

/-- The open polydisc `D(0, r)`. -/
def openPolydisc {d : ℕ} (r : Fin d → ℝ) : Set (Fin d → ℂ) :=
  {z | ∀ i, ‖z i‖ < r i}

/-- An analytic `f : ℂ^d → ℂ` maps `ℝ^d` into `ℝ`. -/
def MapsRealToReal {d : ℕ} (f : (Fin d → ℂ) → ℂ) : Prop :=
  ∀ x : Fin d → ℝ, (f fun i => (x i : ℂ)).im = 0

/-- The `n`-th directional derivative `∂_r^n f(τ x)` of Definition 2.15, evaluated at
`τ`, where the direction is `x` itself (the paper's choice `r = x/‖x‖` up to the
normalisation factor, which is absorbed into the derivative in Lemmas A.3–A.4). -/
noncomputable def directionalDeriv {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (n : ℕ) (τ : ℝ) : ℝ :=
  iteratedDeriv n (fun s : ℝ => f fun i => s * x i) τ

/-- The multi-index partial derivative `∂^α f(0)` of Section 2, evaluated along the
coordinate directions listed in `α`. -/
noncomputable def partialDeriv {d : ℕ} (f : (Fin d → ℝ) → ℝ) (α : List (Fin d)) : ℝ :=
  iteratedFDeriv ℝ α.length f (0 : Fin d → ℝ) (fun s => Pi.single (α.get s) (1 : ℝ))

/-- The gradient directionality `∇f(0) · x` for an analytic `f : ℂ^d → ℂ` and a real
point `x ∈ ℝ^d` (Section 2 / Theorem 3.1). -/
noncomputable def gradDot {d : ℕ} (f : (Fin d → ℂ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  ∑ i, (fderiv ℂ f (0 : Fin d → ℂ)) (Pi.single i (1 : ℂ)) * (x i : ℂ)

/-- The Hessian matrix `H_f(0)` of a real function, using the twice-iterated Fréchet
derivative (Theorem 3.6 / Theorem 4.2 notation). -/
noncomputable def hessian {d : ℕ} (f : (Fin d → ℝ) → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => (fderiv ℝ (fun x => (fderiv ℝ f x) (Pi.single j (1 : ℝ))) 0)
    (Pi.single i (1 : ℝ))

/-- The quadratic-form Hessian `x^T H x` of a matrix `H`. -/
noncomputable def quadForm {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * H i j * x j

/-! ## Spectral filter (Theorem 3.1) -/

/-- The root of unity `ω = e^{-2πi/N}` of Theorem 3.1. -/
noncomputable def omega (N : ℕ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) / (N : ℂ))

/-- The spectral filter `F(x) = (1/(Nδ)) Σ_{k=0}^{N-1} ω^{-k} f(δ ω^k x)` of
Theorem 3.1. -/
noncomputable def spectralFilter {d : ℕ} (N : ℕ) (δ : ℝ)
    (f : (Fin d → ℂ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  (1 / ((N : ℂ) * (δ : ℂ))) *
    ∑ k ∈ Finset.range N,
      (omega N)⁻¹ ^ k * f (fun i => (δ : ℂ) * (omega N) ^ k * (x i : ℂ))

/-! ## Finite-difference coefficients (Definition 2.16) -/

/-- The alternating sign `(-1)^{t-1}` for an integer index `t` (Definition 2.16). -/
def altSign (t : ℤ) : ℝ := if Even (t - 1) then 1 else -1

/-- The finite-difference coefficient
`a_t^{(2m)} = (-1)^{t-1} · 2/t^2 · m! m! / ((m+t)! (m-t)!)` for `t ≠ 0`
(Definition 2.16). -/
noncomputable def centralDiffCoeffRaw (m : ℕ) (t : ℤ) : ℝ :=
  altSign t * (2 / (t : ℝ) ^ 2) *
    (((Nat.factorial m : ℝ) ^ 2) /
      ((Nat.factorial (Int.toNat ((m : ℤ) + t)) : ℝ) *
        (Nat.factorial (Int.toNat ((m : ℤ) - t)) : ℝ)))

/-- The finite-difference coefficients `a_t^{(2m)}` of Definition 2.16, with `a_0`
chosen so that the coefficients sum to zero. -/
noncomputable def centralDiffCoeff (m : ℕ) (t : ℤ) : ℝ :=
  if t = 0 then
    -∑ u ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
      (if u = 0 then 0 else centralDiffCoeffRaw m u)
  else centralDiffCoeffRaw m t

/-- The degree-`2m` central-difference approximation `f_(2m)(x)` of Definition 2.16. -/
noncomputable def finiteDiffSecond {d : ℕ} (m : ℕ) (f : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  ∑ t ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), centralDiffCoeff m t * f (fun i => (t : ℝ) * x i)

end Qatlib.Papers.QSpectralHess24.MainResults.Core
