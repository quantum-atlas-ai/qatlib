/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCoreDefs
import Qatlib.Concepts.QuantumGibbs.FormAlgebra.ParentWeight

set_option backward.isDefEq.respectTransparency false

/-!
# QuantumAlgorithmDev.Papers.NoncommGibbs23.MainResults.Model

Vocabulary layer for the paper-layer formalization of

*Chi-Fang Chen, Michael J. Kastoryano, András Gilyén,
"An efficient and exact noncommutative quantum Gibbs sampler",
arXiv:2311.09207v2 (14 Oct 2025), 45 pages.*

The paper works with finite-dimensional matrices `B(ℂ^D)`, super-operators acting on
them, a full-rank Gibbs reference state `ρ_β`, the modular conjugation
`Γ_ρ[·] = ρ^{1/2} (·) ρ^{1/2}`, and the Kubo–Martin–Schwinger (KMS) detailed-balance
condition of Definition II.1 (p. 7–8).  This file fixes a concrete matrix model for
that vocabulary.  It contains definitions only; the theorem statements live in the
sibling modules, one module per paper section.

Conventions used throughout:

* `Operator D = Matrix (Fin D) (Fin D) ℂ` (from the pinned Physlib/QuantumAlgorithm
  vocabulary).
* A square root of `ρ` is passed explicitly as a pair `(r, rInv)` with
  `r * rInv = 1`, `rInv * r = 1`, `r * r = ρ`.  This avoids committing to a
  particular continuous-functional-calculus normalisation in every statement; the
  frozen `CFC.sqrt` instance satisfies the same interface and is used in
  `ParentHamiltonian` for the Proposition I.1 bridge.
* The modular (Bohr-frequency) eigen-relation is written as
  `rInv * A * r = exp (β * ν / 2) • A`, i.e. `ρ^{1/2} A ρ^{-1/2} = exp(-βν/2) A`,
  matching the paper's `ρ_β ∝ exp(-βH)` convention (Section II.A, p. 7).
-/

set_option autoImplicit false

namespace Qatlib.Papers.NoncommGibbs23.MainResults

open Matrix
open scoped ComplexOrder MatrixOrder BigOperators

variable {D : ℕ}
variable {ι : Type*} [Fintype ι]

/-- Finite-dimensional complex matrices on `D` modes.  Definitionally equal to the
frozen `QuantumAlgorithm.Concepts.MbqcFlow.FlowDecision.Operator`; redeclared here
so that every paper-layer module sees the same abbreviation without extra `open`. -/
abbrev Operator (D : ℕ) := Matrix (Fin D) (Fin D) ℂ

/-! ## Super-operators and the Hilbert–Schmidt adjoint -/

/-- A super-operator on `D × D` matrices, kept unbundled: only pointwise equalities
are needed by the paper-layer statements (the frozen GKSL layer supplies the bundled
linear maps when a semigroup is required). -/
abbrev SuperOp (D : ℕ) := Operator D → Operator D

/-- Hilbert–Schmidt inner product `⟨X,Y⟩ = tr(X† Y)` on complex matrices. -/
noncomputable def hsPair (X Y : Operator D) : ℂ := Matrix.trace (Xᴴ * Y)

/-- `Tdag` is the Hilbert–Schmidt adjoint of `T` (the paper's `T†`, Definition II.1,
p. 7–8). -/
def IsHSAdjoint (T Tdag : SuperOp D) : Prop :=
  ∀ X Y : Operator D, hsPair (T X) Y = hsPair X (Tdag Y)

/-- The modular conjugation `Γ_ρ[X] = ρ^{1/2} X ρ^{1/2}` of Section II.B (p. 9),
represented by an explicit square-root pair. -/
noncomputable def gammaRho (r : Operator D) (X : Operator D) : Operator D :=
  r * X * r

/-- `ρ`-detailed balance (Definition II.1, p. 7–8) in the equivalent transition form
`T†[X] = ρ^{-1/2} T[ρ^{1/2} X ρ^{1/2}] ρ^{-1/2}`.  The pair `(r, rInv)` is an
explicit square root of `ρ`. -/
def IsRhoDetailedBalanced (ρ r rInv : Operator D)
    (T Tdag : SuperOp D) : Prop :=
  r * rInv = 1 ∧ rInv * r = 1 ∧ r * r = ρ ∧
    ∀ X : Operator D, Tdag X = rInv * T (gammaRho r X) * rInv

/-- `ρ`-detailed balance with unitary drift (Definition E.1, p. 41–42):
`L†[X] = ρ^{-1/2} L[ρ^{1/2}Xρ^{1/2}] ρ^{-1/2} + i[Q,X]`. -/
def IsRhoDetailedBalancedDrift (ρ r rInv Q : Operator D)
    (T Tdag : SuperOp D) : Prop :=
  r * rInv = 1 ∧ rInv * r = 1 ∧ r * r = ρ ∧
    ∀ X : Operator D,
      Tdag X = rInv * T (gammaRho r X) * rInv + Complex.I • (Q * X - X * Q)

/-- `(s,ρ)`-detailed balance (Definition E.2, p. 44):
`L†[X] = ρ^{s-1} L[ρ^{1-s} X ρ^{s}] ρ^{-s}`, with the four fractional powers passed
explicitly as `(left, leftInv, right, rightInv)`.  The product relations encode the
identities `ρ^{1-s}ρ^{s-1}=1`, `ρ^{-s}ρ^{s}=1` and `ρ^{1-s}ρ^{s}=ρ`. -/
def IsSDetailedBalanced (ρ left leftInv right rightInv : Operator D)
    (T Tdag : SuperOp D) : Prop :=
  left * leftInv = 1 ∧ leftInv * left = 1 ∧
  right * rightInv = 1 ∧ rightInv * right = 1 ∧
  left * right = ρ ∧
    ∀ X : Operator D, Tdag X = leftInv * T (left * X * right) * rightInv

/-! ## Bohr-frequency jump data and the transition super-operator -/

/-- A self-adjoint jump family with Bohr frequencies (Section II.A, p. 7 and
Definition II.1).  `star` encodes the adjoint pairing `A (star i) = (A i)†`,
`ν (star i) = -ν i`.  The modular eigen-relation
`rInv * A i * r = exp (β * ν i / 2) • A i` is not a field: it is a hypothesis of the
statements that need it, because `r` is supplied by the caller. -/
structure BohrJumpData (D : ℕ) (ι : Type*) where
  /-- Jump operators `A^a`. -/
  A : ι → Operator D
  /-- Bohr frequencies `ν`. -/
  ν : ι → ℝ
  /-- Involution pairing a jump operator with its adjoint. -/
  star : ι → ι
  /-- `star` is an involution. -/
  star_invol : Function.Involutive star
  /-- `A (star i) = (A i)†`. -/
  A_star : ∀ i, A (star i) = (A i)ᴴ
  /-- `ν (star i) = -ν i`. -/
  ν_star : ∀ i, ν (star i) = -ν i
  /-- Coupling coefficients `α_{ν_i ν_j}`. -/
  α : ι → ι → ℂ

/-- The transition part `T[X] = Σ_{i,j} α_{ij} A_i X A_j†` (Eq. (2.2), p. 10). -/
noncomputable def transitionSuper (d : BohrJumpData D ι) (X : Operator D) : Operator D :=
  ∑ i, ∑ j, d.α i j • (d.A i * X * (d.A j)ᴴ)

/-- The Hilbert–Schmidt adjoint of `transitionSuper`: `T†[X] = Σ_{i,j} conj(α_{ij}) A_i† X A_j`. -/
noncomputable def transitionAdjoint (d : BohrJumpData D ι) (X : Operator D) : Operator D :=
  ∑ i, ∑ j, star (d.α i j) • ((d.A i)ᴴ * X * d.A j)

/-- Bohr-frequency skew-symmetry (Eq. (2.4), p. 11, and Proposition II.2, p. 10):
`α_{ij} exp(β(ν_i+ν_j)/2) = α_{-ν_j,-ν_i}`. -/
def BohrSkewSymmetry (β : ℝ) (d : BohrJumpData D ι) : Prop :=
  ∀ i j, d.α i j * ((Real.exp (β * (d.ν i + d.ν j) / 2) : ℝ) : ℂ)
    = d.α (d.star j) (d.star i)

/-- Hermiticity of the coefficient matrix, `α† = α` (explicitly assumed together with
the skew-symmetry in Corollary II.2, p. 12: `α*_{ν1ν2} = α_{ν2ν1}`). -/
def BohrCoeffHermitian (d : BohrJumpData D ι) : Prop :=
  ∀ i j, star (d.α i j) = d.α j i

/-- The modular eigen-relation `ρ^{1/2} A_i ρ^{-1/2} = exp(-βν_i/2) A_i`, written with
the inverse square root so no subtraction of exponents is needed:
`rInv * A_i * r = exp(βν_i/2) • A_i` (Section II.A–B, p. 7–11). -/
def BohrModularEigen (β : ℝ) (r rInv : Operator D) (d : BohrJumpData D ι) : Prop :=
  ∀ i, rInv * d.A i * r = ((Real.exp (β * d.ν i / 2) : ℝ) : ℂ) • d.A i

/-- The purely dissipative (decay) part `D[X] = -½{R,X}` with
`R = Σ_{i,j} α_{ij} A_j† A_i` (Section II.B, p. 8 and Corollary II.2, p. 12). -/
noncomputable def decayOperator (d : BohrJumpData D ι) : Operator D :=
  ∑ i, ∑ j, d.α i j • ((d.A j)ᴴ * d.A i)

noncomputable def decaySuper (d : BohrJumpData D ι) (X : Operator D) : Operator D :=
  (-(1 / 2 : ℂ)) • (decayOperator d * X + X * decayOperator d)

/-- Coherent commutator part `-i[B,X]`. -/
noncomputable def commutatorSuper (B X : Operator D) : Operator D :=
  (-Complex.I) • (B * X - X * B)

/-- The full Lindbladian of Corollary II.2 / Eq. (2.5) in Bohr form:
`L[X] = -i Σ_ν [B_ν,X] + Σ_{a,ν1,ν2} α_{ν1ν2}(A_{ν1} X A_{ν2}† - ½{A_{ν2}†A_{ν1},X})`. -/
noncomputable def bohrLindbladian (d : BohrJumpData D ι) (B : Operator D)
    (X : Operator D) : Operator D :=
  commutatorSuper B X + transitionSuper d X + decaySuper d X

/-- The Bohr-frequency coherent term of Corollary II.2, Eq. (2.5), p. 12:
`B_ν = Σ_{a,ν1-ν2=ν} tanh(-β(ν1-ν2)/4)/(2i) α_{ν1ν2} (A_{ν2})†A_{ν1}`. -/
noncomputable def coherentBohrTerm (β : ℝ) (d : BohrJumpData D ι) : Operator D :=
  ∑ i, ∑ j,
    (((Real.tanh (-(β * (d.ν j - d.ν i) / 4)) : ℝ) : ℂ) / (2 * Complex.I)) •
      (d.α i j • ((d.A j)ᴴ * d.A i))

/-! ## Gaussian and Metropolis transition weights -/

/-- Gaussian transition weight (1.4), p. 3:
`γ(ω) = exp(-(ω+ω_γ)^2/(2σ_γ^2))`; the variance `σ_γ^2 = 2ω_γ/β - σ_E^2` is
encoded by the caller through the three parameters. -/
noncomputable def gaussianWeight (ω ωγ σγ : ℝ) : ℝ :=
  Real.exp (-(ω + ωγ) ^ 2 / (2 * σγ ^ 2))

/-- The Gaussian specialisation (1.5), p. 3: `γ(ω) = exp(-(βω+1)^2/2)` when
`σ_E = σ_γ = ω_γ = 1/β`. -/
noncomputable def gaussianWeightBeta (β ω : ℝ) : ℝ :=
  Real.exp (-(β * ω + 1) ^ 2 / 2)

/-- Metropolis-style transition weight (1.8), p. 4:
`γ^M(ω) = exp(-β max(ω + 1/(2β), 0))` for `σ_E = 1/β`. -/
noncomputable def metropolisWeight (β ω : ℝ) : ℝ :=
  Real.exp (-(β * max (ω + 1 / (2 * β)) 0))

/-- Closed-form Gaussian coefficients (2.3), p. 11:
`α_{ν1ν2} = σ_γ/√(σ_E^2+σ_γ^2) · exp(-(ν1+ν2+2ω_γ)^2/(8(σ_E^2+σ_γ^2)))
· exp(-(ν1-ν2)^2/(8σ_E^2))`. -/
noncomputable def gaussianCoeff (σE σγ ωγ ν1 ν2 : ℝ) : ℝ :=
  σγ / Real.sqrt (σE ^ 2 + σγ ^ 2) *
    Real.exp (-(ν1 + ν2 + 2 * ωγ) ^ 2 / (8 * (σE ^ 2 + σγ ^ 2))) *
    Real.exp (-(ν1 - ν2) ^ 2 / (8 * σE ^ 2))

/-- The effective inverse temperature attached to the Gaussian filter,
`β = 2ω_γ/(σ_E^2 + σ_γ^2)` (Lemma II.2, Eq. (2.4), p. 11). -/
noncomputable def gaussianBeta (σE σγ ωγ : ℝ) : ℝ :=
  2 * ωγ / (σE ^ 2 + σγ ^ 2)

/-- Closed-form CKG coefficient as used in the frozen `CkgBounds` layer
(`ckgWeight`, `CKGWeight.lean`), recorded here so the paper-layer statements can name
the frozen specialization without importing its internals at every use site. -/
noncomputable def ckgCoeff (β ν ν' : ℝ) : ℝ :=
  Real.exp (-(1 : ℝ) / 4) / (2 * Real.sqrt 2) *
    Real.exp (-(β * (ν + ν')) / 4 - (β ^ 2 / 16) * (3 * ν ^ 2 - 2 * ν * ν' + 3 * ν' ^ 2))

end Qatlib.Papers.NoncommGibbs23.MainResults
