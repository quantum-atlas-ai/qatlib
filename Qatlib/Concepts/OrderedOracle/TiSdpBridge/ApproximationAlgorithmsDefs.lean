/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.LchsSimulation.Quadrature.GaussLegendreRule
import Qatlib.Concepts.CoherentSim.CoherentOAA.OddApproximation

/-!
# Approximation identities and matrix certificates

This module defines Chebyshev polynomials, quadrature comparison propositions, and
scalar-to-singular-transform error propositions. `SpectralCertificate`,
`SpectralApproximationCorrect`, and the Schur multiplier definitions specify further matrix
approximation contracts; the singular-transform setting is motivated by [GilyenSuLowWiebe2019],
while the spectral and matrix norm vocabulary follows [HiaiPetz2014].

## Main statements

* `chebRecursionIdentity`, `chebOrthogonality`, and `chebTriangleRepresentation` state the
  polynomial and trigonometric identities.
* `gaussLegendreComparison` and `gaussLegendreCellComparison` specify exactness, normalization,
  and cell error comparisons.
* `scalarToSingularBridge` and `polynomialToSingularBridge` state operator norm error transfers.
* `SpectralApproximationCorrect` and `schurMultiplierBridge` state certificate correctness and
  multiplier bounds.

## References

* [Gilyen et al., 2019][GilyenSuLowWiebe2019]
* [Hiai and Petz, 2014][HiaiPetz2014]
-/

set_option warningAsError false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.LchsSimulation.Quadrature

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge

open Matrix Polynomial

open scoped Matrix.Norms.L2Operator

/-- The real Chebyshev polynomial of the first kind at natural index `n`, using the
integer-indexed Mathlib definition. -/
noncomputable def chebT (n : ℕ) : Polynomial ℝ := Polynomial.Chebyshev.T ℝ (n : ℤ)

/-- The proposition asserting the recurrence `chebT (n + 2) = 2 * X * chebT (n + 1) - chebT n`
for every natural index. -/
def chebRecursionIdentity : Prop :=
  ∀ n : ℕ, chebT (n + 2) = 2 * Polynomial.X * chebT (n + 1) - chebT n

/-- The real-valued Chebyshev weight `1 / sqrt (1 - x^2)`, defined for every real `x` using
total real operations. -/
noncomputable def chebWeight (x : ℝ) : ℝ := 1 / Real.sqrt (1 - x ^ 2)

/-- The proposition that distinct natural-frequency cosine functions have zero product integral
over the interval from zero to pi. -/
def chebOrthogonality : Prop :=
  ∀ m n : ℕ, m ≠ n →
    ∫ x in (0 : ℝ)..Real.pi, Real.cos (m * x) * Real.cos (n * x) = 0

/-- The proposition expressing Chebyshev evaluation at `cos theta` as `cos (n * theta)` for
every natural index and real angle. -/
def chebTriangleRepresentation : Prop :=
  ∀ n : ℕ, ∀ θ : ℝ, (chebT n).eval (Real.cos θ) = Real.cos (n * θ)

/-- The cosine node `cos ((2*j + 1)*pi/(2*N))`, defined for arbitrary natural `N` and `j`. -/
noncomputable def chebNode (N : ℕ) (j : ℕ) : ℝ := Real.cos ((2 * j + 1) * Real.pi / (2 * N))

/-- The proposition giving the cosine formula for `chebT n` evaluated at `chebNode N j` whenever
`j < N`. -/
def chebNodeValues : Prop :=
  ∀ N j : ℕ, j < N → ∀ n : ℕ,
    (chebT n).eval (chebNode N j) = Real.cos (n * (2 * j + 1) * Real.pi / (2 * N))

/-- The proposition asserting a `Q`-node quadrature rule for each positive `Q`, with weights
summing to two and exactness through degree `2*Q - 1`. It also specifies the integral of the
squared node polynomial by its factorial formula. -/
def gaussLegendreComparison : Prop :=
  ∀ Q : ℕ, 1 ≤ Q → ∃ node weight : Fin Q → ℝ,
    (∑ q, weight q = 2) ∧
      (∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
        ∫ x in (-1 : ℝ)..1, p.eval x = ∑ q, weight q * p.eval (node q)) ∧
      (∫ t in (-1 : ℝ)..1, ∏ q : Fin Q, (t - node q) ^ 2) =
        ((2 : ℝ) ^ (2 * Q + 1) * (Q.factorial : ℝ) ^ 4) /
          (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2)

/-- The proposition bounding quadrature error on a positive-length cell for a function with
`2*Q` continuous derivatives. Its hypotheses supply polynomial exactness and the
squared-node-polynomial integral, and its conclusion uses the supremum of the absolute
`2*Q`th derivative on the cell. -/
def gaussLegendreCellComparison : Prop :=
  ∀ Q : ℕ, 1 ≤ Q → ∀ (a h : ℝ) (node weight : Fin Q → ℝ) (f : ℝ → ℝ),
    0 < h →
    (∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
      ∫ x in a..a + h, p.eval x =
        ∑ q, (h / 2) * weight q * p.eval (a + h * (node q + 1) / 2)) →
    (∫ x in a..a + h,
        ∏ q : Fin Q, (x - (a + h * (node q + 1) / 2)) ^ 2) =
      (h ^ (2 * Q + 1) * (Q.factorial : ℝ) ^ 4) /
        (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2) →
    ContDiff ℝ ((2 * Q : ℕ) : WithTop ℕ∞) f →
    |(∫ k in a..a + h, f k) -
        ∑ q, (h / 2) * weight q * f (a + h * (node q + 1) / 2)| ≤
      ((Q.factorial : ℝ) ^ 4 * h ^ ((2 : ℝ) * Q + 1)) /
          (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 3) *
        (⨆ k ∈ Set.Icc a (a + h), |iteratedDeriv (2 * Q) f k|)

/-- The proposition transferring a nonnegative uniform error bound at all matrix singular values
to the operator norm distance between the two corresponding odd singular transforms. -/
def scalarToSingularBridge : Prop :=
  ∀ (O I : Type) [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I]
    (A : Matrix O I ℂ) (f g : ℝ → ℂ) (ε : ℝ),
    0 ≤ ε →
    (∀ i : Fin (Fintype.card I),
      ‖f (Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i) -
        g (Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i)‖ ≤ ε) →
    ‖Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A f -
      Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A g‖ ≤ ε

/-- The polynomial version of the singular-transform error contract, using real polynomial
evaluation at each singular value and complex coercion in the transforms. -/
def polynomialToSingularBridge : Prop :=
  ∀ (O I : Type) [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I]
    (A : Matrix O I ℂ) (p q : Polynomial ℝ) (ε : ℝ),
    0 ≤ ε →
    (∀ i : Fin (Fintype.card I),
      |p.eval (Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i) -
        q.eval (Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i)| ≤ ε) →
    ‖Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A (fun x => ((p.eval x : ℝ) : ℂ)) -
      Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A (fun x => ((q.eval x : ℝ) : ℂ))‖ ≤ ε

/-- Data for a dimension-`D` spectral certificate: rational interval endpoints, rational gap
values, natural multiplicities, and natural time and space bounds. -/
structure SpectralCertificate (D : ℕ) where

  values : Fin D → ℚ × ℚ

  gaps : Fin D → ℚ

  multiplicity : Fin D → ℕ

  bitTime : ℕ

  bitSpace : ℕ

/-- The proposition that, if `A` is Hermitian and the tolerance is positive, a unitary
diagonalization fits the certificate's ordered intervals and gap bounds. It also requires
total multiplicity `D` and the stated dimension-and-tolerance bounds on certificate time and
space. -/
def SpectralApproximationCorrect {D : ℕ} (A : Operator D)
    (cert : SpectralCertificate D) (ε : ℝ) : Prop :=
  A.IsHermitian → 0 < ε →
    ∃ (U : Operator D) (lam : Fin D → ℝ),
      U ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
        A = U * Matrix.diagonal (fun i => (lam i : ℂ)) * Uᴴ ∧
        (∀ i : Fin D, lam i ∈ Set.Icc ((cert.values i).1 : ℝ) ((cert.values i).2 : ℝ)) ∧
        (∀ i j : Fin D, (i : ℕ) < (j : ℕ) → (cert.values i).2 ≤ (cert.values j).1) ∧
        (∀ i j : Fin D, (i : ℕ) < (j : ℕ) → (cert.gaps i : ℝ) ≤ lam j - lam i) ∧
        ∑ i, cert.multiplicity i = D ∧
        cert.bitTime ≤ D ^ 3 * (Nat.ceil (1 / ε) + 1) ∧
        cert.bitSpace ≤ D ^ 2 * (Nat.ceil (1 / ε) + 1)

/-- The condition that `r` is positive and no greater than the operator norm of `z` times the
identity minus `A`. -/
def ResolventCertificate {D : ℕ} (A : Operator D) (z : ℂ) (r : ℝ) : Prop :=
  0 < r ∧ r ≤ ‖z • (1 : Operator D) - A‖

/-- The complex-linear map sending an operator `X` to its entrywise product with `B`. -/
noncomputable def schurMultiplierMap {D : ℕ} (B : Operator D) :
    Operator D →ₗ[ℂ] Operator D where
  toFun X := B ⊙ X
  map_add' X Y := by
    ext i j
    simp [Matrix.hadamard, mul_add]
  map_smul' c X := by
    ext i j
    simp [Matrix.hadamard, smul_eq_mul, mul_left_comm]

/-- The condition that entrywise multiplication by `B` bounds every operator difference in norm
by `M` times the norm of that difference. -/
def SchurMultiplierBounded {D : ℕ} (B : Operator D) (M : ℝ) : Prop :=
  ∀ X Y : Operator D, ‖B ⊙ (X - Y)‖ ≤ M * ‖X - Y‖

/-- The proposition that a `ResolventCertificate A z r` and entrywise bounds `norm (B i j) <=
1/r` imply the Schur multiplier bound `D/r`. -/
def schurMultiplierBridge : Prop :=
  ∀ (D : ℕ) (A : Operator D) (z : ℂ) (r : ℝ),
    ResolventCertificate A z r →
      ∀ B : Operator D, (∀ i j, ‖B i j‖ ≤ 1 / r) →
        SchurMultiplierBounded B ((D : ℝ) / r)

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
