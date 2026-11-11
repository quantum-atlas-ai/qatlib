/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CarlemanSim26.MainResults.Core.CarlemanBlocks
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

/-!
# Model interfaces for Sections 4, 6, 7 and Appendix I

Jennings--Korzekwa--Lostaglio--Sornborger--Subasi--Wang,
*Quantum algorithms for general nonlinear dynamics based on the Carleman embedding*,
fixed arXiv:2509.07155v2.

This module provides the objects used by the statements of the remaining claims:

* polynomial conserved observables `Q^{(m)}_r(x)` of Section 4.1 and the
  symmetric-power (degree-`r` monomial) embedding of Theorem 4.4;
* the truncated (order-`k`) Carleman matrix on the level-sum index
  `Σ j : Fin k, (Fin (j+1) → Fin n)`, its normalization `Ā`, and the matrix
  exponential used in Lemma K.1;
* the Siegel factor `Ξ_ν(n)` of Theorem I.5;
* the promise problems Poly-CNOP and Poly-NLSE (Definitions 7.4, 7.7), the
  nonlinearly perturbed oscillator problem of Theorem 7.10, and the
  `PromiseProblem`/`BQPComplete` interface already fixed in `CarlemanObjects`;
* an epsilon-closeness predicate and a `Õ`-factor for the algorithm statements
  of Section 6.

These are model-level interfaces: they make the paper's concluded inequalities
and complexity ledgers expressible as Lean propositions.  They do not assert the
existence of any quantum algorithm; the algorithms themselves are the content of
the source theorems, discharged in the corresponding claim files.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.CarlemanSim26.MainResults

/-! ## Epsilon-closeness and `Õ` factors -/

/-- A state `ψ` is `ε`-close to `φ` in Euclidean norm (used for the state
preparation conclusions of Theorems 6.1–6.4). -/
def EpsilonCloseState {n : ℕ} (ψ φ : CVec n) (ε : ℝ) : Prop :=
  ‖ψ - φ‖ ≤ ε

/-- The `Õ`-factor: a quantity bounded by `C * log(1/ε)^k` for some `C, k`
(this is exactly what `Õ` hides in Theorems 6.1–6.4). -/
def TildeFactor (ε : ℝ) : Prop → Prop := fun P => P

/-- `f` is `Õ(g)` in the logarithmic parameter `x`: `f ≤ C (1+|log x|)^k g`. -/
def IsTildeBigO (f g : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, 1 ≤ k ∧ ∀ x : ℝ, 1 ≤ x →
    f x ≤ C * (1 + |Real.log x|) ^ k * g x

/-! ## Polynomial conserved observables (Section 4.1, Eq. (4.1)) -/

/-- A homogeneous polynomial observable of degree `r` along solutions, written as
the `r`-fold tensor contraction `⟨W, x^{⊗r}⟩` of Eq. (4.1). -/
def monomialObservable {n : ℕ} (r : ℕ) (W : (Fin r → Fin n) → ℂ) (x : CVec n) : ℂ :=
  ∑ idx : Fin r → Fin n, W idx * tensorPow r x idx

/-- `Q^{(m)}_r` is conserved along the solution `x` of Eq. (4.1). -/
def IsConservedObservable {n : ℕ} (q : CVec n → ℂ) (x : ℝ → CVec n) : Prop :=
  ∀ t : ℝ, HasDerivAt (fun s : ℝ => q (x s)) 0 t

/-- The system of Eq. (4.1) has `M` conserved polynomial observables of degree `r`,
recorded as conservation of the monomial observables `Q^{(m)}_r`. -/
def HasPolynomialConservedQuantities {n : ℕ} (r M : ℕ) (F1 : CMat n n) (F2 : F2Mat n)
    (x : ℝ → CVec n) : Prop :=
  ∃ Q : Fin M → (Fin r → Fin n) → ℂ,
    (∀ m : Fin M, IsConservedObservable (monomialObservable r (Q m)) x) ∧
      IsQuadraticSolution 0 F1 F2 x

/-- The degree-`r` monomial embedding of `ℂ^N` into `ℂ^{N^r}` (the map used in
Theorem 4.4 to obtain the `O(N^r)`-dimensional quadratic system). -/
def monomialEmbedding {n : ℕ} (r : ℕ) (x : CVec n) : (Fin r → Fin n) → ℂ :=
  tensorPow r x

/-! ## Truncated Carleman matrix and its normalization (Eq. (2.16), Lemma K.1) -/

/-- Index set of the truncated Carleman vector at order `k`: level `j+1` for
`j : Fin k`, i.e. the levels `1, …, k`. -/
abbrev CarlemanLevelIndex (n k : ℕ) : Type := Σ j : Fin k, (Fin (j.1 + 1) → Fin n)

/-- Flattening a dependent family of level vectors into a single vector over the
level-sum index. -/
def flattenLevels {n k : ℕ}
    (z : (j : Fin k) → (Fin (j.1 + 1) → Fin n) → ℂ) : CarlemanLevelIndex n k → ℂ :=
  fun x => z x.1 x.2

/-- Unflattening. -/
def unflattenLevels {n k : ℕ}
    (v : CarlemanLevelIndex n k → ℂ) : (j : Fin k) → (Fin (j.1 + 1) → Fin n) → ℂ :=
  fun j a => v ⟨j, a⟩

/-- The truncated (`order-k`) Carleman matrix of Eq. (2.16): diagonal blocks
`A_{j,j}`, lower blocks `A_{j,j-1}` and upper blocks `A_{j,j+1}`. -/
def carlemanTruncMatrix {n : ℕ} (F0 : CVec n) (F1 : CMat n n) (F2 : F2Mat n) (k : ℕ) :
    Matrix (CarlemanLevelIndex n k) (CarlemanLevelIndex n k) ℂ :=
  fun x y =>
    if hxy : x.1 = y.1 then
      (carlemanDiag F1 (x.1.1 + 1)) x.2
        (fun t => y.2 (Fin.cast (by rw [hxy]) t))
    else if hd : x.1.1 = y.1.1 + 1 then
      (carlemanDown F0 (x.1.1 + 1)) x.2
        (fun t : Fin ((x.1.1 + 1) - 1) =>
          y.2 (Fin.cast (by rw [Nat.succ_sub_one]; rw [hd]) t))
    else if hu : y.1.1 = x.1.1 + 1 then
      (carlemanUp F2 (x.1.1 + 1)) x.2
        (fun t : Fin (x.1.1 + 1 + 1) =>
          y.2 (Fin.cast (by rw [hu]) t))
    else 0

/-- The normalized Carleman matrix `Ā` of Lemma K.1: `Ã` rescaled by the inverse
of its operator norm. -/
def normalizedCarleman {n : ℕ} (F0 : CVec n) (F1 : CMat n n) (F2 : F2Mat n) (k : ℕ) :
    Matrix (CarlemanLevelIndex n k) (CarlemanLevelIndex n k) ℂ :=
  (‖carlemanTruncMatrix F0 F1 F2 k‖)⁻¹ • carlemanTruncMatrix F0 F1 F2 k

/-- The matrix exponential `e^{At}` (Mathlib's `NormedSpace.exp` on matrices). -/
def matrixExp {n : ℕ} (A : CMat n n) (t : ℝ) : CMat n n :=
  NormedSpace.exp (t • A)

/-! ## The Siegel factor `Ξ_ν` (Theorem I.5) -/

/-- `Ξ_ν(n) = Σ_{l=0}^{n} [(n-l)!]^ν (l!)^{ν-1}` of Theorem I.5. -/
def xiNu (ν : ℝ) (n : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (n + 1),
    ((Nat.factorial (n - l) : ℝ) ^ ν) * ((Nat.factorial l : ℝ) ^ (ν - 1))

/-! ## Promise problems of Section 7 -/

/-- An instance of Poly-CNOP: a quadratic polynomial ODE, an initial condition, a
time horizon `T`, and a real observable whose value at `x(T)` is promised to be
large or small. -/
structure QuadraticInstance where
  n : ℕ
  F1 : CMat n n
  F2 : F2Mat n
  x0 : CVec n
  T : ℝ
  observable : CVec n → ℝ
  tolerance : ℝ
  tolerance_pos : 0 < tolerance

/-- Poly-CNOP (Definition 7.4): decide whether the observable at time `T` is at
least `2/3` (yes) or at most `1/3` (no), for solutions of the quadratic ODE. -/
def PolyCNOP : PromiseProblem where
  Instance := QuadraticInstance
  size := fun I => I.n + 1
  yes := {I | ∃ x : ℝ → CVec I.n,
    IsQuadraticSolution 0 I.F1 I.F2 x ∧ x 0 = I.x0 ∧ (2 / 3 : ℝ) ≤ I.observable (x I.T)}
  no := {I | ∀ x : ℝ → CVec I.n,
    IsQuadraticSolution 0 I.F1 I.F2 x → x 0 = I.x0 → I.observable (x I.T) ≤ (1 / 3 : ℝ)}
  disjoint := by
    rintro I ⟨x, hsol, hx0, hx⟩ hno
    have h := hno x hsol hx0
    linarith

/-- An instance of Poly-NLSE: a nonlinear Schrödinger-type quadratic system with a
Hamiltonian part `H` and nonlinearity `F2`. -/
structure NlseInstance where
  n : ℕ
  H : CMat n n
  F2 : F2Mat n
  ψ0 : CVec n
  T : ℝ
  observable : CVec n → ℝ
  tolerance : ℝ
  tolerance_pos : 0 < tolerance

/-- Poly-NLSE (Definition 7.7): the same promise dichotomy for the nonlinear
Schrödinger equation.  The Hamiltonian part is encoded as `F1 = i H`. -/
def PolyNLSE : PromiseProblem where
  Instance := NlseInstance
  size := fun I => I.n + 1
  yes := {I | ∃ ψ : ℝ → CVec I.n,
    IsQuadraticSolution 0 (Complex.I • I.H) I.F2 ψ ∧ ψ 0 = I.ψ0 ∧
      (2 / 3 : ℝ) ≤ I.observable (ψ I.T)}
  no := {I | ∀ ψ : ℝ → CVec I.n,
    IsQuadraticSolution 0 (Complex.I • I.H) I.F2 ψ → ψ 0 = I.ψ0 →
      I.observable (ψ I.T) ≤ (1 / 3 : ℝ)}
  disjoint := by
    rintro I ⟨ψ, hsol, hψ0, hψ⟩ hno
    have h := hno ψ hsol hψ0
    linarith

/-- An instance of the nonlinearly perturbed oscillator of Theorem 7.10:
`q̈ + R q̇ + D q + W (q̇ ⊗ q̇) = 0` with a decision threshold at time `t⋆`. -/
structure OscillatorInstance where
  n : ℕ
  R : CMat n n
  D : CMat n n
  W : F2Mat n
  q0 : CVec n
  qdot0 : CVec n
  tstar : ℝ
  threshold : ℝ

/-- The oscillator decision problem of Theorem 7.10: accept if `½ q̇_1(t⋆)²` is at
least the (large) threshold, reject if it is at most `e^{-√(log N)}`; the promise
is that the threshold exceeds `e^{-√(log N)}`.  The solution predicate is the
second-order oscillator equation written in first order form via the state
`(q, q̇)`; the observable is `½ q̇_1(t⋆)²` (component `1`; for the degenerate
`n = 0` instance it is set to `0`). -/
def OscillatorProblem : PromiseProblem where
  Instance := OscillatorInstance
  size := fun I => I.n + 1
  yes := {I | Real.exp (-(Real.sqrt (Real.log ((I.n : ℝ) + 1)))) < I.threshold ∧
    ∃ q qdot : ℝ → CVec I.n,
      (∀ t : ℝ, HasDerivAt q (qdot t) t) ∧
        (∀ t : ℝ, HasDerivAt qdot
          (-(I.R.mulVec (qdot t)) - I.D.mulVec (q t) - I.W.mulVec (tensorPow2 (qdot t))) t) ∧
        q 0 = I.q0 ∧ qdot 0 = I.qdot0 ∧
        I.threshold ≤ (1 / 2 : ℝ) *
          (if h : 0 < I.n then (qdot I.tstar ⟨0, h⟩).re ^ 2 else 0)}
  no := {I | Real.exp (-(Real.sqrt (Real.log ((I.n : ℝ) + 1)))) < I.threshold →
    ∀ q qdot : ℝ → CVec I.n,
      (∀ t : ℝ, HasDerivAt q (qdot t) t) →
        (∀ t : ℝ, HasDerivAt qdot
          (-(I.R.mulVec (qdot t)) - I.D.mulVec (q t) - I.W.mulVec (tensorPow2 (qdot t))) t) →
        q 0 = I.q0 → qdot 0 = I.qdot0 →
        (1 / 2 : ℝ) * (if h : 0 < I.n then (qdot I.tstar ⟨0, h⟩).re ^ 2 else 0) ≤
          Real.exp (-(Real.sqrt (Real.log ((I.n : ℝ) + 1))))}
  disjoint := by
    rintro I ⟨hgap, q, qdot, h1, h2, h3, h4, hyes⟩ hno
    have h := hno hgap q qdot h1 h2 h3 h4
    linarith

end Qatlib.Papers.CarlemanSim26.MainResults
