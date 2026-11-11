/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Forrelation: source model and paper-layer statements

Fixed paper version: Aaronson–Ambainis, *Forrelation: A Problem that Optimally
Separates Quantum from Classical Computing*, arXiv:1411.5729v1 (2014).  Every
theorem below cites the paper's theorem number and printed page.

The model follows the paper's own conventions:

* `{0,1}^n` is `Cube n := Fin n → Bool`; `N = 2^n` is the number of queried bits.
* `sign b = -1` for `b = true` and `+1` for `b = false`; for a real number `x`,
  `signOfReal x = true` iff `x < 0`, mirroring the paper's `sgn`.
* `walsh x y = (-1)^{x·y}` with the mod-2 inner product `dot`.
* `forrelation f g` is `Φ_{f,g}` normalised by `2^{3n/2}`; `kfoldForrelation` is
  the `k`-fold twisted sum normalised by `2^{(k+1)n/2}`.
* Randomized adaptive algorithms are finite mixtures of deterministic decision
  trees (the paper's Section 3.1 notion).  A seed carries a probability weight.
* Nonadaptive classical estimators fix a query set per seed and depend only on it.
* `QuantumQueryAlgorithm` is the abstract acceptance-probability interface of a
  `t`-query quantum algorithm; circuits are not re-formalised.
* `BlockMultilinear`, `Refinement`, `CubePolynomial`, `lambda`, `influence` and
  `variance` are the paper's objects from Sections 5 and 8.
* `gaussLaw m` is the standard Gaussian product measure `N(0,1)^{⊗m}`, obtained
  from Mathlib's `ProbabilityTheory.gaussianReal` and `MeasureTheory.Measure.pi`.

Distributional promises (the uniform measure `U` and the forrelated measure `F`)
are modelled pointwise on their sign-rounded Boolean shadows: an oracle is
"forrelated" when its rounded instance is a valid high-Φ instance.  This is
documented at each affected theorem; the Gaussian laws themselves are used only
where the paper computes an explicit expectation.
-/

set_option autoImplicit false

namespace Qatlib.Papers.Forrelation14.MainResults

open scoped BigOperators

namespace Model

/-! ## 1. The Boolean cube, signs and Walsh characters -/

/-- The Boolean cube `{0,1}^n`. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- Real-valued functions on the Boolean cube, used for real-valued oracles. -/
abbrev RealCube (n : ℕ) := Cube n → ℝ

/-- A real inner-product space of dimension `N`. -/
abbrev Vec (N : ℕ) := Fin N → ℝ

/-- Paper sign convention: `true ↦ -1`, `false ↦ +1`. -/
def sign (b : Bool) : ℝ := if b then -1 else 1

/-- Sign of `false` is `+1`. -/
@[simp] theorem sign_false : sign false = 1 := rfl

/-- Sign of `true` is `-1`. -/
@[simp] theorem sign_true : sign true = -1 := rfl

/-- The sign map never vanishes. -/
theorem sign_ne_zero (b : Bool) : sign b ≠ 0 := by
  cases b <;> norm_num [sign]

/-- The sign map has absolute value one. -/
theorem abs_sign (b : Bool) : |sign b| = 1 := by
  cases b <;> norm_num [sign]

/-- The sign of a real number, as a Boolean: `true ↦ x < 0`. -/
noncomputable def signOfReal (x : ℝ) : Bool := decide (x < 0)

/-- `sign` of `signOfReal x` is the real sign of `x`. -/
theorem sign_signOfReal (x : ℝ) : sign (signOfReal x) = if x < 0 then -1 else 1 := by
  by_cases h : x < 0 <;> simp [sign, signOfReal, h]

/-- The rounded real sign has absolute value one. -/
theorem abs_sign_signOfReal (x : ℝ) : |sign (signOfReal x)| = 1 := abs_sign _

/-- The `0/1` value of a Boolean, in `ZMod 2`. -/
def bitVal (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The `0/1` value of `false` is `0`. -/
@[simp] theorem bitVal_false : bitVal false = 0 := rfl

/-- The `0/1` value of `true` is `1`. -/
@[simp] theorem bitVal_true : bitVal true = 1 := rfl

/-- The mod-2 inner product `x · y` of the paper. -/
def dot {n : ℕ} (x y : Cube n) : ZMod 2 := ∑ i, bitVal (x i) * bitVal (y i)

/-- The Walsh character `(-1)^{x·y}`. -/
def walsh {n : ℕ} (x y : Cube n) : ℝ := if dot x y = 0 then 1 else -1

/-- Walsh characters square to one. -/
theorem walsh_sq {n : ℕ} (x y : Cube n) : walsh x y * walsh x y = 1 := by
  unfold walsh
  split <;> norm_num

/-- A Walsh character is one when the mod-2 inner product vanishes. -/
theorem walsh_eq_one_of_dot_zero {n : ℕ} {x y : Cube n} (h : dot x y = 0) :
    walsh x y = 1 := by
  unfold walsh
  rw [if_pos h]

/-- The mod-2 inner product with the zero vector is zero. -/
theorem dot_zero_right {n : ℕ} (x : Cube n) : dot x (fun _ => false) = 0 := by
  unfold dot bitVal
  simp

/-- The Walsh character against the zero vector is one. -/
theorem walsh_zero_right {n : ℕ} (x : Cube n) : walsh x (fun _ => false) = 1 :=
  walsh_eq_one_of_dot_zero (dot_zero_right x)

/-! ## 2. The Forrelation functionals -/

/-- The normalisation `2^{3n/2} = N√N` with `N = 2^n`. -/
noncomputable def forrelationNorm (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * Real.sqrt ((2 : ℝ) ^ n)

/-- The two-function Forrelation functional `Φ_{f,g}` (Section 1.1.1, p. 3). -/
noncomputable def forrelation {n : ℕ} (f g : Cube n → Bool) : ℝ :=
  (∑ x : Cube n, ∑ y : Cube n, sign (f x) * walsh x y * sign (g y)) /
    forrelationNorm n

/-- The real-valued Forrelation functional. -/
noncomputable def realForrelation {n : ℕ} (f g : RealCube n) : ℝ :=
  (∑ x : Cube n, ∑ y : Cube n, f x * walsh x y * g y) / forrelationNorm n

/-- The normalisation `2^{(k+1)n/2}` of the `k`-fold functional. -/
noncomputable def kfoldNorm (k n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * (Real.sqrt 2) ^ ((k - 1) * n)

/-- The `k`-fold twisted sum `Φ_{f₁,…,f_k}` (Section 1.1.3, p. 4). -/
noncomputable def kfoldForrelation {k n : ℕ} (f : Fin k → Cube n → Bool) : ℝ :=
  (∑ x : Fin k → Cube n,
      (∏ j : Fin k, sign (f j (x j))) *
        (∏ j : Fin k,
          if h : j.val + 1 < k then walsh (x j) (x ⟨j.val + 1, h⟩) else 1)) /
    kfoldNorm k n

/-- The `k`-fold twisted sum with the last character indexed by `z`, i.e. the
quantity `Φ_{f₁,…,f_k}^{(z)}` of Section 9.1, p. 51. -/
noncomputable def kfoldForrelationAt {k n : ℕ} (f : Fin k → Cube n → Bool)
    (z : Cube n) : ℝ :=
  (∑ x : Fin k → Cube n,
      (∏ j : Fin k, sign (f j (x j))) *
        (∏ j : Fin k,
          if h : j.val + 1 < k then walsh (x j) (x ⟨j.val + 1, h⟩)
          else if _ : j.val + 1 = k then walsh (x j) z else 1)) /
    kfoldNorm k n

/-- The unnormalised `k`-fold Hadamard transform used to define the multipliers
`c_x` of Section 9 (p. 51). -/
noncomputable def kfoldFourier {n : ℕ} (f : Cube n → RealCube n) (y : Cube n) : ℝ :=
  (∑ x : Cube n, f x y * walsh x y) / Real.sqrt ((2 : ℝ) ^ n)

/-! ## 3. Encodings of the two-function input -/

/-- The `f` half of a two-function oracle table. -/
def leftFun {n : ℕ} (u : Fin 2 × Cube n → Bool) : Cube n → Bool := fun x => u (0, x)

/-- The `g` half of a two-function oracle table. -/
def rightFun {n : ℕ} (u : Fin 2 × Cube n → Bool) : Cube n → Bool := fun y => u (1, y)

/-- Forrelation value of a two-function oracle table. -/
noncomputable def forrelationValue {n : ℕ} (u : Fin 2 × Cube n → Bool) : ℝ :=
  forrelation (leftFun u) (rightFun u)

/-- The Forrelation promise: `|Φ| ≤ 1/100` or `Φ ≥ 3/5` (Section 1.1.1, p. 3). -/
def forrelationValid {n : ℕ} (u : Fin 2 × Cube n → Bool) : Prop :=
  |forrelationValue u| ≤ 1 / 100 ∨ 3 / 5 ≤ forrelationValue u

/-- The correct decision for a valid input. -/
noncomputable def forrelationAnswer {n : ℕ} (u : Fin 2 × Cube n → Bool) : Bool :=
  decide (3 / 5 ≤ forrelationValue u)

/-- The correct decision for a `k`-fold input. -/
noncomputable def kfoldAnswer {k n : ℕ} (f : Fin k → Cube n → Bool) : Bool :=
  decide (3 / 5 ≤ kfoldForrelation f)

/-- The `k`-fold promise: `|Φ| ≤ 1/100` or `Φ ≥ 3/5`. -/
def kfoldValid {k n : ℕ} (f : Fin k → Cube n → Bool) : Prop :=
  |kfoldForrelation f| ≤ 1 / 100 ∨ 3 / 5 ≤ kfoldForrelation f

/-! ## 4. Randomized adaptive decision trees -/

/-- A finite mixture of adaptive deterministic decision trees over a Boolean
oracle on `σ`, making at most `t` queries. -/
structure RandDecisionTree (σ : Type) [DecidableEq σ] (r t : ℕ) where
  /-- Probability weight of each deterministic tree. -/
  weight : Fin r → ℝ
  weight_nonneg : ∀ s, 0 ≤ weight s
  weight_sum : ∑ s, weight s = 1
  /-- Next coordinate queried after the observed answer list. -/
  query : Fin r → List Bool → σ
  /-- Output after the observed answer list. -/
  output : Fin r → List Bool → Bool

/-- The answer transcript of length `k` of seed `s` on input `x`. -/
def transcript {σ : Type} [DecidableEq σ] {r t : ℕ} (A : RandDecisionTree σ r t)
    (s : Fin r) (x : σ → Bool) : ℕ → List Bool
  | 0 => []
  | k + 1 => transcript A s x k ++ [x (A.query s (transcript A s x k))]

/-- Acceptance probability of a randomized decision tree. -/
noncomputable def RandDecisionTree.acceptProb {σ : Type} [DecidableEq σ] {r t : ℕ}
    (A : RandDecisionTree σ r t) (x : σ → Bool) : ℝ :=
  ∑ s : Fin r, A.weight s * (if A.output s (transcript A s x t) then 1 else 0)

/-- Probability of answering the promise problem correctly. -/
noncomputable def RandDecisionTree.correctProb {σ : Type} [DecidableEq σ] {r t : ℕ}
    (A : RandDecisionTree σ r t) (P : (σ → Bool) → Bool) (x : σ → Bool) : ℝ :=
  if P x then A.acceptProb x else 1 - A.acceptProb x

/-- `A` solves the promise problem to bias `ε`. -/
def SolvesBoundedError {σ : Type} [DecidableEq σ] {r t : ℕ}
    (A : RandDecisionTree σ r t) (P : (σ → Bool) → Bool)
    (valid : (σ → Bool) → Prop) (ε : ℝ) : Prop :=
  ∀ x, valid x → 1 / 2 + ε ≤ A.correctProb P x

/-- A randomized adaptive decision tree over a real-valued oracle on `σ`. -/
structure RealOracleTree (σ : Type) [DecidableEq σ] (r t : ℕ) where
  weight : Fin r → ℝ
  weight_nonneg : ∀ s, 0 ≤ weight s
  weight_sum : ∑ s, weight s = 1
  query : Fin r → List ℝ → σ
  output : Fin r → List ℝ → Bool

/-- The real-answer transcript of length `k` of seed `s` on oracle `o`. -/
def rtranscript {σ : Type} [DecidableEq σ] {r t : ℕ} (A : RealOracleTree σ r t)
    (s : Fin r) (o : σ → ℝ) : ℕ → List ℝ
  | 0 => []
  | k + 1 => rtranscript A s o k ++ [o (A.query s (rtranscript A s o k))]

/-- Acceptance probability of a randomized real-oracle algorithm. -/
noncomputable def RealOracleTree.acceptProb {σ : Type} [DecidableEq σ] {r t : ℕ}
    (A : RealOracleTree σ r t) (o : σ → ℝ) : ℝ :=
  ∑ s : Fin r, A.weight s * (if A.output s (rtranscript A s o t) then 1 else 0)

/-! ## 5. Nonadaptive classical estimators -/

/-- A finite mixture of nonadaptive estimators that read at most `t` coordinates. -/
structure ClassicalEstimator (σ : Type) [DecidableEq σ] (r t : ℕ) where
  weight : Fin r → ℝ
  weight_nonneg : ∀ s, 0 ≤ weight s
  weight_sum : ∑ s, weight s = 1
  queries : Fin r → Finset σ
  queries_card : ∀ s, (queries s).card ≤ t
  estimate : Fin r → (σ → Bool) → ℝ
  reads_only : ∀ s (x y : σ → Bool), (∀ i ∈ queries s, x i = y i) → estimate s x = estimate s y

/-- The expectation of the estimator over the seed. -/
noncomputable def ClassicalEstimator.expectedEstimate {σ : Type} [DecidableEq σ] {r t : ℕ}
    (E : ClassicalEstimator σ r t) (x : σ → Bool) : ℝ :=
  ∑ s : Fin r, E.weight s * E.estimate s x

/-- Probability that the estimator is within `ε` of `target`. -/
noncomputable def ClassicalEstimator.successProb {σ : Type} [DecidableEq σ] {r t : ℕ}
    (E : ClassicalEstimator σ r t) (x : σ → Bool) (target ε : ℝ) : ℝ :=
  ∑ s : Fin r, E.weight s * (if |E.estimate s x - target| ≤ ε then 1 else 0)

/-- A randomized adaptive decision tree with real-valued output (a randomized
estimator), used for the polynomial-estimation results. -/
structure RandRealEstimator (σ : Type) [DecidableEq σ] (r t : ℕ) where
  weight : Fin r → ℝ
  weight_nonneg : ∀ s, 0 ≤ weight s
  weight_sum : ∑ s, weight s = 1
  query : Fin r → List Bool → σ
  output : Fin r → List Bool → ℝ

/-- Forget the real output of an estimator, keeping the query structure. -/
noncomputable def RandRealEstimator.toRandDecisionTree {σ : Type} [DecidableEq σ] {r t : ℕ}
    (A : RandRealEstimator σ r t) : RandDecisionTree σ r t where
  weight := A.weight
  weight_nonneg := A.weight_nonneg
  weight_sum := A.weight_sum
  query := A.query
  output := fun s l => decide (0 ≤ A.output s l)

/-- The estimate of a randomized real estimator on oracle `x`. -/
noncomputable def RandRealEstimator.estimate {σ : Type} [DecidableEq σ] {r t : ℕ}
    (A : RandRealEstimator σ r t) (x : σ → Bool) : ℝ :=
  ∑ s : Fin r, A.weight s *
    A.output s (transcript A.toRandDecisionTree s x t)

/-! ## 6. Quantum query algorithms (abstract model) -/

/-- A `t`-query quantum algorithm, represented by its acceptance probability on
each Boolean input.  The unitary circuit is not re-formalised; this structure is
used only to state simulation and completeness results. -/
structure QuantumQueryAlgorithm (σ : Type) (t : ℕ) where
  accepts : (σ → Bool) → ℝ
  accepts_nonneg : ∀ x, 0 ≤ accepts x
  accepts_le_one : ∀ x, accepts x ≤ 1

/-- A `t`-query quantum algorithm solves the promise problem to bias `ε`. -/
def QuantumQueryAlgorithm.SolvesBoundedError {σ : Type} {t : ℕ}
    (Q : QuantumQueryAlgorithm σ t) (P : (σ → Bool) → Bool)
    (valid : (σ → Bool) → Prop) (ε : ℝ) : Prop :=
  ∀ x, valid x → 1 / 2 + ε ≤ (if P x then Q.accepts x else 1 - Q.accepts x)

/-! ## 7. Block-multilinear polynomials (Sections 5 and 8) -/

/-- A block-multilinear polynomial with `k` blocks of variables indexed by `ι`. -/
structure BlockMultilinear (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] where
  /-- Coefficient of the monomial `∏ j, x j (i j)`. -/
  coeff : (Fin k → ι) → ℝ

/-- Evaluation at a real point. -/
noncomputable def BlockMultilinear.eval {k : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : BlockMultilinear k ι) (x : Fin k → ι → ℝ) : ℝ :=
  ∑ i : Fin k → ι, p.coeff i * ∏ j : Fin k, x j (i j)

/-- Evaluation at a Boolean point (sign encoding). -/
noncomputable def BlockMultilinear.evalBoolean {k : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : BlockMultilinear k ι) (x : Fin k → ι → Bool) : ℝ :=
  p.eval fun j l => sign (x j l)

/-- The paper's boundedness condition `|p(x)| ≤ 1` on the Boolean cube. -/
def BlockMultilinear.Bounded {k : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : BlockMultilinear k ι) : Prop :=
  ∀ x, |p.evalBoolean x| ≤ 1

/-- The diagonal evaluation `p(x, …, x)` of Theorem 18 and Lemma 20. -/
noncomputable def BlockMultilinear.evalDiagonal {k : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : BlockMultilinear k ι) (x : ι → Bool) : ℝ :=
  p.eval fun _ l => sign (x l)

/-- The paper's `Λ_S` of equation (5), p. 32: the sum over the coordinates outside
`S` of the square of the partial coefficient sums inside `S`. -/
noncomputable def BlockMultilinear.Lambda {k : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : BlockMultilinear k ι) (S : Finset (Fin k)) : ℝ :=
  ∑ iS : ({j : Fin k // j ∈ S} → ι),
    (∑ iSc : ({j : Fin k // j ∉ S} → ι),
      p.coeff (fun j => if h : j ∈ S then iS ⟨j, h⟩ else iSc ⟨j, by simpa using h⟩)) ^ 2

/-- A convex refinement of each block variable: the closure of repeated
variable-splittings into equal copies (Section 5.1, pp. 32–33). -/
structure Refinement (k : ℕ) (ι ι' : Type) [Fintype ι] [Fintype ι'] where
  weight : (j : Fin k) → ι → ι' → ℝ
  weight_nonneg : ∀ j l m, 0 ≤ weight j l m
  weight_sum : ∀ j l, ∑ m, weight j l m = 1

/-- Pull a block-multilinear polynomial back along a refinement. -/
noncomputable def BlockMultilinear.pullback {k : ℕ} {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] (p : BlockMultilinear k ι) (R : Refinement k ι ι') :
    BlockMultilinear k ι' where
  coeff i' := ∑ i : Fin k → ι, p.coeff i * ∏ j : Fin k, R.weight j (i j) (i' j)

/-! ## 8. Boolean-cube polynomials, influence and variance (Section 8) -/

/-- A real polynomial on the cube, stored by its Walsh coefficients. -/
structure CubePolynomial (N : ℕ) where
  coeff : Finset (Fin N) → ℝ
  support : Finset (Finset (Fin N))
  support_spec : ∀ S, coeff S ≠ 0 → S ∈ support

/-- Evaluation `Σ_S c_S ∏_{i∈S} x_i` with `x_i = sign (x i)`. -/
noncomputable def CubePolynomial.eval {N : ℕ} (p : CubePolynomial N) (x : Cube N) : ℝ :=
  ∑ S ∈ p.support, p.coeff S * ∏ i ∈ S, sign (x i)

/-- Degree: the largest support size. -/
def CubePolynomial.degree {N : ℕ} (p : CubePolynomial N) : ℕ :=
  p.support.sup Finset.card

/-- Boundedness on the cube. -/
def CubePolynomial.Bounded {N : ℕ} (p : CubePolynomial N) : Prop :=
  ∀ x, |p.eval x| ≤ 1

/-- Uniform average over the cube. -/
noncomputable def cubeAverage (N : ℕ) (F : Cube N → ℝ) : ℝ :=
  (∑ x : Cube N, F x) / (2 : ℝ) ^ N

/-- Flip the `i`-th coordinate. -/
def flipCoord {N : ℕ} (x : Cube N) (i : Fin N) : Cube N :=
  Function.update x i (!x i)

/-- The paper's variance `Var[p] = E[(p - E p)²]`. -/
noncomputable def CubePolynomial.variance {N : ℕ} (p : CubePolynomial N) : ℝ :=
  cubeAverage N fun x => (p.eval x - cubeAverage N p.eval) ^ 2

/-- The paper's influence `Inf_i[p] = E[(p(x^i) - p(x))²]`. -/
noncomputable def CubePolynomial.influence {N : ℕ} (p : CubePolynomial N) (i : Fin N) : ℝ :=
  cubeAverage N fun x => (p.eval (flipCoord x i) - p.eval x) ^ 2

/-- The Fourier formula `Var[p] = Σ_S p̂(S)²`. -/
noncomputable def CubePolynomial.fourierVariance {N : ℕ} (p : CubePolynomial N) : ℝ :=
  ∑ S ∈ p.support, p.coeff S ^ 2

/-- The Fourier formula `Inf_i[p] = Σ_{S ∋ i} p̂(S)²`. -/
noncomputable def CubePolynomial.fourierInfluence {N : ℕ} (p : CubePolynomial N)
    (i : Fin N) : ℝ :=
  ∑ S ∈ p.support.filter (fun S => i ∈ S), p.coeff S ^ 2

/-- The paper's `V[P] := Σ_i I_i[P]` of Section 8.2, p. 49. -/
noncomputable def CubePolynomial.totalInfluence {N : ℕ} (p : CubePolynomial N) : ℝ :=
  ∑ i : Fin N, p.influence i

/-! ## 9. Gaussian data and test vectors (Section 4) -/

/-- The real inner product of two vectors. -/
noncomputable def vinner {N : ℕ} (x y : Vec N) : ℝ := ∑ i, x i * y i

/-- Squared Euclidean norm. -/
noncomputable def vnormSq {N : ℕ} (x : Vec N) : ℝ := vinner x x

/-- Unit vector predicate. -/
def IsUnitVec {N : ℕ} (x : Vec N) : Prop := vnormSq x = 1

/-- The standard Gaussian product measure `N(0,1)^{⊗ι}` on `ι → ℝ`. -/
noncomputable def gaussMeasure (ι : Type) [Fintype ι] : MeasureTheory.Measure (ι → ℝ) :=
  MeasureTheory.Measure.pi fun _ : ι => ProbabilityTheory.gaussianReal 0 1

/-- The standard Gaussian product measure `N(0,1)^{⊗m}` on `ℝ^m`. -/
noncomputable def gaussLaw (m : ℕ) : MeasureTheory.Measure (Vec m) :=
  gaussMeasure (Fin m)

/-- Probability of an event under `gaussLaw m`, as a real number. -/
noncomputable def gaussProb (m : ℕ) (P : Vec m → Prop) : ℝ :=
  ((gaussLaw m) {x : Vec m | P x}).toReal

/-- Probability of an event under the Gaussian measure on `ℝ^{2^n}`. -/
noncomputable def gaussProbCube (n : ℕ) (P : RealCube n → Prop) : ℝ :=
  ((gaussMeasure (Cube n)) {f : RealCube n | P f}).toReal

/-- The data of Section 4.3 (p. 23): a tested Gram–Schmidt basis `w`, normalising
constants `β`, the coefficients `b_i = ⟨Ψ|w_i⟩` and the unnormalised coefficients
`c_i` of equation (2).  The fields are the paper's defining recursions. -/
structure GramSchmidtData {N t : ℕ} (V : Fin t → Vec N) (a : Fin t → ℝ) where
  w : Fin t → Vec N
  beta : Fin t → ℝ
  b : Fin t → ℝ
  c : Fin t → ℝ
  w_rec : ∀ i, w i = beta i • (V i - ∑ j : Fin t, if j < i then vinner (V i) (w j) • w j else 0)
  b_rec : ∀ i, b i = beta i * (a i - ∑ j : Fin t, if j < i then vinner (V i) (w j) * b j else 0)
  c_rec : ∀ i, c i = a i - ∑ j : Fin t, if j < i then vinner (V i) (w j) * c j else 0

/-- `D` is well-behaved (p. 24): `|a_i| ≤ √(2 ln 100t)` for all `i`. -/
def WellBehaved {t : ℕ} (a : Fin t → ℝ) : Prop :=
  ∀ i, |a i| ≤ Real.sqrt (2 * Real.log ((100 : ℝ) * (t : ℝ)))

/-- `Δ_U(D) = a₁² + … + a_t²` (p. 21). -/
noncomputable def DeltaU {t : ℕ} (a : Fin t → ℝ) : ℝ := ∑ i, a i ^ 2

/-- `Δ_F(D) = b₁² + … + b_t²` (p. 23). -/
noncomputable def DeltaF {N t : ℕ} {V : Fin t → Vec N} {a : Fin t → ℝ}
    (G : GramSchmidtData V a) : ℝ := ∑ i, G.b i ^ 2

/-- The residuals `r_i` of eq. (3), p. 26: `r_i = a_i - c_i`. -/
noncomputable def residual {N t : ℕ} {V : Fin t → Vec N} {a : Fin t → ℝ}
    (G : GramSchmidtData V a) (i : Fin t) : ℝ := a i - G.c i

/-- The Hadamard (Walsh) transform with the paper's normalisation `1/√N`. -/
noncomputable def hadamardOf {n : ℕ} (f : RealCube n) : RealCube n :=
  fun y => (∑ x : Cube n, f x * walsh x y) / Real.sqrt ((2 : ℝ) ^ n)

/-- Expectation of `Φ_{F,G}` when `⟨f,g⟩` is drawn from the forrelated measure
`F` (Theorem 9, p. 18): `F = sgn ∘ f`, `G = sgn ∘ Hf`. -/
noncomputable def forrelatedExpectation (n : ℕ) : ℝ :=
  ∫ f : RealCube n,
    forrelation (fun x => signOfReal (f x)) (fun y => signOfReal (hadamardOf f y))
    ∂(gaussMeasure (Cube n))

/-- Expectation of `Φ_{F,G}` for the `k`-fold forrelated measure with multipliers
`c : ℝ^n → ℝ` (Theorem 37, p. 53): the sum `Σ_x c_x F(x) G(x) / √N`. -/
noncomputable def kfoldForrelatedExpectation (n : ℕ) (c : RealCube n) : ℝ :=
  ∫ f : RealCube n,
    (∑ x : Cube n,
        c x * sign (signOfReal (f x)) * sign (signOfReal (hadamardOf f x))) /
      Real.sqrt ((2 : ℝ) ^ n) ∂(gaussMeasure (Cube n))

/-- Hamming distance between two Boolean functions. -/
noncomputable def hammingDist {n : ℕ} (f g : Cube n → Bool) : ℕ :=
  (Finset.univ.filter fun x => f x ≠ g x).card

/-- The uniform probability, over the finite set of `k`-tuples of Boolean functions
on `{0,1}^n`, that a property holds. -/
noncomputable def uniformProb {k n : ℕ} (P : (Fin k → Cube n → Bool) → Prop)
    [DecidablePred P] : ℝ :=
  ((Finset.univ.filter P).card : ℝ) /
    ((Finset.univ : Finset (Fin k → Cube n → Bool)).card : ℝ)

/-- A `k`-tuple is *good* in the sense of Section 10.2, p. 57: all multipliers are
bounded by `log N` and the Lemma-35 concentration holds for every `y`. -/
def GoodTuple {k n : ℕ} (f : Fin k → Cube n → Bool) : Prop :=
  (∀ x : Cube n, |kfoldForrelationAt f x| ≤ Real.log ((2 : ℝ) ^ n)) ∧
    ∀ y : Cube n,
      |(∑ z : Cube n, if dot z y = 0 then (kfoldForrelationAt f z) ^ 2 else 0) - 1 / 2| ≤
        Real.rpow (Real.log ((2 : ℝ) ^ n)) (5 / 2) / Real.sqrt ((2 : ℝ) ^ n)

/-- `A` solves Real Forrelation (p. 20) for a real oracle table `o` carrying the
paper's promise in pointwise form. -/
def IsForrelatedOracle {n : ℕ} (o : Fin 2 × Cube n → ℝ) : Prop :=
  forrelationAnswer (fun p => decide (o p < 0)) = true

/-- An oracle whose sign-rounded instance is a valid low-correlation instance. -/
def IsNearZeroOracle {n : ℕ} (o : Fin 2 × Cube n → ℝ) : Prop :=
  forrelationAnswer (fun p => decide (o p < 0)) = false

/-- `A` solves Real Forrelation with bias `ε`, pointwise on the paper's promise. -/
def SolvesRealForrelation {n r T : ℕ} (A : RealOracleTree (Fin 2 × Cube n) r T)
    (ε : ℝ) : Prop :=
  (∀ o, IsForrelatedOracle o → 1 / 2 + ε ≤ A.acceptProb o) ∧
    ∀ o, IsNearZeroOracle o → A.acceptProb o ≤ 1 / 2 - ε

/-- `A` solves `k`-fold Real Forrelation with bias `ε`. -/
def SolvesKfoldRealForrelation {k n r T : ℕ} (A : RealOracleTree (Fin k × Cube n) r T)
    (ε : ℝ) : Prop :=
  (∀ o, kfoldAnswer (fun j x => decide (o (j, x) < 0)) = true → 1 / 2 + ε ≤ A.acceptProb o) ∧
    ∀ o, kfoldAnswer (fun j x => decide (o (j, x) < 0)) = false →
      A.acceptProb o ≤ 1 / 2 - ε

end Model

/-! ## 10. Claim-level theorems for arXiv:1411.5729 (fixed version: arXiv:1411.5729v1, 21 Nov 2014)

Every theorem below states the paper's claim under the model of Sections 1–9 of
this file.  Where a full formalisation of the paper's query-complexity framework
(BQP, polynomial-time reductions, distributions over oracles) is not available in
this development, the missing layer is recorded in the adjacent `NOTE` comment. -/

namespace Model

/-- A promise problem on `σ → Bool` is solvable by a quantum algorithm with a
polynomial number of queries, to bounded error: the query-count analogue of
`PromiseBQP` used for Theorem 5 (p. 4) and Theorem 25 (p. 38). -/
def InPromiseBQP {σ : Type} [Fintype σ] [DecidableEq σ] (P : (σ → Bool) → Bool)
    (valid : (σ → Bool) → Prop) : Prop :=
  ∃ (C : ℝ) (t : ℕ) (Q : QuantumQueryAlgorithm σ t),
    0 < C ∧ (t : ℝ) ≤ C * (Fintype.card σ : ℝ) ∧
      QuantumQueryAlgorithm.SolvesBoundedError Q P valid (1 / 3)

/-- `P` reduces to `P'` through a map that sends valid instances to valid instances
and preserves the yes/no answer.  The polynomial-time computability of `map` is the
part of the paper's reduction notion that is not modelled here. -/
def ReducesTo {σ τ : Type} (P : (σ → Bool) → Bool) (valid : (σ → Bool) → Prop)
    (P' : (τ → Bool) → Bool) (valid' : (τ → Bool) → Prop) : Prop :=
  ∃ map : (σ → Bool) → (τ → Bool),
    (∀ x, valid x → valid' (map x)) ∧ ∀ x, valid x → (P x = true ↔ P' (map x) = true)

/-- Solves Gaussian Distinguishing (Theorem 2, p. 3; Theorem 11, p. 21) on the test
vectors `V`: in case (i) (independent `N(0,1)` answers) the algorithm rejects with
probability at least `2/3`, and in case (ii) (`aᵢ = ⟨Ψ|Vᵢ⟩`, `Ψ ~ N(0,1)^N`) it
accepts with probability at least `2/3`. -/
noncomputable def SolvesGaussianDistinguishing {N M r t : ℕ}
    (A : RealOracleTree (Fin M) r t) (V : Fin M → Vec N) : Prop :=
  gaussProb M (fun a => 1 / 2 < A.acceptProb a) ≤ 1 / 3 ∧
    2 / 3 ≤ gaussProb N (fun Ψ => 1 / 2 < A.acceptProb fun i => vinner Ψ (V i))

/-- The advantage by which `A` distinguishes the two cases of Gaussian Distinguishing
(used for the general statement of Theorem 11, p. 21). -/
noncomputable def DistinguishesGaussian {N M r t : ℕ} (A : RealOracleTree (Fin M) r t)
    (V : Fin M → Vec N) (γ : ℝ) : Prop :=
  γ ≤ gaussProb N (fun Ψ => 1 / 2 < A.acceptProb fun i => vinner Ψ (V i)) -
    gaussProb M (fun a => 1 / 2 < A.acceptProb a)

/-- The indicator of a proposition, as a real number. -/
noncomputable def indicator (P : Prop) : ℝ :=
  @ite ℝ P (Classical.propDecidable P) 1 0

/-- The Fourier coefficient `f̂(y)` of a Boolean function `f` on `{0,1}^n`
(Theorem 27, p. 41). -/
noncomputable def walshCoeff {n : ℕ} (f : Cube n → Bool) (y : Cube n) : ℝ :=
  (∑ x : Cube n, sign (f x) * walsh x y) / (2 : ℝ) ^ n

/-- A randomized algorithm with a `{0,1}^n`-valued output, used to state the
Fourier Sampling lower bound (Theorem 27, p. 41). -/
structure RandCubeSampler (n r T : ℕ) where
  weight : Fin r → ℝ
  weight_nonneg : ∀ s, 0 ≤ weight s
  weight_sum : ∑ s, weight s = 1
  output : (Cube n → Bool) → Fin r → Cube n

/-- Success condition of Fourier Sampling with error `ε` (Theorem 27, p. 41):
`(1/2) Σ_y |p_{f,y} - f̂(y)²| ≤ ε` for every `f`. -/
noncomputable def SolvesFourierSampling {n r T : ℕ} (A : RandCubeSampler n r T)
    (ε : ℝ) : Prop :=
  ∀ f : Cube n → Bool,
    (1 / 2) * ∑ y : Cube n,
      |(∑ s : Fin r, A.weight s * (if A.output f s = y then (1 : ℝ) else 0)) -
        walshCoeff f y ^ 2| ≤ ε

/-- The multipliers `c_x` of Section 9.1 (p. 51) obtained from `f₁,…,f_{k-2}`: the
`(k-2)`-fold twisted sum with the last character indexed by `x`. -/
noncomputable def kfoldMultiplier {k n : ℕ} (f : Fin (k - 2) → Cube n → Bool)
    (x : Cube n) : ℝ :=
  (∑ y : Fin (k - 2) → Cube n,
      (∏ j : Fin (k - 2), sign (f j (y j))) *
        (∏ j : Fin (k - 2),
          if h : j.val + 1 < k - 2 then walsh (y j) (y ⟨j.val + 1, h⟩)
          else walsh (y j) x)) /
    (2 : ℝ) ^ (((k - 2) + 1) * n / 2)

end Model

/-! ### Theorem 1 (p. 3) -/

/-- **Theorem 1** (arXiv:1411.5729v1, p. 3). Any classical randomized algorithm that
solves the Forrelation promise problem to bounded error must make
`Ω(√N / log N)` queries, `N = 2^n`. -/
/- NOTE (arXiv:1411.5729v1, Theorem 1, p. 3). Paper statement: any classical
randomized algorithm for Forrelation must make Ω(√N/log N) queries (`N = 2^n`).
Proof route: Theorem 1 is deduced from Theorem 2 (Gaussian Distinguishing) by the
discretisation of the two cases; the classical lower bound is transferred from the
Gaussian model to the Boolean cube by rounding the oracle answers to signs.
Lean gap: the paper's lower-bound argument (hybrid/likelihood-ratio analysis of
Gaussian Distinguishing, Section 4) is not formalised; only the statement is given.
Reusable dependencies: `Model.RandDecisionTree`, `Model.SolvesBoundedError`,
`Model.forrelationAnswer`, `Model.forrelationValid`.
Suggested tactics: instantiate `gaussian_distinguishing_lower_bound` (c002) with the
test vectors `{|x⟩} ∪ {|x̂⟩}` and transfer the bound through the sign discretisation. -/
def classical_query_lower_bound_for_Forrelation : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (T n : ℕ),
      (∃ (r : ℕ) (A : Model.RandDecisionTree (Fin 2 × Model.Cube n) r T),
        Model.SolvesBoundedError A Model.forrelationAnswer Model.forrelationValid (1 / 10)) →
      C * (Real.sqrt ((2 : ℝ) ^ n) / Real.log ((2 : ℝ) ^ n)) ≤ (T : ℝ)

/-! ### Theorem 2 (p. 3) -/

/-- **Theorem 2** (arXiv:1411.5729v1, p. 3). Gaussian Distinguishing requires
`Ω((1/ε)/log(M/ε))` classical randomized queries whenever the test set has at most
`M` unit vectors with pairwise inner products at most `ε` in absolute value. -/
/- NOTE (arXiv:1411.5729v1, Theorem 2, p. 3). Paper statement: Gaussian
Distinguishing requires Ω((1/ε)/log(M/ε)) classical randomized queries for
`|V| ≤ M` and `|⟨v|w⟩| ≤ ε` on distinct test vectors.  The two cases are:
(i) independent `N(0,1)` answers; (ii) `a_v = ⟨Ψ|v⟩` with `Ψ ~ N(0,1)^N`.
Proof route (Section 4): pair-by-pair likelihood-ratio/hybrid analysis, giving a
total-variation bound `O(t²ε² + tε√(log M))` for `t` queries; solving for `t`
yields the bound.
Lean gap: the paper's likelihood-ratio computation for product Gaussian measures is
not formalised; `Model.SolvesGaussianDistinguishing` encodes the problem's promise.
Reusable dependencies: `Model.gaussProb`, `Model.gaussLaw`, `Model.vinner`,
`Model.IsUnitVec`, `Model.RealOracleTree.acceptProb`.
Suggested tactics: prove a query-by-query hybrid lemma bounding the change in
acceptance probability by `O(ε)` per query and sum over the `t` queries. -/
def gaussian_distinguishing_lower_bound (M : ℕ) (ε : ℝ) : Prop :=
  ∀ (hε : 0 < ε), ∃ c : ℝ, 0 < c ∧ ∀ (N r t : ℕ) (V : Fin M → Model.Vec N)
      (A : Model.RealOracleTree (Fin M) r t),
      (∀ i, Model.IsUnitVec (V i)) →
      (∀ i j : Fin M, i ≠ j → |Model.vinner (V i) (V j)| ≤ ε) →
      Model.SolvesGaussianDistinguishing A V →
      c * (1 / ε) / Real.log ((M : ℝ) / ε) ≤ (t : ℝ)

/-! ### Theorem 3 (p. 4) -/

/-- **Theorem 3** (arXiv:1411.5729v1, p. 4). The acceptance probability of any
`t`-query quantum algorithm on an `N`-bit input can be estimated to constant
additive error, with high probability, using `O(N^{1-1/(2t)})` nonadaptive classical
randomized queries. -/
/- NOTE (arXiv:1411.5729v1, Theorem 3, p. 4). Paper statement: for `t = O(1)`,
`Pr[Q accepts X]` can be estimated to constant error and high probability with
`O(N^{1-1/2^t})` nonadaptive classical randomized queries.  (The paper writes the
exponent as `1 - 1/2^t`; Theorem 18 states the general form `1 - 1/k` for the
degree-`2t` block-multilinear polynomial, which is the version formalised here.)
Proof route: Lemma 20 turns the algorithm into a bounded block-multilinear
polynomial of degree `2t`; Theorem 18 then estimates it nonadaptively with
`O((N/ε²)^{1-1/(2t)})` queries.
Lean gap: neither Lemma 20's circuit-to-polynomial construction (which needs a
formalised quantum circuit model) nor Theorem 18's sampling analysis is formalised.
Reusable dependencies: `Model.QuantumQueryAlgorithm`,
`Model.RandRealEstimator`, `Model.ClassicalEstimator`.
Suggested tactics: reduce to `randomized_algorithm_estimates_block_multilinear`
(c017) after `quantum_to_block_multilinear_polynomial` (c018). -/
def constant_query_acceptance_estimation (N t : ℕ) (Q : Model.QuantumQueryAlgorithm (Fin N) t) : Prop :=
  ∀ (hN : 0 < N), ∃ C : ℝ, 0 < C ∧ ∀ (r k : ℕ) (E : Model.ClassicalEstimator (Fin N) r k),
      (∀ x : Fin N → Bool, 99 / 100 ≤ E.successProb x (Q.accepts x) (1 / 100)) →
      C * (N : ℝ) ^ (1 - 1 / (2 * (t : ℝ))) ≤ (k : ℝ)

/-! ### Theorem 4 (p. 4) -/

/-- **Theorem 4** (arXiv:1411.5729v1, p. 4). Every degree-`k` real polynomial that is
bounded in `[-1,1]` on the Boolean cube and is block-multilinear with `k` blocks can
be approximated to within `±ε` with high probability by nonadaptively querying
`O((N/ε²)^{1-1/k})` variables. -/
/- NOTE (arXiv:1411.5729v1, Theorem 4, p. 4). Paper statement: every degree-`k`
polynomial `p : {-1,1}^N → ℝ` that is (i) bounded in `[-1,1]` and (ii) block-
multilinear with `k` blocks can be approximated to within ±ε, with high probability,
by nonadaptively querying `O((N/ε²)^{1-1/k})` variables.
Proof route (Section 5): Lemma 21/Corollary 22 split variables so that the
"diagonal" `Λ`-norm becomes small, then a second-moment bound over the sampled
blocks (Lemma 23) gives concentration.
Lean gap: the variable-splitting construction and the sampling second-moment bound
are not formalised; `Model.BlockMultilinear`, `Model.Refinement` and
`Model.BlockMultilinear.Lambda` provide the statements' objects.
Reusable dependencies: `Model.BlockMultilinear.evalDiagonal`,
`Model.ClassicalEstimator.successProb`, `Model.BlockMultilinear.Lambda`.
Suggested tactics: combine c019/c020 (splittings) with Chebyshev applied to the
sampled estimate, as in Lemma 23 (c021). -/
def block_multilinear_lower_bound (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (p : Model.BlockMultilinear k ι) (ε : ℝ) : Prop :=
  ∀ (hk : 0 < k), ∀ (hp : p.Bounded), ∀ (hε : 0 < ε), ∃ C : ℝ, 0 < C ∧ ∀ (r t : ℕ) (E : Model.ClassicalEstimator ι r t),
      (∀ x : ι → Bool, 99 / 100 ≤ E.successProb x (p.evalDiagonal x) ε) →
      C * ((Fintype.card ι : ℝ) / ε ^ 2) ^ (1 - 1 / (k : ℝ)) ≤ (t : ℝ)

/-! ### Theorem 5 (p. 4) -/

/-- **Theorem 5** (arXiv:1411.5729v1, p. 4). For `k = poly(n)`, the `k`-fold
Forrelation promise problem is `PromiseBQP`-complete: it is solvable by a
polynomial-query quantum algorithm, and every `PromiseBQP` problem reduces to it. -/
/- NOTE (arXiv:1411.5729v1, Theorem 5, p. 4). Paper statement: if `f₁,…,f_k` are
described explicitly and `k = poly(n)`, then `k`-fold Forrelation is a
`BQP`-complete promise problem.
Proof route: containment is Proposition 6 (⌈k/2⌉ quantum queries); hardness is
Theorem 25 (Section 6), reducing `QSim`/`QSim_d` to explicit `k`-fold Forrelation.
Lean gap: `PromiseBQP` and polynomial-time reductions are only modelled abstractly
(`Model.InPromiseBQP`, `Model.ReducesTo`); the quantum circuit model and the
computability/efficiency of the reduction map are not formalised.
Reusable dependencies: `Model.InPromiseBQP`, `Model.ReducesTo`,
`Model.QuantumQueryAlgorithm`, `Model.kfoldAnswer`, `Model.kfoldValid`.
Suggested tactics: instantiate `Model.InPromiseBQP` with the ⌈k/2⌉-query forrelation
circuit for containment, and c022 for hardness. -/
def kfold_Forrelation_BQP_complete (k n : ℕ) : Prop :=
  ∀ (hk : 0 < k), Model.InPromiseBQP
        (fun u : Fin k × Model.Cube n → Bool => Model.kfoldAnswer (fun j x => u (j, x)))
        (fun u => Model.kfoldValid (fun j x => u (j, x))) ∧
      ∀ (m : ℕ) (P : (Fin m → Bool) → Bool) (valid : (Fin m → Bool) → Prop),
        Model.InPromiseBQP P valid →
        Model.ReducesTo P valid
          (fun u : Fin k × Model.Cube n → Bool => Model.kfoldAnswer (fun j x => u (j, x)))
          (fun u => Model.kfoldValid (fun j x => u (j, x)))

/-! ### Proposition 6 (p. 13) -/

/- NOTE (arXiv:1411.5729v1, Proposition 6, p. 13). The quantum circuit itself
(⌈k/2⌉ queries, `O(nk)` gates) is not formalised; this theorem isolates and proves
the arithmetic of the acceptance probability that the proposition derives from it.
Proof route: acceptance probability = `(3/4)·((1+Φ)/2)`; substituting the two
promise regimes gives `< 0.4` and `≥ 0.6`.
Reusable dependencies: `Model.kfoldForrelation`, `Model.kfoldValid`.
Suggested tactics: `nlinarith` after unfolding `|Φ| ≤ 1/100` with `abs_le`. -/
/-- **Proposition 6** (arXiv:1411.5729v1, p. 13). The `k`-fold Forrelation algorithm
rejects with probability `1/4` and otherwise runs a controlled circuit whose
acceptance probability is `(1+Φ)/2`, hence accepts with probability
`(3/4)·((1+Φ)/2)`.  On the promise `|Φ| ≤ 1/100` this is `< 0.4`, and on
`Φ ≥ 3/5` it is `≥ 0.6`. -/
theorem kfold_Forrelation_solvable_error_four_tenths (Φ : ℝ) :
    (|Φ| ≤ 1 / 100 → (3 / 4) * ((1 + Φ) / 2) < 2 / 5) ∧
      (3 / 5 ≤ Φ → 3 / 5 ≤ (3 / 4) * ((1 + Φ) / 2)) := by
  constructor
  · intro h
    have h' := abs_le.mp h
    nlinarith [h'.1, h'.2]
  · intro h
    nlinarith

/-! ### Lemma 7 (p. 15) -/

/-- **Lemma 7** (arXiv:1411.5729v1, p. 15). Let the `v_i` be unit vectors with
`|⟨v_i|v_j⟩| ≤ ε` for `i ≠ j`, and let `w_j, β_j` be the Gram–Schmidt data.  If
`t ≤ 0.1/ε`, then `|⟨v_i|w_j⟩| ≤ ε + 2jε²` for `j < i` and `β_i ≤ 1 + 2iε²`. -/
/- NOTE (arXiv:1411.5729v1, Lemma 7, p. 15). Paper statement: for unit vectors with
`|⟨v_i|v_j⟩| ≤ ε` (`i ≠ j`) and `t ≤ 0.1/ε`, one has `|⟨v_i|w_j⟩| ≤ ε + 2jε²` and
`β_i ≤ 1 + 2iε²`; in particular `≤ 1.2ε` and `≤ 1 + 0.2ε`.
Proof route: induction on `j` in the Gram–Schmidt recursion, using the geometric
decay of the error terms; the factor `2` sums a geometric series with ratio `ε²`.
Lean gap: the Gram–Schmidt induction has not been carried out; the recursion is
available as the fields `Model.GramSchmidtData.w_rec` and `beta`.
Reusable dependencies: `Model.GramSchmidtData`, `Model.IsUnitVec`,
`Model.vinner`.
Suggested tactics: induction on `j` (via `Fin` well-founded recursion), bounding the
perturbation `∑_{k<j} ⟨v_i|w_k⟩⟨v_j|w_k⟩` with the inductive hypothesis and
`abs_sum_le_sum_abs`. -/
def gram_schmidt_lemma (N t : ℕ) (V : Fin t → Model.Vec N) (a : Fin t → ℝ) (G : Model.GramSchmidtData V a) (ε : ℝ) : Prop :=
  ∀ (hε : 0 < ε), ∀ (hunit : ∀ i, Model.IsUnitVec (V i)), ∀ (horth : ∀ i j : Fin t, i ≠ j → |Model.vinner (V i) (V j)| ≤ ε), ∀ (htε : (t : ℝ) ≤ 0.1 / ε), (∀ i j : Fin t, j < i →
      |Model.vinner (V i) (G.w j)| ≤ ε + 2 * ((j : ℕ) : ℝ) * ε ^ 2) ∧
      (∀ i : Fin t, G.beta i ≤ 1 + 2 * ((i : ℕ) : ℝ) * ε ^ 2)

/-! ### Theorem 9 (p. 18) -/

/-- **Theorem 9** (arXiv:1411.5729v1, p. 18). If `⟨f,g⟩` is drawn from the forrelated
measure `F` and `F = sgn ∘ f`, `G = sgn ∘ Hf`, then
`E[Φ_{F,G}] = 2/π ± O(log N / N)`, `N = 2^n`. -/
/- NOTE (arXiv:1411.5729v1, Theorem 9, p. 18). Paper statement:
`E_{f,g~F}[Φ_{F,G}] = 2/π ± O(log N/N)` with `F = sgn∘f`, `G = sgn∘g` and
`g = Hf` the Hadamard transform.
Proof route (Section 3.3): condition on the Gaussian vector; the Hadamard transform
makes `F` and `G` jointly Gaussian with correlation `1/√N` per coordinate; the
`2/π` constant comes from `E[sgn(X) sgn(Y)] = (2/π) arcsin ρ` with `ρ = 1/√N`, and
the error is a union bound over the `N` coordinates.
Lean gap: the Gaussian correlation computation and `E[sgn sgn] = (2/π)arcsin ρ`
are not formalised; the expectation is packaged as `Model.forrelatedExpectation`.
Reusable dependencies: `Model.forrelatedExpectation`, `Model.hadamardOf`,
`Model.gaussMeasure`, `Model.forrelation`.
Suggested tactics: rewrite the integral coordinate-wise using
`MeasureTheory.Integral.integral_fintype_prod_eq_prod` and the covariance formula
for `gaussianReal`. -/
def forrelated_measure_real_forrelation (n : ℕ) : Prop :=
  ∀ (hn : 1 ≤ n), ∃ C : ℝ, 0 < C ∧
      |Model.forrelatedExpectation n - 2 / Real.pi| ≤
        C * Real.log ((2 : ℝ) ^ n) / ((2 : ℝ) ^ n)

/-! ### Corollary 10 (p. 20) -/

/-- **Corollary 10** (arXiv:1411.5729v1, p. 20). A `T`-query algorithm solving
Forrelation with bounded error yields an `O(T)`-query algorithm solving Real
Forrelation with bounded error. -/
/- NOTE (arXiv:1411.5729v1, Corollary 10, p. 20). Paper statement: a `T`-query
Forrelation algorithm gives an `O(T)`-query Real Forrelation algorithm.
Proof route: run `A` itself on the real oracle; Theorem 9 and Markov's inequality
show that the sign-rounded instance is Forrelated with constant probability, and
`A`'s bounded error then transfers to constant bias.
Lean gap: Theorem 9's expectation bound (c008) and the Markov step are not
formalised; the transfer of the acceptance probability from the Boolean shadow to
the real oracle (`A.acceptProb ∘ sign ∘ o`) has not been written out.
Reusable dependencies: `Model.RealOracleTree`, `Model.SolvesRealForrelation`,
`Model.RandDecisionTree`, `Model.SolvesBoundedError`.
Suggested tactics: build `A'` with the same seeds and queries as `A`, with output
`A.output s (l.map (fun x => decide (x < 0)))`, and prove by induction on the
transcript length that the sign-rounded real transcript equals the Boolean one. -/
def real_forrelation_reduces_to_forrelation (n r T : ℕ) (A : Model.RandDecisionTree (Fin 2 × Model.Cube n) r T) : Prop :=
  ∀ (hA : Model.SolvesBoundedError A Model.forrelationAnswer Model.forrelationValid
      (1 / 10)), ∃ (r' T' : ℕ) (A' : Model.RealOracleTree (Fin 2 × Model.Cube n) r' T'),
      (T' : ℝ) ≤ 4 * (T : ℝ) ∧ Model.SolvesRealForrelation A' (1 / 5)

/-! ### Theorem 11 (p. 21) -/

/-- **Theorem 11** (arXiv:1411.5729v1, p. 21). If `|V| ≤ M` and all distinct test
vectors satisfy `|⟨v|w⟩| ≤ ε`, then any classical algorithm for Gaussian
Distinguishing with advantage `1/4` makes `Ω((1/ε)/log(M/ε))` queries. -/
/- NOTE (arXiv:1411.5729v1, Theorem 11, p. 21). Paper statement: for `|V| ≤ M` and
`|⟨v|w⟩| ≤ ε` on distinct vectors, any classical algorithm for Gaussian
Distinguishing must make `Ω((1/ε)/log(M/ε))` queries.  This is the general form of
Theorem 2, restated in Section 4.2 with the advantage formulation.
Proof route: as for Theorem 2, via the query-by-query hybrid bound
`|Pr_i[accept] - Pr_ii[accept]| = O(t²ε² + tε√(log M))`.
Lean gap: identical to c002 — the likelihood-ratio/hybrid argument is not
formalised; here the solver predicate is the advantage form
`Model.DistinguishesGaussian A V (1/4)`.
Reusable dependencies: `Model.DistinguishesGaussian`, `Model.gaussProb`,
`Model.RealOracleTree.acceptProb`, `Model.IsUnitVec`.
Suggested tactics: derive from `gaussian_distinguishing_lower_bound` (c002) by
converting the advantage form into the two threshold inequalities. -/
def gaussian_distinguishing_lower_bound_general (M : ℕ) (ε : ℝ) : Prop :=
  ∀ (hε : 0 < ε), ∃ c : ℝ, 0 < c ∧ ∀ (N r t : ℕ) (V : Fin M → Model.Vec N)
      (A : Model.RealOracleTree (Fin M) r t),
      (∀ i, Model.IsUnitVec (V i)) →
      (∀ i j : Fin M, i ≠ j → |Model.vinner (V i) (V j)| ≤ ε) →
      Model.DistinguishesGaussian A V (1 / 4) →
      c * (1 / ε) / Real.log ((M : ℝ) / ε) ≤ (t : ℝ)

/-! ### Proposition 12 (p. 24) -/

/- NOTE (arXiv:1411.5729v1, Proposition 12, p. 24). Paper statement: `D` is
well-behaved (`|a_i| ≤ √(2 ln 100t)` for all `i ∈ [t]`) with probability at least
`0.99` over `U`, because each `Pr[|a_i| > √(2 ln 100t)] < 1/(100t)`.
Proof route: the single-coordinate Gaussian tail bound plus the union bound; this
theorem proves the union-bound arithmetic and keeps the tail estimates `p i` as
hypotheses (they follow from the Gaussian law of `a_i`).
Lean gap: the tail estimate `Pr[|a_i| > √(2 ln 100t)] < 1/(100t)` for the specific
law of `a_i` is not derived from `Model.gaussLaw`.
Reusable dependencies: `Model.WellBehaved`, `Model.gaussProb`, `Model.gaussLaw`.
Suggested tactics: `Finset.sum_le_sum` against `1/(100t)` and `Finset.card_univ`,
then `field_simp`. -/
/-- **Proposition 12** (arXiv:1411.5729v1, p. 24). `D` is well-behaved with
probability at least `0.99` over the random unitary `U`: the failure probability of
the `i`-th coefficient is at most `1/(100t)`, so the union bound over the `t`
coefficients is at most `1/100`. -/
theorem well_behaved_measure_lower_bound (t : ℕ) (ht : 0 < t) (p : Fin t → ℝ)
    (hp : ∀ i, p i ≤ 1 / ((100 : ℝ) * (t : ℝ))) :
    1 - ∑ i, p i ≥ 99 / 100 := by
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hsum : ∑ i : Fin t, p i ≤ 1 / 100 := by
    calc ∑ i : Fin t, p i
        ≤ ∑ _i : Fin t, 1 / ((100 : ℝ) * (t : ℝ)) := Finset.sum_le_sum (fun i _ => hp i)
      _ = (t : ℝ) * (1 / ((100 : ℝ) * (t : ℝ))) := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = 1 / 100 := by
            field_simp
  linarith

/-! ### Lemma 13 (p. 24) -/

/-- **Lemma 13** (arXiv:1411.5729v1, p. 24). If `t ≤ √N/10` and `D` is well-behaved,
then `|c_i - b_i| = O(i √(log N / N))` for all `i ∈ [t]`. -/
/- NOTE (arXiv:1411.5729v1, Lemma 13, p. 24). Paper statement: for `t ≤ √N/10` and
`D` well-behaved, `|c_i - b_i| = O(i √(log N/N))`.
Proof route: expand the Gram–Schmidt recursion for `c_i - b_i`; each term is a
product of an inner product `|⟨v|w_j⟩| = O(ε)` (Lemma 7) with a coefficient of size
`O(√(log N))` (well-behavedness), and the errors sum geometrically.
Lean gap: the recursion comparison is not formalised; `Model.GramSchmidtData.c_rec`
and `b_rec` are available.
Reusable dependencies: `Model.GramSchmidtData`, `Model.WellBehaved`,
`Model.vinner`.
Suggested tactics: subtract the two recursions and bound the difference by
induction, using `gram_schmidt_lemma` (c007) for the inner products. -/
def coefficient_close_to_walsh (N t : ℕ) (V : Fin t → Model.Vec N) (a b c : Fin t → ℝ) : Prop :=
  ∀ (hV : ∀ i, Model.IsUnitVec (V i)), ∀ (hb : ∀ i, |b i| ≤ 1), ∀ (hwell : Model.WellBehaved a), ∀ (htN : (t : ℝ) ≤ Real.sqrt (N : ℝ) / 10), ∃ C : ℝ, 0 < C ∧ ∀ i : Fin t,
      |c i - b i| ≤ C * ((i : ℕ) : ℝ) *
        Real.sqrt (Real.log (N : ℝ) / (N : ℝ))

/-! ### Lemma 14 (p. 26) -/

/- NOTE (arXiv:1411.5729v1, Lemma 14, p. 26). Paper statement: if
`|r_i| ≤ 1/(1750√t)` for all `i`, then `|Σ_i r_i a_i| ≤ 0.01` with probability at
least `0.99` (via Lemma 8, Gaussian Azuma).  The paper then applies this with
`Δ' = Σ_i r_i(2a_i - r_i) ≤ 2Σ_i r_i a_i + Σ_i r_i² ≤ 0.02 + 1/1750²`.
This theorem proves the deterministic consequence, taking the Azuma bound
`|Σ_i r_i a_i| ≤ 0.01` as a hypothesis.
Lean gap: Gaussian Azuma's inequality (Lemma 8, Shamir [20]) is not formalised, so
the martingale tail bound is an explicit hypothesis here.
Reusable dependencies: `Model.residual`, `Model.DeltaF`, `Model.GramSchmidtData`.
Suggested tactics: rewrite `Σ r_i(2a_i - r_i)` as `2Σ r_i a_i - Σ r_i²` with
`Finset.sum_sub_distrib`, bound `Σ r_i²` by `t·(1/(1750√t))² = 1/1750²`, and
close with `abs_add`/`nlinarith`. -/
/-- **Lemma 14** (arXiv:1411.5729v1, p. 26). If `|r_i| ≤ 1/(1750√t)` for all `i` and
`|Σ_i r_i a_i| ≤ 0.01`, then the change `Δ' = Σ_i r_i(2a_i - r_i)` of the residual
computation is at most `0.03`: `Δ' ≤ 2Σ_i r_i a_i + Σ_i r_i²`. -/
theorem residual_small_linear_form (t : ℕ) (ht : 0 < t) (r a : Fin t → ℝ)
    (hr : ∀ i, |r i| ≤ 1 / (1750 * Real.sqrt (t : ℝ)))
    (htail : |∑ i, r i * a i| ≤ 1 / 100) :
    |∑ i, r i * (2 * a i - r i)| ≤ 3 / 100 := by
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hsq : ∑ i : Fin t, r i ^ 2 ≤ 1 / (1750 : ℝ) ^ 2 := by
    have key : ∀ i : Fin t, r i ^ 2 ≤ 1 / ((1750 : ℝ) ^ 2 * (t : ℝ)) := by
      intro i
      have hpos : (0 : ℝ) < 1750 * Real.sqrt (t : ℝ) := by positivity
      have h2 : (r i) ^ 2 ≤ (1 / (1750 * Real.sqrt (t : ℝ))) ^ 2 := by
        have h := abs_le.mp (hr i)
        nlinarith [h.1, h.2, hpos]
      calc (r i) ^ 2 ≤ (1 / (1750 * Real.sqrt (t : ℝ))) ^ 2 := h2
        _ = 1 / ((1750 : ℝ) ^ 2 * (t : ℝ)) := by
            have hs : Real.sqrt (t : ℝ) ^ 2 = (t : ℝ) := Real.sq_sqrt htR.le
            field_simp
            ring_nf
            rw [hs]
    calc ∑ i : Fin t, r i ^ 2
        ≤ ∑ _i : Fin t, 1 / ((1750 : ℝ) ^ 2 * (t : ℝ)) :=
          Finset.sum_le_sum (fun i _ => key i)
      _ = (t : ℝ) * (1 / ((1750 : ℝ) ^ 2 * (t : ℝ))) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = 1 / (1750 : ℝ) ^ 2 := by
          field_simp
  have hnonneg : (0 : ℝ) ≤ ∑ i : Fin t, r i ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hsplit : (∑ i : Fin t, r i * (2 * a i - r i)) =
      2 * (∑ i : Fin t, r i * a i) - ∑ i : Fin t, r i ^ 2 := by
    calc (∑ i : Fin t, r i * (2 * a i - r i))
        = ∑ i : Fin t, (2 * (r i * a i) - r i ^ 2) :=
          Finset.sum_congr rfl (fun i _ => by ring)
      _ = 2 * (∑ i : Fin t, r i * a i) - ∑ i : Fin t, r i ^ 2 := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsplit]
  have h1 := abs_le.mp htail
  have h2 : |2 * (∑ i : Fin t, r i * a i) - ∑ i : Fin t, r i ^ 2| ≤
      |2 * (∑ i : Fin t, r i * a i)| + |∑ i : Fin t, r i ^ 2| := abs_sub _ _
  rw [abs_mul, abs_two, abs_of_nonneg hnonneg] at h2
  nlinarith [h2, h1.1, h1.2, hsq]

/-! ### Proposition 15 (p. 27) -/

/-- **Proposition 15** (arXiv:1411.5729v1, p. 27). If `D` is well-behaved and
`t < √N/10`, then `|r_i| = O(i √(log N / N))` for all `i ∈ [t]`. -/
/- NOTE (arXiv:1411.5729v1, Proposition 15, p. 27). Paper statement: if `D` is
well-behaved and `t < √N/10`, then `|r_i| = O(i√(log N/N))` for all `i`.
Proof route: `r_i = a_i - c_i`, so the bound follows from
`|a_i - c_i| ≤ |a_i - b_i| + |b_i - c_i|`, where `|a_i - b_i| = O(√(log N))` from
well-behavedness and `|c_i - b_i| = O(i√(log N/N))` is Lemma 13.
Lean gap: the comparison of `a_i` and `b_i` through the Gram–Schmidt recursion is
not formalised.
Reusable dependencies: `Model.residual`, `Model.GramSchmidtData`,
`Model.WellBehaved`.
Suggested tactics: `|r i| ≤ |a i| + |c i|` and combine c012 with
`|a_i| ≤ √(2 ln 100t) ≤ O(√(log N))` for `t < √N`. -/
def residual_bound_well_behaved (N t : ℕ) (V : Fin t → Model.Vec N) (a : Fin t → ℝ) (G : Model.GramSchmidtData V a) : Prop :=
  ∀ (hwell : Model.WellBehaved a), ∀ (ht : (t : ℝ) < Real.sqrt (N : ℝ) / 10), ∃ C : ℝ, 0 < C ∧ ∀ i : Fin t,
      |Model.residual G i| ≤ C * ((i : ℕ) : ℝ) *
        Real.sqrt (Real.log (N : ℝ) / (N : ℝ))

/-! ### Lemma 16 (p. 28) -/

/-- **Lemma 16** (Central Martingale Lemma, arXiv:1411.5729v1, p. 28). If
`200 ≤ t < √N/10`, then with probability at least `0.99` over the Gaussian data
`a`, for every `i ∈ [t]` and every test vector `v`,
`|Σ_{j<i} ⟨v|w_j⟩ a_j| ≤ 30 √(i ln(Mt)/N)`. -/
/- NOTE (arXiv:1411.5729v1, Lemma 16, p. 28). Paper statement: for
`200 ≤ t < √N/10`, with probability at least `0.99`, for all `i` and all `v`,
`|Σ_{j<i}⟨v|w_j⟩a_j| ≤ 30√(i ln(Mt)/N)`, where `M` bounds the number of test
vectors.
Proof route: for fixed `i, v` the sum is Gaussian with variance
`O(i·ln(Mt)/N)`; a Gaussian tail bound plus a union bound over the `M` test vectors
and `t` values of `i` gives the claim.
Lean gap: the Gaussian tail estimate for the linear form and the union bound are not
formalised; the event is expressed with `Model.gaussProb` on the data vector.
Reusable dependencies: `Model.gaussProb`, `Model.vinner`, `Model.gaussLaw`.
Suggested tactics: compute the variance of `Σ_j ⟨v|w_j⟩ a_j` using orthonormality of
the `w_j`, apply a Gaussian tail bound (Chernoff), and union-bound over `(i, v)`. -/
def central_martingale_lemma (N t : ℕ) (V : Fin t → Model.Vec N) : Prop :=
  ∀ (ht : 200 ≤ t), ∀ (hV : ∀ i, Model.IsUnitVec (V i)), ∀ (htN : (t : ℝ) < Real.sqrt (N : ℝ) / 10), 99 / 100 ≤ Model.gaussProb t (fun a =>
      ∀ (i : Fin t) (v : Model.Vec N),
        |∑ j : Fin t, if j < i then Model.vinner v (V j) * a j else 0| ≤
          30 * Real.sqrt (((i : ℕ) : ℝ) * Real.log ((2 : ℝ) ^ N) * (t : ℝ) / (N : ℝ)))

/-! ### Lemma 17 (p. 28) -/

/-- **Lemma 17** (arXiv:1411.5729v1, p. 28). If `t < √N/10`, then with probability
at least `0.99` over the Gaussian data, `|r_i| = O(√(i log(Mt)/N))` for all
`i ∈ [t]`. -/
/- NOTE (arXiv:1411.5729v1, Lemma 17, p. 28). Paper statement: for `t < √N/10`,
with probability at least `0.99`, `|r_i| = O(√(i log(Mt)/N))` for all `i`.
Proof route: `r_i` is the residual after `i` Gram–Schmidt steps, so its size is
controlled by the martingale bound of Lemma 16 with `v = v_i` plus the diagonal term.
Lean gap: the martingale bound (c015) is not formalised; the claim is stated as a
high-probability event under `Model.gaussProb`.
Reusable dependencies: `Model.residual`, `Model.GramSchmidtData`, `Model.gaussProb`.
Suggested tactics: instantiate `central_martingale_lemma` (c015) with `v = V i` and
bound the remaining diagonal term by `O(1/√N)` using Lemma 7 (c007). -/
def residual_bound_with_high_probability (N t : ℕ) (V : Fin t → Model.Vec N) : Prop :=
  ∀ (hV : ∀ i, Model.IsUnitVec (V i)), ∀ (htN : (t : ℝ) < Real.sqrt (N : ℝ) / 10), ∃ C : ℝ, 0 < C ∧ 99 / 100 ≤ Model.gaussProb t (fun a =>
      ∀ (G : Model.GramSchmidtData V a) (i : Fin t),
        |Model.residual G i| ≤
          C * Real.sqrt (((i : ℕ) : ℝ) * Real.log ((2 : ℝ) ^ N) * (t : ℝ) / (N : ℝ)))

/-! ### Theorem 18 (p. 30) -/

/-- **Theorem 18** (arXiv:1411.5729v1, p. 30). A bounded block-multilinear polynomial
of degree `k` on `k` blocks of `m` variables each can be estimated to within `±ε`
with high probability using `O((N/ε²)^{1-1/k})` nonadaptive queries, `N = k·m`. -/
/- NOTE (arXiv:1411.5729v1, Theorem 18, p. 30). Paper statement: a bounded
block-multilinear polynomial `p : {-1,1}^N → [-1,1]` of degree `k` can be estimated
to within ±ε, with high probability, by nonadaptively querying
`O((N/ε²)^{1-1/k})` variables.
Proof route: the variable-splitting lemmas make `Λ_S` small; sampling a random
block then gives an unbiased estimator whose second moment is `O(ε²)`, and Chebyshev
yields the success probability.
Lean gap: the sampling estimator and its second-moment computation are not
formalised.  This is the "equal blocks" version of Theorem 4 with `N = k·m`.
Reusable dependencies: `Model.BlockMultilinear`, `Model.BlockMultilinear.Lambda`,
`Model.ClassicalEstimator.successProb`.
Suggested tactics: prove the second-moment identity for the sampled monomial and
apply Chebyshev, following Section 5.2. -/
def randomized_algorithm_estimates_block_multilinear (k m : ℕ) (p : Model.BlockMultilinear k (Fin m)) (ε : ℝ) : Prop :=
  ∀ (hk : 0 < k), ∀ (hm : 0 < m), ∀ (hp : p.Bounded), ∀ (hε : 0 < ε), ∃ C : ℝ, 0 < C ∧ ∀ (r t : ℕ) (E : Model.ClassicalEstimator (Fin m) r t),
      (∀ x : Fin m → Bool, 99 / 100 ≤ E.successProb x (p.evalDiagonal x) ε) →
      C * (((k * m : ℕ) : ℝ) / ε ^ 2) ^ (1 - 1 / (k : ℝ)) ≤ (t : ℝ)

/-! ### Lemma 20 (p. 30) -/

/-- **Lemma 20** (arXiv:1411.5729v1, p. 30). A `t`-query quantum algorithm gives a
block-multilinear polynomial of degree `2t` that is bounded in `[-1,1]` and whose
diagonal equals the algorithm's acceptance probability. -/
/- NOTE (arXiv:1411.5729v1, Lemma 20, p. 30). Paper statement: a `t`-query quantum
algorithm yields a block-multilinear polynomial `p` of degree `2t` with
`p(x,…,x) = Pr[A accepts x]` and `|p| ≤ 1` on the cube.
Proof route: Beals et al. [5] (Lemma 19) gives a degree-`2t` multilinear polynomial
for the acceptance probability; grouping the variables into `2t` blocks (one per
query) makes it block-multilinear.
Lean gap: no quantum circuit model or Beals-et-al. polynomial construction is
available; `Model.QuantumQueryAlgorithm` only stores the acceptance probabilities.
Reusable dependencies: `Model.QuantumQueryAlgorithm`,
`Model.BlockMultilinear.evalDiagonal`, `Model.BlockMultilinear.Bounded`.
Suggested tactics: instantiate the polynomial with coefficients read off the
algorithm's final state amplitudes, as in the proof of Lemma 19. -/
def quantum_to_block_multilinear_polynomial (N t : ℕ) (Q : Model.QuantumQueryAlgorithm (Fin N) t) : Prop :=
  ∃ p : Model.BlockMultilinear (2 * t) (Fin N),
      p.Bounded ∧ ∀ x : Fin N → Bool, p.evalDiagonal x = Q.accepts x

/-! ### Lemma 21 (p. 32) -/

/-- **Lemma 21** (arXiv:1411.5729v1, p. 32). For nonempty `S ⊆ [k]` and `δ > 0`
there is a sequence of variable-splittings introducing at most `1/δ` new variables
per block such that `Λ_S ≤ δ`. -/
/- NOTE (arXiv:1411.5729v1, Lemma 21, p. 32). Paper statement: for nonempty `S ⊆ [k]`
there are variable-splittings introducing at most `1/δ` new variables per block with
`Λ_S ≤ δ` for the refined polynomial.
Proof route (Section 5.1): split each variable in the blocks of `S` into copies with
equal weight; the `Λ_S` norm is convex in the splitting weights, so an averaging
argument produces weights achieving `Λ_S ≤ δ`.
Lean gap: the convexity/averaging argument over the splitting distribution is not
formalised; `Model.Refinement` and `Model.BlockMultilinear.Lambda` are available.
Reusable dependencies: `Model.Refinement`, `Model.BlockMultilinear.pullback`,
`Model.BlockMultilinear.Lambda`.
Suggested tactics: prove `Λ_S` is convex in `R`, apply the minimax/averaging
argument of the paper with uniform weights. -/
def one_variable_splitting_lambda_bound (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (p : Model.BlockMultilinear k ι) (S : Finset (Fin k)) (δ : ℝ) : Prop :=
  ∀ (hS : S.Nonempty), ∀ (hδ : 0 < δ), ∃ m : ℕ, ((m : ℝ) ≤ 1 / δ) ∧
      ∃ R : Model.Refinement k ι (ι × Fin (m + 1)),
        (p.pullback R).Lambda S ≤ δ

/-! ### Corollary 22 (p. 34) -/

/-- **Corollary 22** (arXiv:1411.5729v1, p. 34). Applying Lemma 21 to all `2^k`
subsets of `[k]` gives a refinement with at most `2^k/δ` new variables per block and
`Λ_{[k-1]} ≤ δ`. -/
/- NOTE (arXiv:1411.5729v1, Corollary 22, p. 34). Paper statement: there is a
sequence of splittings introducing at most `2^k/δ` new variables with
`Λ_{[k-1]} ≤ δ`.
Proof route: iterate Lemma 21 over all `S ⊆ [k]`; the `Λ_S` norms for different `S`
are simultaneously controlled by the product refinement.
Lean gap: the iteration over `2^k` subsets and the bookkeeping of the composed
refinement are not formalised.
Reusable dependencies: `Model.Refinement`, `Model.BlockMultilinear.Lambda`,
`Model.BlockMultilinear.pullback`.
Suggested tactics: induct over the power set of `Fin k`, composing refinements and
multiplying the bounds on the number of new variables. -/
def all_variables_splitting_lambda_bound (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (p : Model.BlockMultilinear k ι) (δ : ℝ) : Prop :=
  ∀ (hk : 0 < k), ∀ (hδ : 0 < δ), ∃ m : ℕ, ((m : ℝ) ≤ (2 : ℝ) ^ k / δ) ∧
      ∃ R : Model.Refinement k ι (ι × Fin (m + 1)),
        (p.pullback R).Lambda (Finset.univ.filter (fun j : Fin k => j.val + 1 < k)) ≤ δ

/-! ### Lemma 23 (p. 36) -/

/-- **Lemma 23** (arXiv:1411.5729v1, p. 36). If for every `S ⊆ [k]` with `|S| = ℓ` the
sum over pairs of coefficient products that agree on `S` and differ elsewhere is at
most `δ`, then the sum over all pairs in `T_ℓ` is at most `δ · C(k,ℓ)`. -/
/- NOTE (arXiv:1411.5729v1, Lemma 23, p. 36). Paper statement:
`Σ_{(i,i') ∈ T_ℓ} b_i b_{i'} ≤ δ C(k,ℓ)`, where `T_ℓ` consists of pairs of index
tuples agreeing exactly on some `S` with `|S| = ℓ`.
Proof route: decompose `T_ℓ` into the disjoint union of the `T_S` over `|S| = ℓ`,
and bound each inner sum by `δ` by completing squares (the paper's argument adds the
diagonal pairs and regroups).
Lean gap: the identification of `T_ℓ` with the disjoint union and the per-`S` bound
are not formalised; the sum decomposition is what this statement encodes.
Reusable dependencies: `Model.BlockMultilinear.coeff`, `Model.Refinement`.
Suggested tactics: `Finset.sum_biUnion` over the disjoint `T_S`, then
`Finset.sum_le_sum` with the per-`S` hypothesis. -/
def multipliers_bounded {k : ℕ} (ι : Type) [Fintype ι] [DecidableEq ι] (b : (Fin k → ι) → ℝ) (ℓ : ℕ) (δ : ℝ) : Prop :=
  ∀ (hδ : 0 ≤ δ), ∀ (hS : ∀ S ∈ (Finset.univ.filter (fun S : Finset (Fin k) => S.card = ℓ)),
      (∑ p ∈ (Finset.univ : Finset ((Fin k → ι) × (Fin k → ι))).filter
          (fun p => p.1 ≠ p.2 ∧ ∀ j ∈ S, p.1 j = p.2 j), b p.1 * b p.2) ≤ δ), (∑ p ∈ (Finset.univ : Finset ((Fin k → ι) × (Fin k → ι))).filter
        (fun p => p.1 ≠ p.2 ∧
          ∃ S ∈ (Finset.univ.filter (fun S : Finset (Fin k) => S.card = ℓ)),
            ∀ j ∈ S, p.1 j = p.2 j), b p.1 * b p.2)
      ≤ δ * ((Finset.univ.filter (fun S : Finset (Fin k) => S.card = ℓ)).card : ℝ)

/-! ### Theorem 25 (p. 38) -/

/-- **Theorem 25** (arXiv:1411.5729v1, p. 38). Explicit `k`-fold Forrelation with
`k = poly(n)` is `PromiseBQP`-hard: every `PromiseBQP` promise problem reduces to it. -/
/- NOTE (arXiv:1411.5729v1, Theorem 25, p. 38). Paper statement: explicit `k`-fold
Forrelation, for `k = poly(n)`, is `PromiseBQP`-hard (with `f_i(x) = (-1)^{C(x)}`
where `C` is a product of at most three bits of the circuit description).
Proof route: `QSim` is `PromiseBQP`-complete (Lemma 24); Theorem 26 reduces
`QSim_d` to explicit `(2d+1)`-fold Forrelation; `k = 2d+1 = poly(n)`.
Lean gap: the circuit-output encoding (`(-1)^{C(x)}`) and the polynomial-time
computability of the reduction are not modelled; `Model.ReducesTo` only records the
answer-preserving map.
Reusable dependencies: `Model.InPromiseBQP`, `Model.ReducesTo`,
`Model.kfoldAnswer`, `Model.kfoldValid`.
Suggested tactics: combine c023 (`QSim_d ≤_p` explicit `(2d+1)`-fold Forrelation)
with Lemma 24's `PromiseBQP`-completeness of `QSim`. -/
def explicit_kfold_Forrelation_PromiseBQP_hard (k n m : ℕ) : Prop :=
  ∀ (hk : 0 < k), ∀ (P : (Fin m → Bool) → Bool) (valid : (Fin m → Bool) → Prop),
      Model.InPromiseBQP P valid →
      Model.ReducesTo P valid
        (fun u : Fin k × Model.Cube n → Bool => Model.kfoldAnswer (fun j x => u (j, x)))
        (fun u => Model.kfoldValid (fun j x => u (j, x)))

/-! ### Theorem 26 (p. 40) -/

/-- **Theorem 26** (arXiv:1411.5729v1, p. 40). `QSim_d` is polynomial-time reducible
to explicit `(2d+1)`-fold Forrelation; hence every `PromiseBQP` problem reduces to
some explicit `k`-fold Forrelation instance. -/
/- NOTE (arXiv:1411.5729v1, Theorem 26, p. 40). Paper statement: `QSim_d` is
polynomial-time reducible to explicit `(2d+1)`-fold Forrelation.
Proof route: simulate the `d`-qubit circuit with `2d+1` layers; the acceptance
amplitude becomes a `(2d+1)`-fold twisted sum with multipliers `(-1)^{p(x)}` for a
degree-3 polynomial `p` (Section 6.3).
Lean gap: the `QSim` interaction model and the circuit-to-Forrelation encoding are
not formalised; the statement is phrased as a reduction from an abstract
`PromiseBQP` problem, which is the composition of Lemma 24 with the theorem.
Reusable dependencies: `Model.ReducesTo`, `Model.InPromiseBQP`,
`Model.kfoldAnswer`, `Model.kfoldValid`.
Suggested tactics: instantiate `Model.ReducesTo` with the explicit encoding map and
verify the promise is preserved by the twisted-sum identity. -/
def QSim_reduces_to_explicit_kfold_Forrelation (d n m : ℕ) : Prop :=
  ∀ (hd : 0 < d), ∀ (P : (Fin m → Bool) → Bool) (valid : (Fin m → Bool) → Prop),
      Model.InPromiseBQP P valid →
      Model.ReducesTo P valid
        (fun u : Fin (2 * d + 1) × Model.Cube n → Bool =>
          Model.kfoldAnswer (fun j x => u (j, x)))
        (fun u => Model.kfoldValid (fun j x => u (j, x)))

/-! ### Theorem 27 (p. 41) -/

/-- **Theorem 27** (arXiv:1411.5729v1, p. 41). For `ε = 0.01`, the randomized query
complexity of Fourier Sampling is `Ω(N/log N)`. -/
/- NOTE (arXiv:1411.5729v1, Theorem 27, p. 41). Paper statement: for `ε = 0.01`,
Fourier Sampling requires `Ω(N/log N)` randomized queries, where success means
`(1/2)Σ_y |p_{f,y} - f̂(y)²| ≤ ε` for all `f`.
Proof route: fix the hardest coordinate `y*` by an averaging argument, then show
that `t` queries cannot estimate `f̂(y*)²` (a degree-2 Fourier coefficient) to
constant error, using a polynomial-method/adversary bound.
Lean gap: the polynomial-method lower bound is not formalised; the success condition
is encoded by `Model.SolvesFourierSampling` with the explicit Fourier coefficient
`Model.walshCoeff`.
Reusable dependencies: `Model.RandCubeSampler`, `Model.SolvesFourierSampling`,
`Model.walshCoeff`.
Suggested tactics: prove the degree-2 Fourier coefficient cannot be approximated by
a `t`-query decision tree with `t = o(N/log N)`, via the polynomial method on the
Fourier spectrum. -/
def fourier_sampling_query_lower_bound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (n r T : ℕ) (A : Model.RandCubeSampler n r T),
      Model.SolvesFourierSampling A (1 / 100) →
      c * ((2 : ℝ) ^ n / Real.log ((2 : ℝ) ^ n)) ≤ (T : ℝ)

/-! ### Lemma 28 (p. 46) -/

/- NOTE (arXiv:1411.5729v1, Lemma 28, p. 46). Paper statement:
`Σ_i Inf_i[p] ≤ k Var[p]`.
Proof route: `Inf_i[p] = Σ_{S ∋ i} p̂(S)²` and `Var[p] = Σ_S p̂(S)²`, so the sum
over `i` counts each `p̂(S)²` exactly `|S|` times; `|S| ≤ k` for `S` in the support
of a degree-`k` polynomial.
Lean gap: the identification `Inf_i[p] = Σ_{S ∋ i} p̂(S)²` and
`Var[p] = Σ_S p̂(S)²` (the Fourier formulas for influence/variance of a Boolean
polynomial) is not formalised; the proof below establishes the Fourier-form
statement `Σ_i fourierInfluence i ≤ degree · fourierVariance`, from which the paper's
statement follows once that identification is supplied.
Reusable dependencies: `Model.CubePolynomial.fourierInfluence`,
`Model.CubePolynomial.fourierVariance`, `Model.CubePolynomial.degree`,
`Model.CubePolynomial.support_spec`.
Suggested tactics: exchange the two finite sums (`Finset.sum_comm`), rewrite
`Σ_i [i ∈ S] p̂(S)²` as `|S| p̂(S)²`, then bound `|S| ≤ degree` termwise. -/
/-- **Lemma 28** (arXiv:1411.5729v1, p. 46). For a real polynomial `p` of degree `k`,
the sum of the influences is at most `k` times the variance:
`Σ_i Inf_i[p] ≤ k Var[p]`.  In Fourier form,
`Σ_i Σ_{S ∋ i} p̂(S)² = Σ_S |S| p̂(S)² ≤ k Σ_S p̂(S)²`. -/
theorem sum_influence_le_degree_mul_variance (N : ℕ) (p : Model.CubePolynomial N) :
    ∑ i : Fin N, p.fourierInfluence i ≤ (p.degree : ℝ) * p.fourierVariance := by
  have hstep : ∀ i : Fin N, p.fourierInfluence i =
      ∑ S ∈ p.support, if i ∈ S then p.coeff S ^ 2 else 0 := by
    intro i
    simp only [Model.CubePolynomial.fourierInfluence, Finset.sum_filter]
  have hcount : ∀ S : Finset (Fin N),
      (∑ i : Fin N, (if i ∈ S then p.coeff S ^ 2 else 0)) =
        (S.card : ℝ) * p.coeff S ^ 2 := by
    intro S
    rw [← Finset.sum_filter]
    have h : (Finset.univ.filter (fun i : Fin N => i ∈ S)) = S := by
      ext i
      simp
    rw [h, Finset.sum_const, nsmul_eq_mul]
  have hswap : (∑ i : Fin N, ∑ S ∈ p.support, (if i ∈ S then p.coeff S ^ 2 else 0)) =
      ∑ S ∈ p.support, ∑ i : Fin N, (if i ∈ S then p.coeff S ^ 2 else 0) :=
    Finset.sum_comm
  calc ∑ i : Fin N, p.fourierInfluence i
      = ∑ S ∈ p.support, (S.card : ℝ) * p.coeff S ^ 2 := by
        rw [Finset.sum_congr rfl (fun i _ => hstep i), hswap]
        exact Finset.sum_congr rfl (fun S _ => hcount S)
    _ ≤ (p.degree : ℝ) * ∑ S ∈ p.support, p.coeff S ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro S hS
        have hsc : (S.card : ℝ) ≤ (p.degree : ℝ) := by
          have hle : S.card ≤ p.support.sup Finset.card := Finset.le_sup hS
          exact_mod_cast hle
        exact mul_le_mul_of_nonneg_right hsc (sq_nonneg _)
    _ = (p.degree : ℝ) * p.fourierVariance := by
        simp only [Model.CubePolynomial.fourierVariance]

/-! ### Corollary 30 (p. 46) -/

/-- **Corollary 30** (arXiv:1411.5729v1, p. 46). There is a constant `C > 0` such that
for every bounded degree-`k` polynomial with `Var[p] ≥ C/N`, some coordinate has
`Inf_i[p] ≥ (C/k) Var[p]²`. -/
/- NOTE (arXiv:1411.5729v1, Corollary 30, p. 46). Paper statement: there is `C > 0`
such that `‖p‖∞ ≤ 1` and `Var[p] ≥ C/N` imply `∃ i, Inf_i[p] ≥ (C/k)Var[p]²`.
Proof route: rescale `q := p/√Var[p]` so that `Var[q] = 1` and `‖q‖∞ ≤ 1/√Var[p]`;
then apply the Dinur–Friedgut–Kindler–O'Donnell theorem (Theorem 29): some `i` has
`Inf_i[q] ≥ C/(k·Var[p])`, i.e. `Inf_i[p] ≥ C·Var[p]²/k`.
Lean gap: Theorem 29 (Dinur et al. [14, Theorem 3]) is not available in this
development.
Reusable dependencies: `Model.CubePolynomial.variance`,
`Model.CubePolynomial.influence`, `Model.CubePolynomial.Bounded`,
`sum_influence_le_degree_mul_variance` (c025).
Suggested tactics: apply Theorem 29 to `p/√Var[p]`; the rescaling identity
`Inf_i[λp] = λ²Inf_i[p]` follows by unfolding the definitions. -/
def influence_degree_tradeoff (N k : ℕ) (p : Model.CubePolynomial N) (C : ℝ) : Prop :=
  ∀ (hC : 0 < C), ∀ (hdeg : p.degree ≤ k), ∀ (hbound : p.Bounded), ∀ (hvar : C / (N : ℝ) ≤ p.variance), ∃ i : Fin N, (C / (k : ℝ)) * p.variance ^ 2 ≤ p.influence i

/-! ### Corollary 32 (p. 47) -/

/-- **Corollary 32** (arXiv:1411.5729v1, p. 47). There is a constant `C > 0` such that
if a bounded degree-`k` polynomial satisfies `Σ_i p̂({i})² = v`, then some singleton
Fourier coefficient has `|p̂({i})| ≥ v/(Ck)`. -/
/- NOTE (arXiv:1411.5729v1, Corollary 32, p. 47). Paper statement: for a bounded real
polynomial `p : {-1,1}^N → [-1,1]` of degree `k` with `Σ_i p̂({i})² = v`, there is
`i` with `|p̂({i})| ≥ v/(Ck)`.
Proof route: rescale `q := p/√v`, so `Σ_i q̂({i})² = 1`; then apply Lemma 31 of
Dinur et al. [14] to get `|q̂({i})| ≥ 1/(Ck)` for some `i`, i.e.
`|p̂({i})| ≥ v/(Ck)`.
Lean gap: Lemma 31 of Dinur et al. [14] is not available in this development.
Reusable dependencies: `Model.CubePolynomial.coeff`, `Model.CubePolynomial.Bounded`,
`Model.CubePolynomial.degree`.
Suggested tactics: rescale and apply the Dinur et al. lemma; the scaling of Fourier
coefficients is immediate from the definition. -/
def low_influence_low_degree_bound (N k : ℕ) (p : Model.CubePolynomial N) (C v : ℝ) : Prop :=
  ∀ (hC : 0 < C), ∀ (hdeg : p.degree ≤ k), ∀ (hbound : p.Bounded), ∀ (hv : 0 ≤ v), ∀ (hsum : ∑ i : Fin N, p.coeff {i} ^ 2 = v), ∃ i : Fin N, v / (C * (k : ℝ)) ≤ |p.coeff {i}|

/-! ### Lemma 33 (p. 49) -/

/-- **Lemma 33** (arXiv:1411.5729v1, p. 49). There is `C > 0` such that if the total
influence satisfies `V[P] ≥ C log N / N`, then some coordinate has
`I_i[P] = Ω(V[P]²)`. -/
/- NOTE (arXiv:1411.5729v1, Lemma 33, p. 49). Paper statement: there is `C > 0` such
that `V[P] ≥ C log N/N` implies `∃ i, I_i[P] = Ω(V[P]²)`.
Proof route: substitute each variable `x_i = 1` with probability `1/2`; the resulting
polynomial `q` satisfies `|q̂({i}) - (1/2)Σ_{j≠i} a_{ij}| = O(√(I_i[P] log(1/ε)))`
with probability `1-ε` (Azuma, eq. (12)), and the `Σ_i q̂({i})² = 1` normalisation
(with the `V[P]` lower bound) forces some `i` to have a large `q̂({i})`, giving
`I_i[P] = Ω(V[P]²)`.
Lean gap: the random-substitution construction and Azuma's inequality are not
formalised.
Reusable dependencies: `Model.CubePolynomial.totalInfluence`,
`Model.CubePolynomial.influence`, `Model.CubePolynomial.variance`.
Suggested tactics: prove the concentration claim (12) via Azuma, then argue by
contradiction if all `I_i[P]` were `o(V[P]²)`. -/
def variance_implies_influential_coordinate (N : ℕ) (p : Model.CubePolynomial N) (C : ℝ) : Prop :=
  ∀ (hC : 0 < C), ∀ (hV : C * Real.log (N : ℝ) / (N : ℝ) ≤ p.totalInfluence), ∃ c : ℝ, 0 < c ∧ ∃ i : Fin N, c * p.totalInfluence ^ 2 ≤ p.influence i

/-! ### Lemma 34 (p. 51) -/

/-- **Lemma 34** (arXiv:1411.5729v1, p. 51). For uniformly random `f₁,…,f_k`,
`Pr[|Φ| ≥ t/√N] = O(1/t^t)`. -/
/- NOTE (arXiv:1411.5729v1, Lemma 34, p. 51). Paper statement: for uniformly random
`f₁,…,f_k : {0,1}^n → {-1,1}`, `Pr[|Φ_{f₁,…,f_k}| ≥ t/√N] = O(1/t^t)`.
Proof route: condition on `f₁,…,f_{k-1}`, write `Φ = (1/√N)Σ_x α_x f_k(x)` with
`|α_x| ≤ 1`; Hoeffding/Bennett for the sum of independent signs gives the
`t^{-t}` tail.
Lean gap: the Bennett/Hoeffding tail bound for the random-sign sum is not
formalised; the probability is expressed as a finite average over tuples.
Reusable dependencies: `Model.kfoldForrelation`, `Model.Cube n`.
Suggested tactics: prove the conditional tail bound for a Rademacher sum (Chernoff
with `exp` bounds) and average over `f₁,…,f_{k-1}`. -/
def kfold_Forrelation_second_moment (k n : ℕ) (t : ℝ) : Prop :=
  ∀ (hk : 0 < k), ∀ (ht : 1 ≤ t), ∃ C : ℝ, 0 < C ∧
      ((∑ f : Fin k → Model.Cube n → Bool,
          if t / Real.sqrt ((2 : ℝ) ^ n) ≤ |Model.kfoldForrelation f| then (1 : ℝ) else 0) /
        (2 : ℝ) ^ (k * 2 ^ n)) ≤ C / t ^ t

/-! ### Lemma 35 (p. 51) -/

/-- **Lemma 35** (arXiv:1411.5729v1, p. 51). With probability `1 - O(1/N)`, for all
`y`, `|Σ_{z : z·y = 0} Φ^{(z)²} - 1/2| ≤ log^{5/2}N/√N`. -/
/- NOTE (arXiv:1411.5729v1, Lemma 35, p. 51). Paper statement: for uniformly random
`f₁,…,f_k`, with probability `1 - O(1/N)`, for all `y ∈ {0,1}^n`,
`|Σ_{z: z·y=0} Φ^{(z)²} - 1/2| ≤ log^{5/2}N/√N`.
Proof route: the sum is the probability that the Forrelation algorithm's output
starts with `0`, an average of squared Gaussians; concentration of `χ²`-type
variables plus a union bound over the `N` values of `y`.
Lean gap: the `χ²` concentration argument is not formalised; the conclusion is
packaged as the second conjunct of `Model.GoodTuple`.
Reusable dependencies: `Model.kfoldForrelationAt`, `Model.GoodTuple`, `Model.dot`.
Suggested tactics: express the sum as `(1/N)Σ_x ((α⁰_x f_k(0x) + α¹_x f_k(1x))/√2)²`
and apply Bernstein's inequality (as in the paper), then union-bound over `y`. -/
def kfold_Forrelation_concentration (k n : ℕ) : Prop :=
  ∀ (hk : 0 < k), ∃ C : ℝ, 0 < C ∧
      (1 - C / (2 : ℝ) ^ n ≤
        (∑ f : Fin k → Model.Cube n → Bool,
          Model.indicator (Model.GoodTuple f)) / (2 : ℝ) ^ (k * 2 ^ n))

/-! ### Proposition 36 (p. 53) -/

/-- **Proposition 36** (arXiv:1411.5729v1, p. 53). With probability `1 - o(1/N)` over
`f₁,…,f_{k-2}` the multipliers `c_x` satisfy `|c_x| ≤ log N` for all `x`, and always
`Σ_x c_x² = N`. -/
/- NOTE (arXiv:1411.5729v1, Proposition 36, p. 53). Paper statement: with
probability `1 - o(1/N)`, `|c_x| ≤ log N` for all `x ∈ {0,1}^n`; also `Σ_x c_x² = N`.
Proof route: Lemma 34 with `t = log N` gives `Pr[|c_x| > log N] = O(N^{-log log N})`
per `x`, and the union bound over `N` values of `x` gives `o(1/N)`; the identity
`Σ_x c_x² = N` is Parseval.
Lean gap: the tail estimate of Lemma 34 (c029) and the Parseval identity are not
formalised; the multipliers are encoded as `Model.kfoldMultiplier`.
Reusable dependencies: `Model.kfoldMultiplier`, `Model.kfoldForrelationAt`.
Suggested tactics: apply `kfold_Forrelation_second_moment` (c029) with `t = log N`,
union-bound over `x`, and prove Parseval by expanding the twisted sum. -/
def multipliers_are_small (k n : ℕ) : Prop :=
  ∀ (hk : 2 ≤ k), ∃ C : ℝ, 0 < C ∧
      (1 - C / (2 : ℝ) ^ n ≤
        (∑ f : Fin (k - 2) → Model.Cube n → Bool,
          if ∀ x : Model.Cube n, |Model.kfoldMultiplier f x| ≤ Real.log ((2 : ℝ) ^ n)
          then (1 : ℝ) else 0) / (2 : ℝ) ^ ((k - 2) * 2 ^ n)) ∧
      ∀ f : Fin (k - 2) → Model.Cube n → Bool,
        ∑ x : Model.Cube n, Model.kfoldMultiplier f x ^ 2 = (2 : ℝ) ^ n

/-! ### Theorem 37 (p. 53) -/

/-- **Theorem 37** (arXiv:1411.5729v1, p. 53). If the multipliers satisfy
`|c_x| ≤ log N` for all `x`, then `E[Φ_{F,G}] = 2/π ± O(log³N/N)`. -/
/- NOTE (arXiv:1411.5729v1, Theorem 37, p. 53). Paper statement: for fixed
`f₁,…,f_{k-2}` with `|c_x| ≤ log N`, the `k`-fold Forrelation expectation over
`⟨f,g⟩` from the forrelated measure is `2/π ± O(log³N/N)`.
Proof route: condition on `f₁,…,f_{k-2}`; `⟨f,g⟩` is a Gaussian pair with per-
coordinate correlation `c_x/√N`, so `E[sgn sgn] = (2/π)arcsin(c_x/√N)`, and a Taylor
expansion of `arcsin` plus `|c_x| ≤ log N` and Parseval `Σ c_x² = N` gives the error
`O(log³N/N)`.
Lean gap: the `arcsin` expansion and the `E[sgn sgn]` computation are not
formalised; the expectation is `Model.kfoldForrelatedExpectation`.
Reusable dependencies: `Model.kfoldForrelatedExpectation`, `Model.kfoldMultiplier`,
`Model.gaussMeasure`, `Model.hadamardOf`.
Suggested tactics: use `Real.arcsin` Taylor bounds (`|arcsin z - z| ≤ C|z|³` for
`|z| ≤ 1/2`) and `Σ_x |c_x|³ ≤ log N · Σ_x c_x² = N log N`. -/
def kfold_forrelated_expectation_approx (k n : ℕ) (c : Model.Cube n → ℝ) : Prop :=
  ∀ (hk : 2 ≤ k), ∀ (hc : ∀ x, |c x| ≤ Real.log ((2 : ℝ) ^ n)), ∃ C : ℝ, 0 < C ∧
      |Model.kfoldForrelatedExpectation n c - 2 / Real.pi| ≤
        C * Real.log ((2 : ℝ) ^ n) ^ 3 / (2 : ℝ) ^ n

/-! ### Corollary 38 (p. 55) -/

/-- **Corollary 38** (arXiv:1411.5729v1, p. 55). A `T`-query algorithm solving
`k`-fold Forrelation with bounded error gives an `O(T)`-query algorithm solving
`k`-fold Real Forrelation with bounded error. -/
/- NOTE (arXiv:1411.5729v1, Corollary 38, p. 55). Paper statement: a `T`-query
`k`-fold Forrelation solver gives an `O(T)`-query `k`-fold Real Forrelation solver.
Proof route: identical to Corollary 10 (c009) with Theorem 37 (c032) replacing
Theorem 9: the sign-rounded instance is `k`-fold Forrelated with probability
`≥ 0.6`, so running the Boolean algorithm on the real oracle works.
Lean gap: Theorem 37 (c032) and the Markov step are not formalised; the transfer of
the acceptance probability to the real oracle is not written out.
Reusable dependencies: `Model.SolvesKfoldRealForrelation`, `Model.RealOracleTree`,
`Model.kfoldAnswer`, `Model.kfoldValid`.
Suggested tactics: same construction as c009 (same seeds and queries, output applied
to the sign-rounded transcript). -/
def kfold_real_forrelation_reduces (k n r T : ℕ) (A : Model.RandDecisionTree (Fin k × Model.Cube n) r T) : Prop :=
  ∀ (hA : Model.SolvesBoundedError A (fun u => Model.kfoldAnswer (fun j x => u (j, x)))
      (fun u => Model.kfoldValid (fun j x => u (j, x))) (1 / 10)), ∃ (r' T' : ℕ) (A' : Model.RealOracleTree (Fin k × Model.Cube n) r' T'),
      (T' : ℝ) ≤ 4 * (T : ℝ) ∧ Model.SolvesKfoldRealForrelation A' (1 / 5)

/-! ### Theorem 39 (p. 55) -/

/-- **Theorem 39** (arXiv:1411.5729v1, p. 55). `k`-fold Real Forrelation requires
`Ω(√N / log^{7/2} N)` randomized queries. -/
/- NOTE (arXiv:1411.5729v1, Theorem 39, p. 55). Paper statement: `k`-fold Real
Forrelation requires `Ω(√N/log^{7/2}N)` randomized queries.
Proof route: give away `f₁,…,f_{k-2}`; the problem becomes 2-fold Real Forrelation
with known multipliers `c_x`, which is an instance of Gaussian Distinguishing with
test vectors `{|i⟩} ∪ {|ψ_y⟩}`; combine Theorem 11 with Theorem 37's multiplier
bounds and the `log N` error terms for the `log^{7/2}` loss.
Lean gap: Theorem 11 (c010), Theorem 37 (c032) and the reduction of the `k`-fold
real problem to Gaussian Distinguishing are not formalised.
Reusable dependencies: `Model.SolvesKfoldRealForrelation`,
`gaussian_distinguishing_lower_bound_general` (c010).
Suggested tactics: instantiate c010 with the `2N` test vectors and `ε = 1/√N`, and
use c032 to control the multipliers, as in Section 9.3. -/
def kfold_real_forrelation_lower_bound (k n : ℕ) : Prop :=
  ∀ (hk : 2 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ (r T : ℕ) (A : Model.RealOracleTree (Fin k × Model.Cube n) r T),
      Model.SolvesKfoldRealForrelation A (1 / 10) →
      c * (Real.sqrt ((2 : ℝ) ^ n) / (Real.log ((2 : ℝ) ^ n)) ^ (7 / 2 : ℝ)) ≤
        (T : ℝ)

/-! ### Lemma 40 (p. 57) -/

/-- **Lemma 40** (arXiv:1411.5729v1, p. 57). If `Φ_{f₁,…,f_k} ≥ 0`, then for every
`ε > 0` there are `g_i` differing from `f_i` on at most `ε2^n` coordinates with
`Φ_{g₁,…,g_k} ≤ (1-ε)^k Φ_{f₁,…,f_k}`. -/
/- NOTE (arXiv:1411.5729v1, Lemma 40, p. 57). Paper statement: if `Φ ≥ 0`, then for
all `ε > 0` there are `g_i` with `Pr_x[f_i ≠ g_i] ≤ ε` and
`Φ_{g₁,…,g_k} ≤ (1-ε)^k Φ_f`.
Proof route: choose each `g_i` by re-randomising on a random `ε2^n`-subset and
copying `f_i` elsewhere; linearity of expectation gives `E[Φ_g] = (1-ε)^k Φ_f`, so
some choice achieves at most the expectation.
Lean gap: the probabilistic method step (existence from an expectation over the
re-randomisation) is not formalised; the statement is given in the equivalent
Hamming-distance form `hammingDist ≤ ε2^n`.
Reusable dependencies: `Model.kfoldForrelation`, `Model.hammingDist`.
Suggested tactics: prove `E[Φ_g] = (1-ε)^k Φ_f` by expanding the twisted sum and
using `E[g_i(x)] = (1-ε)f_i(x)`, then take the minimising choice. -/
def kfold_Forrelation_gentle_perturbation (k n : ℕ) (f : Fin k → Model.Cube n → Bool) (ε : ℝ) : Prop :=
  ∀ (hΦ : 0 ≤ Model.kfoldForrelation f), ∀ (hε : 0 < ε), ∀ (hε1 : ε ≤ 1), ∃ g : Fin k → Model.Cube n → Bool,
      (∀ i, (Model.hammingDist (f i) (g i) : ℝ) ≤ ε * (2 : ℝ) ^ n) ∧
        Model.kfoldForrelation g ≤ (1 - ε) ^ k * Model.kfoldForrelation f

/-! ### Proposition 41 (p. 58) -/

/-- **Proposition 41** (arXiv:1411.5729v1, p. 58). A uniformly random `k`-tuple is
good with probability at least `1 - δ_k`, where `δ_k → 0` as the constant `C_k`
increases; "good" means all multipliers are `≤ log N` and the Lemma-35 concentration
holds for every `y`. -/
/- NOTE (arXiv:1411.5729v1, Proposition 41, p. 58). Paper statement: a uniform random
`k`-tuple is good with probability at least `1 - δ_k`, where `δ_k → 0` (δ_k depends
on the constant `C_k` in the concentration bound).
Proof route: combine Lemma 34 (multiplier bound `|c_x| ≤ log N` via union bound)
with Lemma 35 (`χ²` concentration for all `y`); both hold with probability
`1 - O(1/N^{1-o(1)})`.
Lean gap: Lemmas 34/35 (c029, c030) are not formalised; "good" is encoded by
`Model.GoodTuple`.
Reusable dependencies: `Model.GoodTuple`, `Model.kfoldForrelationAt`,
`Model.kfoldMultiplier`.
Suggested tactics: intersect the two high-probability events of c029 and c030 and
apply the union bound. -/
def random_tuple_is_good (k n : ℕ) (δ : ℝ) : Prop :=
  ∀ (hk : 0 < k), ∀ (hδ : 0 < δ), ∃ Ck : ℝ, 0 < Ck ∧
      (1 - δ ≤
        (∑ f : Fin k → Model.Cube n → Bool,
          Model.indicator (Model.GoodTuple f)) / (2 : ℝ) ^ (k * 2 ^ n))

/-! ### Lemma 42 (p. 58) -/

/-- **Lemma 42** (arXiv:1411.5729v1, p. 58). If `⟨f₁,…,f_k⟩` is good and each `g_i`
differs from `f_i` on at most an `ε`-fraction of coordinates, then
`|Φ_f - Φ_g| = O(k √(ε log(1/ε)))`. -/
/- NOTE (arXiv:1411.5729v1, Lemma 42, p. 58). Paper statement: for a good `k`-tuple
and modifications with `Pr_x[f_i ≠ g_i] ≤ ε`, `|Φ_f - Φ_g| = O(k√(ε log(1/ε)))`.
Proof route: the hybrid argument (Bennett–Bernstein–Brassard–Vazirani): replace the
oracles one at a time; each replacement changes the twisted sum by
`O(√(ε log(1/ε)))` because good tuples have bounded multipliers and the `χ²`
concentration of Lemma 35.
Lean gap: the hybrid argument with the concentration bounds is not formalised.
Reusable dependencies: `Model.GoodTuple`, `Model.kfoldForrelation`,
`Model.hammingDist`.
Suggested tactics: `|Φ_f - Φ_g| ≤ Σ_i |Φ_{f₁,…,f_i,g_{i+1},…,g_k} - Φ_{f₁,…,g_i,…}|`
by the triangle inequality, and bound each term with the good-tuple concentration. -/
def good_tuple_perturbation_stable (k n : ℕ) (f g : Fin k → Model.Cube n → Bool) (ε : ℝ) : Prop :=
  ∀ (hgood : Model.GoodTuple f), ∀ (hε : 0 < ε), ∀ (hmod : ∀ i, (Model.hammingDist (f i) (g i) : ℝ) ≤ ε * (2 : ℝ) ^ n), ∃ C : ℝ, 0 < C ∧
      |Model.kfoldForrelation f - Model.kfoldForrelation g| ≤
        C * (k : ℝ) * Real.sqrt (ε * Real.log (1 / ε))

end Qatlib.Papers.Forrelation14.MainResults
