/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceExactnessOpti

set_option backward.isDefEq.respectTransparency false

/-!
# GevreyGrad19 — paper-layer model (arXiv:1909.13528v1)

Cornelissen, *Quantum gradient estimation of Gevrey functions*, fixed
arXiv:1909.13528v1 (30 Sep 2019), PDF SHA-256 available in the task assets.

This module fixes the notation used by every claim file of the paper block:

* `Gevrey d c σ Ω` — Definition 2.1 (Gevrey class): smooth functions on the
  open set `Ω ⊆ ℝ^d` whose partial derivatives obey
  `|∂_α f x| ≤ ½ c^k (k!)^σ` for all `x ∈ Ω`, `k : ℕ` and multi-index
  `α : Fin k → Fin d`.
* `paperCentralCoeff m ℓ` — Definition 3.3 (central-difference coefficients),
  where `a_0^(2m) = 1` and, for `ℓ ≠ 0`, the coefficient equals the standard
  binomial form of Gilyén–Arunachalam–Wiebe (defined in the Frozen concept
  layer, with `a_0 = 0`); the paper explicitly flags this `ℓ = 0` discrepancy
  in footnote 13.
* `smoothing m f` — Definition 3.5 (2m-th order smoothing `f_(2m)`).
* `testFunction d c ε b` and `testClass d c ε` — Definition 4.1 (test
  functions and their class).
* `grad`, `loneError`, `successProb`, `queryCost` — the math objects of
  Definition 2.4 (quantum gradient estimation algorithms).  The paper only
  uses the law of `A(f)`, the success probability `P_A(f)` and the worst-case
  query count `T_A(f)`; we model exactly those.

Boundary: we do **not** build a Hilbert-space / circuit semantics of the phase
oracle, the fractional phase oracle, the block encoding or the QFT.  Claims
whose content is a circuit-synthesis or measurement-statistics statement are
stated over explicit, mathematical objects (a law of outcomes, a probability
mass function, a unitary matrix) and carry `sorry` where the synthesis /
Dirichlet-kernel argument is not formalised; this is recorded inline.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace Qatlib.Papers.GevreyGrad19.MainResults

/-- Paper Definition 2.1 (Gevrey class `G_{d,c,σ,Ω}`).  `f` belongs to the
class when it is `C^∞` on the open set `Ω` and every partial derivative of
order `k` at a point of `Ω` is bounded by `½ c^k (k!)^σ`.

The `k`-th partial derivative `∂_α f x` for `α : Fin k → Fin d` is read off the
`k`-th iterated Fréchet derivative evaluated on the unit basis vectors
`e_{α 0}, …, e_{α (k-1)}`; for `x` in the open set `Ω` where `f` is `C^∞` this
is the ordinary partial derivative of the paper. -/
def Gevrey (d : ℕ) (c σ : ℝ) (Ω : Set (Fin d → ℝ)) : Set ((Fin d → ℝ) → ℝ) :=
  { f | ContDiffOn ℝ ⊤ f Ω ∧
        ∀ x ∈ Ω, ∀ (k : ℕ), ∀ α : Fin k → Fin d,
          |iteratedFDeriv ℝ k f x (fun i => Pi.single (α i) (1 : ℝ))| ≤
            (1 / 2) * c ^ k * ((k.factorial : ℝ) ^ σ) }

/-- The `k`-fold unit-vector multi-index partial derivative of `f` at `x`. -/
def partialDeriv {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (k : ℕ)
    (α : Fin k → Fin d) : ℝ :=
  iteratedFDeriv ℝ k f x (fun i => Pi.single (α i) (1 : ℝ))

/-- Paper gradient `∇f(x)`, read as the vector of first partial derivatives. -/
def grad {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => partialDeriv f x 1 (fun _ => i)

/-- Paper Definition 3.3 (central-difference coefficients `a_ℓ^(2m)`).

For `ℓ ≠ 0` we use the standard binomial form
`(−1)^(|ℓ|−1)/ℓ · C(m,|ℓ|)/C(m+|ℓ|,|ℓ|)`, which is provably equal to the
paper's factorial formula `(−1)^(ℓ+1)(m!)^2 / (ℓ (m+ℓ)! (m−ℓ)!)` whenever
`−m ≤ ℓ ≤ m` (see `paperCentralCoeff_eq_source_formula` in
`CentralDifferenceProperties`).  The value at `ℓ = 0` is `1` as in the paper
(footnote 13: Gilyén et al. use `0` there, the paper uses `1`). -/
def paperCentralCoeff (m : ℕ) (ℓ : ℤ) : ℝ :=
  if ℓ = 0 then 1
  else Qatlib.Concepts.GradientOracle.CentralDiff.centralDiffCoeff m ℓ

/-- Paper Definition 3.5: the `2m`-th order smoothing
`f_(2m)(x) = Σ_{ℓ=−m}^m a_ℓ^(2m) f(ℓ x)`. -/
def smoothing {d : ℕ} (m : ℕ) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ ℓ ∈ Finset.Ico (-(m : ℤ)) ((m : ℤ) + 1),
    paperCentralCoeff m ℓ * f (fun i => (ℓ : ℝ) * x i)

/-- Paper Definition 4.1: test function `f_{d,c,ε,b}` for a vertex
`b : Fin d → ℝ` with entries `±1`:
`Σ_j (73 ε b_j / (c d)) sin(c x_j) ∏_{k≠j} cos(c x_k)`. -/
def testFunction (d : ℕ) (c ε : ℝ) (b : Fin d → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ j : Fin d,
    (73 * ε * b j / (c * d)) * Real.sin (c * x j) *
      ∏ k ∈ Finset.univ.erase j, Real.cos (c * x k)

/-- `b ∈ {−1,1}^d`. -/
def IsVertex {d : ℕ} (b : Fin d → ℝ) : Prop := ∀ j, b j = 1 ∨ b j = -1

/-- Paper Definition 4.1: the class `F_{d,c,ε} = {f_{d,c,ε,b} : b ∈ {−1,1}^d}`,
as a set of functions. -/
def testClass (d : ℕ) (c ε : ℝ) : Set ((Fin d → ℝ) → ℝ) :=
  { f | ∃ b : Fin d → ℝ, IsVertex b ∧ f = testFunction d c ε b }

/-- The `ℓ¹` distance between a candidate `g` and the true gradient `∇f(0)`. -/
def loneError {d : ℕ} (g : Fin d → ℝ) (f : (Fin d → ℝ) → ℝ) : ℝ :=
  ∑ i, |g i - grad f 0 i|

/-- A quantum gradient estimation algorithm, modelled by the law of its output
`A(f)` for each input function `f` (Definition 2.4, item 1).  Only the output
distribution is used by the paper's success-probability arguments. -/
structure GradientEstimator (d : ℕ) where
  /-- Law of `A(f)`, the random output vector of the algorithm on input `f`. -/
  law : ((Fin d → ℝ) → ℝ) → MeasureTheory.Measure (Fin d → ℝ)
  /-- `T_A(f)`, the worst-case number of controlled phase-oracle queries of `A`
  on input `f` (Definition 2.4, item 3).  Kept as an opaque real-valued
  function of the input; the lower-bound claims are statements about it. -/
  queryCost : ((Fin d → ℝ) → ℝ) → ℝ

/-- `P_A(f)`, the success probability of `A` on `f` at precision `ε` in `ℓ¹`
(Definition 2.4, item 4). -/
def successProb {d : ℕ} (A : GradientEstimator d) (f : (Fin d → ℝ) → ℝ)
    (ε : ℝ) : ℝ≥0∞ :=
  A.law f { g | loneError g f ≤ ε }

/-- `A` is an `ε`-precise `ℓ¹`-approximate gradient estimation algorithm for the
function class `F` with success probability lower bounded by `P`
(Definition 2.4). -/
def IsGradientEstimator {d : ℕ} (A : GradientEstimator d)
    (F : Set ((Fin d → ℝ) → ℝ)) (ε P : ℝ) : Prop :=
  ∀ f ∈ F, ENNReal.ofReal P ≤ successProb A f ε

/-- `T_A(f)`, the (worst-case) number of phase-oracle queries of `A` on `f`
(Definition 2.4, item 3), read off the algorithm record. -/
def queryCost {d : ℕ} (A : GradientEstimator d) (f : (Fin d → ℝ) → ℝ) : ℝ :=
  A.queryCost f

/-- Soft-`O` notation `O~(g)`: `f ≤ C g (log(g+2))^k` for some constant `C > 0`
and integer `k`, the paper's tilde-`O` hiding polylogarithmic factors. -/
def SoftO (f g : ℝ) : Prop :=
  ∃ k : ℕ, ∃ C : ℝ, 0 < C ∧ f ≤ C * g * (Real.log (g + 2)) ^ k


/-- Paper eq. (19)-type neighbour `b^{±j} = b − 2 b_j e_j`: flip the `j`-th
entry of a vertex `b : {−1,1}^d`. -/
def flipVertex {d : ℕ} (b : Fin d → ℝ) (j : Fin d) : Fin d → ℝ :=
  fun i => if i = j then -b i else b i

/-- Uniform average of `g` over a finite grid `G` (the expectation under the
uniform distribution `U(G)` of Algorithm 3.7 / Lemma 3.10). -/
def uniformMean {α : Type*} (G : Finset α) (g : α → ℝ) : ℝ :=
  (G.card : ℝ)⁻¹ * ∑ x ∈ G, g x

/-- Diagonal phase-oracle operator on the `N`-qubit computational basis
(Definition 2.3): `O_{f,G} |x⟩ = e^{i f(x)}|x⟩`, represented by the diagonal
matrix with phases `θ` on the chosen basis. -/
def phaseOracleMatrix {N : ℕ} (θ : Fin (2 ^ N) → ℝ) :
    Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ :=
  Matrix.diagonal (fun i => Complex.exp (Complex.I * (θ i : ℂ)))

/-- The ancilla-zero block `(⟨0|^{⊗N'} ⊗ I) U (|0⟩^{⊗N'} ⊗ I)` of a unitary on
`N ≥ n` qubits, as a `2^n × 2^n` matrix (ancilla-major ordering, so the
`s`-th computational basis vector of the `n`-qubit register sits at index `s`). -/
def ancillaZeroBlock {N n : ℕ} (h : n ≤ N) (U : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun i j =>
    U ⟨i, lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) h)⟩
      ⟨j, lt_of_lt_of_le j.isLt (Nat.pow_le_pow_right (by norm_num) h)⟩

/-- Spectral (operator `ℓ²`) norm of a square complex matrix, defined as the
supremum of `‖M x‖ / ‖x‖` over non-zero vectors.  This is the norm in which
the block-encoding error of [GSLW19, Definition 43] and Theorem 3.6 is
measured. -/
def spectralNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sSup { r : ℝ | ∃ x : Fin n → ℂ, x ≠ 0 ∧ r = ‖M.mulVec x‖ / ‖x‖ }

/-- Block-encoding error `‖(⟨0|⊗I) U (|0⟩⊗I) − T‖` in the spectral (operator)
norm (the quantity bounded by `δ` in Theorem 3.6 / Definition 43 of [GSLW19]). -/
def blockError {N n : ℕ} (h : n ≤ N) (U : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ)
    (T : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) : ℝ :=
  spectralNorm (ancillaZeroBlock h U - T)

/-- QFT amplitude of measurement outcome `b` for
`|ψ⟩ = 2^{-n/2} Σ_k e^{i a k}|k⟩` under the inverse QFT of eq. (13)
(the conjugate-phase convention of the paper).  The probability of `b` is
`qftOutcomeProb n a b = ‖qftAmplitude n a b‖²`. -/
def qftAmplitude (n : ℕ) (a : ℝ) (b : ℤ) : ℂ :=
  ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℝ) *
    (∑ k ∈ Finset.Ico (-(2 ^ (n - 1) : ℤ)) (2 ^ (n - 1) : ℤ),
      Complex.exp (Complex.I * ((a * (k : ℝ) - 2 * Real.pi * (k : ℝ) * (b : ℝ) /
        (2 : ℝ) ^ n : ℝ) : ℂ)))

/-- Measurement probability `P[b]` of outcome `b` in Theorem 3.12. -/
def qftOutcomeProb (n : ℕ) (a : ℝ) (b : ℤ) : ℝ :=
  Complex.normSq (qftAmplitude n a b)


/-- Vertex `b ∈ {−1,1}^d` encoded by a Boolean vector (`true ↦ 1`,
`false ↦ −1`); this makes the vertex set a `Finset` with cardinality `2^d`
(Lemma 4.4 / 4.5 count vertices). -/
def vertexOf {d : ℕ} (v : Fin d → Bool) : Fin d → ℝ :=
  fun i => if v i then 1 else -1

/-- `d^{-1/p}` in the paper's notation, with the convention `d^{-1/∞} = 1`
(`p = ⊤`).  Used for `ε′ = ε d^{-1/p}` (Algorithm 3.7, derived constant 1). -/
def invDExp (p : ℝ≥0∞) : ℝ :=
  if p = ⊤ then 0 else 1 / p.toReal

/-- The exponent `1 − 1/p` appearing in the hypothesis
`ε < c / (292 d^{1-1/p})` of Theorem 4.7, with `1 − 1/∞ = 1`. -/
def dExp (p : ℝ≥0∞) : ℝ :=
  if p = ⊤ then 1 else 1 - 1 / p.toReal

/-- The `ℓ^p` distance between a candidate gradient `g` and the true gradient
`∇f(0)`, with the `ℓ^∞` case `p = ⊤` as the maximum absolute coordinate
(Definition 2.4, general `p ∈ [1,∞]`). -/
def lpError {d : ℕ} (p : ℝ≥0∞) (g : Fin d → ℝ) (f : (Fin d → ℝ) → ℝ) : ℝ :=
  if p = ⊤ then sSup (Set.range fun i => |g i - grad f 0 i|)
  else (∑ i, |g i - grad f 0 i| ^ p.toReal) ^ (1 / p.toReal)

/-- `A` is an `ε`-precise `ℓ^p`-approximate gradient estimator for `F` with
success probability at least `P` (Definition 2.4, general `p`). -/
def IsGradientEstimatorP {d : ℕ} (A : GradientEstimator d)
    (F : Set ((Fin d → ℝ) → ℝ)) (p : ℝ≥0∞) (ε P : ℝ) : Prop :=
  ∀ f ∈ F, ENNReal.ofReal P ≤ A.law f { g | lpError p g f ≤ ε }

/-- Algorithm 3.7, derived constant 1: `ε′ = ε d^{-1/p}`. -/
def alg37epsPrime (d : ℕ) (p : ℝ≥0∞) (ε : ℝ) : ℝ :=
  ε / (d : ℝ) ^ invDExp p

/-- Algorithm 3.7, derived constant 2: `m = max(log(c d/ε′)^σ, 2)`. -/
def alg37m (c σ : ℝ) (d : ℕ) (p : ℝ≥0∞) (ε : ℝ) : ℕ :=
  max ⌈Real.log (c * d / alg37epsPrime d p ε) ^ σ⌉₊ 2

/-- Algorithm 3.7, derived constant 3:
`r = (2 e m c d^σ / 2^σ) · (272 π e m c d^σ / (2^σ ε′))^{1/(2m)}`. -/
def alg37r (c σ : ℝ) (d : ℕ) (p : ℝ≥0∞) (ε : ℝ) : ℝ :=
  let m : ℝ := (alg37m c σ d p ε : ℝ)
  let ep := alg37epsPrime d p ε
  (2 * Real.exp 1 * m * c * (d : ℝ) ^ σ / (2 : ℝ) ^ σ) *
    (272 * Real.pi * Real.exp 1 * m * c * (d : ℝ) ^ σ /
      ((2 : ℝ) ^ σ * ep)) ^ (1 / (2 * m))

/-- Algorithm 3.7, derived constant 4: `S = ⌈8π/(r ε′)⌉`. -/
def alg37S (c σ : ℝ) (d : ℕ) (p : ℝ≥0∞) (ε : ℝ) : ℕ :=
  ⌈8 * Real.pi / (alg37r c σ d p ε * alg37epsPrime d p ε)⌉₊

/-- Algorithm 3.7, derived constant 5: `n = ⌈log(12c/ε′)⌉`. -/
def alg37n (c : ℝ) (d : ℕ) (p : ℝ≥0∞) (ε : ℝ) : ℕ :=
  ⌈Real.log (12 * c / alg37epsPrime d p ε)⌉₊

/-- Algorithm 3.7, derived constant 9: `N = ⌈18 log(3d)⌉`. -/
def alg37N (d : ℕ) : ℕ :=
  ⌈18 * Real.log (3 * (d : ℝ))⌉₊

/-- Algorithm 3.7, derived constant 6–7: the grid
`G = {2 r k / 2^n + 1/2 : k ∈ {−2^{n−1},…,2^{n−1}−1}^d}`. -/
def alg37Grid (d n : ℕ) (r : ℝ) : Finset (Fin d → ℝ) := by
  classical
  exact (Fintype.piFinset
      (fun _ : Fin d => Finset.Ico (-(2 ^ (n - 1) : ℤ)) (2 ^ (n - 1) : ℤ))).image
    (fun k => fun i => 2 * r * (k i : ℝ) / (2 : ℝ) ^ n + 1 / 2)

/-- Number of phase-oracle queries used by one application of the smoothing
oracle of Theorem 3.6 at precision `δ`: `O~(m log(m/δ))`, rendered as the
explicit budget `97 m log(m/δ + 2)`. -/
def smoothingOracleQueries (m : ℕ) (δ : ℝ) : ℝ :=
  97 * (m : ℝ) * Real.log ((m : ℝ) / δ + 2)

/-- Total phase-oracle query count of Algorithm 3.7, using `N` repetitions of
an inner loop that applies the smoothing oracle `S` times at precision
`δ = 1/(12 √(2S))` (Algorithm 3.7, step 1; Theorem 3.8). -/
def alg37QueryCount (c σ : ℝ) (d : ℕ) (p : ℝ≥0∞) (ε : ℝ) : ℝ :=
  (alg37N d : ℝ) * (alg37S c σ d p ε : ℝ) *
    smoothingOracleQueries (alg37m c σ d p ε)
      (1 / (12 * Real.sqrt (2 * (alg37S c σ d p ε : ℝ))))

/-- One coordinate of the inner-loop output law (Algorithm 3.7, step 1,
items (c)–(e)): measuring outcome `k` with probability `qftOutcomeProb n a k`
and returning `g = scale · k` (`scale = 2π/(S r)`). -/
def alg37InnerCoordLaw (n : ℕ) (a scale : ℝ) : MeasureTheory.Measure ℝ :=
  ∑ k ∈ Finset.Ico (-(2 ^ (n - 1) : ℤ)) (2 ^ (n - 1) : ℤ),
    ENNReal.ofReal (qftOutcomeProb n a k) • MeasureTheory.Measure.dirac (scale * (k : ℝ))

/-- Inner-loop output law of Algorithm 3.7 for input `f`: the product over the
`d` coordinates of the QFT outcome laws with phase slope
`a_j = (S r / 2^n) ∂_j f(0)` and output scale `2π/(S r)`. -/
def alg37InnerLaw {d : ℕ} (n : ℕ) (S r : ℝ) (f : (Fin d → ℝ) → ℝ) :
    MeasureTheory.Measure (Fin d → ℝ) :=
  MeasureTheory.Measure.pi (fun j : Fin d =>
    alg37InnerCoordLaw n (S * r / (2 : ℝ) ^ n * grad f 0 j) (2 * Real.pi / (S * r)))

/-- Law of the coordinate-wise mean of `N` i.i.d. samples from `ν`
(Algorithm 3.7, step 2). -/
def meanLaw {d : ℕ} (N : ℕ) (ν : MeasureTheory.Measure (Fin d → ℝ)) :
    MeasureTheory.Measure (Fin d → ℝ) :=
  MeasureTheory.Measure.map
    (fun xs : Fin N → Fin d → ℝ => fun i => (N : ℝ)⁻¹ * ∑ t, xs t i)
    (MeasureTheory.Measure.pi (fun _ : Fin N => ν))

/-- Output law of Algorithm 3.7: coordinate-wise mean of `N` inner-loop
samples. -/
def alg37OutputLaw {d : ℕ} (c σ : ℝ) (p : ℝ≥0∞) (ε : ℝ)
    (f : (Fin d → ℝ) → ℝ) : MeasureTheory.Measure (Fin d → ℝ) :=
  meanLaw (alg37N d) (alg37InnerLaw (alg37n c d p ε) (alg37S c σ d p ε)
    (alg37r c σ d p ε) f)

/-- Embed an `n`-qubit vector into `N ≥ n` qubits with the ancilla register in
state `|0⟩` (ancilla-major ordering: indices `< 2^n` have ancilla zero). -/
def embedZeroVec {n N : ℕ} (h : n ≤ N) (v : Fin (2 ^ n) → ℂ) : Fin (2 ^ N) → ℂ :=
  fun i => if hi : (i : ℕ) < 2 ^ n then v ⟨i, hi⟩ else 0

/-- The uniform superposition vector `2^{-k/2} Σ_i |i⟩` on `k` qubits. -/
def uniformStateVec (k : ℕ) : Fin (2 ^ k) → ℂ :=
  fun _ => ((Real.sqrt ((2 : ℝ) ^ k))⁻¹ : ℝ)

/-- The state `|ψ̃⟩ = 2^{-nd/2} Σ_k e^{i (S r/2^n) ∇f(0)·k} |x_k⟩_G`, represented
on `nd` qubits with the computational-basis embedding `|x_k⟩_G ↦ |k⟩`; the
phase of index `i` is supplied by `θ`. -/
def idealStateVec (n d : ℕ) (θ : Fin (2 ^ (n * d)) → ℝ) : Fin (2 ^ (n * d)) → ℂ :=
  fun i => ((Real.sqrt ((2 : ℝ) ^ (n * d)))⁻¹ : ℝ) * Complex.exp (Complex.I * (θ i : ℂ))

end Qatlib.Papers.GevreyGrad19.MainResults
