/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Source model for Raz–Tal, *Oracle Separation of BQP and PH*

Ran Raz and Avishay Tal, ECCC TR18-107, May 31, 2018 (STOC 2019 / JACM 2022).
The statements below fix the paper's notation:

* `n : ℕ`, `N = 2 ^ n`, inputs are sign tables indexed by `Idx n = Fin n → Bool`
  (a bit-vector of length `n`, of cardinality `N`); `true` encodes the sign `-1`,
  `false` the sign `+1` (matching `realSign` of the frozen
  `BqpPh.Forrelation` development);
* `H_{ij} = (-1)^{⟨i,j⟩} / √N` is the normalized `N × N` Walsh–Hadamard matrix,
  `⟨i,j⟩ = ∑_k i_k j_k mod 2`;
* `G` (resp. `G'` for a parameter `ε`) is the zero-mean multivariate Gaussian on
  `ℝ^{2N}` with covariance `ε • [[I,H],[H,I]]` (Definition 4.1 / §4.2), constructed
  concretely with Mathlib's `ProbabilityTheory.multivariateGaussian`;
* `D` is obtained from `G'` by truncation to `[-1,1]` followed by independent sign
  sampling with expectation `trnc(z_i)` (§4.2);
* `φ(x,y) = N^{-1} ∑_{i,j} x_i H_{ij} y_j` is the Forrelation score of §6.

The file also fixes the lightweight interfaces used to state the algorithmic and
circuit-complexity conclusions: `QuantumAlgorithm` records the acceptance probability
together with the query and time counts, and `SignCircuit` records the output function
of a Boolean circuit together with its size and depth.  These interfaces only model the
quantities that appear in the paper's statements; they do not pretend to formalize a
unitary machine model or a gate-level circuit model.
-/

namespace Qatlib.Papers.BQPvsPHRaz18.OracleSep.SourceModel

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-! ## The index set and the Hadamard kernel -/

/-- The `n`-bit index type, of cardinality `N = 2 ^ n`. -/
abbrev Idx (n : ℕ) : Type := Fin n → Bool

/-- `N = 2 ^ n`. -/
def N (n : ℕ) : ℕ := 2 ^ n

/-- The card idx property in the paper model. -/
theorem card_idx (n : ℕ) : Fintype.card (Idx n) = N n := by
  simp [Idx, N]

/-- The Hadamard sign `(-1)^{⟨i,j⟩}`, where `⟨i,j⟩ = ∑ k, i k * j k` computed mod 2. -/
def hadSign {n : ℕ} (i j : Idx n) : ℝ :=
  if Even (Finset.univ.filter (fun k => i k && j k)).card then 1 else -1

/-- The normalized Hadamard entry `H_{ij} = (-1)^{⟨i,j⟩} / √N`. -/
def hadEntry {n : ℕ} (i j : Idx n) : ℝ :=
  hadSign i j * (Real.sqrt (N n : ℝ))⁻¹

/-- The `2N` coordinates: `Sum.inl i` is `x_i` and `Sum.inr j` is `y_j`. -/
abbrev PIdx (n : ℕ) : Type := Idx n ⊕ Idx n

/-- The sign of a Boolean input bit, with `true ↦ -1` and `false ↦ 1`.
This is definitionally the frozen `BqpPh.Forrelation.realSign`. -/
def signVal (b : Bool) : ℝ := if b then -1 else 1

/-! ## The Gaussian distributions `G` and `G'` and the distribution `D` -/

/-- The covariance matrix `ε • [[I, H], [H, I]]` of `G'`. -/
def forrelCov (n : ℕ) (ε : ℝ) : Matrix (PIdx n) (PIdx n) ℝ :=
  fun p q =>
    match p, q with
    | Sum.inl i, Sum.inl j => if i = j then ε else 0
    | Sum.inl i, Sum.inr j => ε * hadEntry i j
    | Sum.inr i, Sum.inl j => ε * hadEntry i j
    | Sum.inr i, Sum.inr j => if i = j then ε else 0

/-- `G'`: the zero-mean multivariate Gaussian on `ℝ^{2N}` with covariance
`ε • [[I,H],[H,I]]`.  For `ε = 1` this is the paper's `G`, and for the paper's
choice `ε = 1/(24 log N)` it is `G'` (§4.2).  When `ε ≥ 0` the matrix
`forrelCov n ε` is positive semidefinite and this is a genuine probability law. -/
def gaussianForrelation (n : ℕ) (ε : ℝ) : Measure (EuclideanSpace ℝ (PIdx n)) :=
  multivariateGaussian 0 (forrelCov n ε)

/-- Truncation `trnc(a) = min(1, max(-1, a))` to `[-1,1]` (§4.2). -/
def trnc (a : ℝ) : ℝ := min 1 (max (-1) a)

/-- Coordinatewise truncation of a `2N`-dimensional vector. -/
def trncVec {n : ℕ} (z : EuclideanSpace ℝ (PIdx n)) : EuclideanSpace ℝ (PIdx n) :=
  WithLp.toLp 2 (fun p => trnc (z p))

/-- The indicator of the truncation event `z ≠ trnc z`, as a real number. -/
def truncIndicator {n : ℕ} (z : EuclideanSpace ℝ (PIdx n)) : ℝ := by
  classical exact if trncVec z = z then 0 else 1

/-- The `ε` of §4.2, `ε = 1/(24 log N)`. -/
def eps (n : ℕ) : ℝ := 1 / (24 * Real.log (N n : ℝ))

/-- The fair coin on `Bool` (mass `p` on `true`, `1-p` on `false`). -/
def coin (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true + ENNReal.ofReal (1 - p) • Measure.dirac false

/-- The uniform distribution on the sign tables `α → {±1}`. -/
def uniformSigns (α : Type) [Fintype α] : Measure (α → Bool) :=
  Measure.pi (fun _ : α => coin (1 / 2))

/-- The distribution `D` of §4.2: draw `z ~ G'`, truncate coordinatewise, and sample
each output sign independently with expectation `trnc(z_i)`. -/
def forrelD (n : ℕ) (ε : ℝ) : Measure (PIdx n → Bool) :=
  (gaussianForrelation n ε).bind
    (fun z => Measure.pi (fun p => coin ((1 + trnc (z p)) / 2)))

/-- `D1 = D^{⊗m}`, the concatenation of `m` independent blocks with distribution `D`
(§8.2); inputs are sign tables on `m · 2N` bits. -/
def forrelD1 (n m : ℕ) (ε : ℝ) : Measure ((Fin m × PIdx n) → Bool) :=
  (Measure.pi (fun _ : Fin m => forrelD n ε)).map (fun w q => w q.1 q.2)

/-- `D0`, the tensor-product distribution of §8.3 over `(2N)^m` bits:
`z_{i₁…i_m} = ∏_j z^{(j)}_{i_j}` with `z^{(j)} ~ D` independent. -/
def forrelD0 (n m : ℕ) (ε : ℝ) : Measure ((Fin m → PIdx n) → Bool) :=
  (Measure.pi (fun _ : Fin m => forrelD n ε)).map
    (fun w q => by classical exact decide ((∏ j, signVal (w j (q j))) = 1))

/-- `Ũ`, the tensor product of `m` copies of the uniform distribution (§8.3). -/
def forrelU0 (n m : ℕ) : Measure ((Fin m → PIdx n) → Bool) :=
  (Measure.pi (fun _ : Fin m => uniformSigns (PIdx n))).map
    (fun w q => by classical exact decide ((∏ j, signVal (w j (q j))) = 1))

/-! ## The Forrelation score and Gaussian moments -/

/-- The Forrelation score `φ(x,y) = N^{-1} ∑_{i,j} x_i H_{ij} y_j` of §6. -/
def score {n : ℕ} (z : EuclideanSpace ℝ (PIdx n)) : ℝ :=
  ((N n : ℝ))⁻¹ * ∑ i, ∑ j, z (Sum.inl i) * hadEntry i j * z (Sum.inr j)

/-- `φ` on a pair of sign tables, used for the uniform claim (Claim 6.1). -/
def scoreSigns {n : ℕ} (x y : Idx n → Bool) : ℝ :=
  (∑ i, ∑ j, signVal (x i) * hadEntry i j * signVal (y j)) /
    (Fintype.card (Idx n) : ℝ)

/-- The Gaussian moment `Ĝ(S,T) = E_{(x,y)~G}[∏_{i∈S} x_i ∏_{j∈T} y_j]` (Claim 4.1). -/
def gaussMoment (n : ℕ) (S T : Finset (Idx n)) : ℝ :=
  ∫ z : EuclideanSpace ℝ (PIdx n),
    (∏ i ∈ S, z (Sum.inl i)) * (∏ j ∈ T, z (Sum.inr j))
    ∂(gaussianForrelation n 1)

/-! ## Algorithmic and circuit interfaces -/

/-- An algorithm on sign-table inputs indexed by `α`, recorded by its acceptance
probability and its query / runtime counts.  The two resource fields are the quantities
bounded in the paper's theorem statements. -/
structure QuantumAlgorithm (α : Type) where
  /-- Acceptance probability on each input. -/
  acceptProb : (α → Bool) → ℝ
  /-- Acceptance probabilities are probabilities. -/
  nonneg : ∀ x, 0 ≤ acceptProb x
  /-- Acceptance probabilities are probabilities. -/
  le_one : ∀ x, acceptProb x ≤ 1
  /-- Number of queries to the input. -/
  queries : ℕ
  /-- Running time. -/
  runtime : ℕ

/-- A Boolean circuit on sign-table inputs indexed by `α`, recorded by its output on
sign inputs together with its size and depth.  `value` is required to output `±1`. -/
structure SignCircuit (α : Type) where
  /-- Output of the circuit on a sign input. -/
  value : (α → Bool) → ℝ
  /-- A Boolean circuit outputs a sign. -/
  value_sign : ∀ x, value x = 1 ∨ value x = -1
  /-- Number of gates. -/
  size : ℕ
  /-- Circuit depth. -/
  depth : ℕ

/-- `s` is quasipoly in `N`, i.e. `s ≤ exp((log N)^k)` for some constant `k`. -/
def IsQuasiPolySize (s N : ℕ) : Prop :=
  ∃ k : ℕ, (s : ℝ) ≤ Real.exp ((Real.log (N : ℝ)) ^ k)

/-- The `S`-th Fourier coefficient `Â(S) = 2^{-m} ∑_x A(x) ∏_{i∈S} x_i` of a Boolean
function, with `x` ranging over sign inputs (Equation (4) of §7). -/
def fourierCoeff {α : Type} [Fintype α] [DecidableEq α]
    (f : (α → Bool) → ℝ) (S : Finset α) : ℝ :=
  ((2 : ℝ) ^ Fintype.card α)⁻¹ * ∑ x : α → Bool, f x * ∏ i ∈ S, signVal (x i)

/-- The multilinear extension `∑_S c(S) ∏_{i∈S} z_i` written in the Fourier basis
(Equation (4)). -/
def mlextOfCoeff {α : Type} [Fintype α] [DecidableEq α]
    (c : Finset α → ℝ) (z : α → ℝ) : ℝ :=
  ∑ S, c S * ∏ i ∈ S, z i

/-- The multilinear extension of a Boolean function, in its Fourier basis. -/
def mlext {α : Type} [Fintype α] [DecidableEq α]
    (f : (α → Bool) → ℝ) (z : α → ℝ) : ℝ :=
  mlextOfCoeff (fourierCoeff f) z

/-- The value of the multilinear extension at the origin, which is the uniform
expectation `E_{u~U}[A(u)]` (§7: `A(0) = Â(∅) = E[A]`). -/
def mlextZero {α : Type} [Fintype α] [DecidableEq α]
    (f : (α → Bool) → ℝ) : ℝ :=
  mlext f (fun _ => 0)

end

end Qatlib.Papers.BQPvsPHRaz18.OracleSep.SourceModel
