/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FiniteInformationDivergence
import Qatlib.Concepts.BlockEncoding.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.CStarAlgebra.Matrix

set_option backward.isDefEq.respectTransparency false

/-!
# QTopEigenvec24 — paper-layer vocabulary

Fixed source: arXiv:2405.14765 (2024), *A Quantum Speed-Up for Approximating the
Top Eigenvectors of a Matrix*.

This module collects the small amount of paper-local vocabulary shared by the
`MainResults` statements:

* `HasSparsity` — the paper's sparsity `s` (Definition 2.1 regime);
* `BlockEncoding` — Definition 2.6 (`(α,a,ε)`-block-encoding) with the concrete
  ancilla embedding of `Fin d` into `Fin (2^a) × Fin d`;
* `Cost` and `SoftO` — the paper's `Õ(·)` cost ledgers;
* `IsSubGaussian` — the paper's τ-sub-Gaussian moment-generating-function
  definition (§2.9, page 15);
* `ZLaw`, `discreteGaussianMass`, `ZLaw.tv` — laws on `ℤ`, the discrete
  Gaussian density `p_s(x) = exp(-πx²/s²)` and total variation distance, used
  by Theorem 2.29 / Corollary 2.28;
* `IsEigenpair`, `IsUnitVector` and `normedOverlap` — spectral notation.

Everything here is definitional; the individual claims live in the section
files and state their analytic content directly.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Classical

namespace Qatlib.Papers.QTopEigenvec24.MainResults

/-! ## Sparsity and block encodings -/

/-- The paper's sparsity condition: every row of `A` has at most `s` nonzero
entries (Definition 2.1 / the setting of Theorems 2.8 and 2.10). -/
def HasSparsity {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (s : ℕ) : Prop :=
  ∀ i : Fin d, (Finset.univ.filter (fun j : Fin d => A i j ≠ 0)).card ≤ s

/-- The ancilla embedding `i ↦ |0^a⟩|i⟩` used to read the encoded corner of a
block-encoding unitary. -/
def ancillaEmbed (a d : ℕ) : Fin d → Fin (2 ^ a) × Fin d := fun i => (0, i)

/-- Definition 2.6: a `(α, a, ε)`-block-encoding of `A` is an `(a + log d)`-qubit
unitary `U` whose `|0^a⟩`-corner is `ε`-close (spectral norm) to `A / α`.
The ancilla register is concretely `Fin (2^a)`. -/
def BlockEncoding {d a : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (U : Matrix (Fin (2 ^ a) × Fin d) (Fin (2 ^ a) × Fin d) ℂ) (α ε : ℝ) : Prop :=
  U ∈ Matrix.unitaryGroup (Fin (2 ^ a) × Fin d) ℂ ∧
    ‖A - α • (Matrix.of fun i j => U (ancillaEmbed a d i) (ancillaEmbed a d j))‖ ≤ ε

/-! ## Cost ledgers and soft-`O` -/

/-- A paper-level resource ledger.  `time` is total time and `queries` is the
number of oracle calls; both are real-valued accounting counters. -/
structure Cost where
  time : ℝ
  queries : ℝ

/-- `SoftO cost bound scale` records the paper's `Õ(bound)` notation: for every
`η > 0` the cost is at most `bound · (max scale 1)^η`, i.e. the bound is only
violated by a polynomial-logarithmic factor.  This makes the paper's
`(s/ε)^{o(1)}` and `polylog(·)` factors explicit parameters of the statement. -/
def SoftO (cost bound scale : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → cost ≤ bound * (max scale 1) ^ η

/-! ## Sub-Gaussian real laws (paper §2.9, page 15) -/

/-- A finite real random variable is `τ`-sub-Gaussian with parameter `α` when
its moment generating function satisfies `E[e^{tX}] ≤ e^τ e^{α²t²/2}` for all
`t` (paper §2.9, page 15). -/
def IsSubGaussian {Ω : Type} [Fintype Ω]
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist Ω)
    (X : Ω → ℝ) (τ α : ℝ) : Prop :=
  ∀ t : ℝ, p.expect (fun ω => Real.exp (t * X ω)) ≤
    Real.exp τ * Real.exp (α ^ 2 * t ^ 2 / 2)

/-! ## Laws on `ℤ` and discrete Gaussians (paper §2.9, page 16) -/

/-- A probability law on `ℤ` represented by its mass function. -/
structure ZLaw where
  /-- Probability mass at each integer. -/
  mass : ℤ → ℝ
  /-- Masses are nonnegative. -/
  nonneg : ∀ x : ℤ, 0 ≤ mass x
  /-- Total mass is one. -/
  sum_one : ∑' x : ℤ, mass x = 1

namespace ZLaw

/-- Total variation distance between two laws on `ℤ`. -/
def tv (p q : ZLaw) : ℝ := (∑' x : ℤ, |p.mass x - q.mass x|) / 2

end ZLaw

/-- The unnormalised discrete Gaussian density `p_s(x) = exp(-πx²/s²)`
(§2.9, page 16). -/
def discreteGaussianMass (s x : ℝ) : ℝ := Real.exp (- Real.pi * x ^ 2 / s ^ 2)

/-- The unnormalised discrete Gaussian density restricted to a finite window
`[-L, R]`, i.e. the numerator of `D_{ℤ,s}^{[-L,R]}`. -/
def truncatedGaussianMass (s : ℝ) (L R : ℕ) (x : ℤ) : ℝ :=
  if -(L : ℤ) ≤ x ∧ x ≤ (R : ℤ) then discreteGaussianMass s (x : ℝ) else 0

/-! ## Spectral notation -/

/-- `v` is a unit vector (`ℓ₂` norm one). -/
def IsUnitVector {d : ℕ} (v : Fin d → ℂ) : Prop := ‖v‖ = 1

/-- `v` is an eigenvector of `A` with eigenvalue `lam`. -/
def IsEigenpair {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) (lam : ℂ) : Prop :=
  v ≠ 0 ∧ A *ᵥ v = lam • v

/-- The absolute overlap `|⟨v, w⟩|` of two vectors. -/
def normedOverlap {d : ℕ} (v w : Fin d → ℂ) : ℝ :=
  ‖∑ i, star (v i) * w i‖

/-- `w` approximates the unit vector `v` with ℓ₂-error at most `ε`
(equivalently `|⟨w,v⟩| ≥ 1 - ε²/2`, page 28). -/
def L2Approximates {d : ℕ} (v w : Fin d → ℂ) (ε : ℝ) : Prop := ‖w - v‖ ≤ ε

/-! ## Finite probability helpers

The paper's probabilistic statements are stated over an abstract *finite*
probability space `Ω`, a law `p : FinDist Ω`, and random variables
`Ω → X`.  `pr` is the probability of an event; `prodLaw` is the `n`-fold
product law used for independent samples; `expectC` and `covVec` are the
complex expectation and covariance matrix of a vector-valued random variable.
-/

/-- Probability of an event under a finite law. -/
def pr {Ω : Type*} [Fintype Ω] (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist Ω)
    (A : Ω → Prop) [DecidablePred A] : ℝ :=
  ∑ ω ∈ Finset.univ.filter A, p.prob ω

/-- The `L`-fold product of a finite law (independent samples). -/
def prodLaw {X : Type*} [Fintype X] [DecidableEq X]
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (L : ℕ) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L → X) where
  prob := p.probOf
  nonneg ω := Finset.prod_nonneg fun i _ => p.nonneg (ω i)
  sum_one := p.sum_probOf L

/-- Complex expectation under a finite law. -/
noncomputable def expectC {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist Ω) (f : Ω → ℂ) : ℂ :=
  ∑ ω, (p.prob ω : ℂ) * f ω

/-- Covariance matrix of a vector-valued complex random variable. -/
noncomputable def covVec {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {d : ℕ}
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist Ω)
    (Z : Ω → Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j =>
    expectC p (fun ω => Z ω i * star (Z ω j)) -
      expectC p (fun ω => Z ω i) * star (expectC p (fun ω => Z ω j))

/-! ## Gaussian and spherical laws (paper §2.7–2.9)

Gaussian laws are characterised by their moment generating function on all
linear functionals, which is what identifies the i.i.d. standard normal
distribution among laws on a finite probability space.  The uniform law on the
sphere is characterised by rotation invariance together with support on the
unit sphere.
-/

/-- `v` has the law of a vector with i.i.d. standard normal coordinates: every
linear functional has the standard normal moment generating function. -/
def IsStdGaussianVectorLaw {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {d : ℕ}
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist Ω)
    (v : Ω → Fin d → ℝ) : Prop :=
  ∀ w : Fin d → ℝ,
    p.expect (fun ω => Real.exp (∑ i, w i * v ω i)) =
      Real.exp ((∑ i, w i ^ 2) / 2)

/-- `G` has the law of a matrix with i.i.d. standard normal entries: every
linear functional has the standard normal moment generating function. -/
def IsIIDStdGaussianMatrixLaw {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {n N : ℕ}
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist Ω)
    (G : Ω → Matrix (Fin n) (Fin N) ℝ) : Prop :=
  ∀ C : Matrix (Fin n) (Fin N) ℝ,
    p.expect (fun ω => Real.exp (∑ i, ∑ j, C i j * G ω i j)) =
      Real.exp ((∑ i, ∑ j, C i j ^ 2) / 2)

/-- The upper-triangular entries of `E` are independent centred Gaussian with
variance `σ²` (the paper's noise model, §5.1).  The lower-triangular entries of
the test matrix `C` are required to vanish, so only the upper-triangular
entries of `E` are constrained. -/
def HasUpperIIDGaussianNoise {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {d : ℕ}
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist Ω)
    (σ : ℝ) (E : Ω → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ C : Matrix (Fin d) (Fin d) ℝ, (∀ i j : Fin d, j < i → C i j = 0) →
    p.expect (fun ω => Real.exp (∑ i, ∑ j, C i j * E ω i j)) =
      Real.exp ((σ ^ 2 / 2) * ∑ i, ∑ j, C i j ^ 2)

/-- The paper's noisy symmetric matrix `A_{ij} = u_i u_j / d + e_{ij}` for
`i ≤ j`, mirrored below the diagonal. -/
noncomputable def noisyMatrix {d : ℕ} (u : Fin d → ℝ)
    (E : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => if i ≤ j then u i * u j / d + E i j else u j * u i / d + E j i

/-- A rotation-invariant law supported on the unit sphere is the uniform law
`u ∼ S^{d-1}` (§2.10). -/
def IsUniformSphereLaw {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {d : ℕ}
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist Ω)
    (u : Ω → Fin d → ℝ) : Prop :=
  (∀ ω, Real.sqrt (∑ i, (u ω i) ^ 2) = 1) ∧
    ∀ (O : Matrix (Fin d) (Fin d) ℝ), Oᵀ * O = 1 →
      ∀ S : Set (Fin d → ℝ),
        pr p (fun ω => u ω ∈ S) = pr p (fun ω => (O *ᵥ u ω) ∈ S)

/-! ## Born-rule sample laws (§3) -/

/-- The Born probability of a computational-basis outcome of the state
`|0̄⟩|ψ⟩ + |0̄^⊥⟩`: outcome `some i` has probability `|ψ_i|²`, and the
orthogonal leak has the remaining mass. -/
def bornProb {d : ℕ} (ψ : Fin d → ℂ) : Option (Fin d) → ℝ
  | some i => ‖ψ i‖ ^ 2
  | none => 1 - ∑ i, ‖ψ i‖ ^ 2

/-- `X` is the outcome of measuring `n` copies of `|0̄⟩|ψ⟩ + |0̄^⊥⟩` in the
computational basis (independent Born samples). -/
def IsBornSampleLaw {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {d n : ℕ}
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist Ω)
    (ψ : Fin d → ℂ) (X : Ω → Fin n → Option (Fin d)) : Prop :=
  ∀ s : Fin n → Option (Fin d), pr p (fun ω => X ω = s) = ∏ k, bornProb ψ (s k)

/-- The empirical frequency of outcome `|i⟩` in a list of measurement
outcomes: the paper's `s_i`. -/
def empiricalFreq {d n : ℕ} (X : Fin n → Option (Fin d)) (i : Fin d) : ℝ :=
  ((Finset.univ.filter (fun k => X k = some i)).card : ℝ) / n

/-- Pushforward of a finite law along a map (the law of `f` under `p`).
The codomain type is an explicit argument so that its `Fintype` instance is
resolved from the given type rather than by unification. -/
def pushforwardTo {Ω : Type*} [Fintype Ω] (Ω' : Type*) [Fintype Ω']
    (f : Ω → Ω') (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist Ω) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist Ω' where
  prob y := ∑ ω, if f ω = y then p.prob ω else 0
  nonneg y := Finset.sum_nonneg fun ω _ => by
    by_cases h : f ω = y
    · simpa [h] using p.nonneg ω
    · simp [h]
  sum_one := by
    rw [Finset.sum_comm]
    have h : ∀ ω : Ω, (∑ y : Ω', if f ω = y then p.prob ω else 0) = p.prob ω := by
      intro ω
      rw [Finset.sum_eq_single (f ω)]
      · simp
      · intro y _ hy; rw [if_neg (Ne.symm hy)]
      · intro hmem; exact absurd (Finset.mem_univ (f ω)) hmem
    rw [Finset.sum_congr rfl (fun ω _ => h ω), p.sum_one]

/-- Conditioning a finite law on an event of positive probability: the law of
`X | A` (paper Corollary 2.24). -/
def condLaw {Ω : Type*} [Fintype Ω]
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist Ω) (A : Ω → Prop)
    [DecidablePred A] (hA : 0 < pr p A) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist Ω where
  prob ω := if A ω then p.prob ω / pr p A else 0
  nonneg ω := by
    by_cases h : A ω
    · simp only [h, if_true]; exact div_nonneg (p.nonneg ω) (le_of_lt hA)
    · simp [h]
  sum_one := by
    have h1 : ∑ ω, (if A ω then p.prob ω / pr p A else 0)
        = ∑ ω ∈ Finset.univ.filter A, p.prob ω / pr p A := by
      rw [Finset.sum_filter]
    have h2 : ∑ ω ∈ Finset.univ.filter A, p.prob ω / pr p A
        = (∑ ω ∈ Finset.univ.filter A, p.prob ω) / pr p A := by
      rw [Finset.sum_div]
    rw [h1, h2]
    show (∑ ω ∈ Finset.univ.filter A, p.prob ω) / (∑ ω ∈ Finset.univ.filter A, p.prob ω) = 1
    exact div_self (ne_of_gt hA)

/-! ## Norms on `Fin d → ℝ` and Hamming distance -/

/-- The ℓ₂ norm of a real vector. -/
def ell2 {d : ℕ} (v : Fin d → ℝ) : ℝ := Real.sqrt (∑ i, (v i) ^ 2)

/-- The ℓ₂ norm of a complex vector. -/
def ell2C {d : ℕ} (v : Fin d → ℂ) : ℝ := Real.sqrt (∑ i, ‖v i‖ ^ 2)

/-- Hamming distance between two sign vectors encoded as Booleans. -/
def hammingDist {d : ℕ} (u w : Fin d → Bool) : ℕ :=
  (Finset.univ.filter (fun i => u i ≠ w i)).card

/-! ## Entry-query algorithms (§4–5)

An algorithm is modelled by its (worst-case) query count together with its
output map; for quantum algorithms the output is a finite law on answers.
This abstracts away the circuit description, which is not part of the
library's interfaces, while keeping the query ledger on which the paper's
upper and lower bounds are stated.
-/

/-- A classical algorithm with entry-query access to real `d × d` matrices. -/
structure RealClassicalAlgorithm (d : ℕ) (Out : Type*) where
  /-- Worst-case number of entry queries. -/
  queries : ℝ
  /-- The algorithm's output on a matrix. -/
  output : Matrix (Fin d) (Fin d) ℝ → Out

/-- A quantum algorithm with entry-query access to real `d × d` matrices,
whose (randomised) output is a finite law. -/
structure RealQuantumAlgorithm (d : ℕ) (Out : Type*) [Fintype Out] where
  /-- Worst-case number of entry queries. -/
  queries : ℝ
  /-- The output law on a matrix. -/
  output : Matrix (Fin d) (Fin d) ℝ →
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist Out

/-- A quantum algorithm with entry-query access to complex `d × d` matrices. -/
structure ComplexQuantumAlgorithm (d : ℕ) (Out : Type*) [Fintype Out] where
  /-- Worst-case number of entry queries. -/
  queries : ℝ
  /-- The output law on a matrix. -/
  output : Matrix (Fin d) (Fin d) ℂ →
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist Out


/-! ## Randomised algorithms and total-variation closeness

The paper's upper-bound claims assert the existence of an algorithm whose output
is a random variable.  `EstimatorAlgorithm` bundles the algorithm's finite
randomness (`Ω`, `law`), its cost ledger and its output random variable; the
input type is the object the algorithm is given (a matrix, a unitary, ...).
`realTV` is the paper's total variation distance between the laws of two real
random variables (page 8), computed over the union of their finite supports.
-/

/-- A randomised algorithm: finite randomness, a cost ledger, and an output
random variable depending on the algorithm's input. -/
structure EstimatorAlgorithm (In : Type) (Out : Type) where
  /-- The finite sample space of the algorithm's internal randomness. -/
  Ω : Type
  /-- Finiteness of the sample space. -/
  [instFintype : Fintype Ω]
  /-- Decidable equality on the sample space. -/
  [instDecidableEq : DecidableEq Ω]
  /-- The law of the algorithm's internal randomness. -/
  law : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist Ω
  /-- Resource ledger of the algorithm. -/
  cost : Cost
  /-- The algorithm's output random variable on input `A`. -/
  output : In → Ω → Out

namespace EstimatorAlgorithm

/-- Probability that the algorithm's output on input `A` satisfies `P`. -/
def pr {In Out : Type} (alg : EstimatorAlgorithm In Out) (A : In) (P : Out → Prop) : ℝ :=
  @Qatlib.Papers.QTopEigenvec24.MainResults.pr alg.Ω alg.instFintype alg.law
    (fun ω => P (alg.output A ω)) (Classical.decPred _)

end EstimatorAlgorithm

/-- Total variation distance between the laws of two real random variables
(paper page 8: `d_TV(P,Q) = ½ ∑_x |P(x) - Q(x)|`), summed over the union of the
two finite supports. -/
def realTV {Ω Ω' : Type} [Fintype Ω] [Fintype Ω']
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist Ω)
    (q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist Ω')
    (X : Ω → ℝ) (Y : Ω' → ℝ) : ℝ :=
  (∑ v ∈ (Finset.univ.image X ∪ Finset.univ.image Y),
      |pr p (fun ω => X ω = v) - pr q (fun ω' => Y ω' = v)|) / 2

/-- A real random variable together with the proof that it is `τ`-sub-Gaussian
with parameter `ε` (paper §2.8, page 15). -/
structure SubGaussianLaw where
  /-- Sample space. -/
  Ω : Type
  /-- Finiteness of the sample space. -/
  [instFintype : Fintype Ω]
  /-- Decidable equality on the sample space. -/
  [instDecidableEq : DecidableEq Ω]
  /-- The law. -/
  law : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist Ω
  /-- The random variable. -/
  X : Ω → ℝ
  /-- Sub-Gaussian slack parameter `τ`. -/
  τ : ℝ
  /-- Sub-Gaussian width parameter `ε`. -/
  ε : ℝ
  /-- The moment-generating-function bound. -/
  subG : IsSubGaussian law X τ ε

/-- `err` is `τ`-close (in total variation) to a `τ`-sub-Gaussian random
variable with parameter `ε` (paper's "τ-close to τ-subG(ε²)", page 15). -/
def IsCloseToSubGaussian {Ω : Type} [Fintype Ω]
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist Ω)
    (err : Ω → ℝ) (τ ε : ℝ) : Prop :=
  ∃ R : SubGaussianLaw, R.τ = τ ∧ R.ε = ε ∧
    @realTV Ω R.Ω (inferInstance) R.instFintype p R.law err R.X ≤ τ

/-- `err` is `δ`-close in total variation to the discrete Gaussian law on the
lattice `offset + step · ℤ` with width `width`.  The predicate requires `err`
to be lattice-valued, which makes the total variation distance an explicit
sum over lattice points. -/
def IsDeltaCloseToLatticeGaussian {Ω : Type} [Fintype Ω]
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist Ω)
    (err : Ω → ℝ) (step offset width δ : ℝ) : Prop :=
  (∀ ω, ∃ k : ℤ, err ω = offset + step * (k : ℝ)) ∧
    ∃ Zc : ℝ, 0 < Zc ∧
      (∑' k : ℤ, |pr p (fun ω => err ω = offset + step * (k : ℝ)) -
        discreteGaussianMass width (k : ℝ) / Zc|) / 2 ≤ δ

end Qatlib.Papers.QTopEigenvec24.MainResults
