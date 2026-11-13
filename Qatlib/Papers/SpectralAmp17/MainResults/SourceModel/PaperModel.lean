/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SpectralAmp17 — algebraic vocabulary and legacy resource metadata

`StandardForm` records a Hermitian matrix, a block identity, and real-valued
resource labels. It does not require unitarity of `U`, nonnegative counts, or a
circuit implementing `U`. Its fields alone cannot certify query complexity.
The resource specifications in sibling modules have no existence proofs.

The remaining definitions express polynomial evaluation, time evolution,
projector conditions, and approximation predicates. `BlackBoxSimulator` also
stores metadata only: its proposition-valued flag is not an execution model.
-/

open scoped Matrix.Norms.L2Operator BigOperators
open Polynomial

namespace Qatlib.Papers.SpectralAmp17.MainResults.SourceModel

universe u v

/-- Legacy algebraic block-encoding record inspired by Definition 1.
The block identity and norm bound are certified. Unitarity and the resource
labels are not certified by this structure; it is not a circuit witness. -/
structure StandardForm (S A : Type*) [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] where
  /-- The encoded system Hamiltonian. -/
  H : Matrix S S ℂ
  /-- The signal matrix on system ⊗ ancilla; unitarity is not a field. -/
  U : Matrix (S × A) (S × A) ℂ
  /-- Normalization `α ≥ ‖H‖`. -/
  α : ℝ
  /-- Positivity of the normalization. -/
  α_pos : 0 < α
  /-- `H` is Hermitian. -/
  hermitian : H.IsHermitian
  /-- `‖H‖ ≤ α`. -/
  norm_le : ‖H‖ ≤ α
  /-- The ancilla basis point `|0⟩_a`. -/
  ancilla0 : A
  /-- `(⟨0|_a ⊗ I) U (|0⟩_a ⊗ I) = H / α`. -/
  encodes : (fun s s' => U (s, ancilla0) (s', ancilla0))
              = ((α : ℂ))⁻¹ • H
  /-- Unconstrained query label; no execution count is certified. -/
  queries : ℝ
  /-- Unconstrained gate label; no execution count is certified. -/
  gates : ℝ

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

/-- Spectral multiplication `B[Ĥ] = ∑_{j=0}^{deg B} b_j Ĥ^j`
(Thm. 2, Thm. 4 of the paper). -/
noncomputable def polyEval (p : Polynomial ℝ) (H : Matrix S S ℂ) : Matrix S S ℂ :=
  ∑ j ∈ Finset.range (p.natDegree + 1), (p.coeff j : ℂ) • H ^ j

/-- The matrix exponential, as an absolutely convergent power series. -/
noncomputable def matrixExp (H : Matrix S S ℂ) : Matrix S S ℂ :=
  ∑' n : ℕ, ((n.factorial : ℝ)⁻¹ : ℂ) • H ^ n

/-- Time evolution `e^{-i Ĥ t}`. -/
noncomputable def timeEvolution (H : Matrix S S ℂ) (t : ℝ) : Matrix S S ℂ :=
  matrixExp ((-(Complex.I * (t : ℂ))) • H)

/-- The paper's parity condition: `B` is a parity-`(N mod 2)` polynomial. -/
def IsParityPoly (p : Polynomial ℝ) (N : ℕ) : Prop :=
  ∀ x : ℝ, p.eval (-x) = (-1 : ℝ) ^ (N % 2) * p.eval x

/-- Oddness of a real polynomial on `ℝ`. -/
def IsOddPoly (p : Polynomial ℝ) : Prop := ∀ x : ℝ, p.eval (-x) = -p.eval x

/-- Evenness of a real polynomial on `ℝ`. -/
def IsEvenPoly (p : Polynomial ℝ) : Prop := ∀ x : ℝ, p.eval (-x) = p.eval x

/-- The paper's sign function (Eq. 58): `sgn 0 = 1/2`. -/
noncomputable def signFun (x : ℝ) : ℝ :=
  if 0 < x then 1 else if x < 0 then -1 else 1 / 2

/-- The paper's rectangle function (Eq. 59): `rect(±1/2) = 1/2`. -/
noncomputable def rectFun (x : ℝ) : ℝ :=
  if |x| < 1 / 2 then 1 else if |x| > 1 / 2 then 0 else 1 / 2

/-- Concrete reading of the paper's `O(·)`: a universal positive constant. -/
def bigOConst (Q bound : ℝ) : Prop := ∃ C : ℝ, 0 < C ∧ Q ≤ C * bound

/-- Pointwise form of the paper's `max_{x ∈ s}` error condition. -/
def approxOn (p : Polynomial ℝ) (f : ℝ → ℝ) (s : Set ℝ) (ε : ℝ) : Prop :=
  ∀ x ∈ s, |p.eval x - f x| ≤ ε

/-- The bound `|p(x)| ≤ 1` for `x ∈ [-1,1]`. -/
def unitRangeOnUnit (p : Polynomial ℝ) : Prop :=
  ∀ x : ℝ, |x| ≤ 1 → |p.eval x| ≤ 1

/-- `Π̂` is the orthogonal projector onto the low-energy subspace of `Ĥ/α`
with energies in `[-1, -1+Δ]` (Thm. 3, Cor. 2). -/
def IsLowEnergyProjector (H : Matrix S S ℂ) (α Δ : ℝ) (P : Matrix S S ℂ) : Prop :=
  P * P = P ∧ P.IsHermitian ∧ P * H = H * P ∧
    ∀ ψ : S → ℂ, P.mulVec ψ = ψ →
      ∃ lam : ℝ, -1 ≤ lam ∧ lam ≤ -1 + Δ ∧
        ((α : ℂ))⁻¹ • (H.mulVec ψ) = (lam : ℂ) • ψ

/-- A normalized target vector whose multiple `λ t` is the `b = 0` part
of the first column of `G`. This predicate does not constrain the other
entries or certify unitarity or a complete state-preparation circuit. -/
def HasAmplitude {d : ℕ} [NeZero d] (G : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ)
    (lam : ℝ) : Prop :=
  ∃ t : Fin d → ℂ, (∑ i : Fin d, ‖t i‖ ^ 2) = 1 ∧
    (∀ i, G (i, 0) (0, 0) = (lam : ℂ) * t i)

/-- The `d`-sparse matrix-oracle model of Definition 2: the Hamiltonian has at
most `d` nonzero entries per row, with the named max-norm and induced 1-norm. -/
structure SparseAccess (n : Type*) [Fintype n] [DecidableEq n] where
  /-- The Hamiltonian. -/
  H : Matrix n n ℂ
  /-- Sparsity bound. -/
  d : ℕ
  /-- Max-norm `‖Ĥ‖_max = max_{jk} |Ĥ_jk|`. -/
  maxNorm : ℝ
  /-- Induced 1-norm `‖Ĥ‖₁ = max_j ∑_k |Ĥ_jk|`. -/
  oneNorm : ℝ
  hermitian : H.IsHermitian
  maxNorm_nonneg : 0 ≤ maxNorm
  oneNorm_nonneg : 0 ≤ oneNorm
  row_sparse : ∀ i, (Finset.univ.filter (fun j => H i j ≠ 0)).card ≤ d

/-- Legacy simulator metadata, without an oracle program or a link between
`queries` and `output`. The `usesSparseOracles` field stores a proposition,
not a proof of that proposition. This is not an algorithm certificate. -/
structure BlackBoxSimulator (n : Type*) [Fintype n] [DecidableEq n] where
  /-- Unconstrained reported sparse-oracle query label. -/
  queries : ℝ
  /-- Reported output operator, without an execution certificate. -/
  output : Matrix n n ℂ
  /-- Proposition-valued label; the record does not require its proof. -/
  usesSparseOracles : Prop

/-- `alg` approximates `e^{-iĤt}` to operator-norm error `ε`. -/
def ApproximatesTimeEvolution {n : Type*} [Fintype n] [DecidableEq n]
    (alg : BlackBoxSimulator n) (H : Matrix n n ℂ) (t ε : ℝ) : Prop :=
  ‖alg.output - timeEvolution H t‖ ≤ ε

end Qatlib.Papers.SpectralAmp17.MainResults.SourceModel
