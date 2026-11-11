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
# SpectralAmp17 — source model (paper vocabulary)

Fixed source: Low & Chuang, *Hamiltonian Simulation by Uniform Spectral
Amplification*, arXiv:1707.05391 (working text = the arXiv preprint; PDF at
`prove/assets/1707.05391.pdf`).

This module records the paper's vocabulary so that every active Claim of
`SpectralAmp17` can be stated as a Lean theorem whose hypotheses and conclusion
match the printed text:

* `StandardForm` — Definition 1 (`standard-form-(Ĥ, α, Û, d)`): the encoded
  Hamiltonian `H` is the `(0,0)`-block of the signal unitary `U` scaled by `α⁻¹`.
  `queries`/`gates` record the paper's cost parameters `Q` and the primitive-gate
  count.
* `polyEval` — spectral multiplication `B[Ĥ] = ∑ b_j Ĥ^j` (Thm. 2–4).
* `matrixExp` / `timeEvolution` — `e^{-iĤt}` used by Thm. 5, 6, 8, Lem. 8, Cor. 1–2.
* `IsParityPoly` — the parity condition of Thm. 4, 7, Lem. 4.
* `signFun`, `rectFun` — the paper's `sgn` (Eq. 58) and `rect` (Eq. 59).
* `IsLowEnergyProjector` — the projector `Π̂` of Thm. 3 / Cor. 2.
* `HasAmplitude` — the state-preparation condition of Thm. 7/8, Lem. 4 (`G|0⟩_a|0⟩_b = λ|t⟩_a|0⟩_b + √(1−λ²)|t⊥⟩_ab`).
* `bigOConst` — the paper's `O(·)` read as `Q ≤ C · bound`.

Everything here is definitional; the claim theorems live in the sibling blocks.
-/

open scoped Matrix.Norms.L2Operator BigOperators
open Polynomial

namespace Qatlib.Papers.SpectralAmp17.MainResults.SourceModel

universe u v

/-- Definition 1 of the paper: a `standard-form-(Ĥ, α, Û, d)` encoding.
`H` acts on the system register `S`, `U` jointly on `S × A` (`A` = the ancilla
register, `d = card A`), `α` is the normalization with `‖H‖ ≤ α`, and the
`(0,0)`-block of `U` in the ancilla basis point `ancilla0` equals `H / α`.
`queries` and `gates` are the paper's cost parameters for the circuit of `U`. -/
structure StandardForm (S A : Type*) [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] where
  /-- The encoded system Hamiltonian. -/
  H : Matrix S S ℂ
  /-- The signal unitary on system ⊗ ancilla. -/
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
  /-- Number of queries to the controlled signal unitary. -/
  queries : ℝ
  /-- Number of primitive quantum gates. -/
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

/-- The state-preparation condition of Thm. 7/8 and Lem. 4:
`G|0⟩_a|0⟩_b = λ|t⟩_a|0⟩_b + √(1−λ²)|t⊥⟩_ab`, i.e. the `b = 0` part of the
first column is exactly `λ t`, and the `b = 1` part lives on `t⊥`
(automatic from unitarity). -/
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

/-- A black-box simulation algorithm for Thm. 6: it carries the number of
queries it makes to the sparse matrix oracles of Definition 2, its output
operator, and the flag that it really uses only these oracles.  The paper's
lower bound quantifies over all such algorithms. -/
structure BlackBoxSimulator (n : Type*) [Fintype n] [DecidableEq n] where
  /-- Number of queries to the sparse oracles. -/
  queries : ℝ
  /-- The operator produced by the algorithm. -/
  output : Matrix n n ℂ
  /-- The algorithm is a sparse-oracle query algorithm (black-box model). -/
  usesSparseOracles : Prop

/-- `alg` approximates `e^{-iĤt}` to operator-norm error `ε`. -/
def ApproximatesTimeEvolution {n : Type*} [Fintype n] [DecidableEq n]
    (alg : BlackBoxSimulator n) (H : Matrix n n ℂ) (t ε : ℝ) : Prop :=
  ‖alg.output - timeEvolution H t‖ ≤ ε

end Qatlib.Papers.SpectralAmp17.MainResults.SourceModel
