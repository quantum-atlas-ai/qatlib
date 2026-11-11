/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceModel — shared model for the NLTS paper layer

Anshu–Breuckmann–Nirkhe, *NLTS Hamiltonians from good quantum codes*,
fixed arXiv:2206.13228v4 (STOC 2023; v4 dated 2024-12-05),
PDF `prove/assets/2206.13228v4.pdf`.

This module fixes the source-level vocabulary shared by the four active claims:
bit strings over `F₂`, Hamming weight, classical binary codes, the clustering
property (Property 1, p.2), measurement distributions together with Fact 3
(p.4), and a local-Hamiltonian / circuit-depth interface used by Theorem 1
(p.2) and Theorem 5 (p.5).

Modeling notes (kept explicit so the statements are checkable against the paper):

* A bit string is `Fin n → ZMod 2`; `hammingWeight` counts nonzero coordinates,
  matching the paper's `|·|`.
* `BinaryCode n` is a `ZMod 2`-submodule of the ambient space, so it carries
  code membership; `Cxperp`/`Czperp` are passed explicitly instead of taking
  orthogonal complements, because the paper states Property 1 with the fixed
  classical codes `(Cx, Cz)`.
* `IsCloseTo`/`IsFarFrom` encode the paper's distance-to-code `|y|_C`:
  `|y|_C ≤ r` means some codeword `s ∈ C` has `|y + s| ≤ r`, and
  `|y|_C ≥ r` means every codeword does.
* A `LocalTerm` is a supported observable with an explicit matrix on the full
  register; the Hamiltonian is only used through its energy functional.  The
  checks/`X`-terms of a CSS code are turned into actual diagonal/flip matrices
  in `zPauliOp`/`xPauliOp` so `CssCode.localHamiltonian` is the paper's
  `H = Hx + Hz` construction rather than an unspecified black box.
* `CircuitComplexityModel` records the minimal circuit depth of a state as a
  function `depth : QubitState n → ℕ`; the paper's "circuit complexity" and
  "circuit depth" are both represented by this source quantity, and `IsOmegaLog`
  is the pointwise reading of `Ω(log n)`.

Boundary: this file contains definitions only; no claim is proved here.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.NLTSAnshu23.MainResults.Model

/-! ## Bit strings and Hamming weight -/

/-- Bit strings on `n` bits, the paper's ambient space `{0,1}^n ≅ F₂^n`. -/
abbrev BitString (n : ℕ) := Fin n → ZMod 2

/-- Hamming weight `|x|`: the number of nonzero coordinates. -/
def hammingWeight {n : ℕ} (x : BitString n) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ 0).card

/-- Weight of the syndrome `H x` of a vector under a parity-check matrix. -/
def syndromeWeight {m n : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    (x : BitString n) : ℕ :=
  hammingWeight (H *ᵥ x)

/-! ## Binary codes and distance to a code -/

/-- A binary linear code, i.e. a `ZMod 2`-submodule of `F₂^n`. -/
abbrev BinaryCode (n : ℕ) := Submodule (ZMod 2) (BitString n)

/-- `|y|_C ≤ r`: some codeword `s ∈ C` has Hamming distance `|y + s| ≤ r`. -/
abbrev IsCloseTo {n : ℕ} (C : BinaryCode n) (y : BitString n) (r : ℝ) : Prop :=
  ∃ s : BitString n, s ∈ C ∧ (hammingWeight (y + s) : ℝ) ≤ r

/-- `|y|_C ≥ r`: every codeword `s ∈ C` has Hamming distance `|y + s| ≥ r`. -/
abbrev IsFarFrom {n : ℕ} (C : BinaryCode n) (y : BitString n) (r : ℝ) : Prop :=
  ∀ s : BitString n, s ∈ C → r ≤ (hammingWeight (y + s) : ℝ)

/-! ## CSS codes and Property 1 (clustering of approximate code-words) -/

/-- A `[[n,k,d]]` CSS code presented by its two classical parity-check matrices
`Hx`, `Hz` (with `mx`, `mz` rows) and the four classical codes `Cx`, `Cz`,
`Cx^⊥`, `Cz^⊥` that appear in Property 1.  The parameters `n`, `k` are kept
explicit because they enter the quantitative bounds of Theorem 5. -/
structure CssCode (n k : ℕ) where
  /-- Number of `X`-type checks. -/
  mx : ℕ
  /-- Number of `Z`-type checks. -/
  mz : ℕ
  /-- `X`-type parity-check matrix. -/
  Hx : Matrix (Fin mx) (Fin n) (ZMod 2)
  /-- `Z`-type parity-check matrix. -/
  Hz : Matrix (Fin mz) (Fin n) (ZMod 2)
  /-- The classical `X`-code. -/
  Cx : BinaryCode n
  /-- The classical `Z`-code. -/
  Cz : BinaryCode n
  /-- The dual of the `X`-code, the Z-side stabilizer code. -/
  Cxperp : BinaryCode n
  /-- The dual of the `Z`-code, the X-side stabilizer code. -/
  Czperp : BinaryCode n

/-- Property 1 (p.2): clustering of approximate code-words.  For all sufficiently
small `0 ≤ δ < δ₀` and every vector `y`, membership in the approximate-codeword
set `G^z_δ` (resp. `G^x_δ`) forces either distance `≤ c₁δn` from the opposite
dual code or distance `≥ c₂n` from it. -/
abbrev CssCode.HasProperty1 {n k : ℕ} (code : CssCode n k)
    (δ0 c1 c2 : ℝ) : Prop :=
  ∀ δ : ℝ, 0 ≤ δ → δ < δ0 →
    (∀ y : BitString n,
        (hammingWeight (code.Hz *ᵥ y) : ℝ) ≤ δ * (code.mz : ℝ) →
        IsCloseTo code.Cxperp y (c1 * δ * (n : ℝ)) ∨
        IsFarFrom code.Cxperp y (c2 * (n : ℝ))) ∧
    (∀ y : BitString n,
        (hammingWeight (code.Hx *ᵥ y) : ℝ) ≤ δ * (code.mx : ℝ) →
        IsCloseTo code.Czperp y (c1 * δ * (n : ℝ)) ∨
        IsFarFrom code.Czperp y (c2 * (n : ℝ)))

/-! ## The local Hamiltonian associated with a CSS code

The paper associates to each row `w` of `H_z` the term `(1/2)(I - Z^w)` and to
each row of `H_x` the analogous `(1/2)(I - X^w)`.  We build those matrices
concretely on the computational basis. -/

/-- The Pauli `Z`-operator `Z^w` on the computational basis: it multiplies the
basis vector `|x⟩` by `(-1)^{w·x}`. -/
def zPauliOp {n : ℕ} (w : BitString n) : Matrix (BitString n) (BitString n) ℂ :=
  Matrix.diagonal fun x => if (∑ i, w i * x i) = 0 then (1 : ℂ) else -1

/-- The Pauli `X`-operator `X^w`: it maps the basis vector `|b⟩` to `|b + w⟩`. -/
def xPauliOp {n : ℕ} (w : BitString n) : Matrix (BitString n) (BitString n) ℂ :=
  fun a b => if a = b + w then (1 : ℂ) else 0

/-- A supported local observable on `n` qubits. -/
structure LocalTerm (n : ℕ) where
  /-- The support of the term. -/
  support : Finset (Fin n)
  /-- The full-register matrix of the term. -/
  op : Matrix (BitString n) (BitString n) ℂ

/-- A local Hamiltonian as a finite list of local terms. -/
structure LocalHamiltonian (n : ℕ) where
  /-- The local terms. -/
  terms : Finset (LocalTerm n)

/-- `Z`-check term `(1/2)(I - Z^w)` attached to a row `w` of `H_z`. -/
def zTerm {n : ℕ} (w : BitString n) : LocalTerm n where
  support := Finset.univ.filter fun i => w i ≠ 0
  op := (1 / 2 : ℂ) • ((1 : Matrix (BitString n) (BitString n) ℂ) - zPauliOp w)

/-- `X`-check term `(1/2)(I - X^w)` attached to a row `w` of `H_x`. -/
def xTerm {n : ℕ} (w : BitString n) : LocalTerm n where
  support := Finset.univ.filter fun i => w i ≠ 0
  op := (1 / 2 : ℂ) • ((1 : Matrix (BitString n) (BitString n) ℂ) - xPauliOp w)

/-- The local Hamiltonian `H = H_x + H_z` of a CSS code, as the union of the
terms attached to the rows of `H_x` and `H_z`. -/
def CssCode.localHamiltonian {n k : ℕ} (code : CssCode n k) : LocalHamiltonian n :=
  letI := Classical.decEq (LocalTerm n)
  { terms :=
      (Finset.univ.image fun i : Fin code.mz => zTerm fun q => code.Hz i q) ∪
      (Finset.univ.image fun i : Fin code.mx => xTerm fun q => code.Hx i q) }

/-- A term is Hermitian. -/
abbrev LocalTerm.IsHermitian {n : ℕ} (t : LocalTerm n) : Prop :=
  Matrix.conjTranspose t.op = t.op

/-- A term is positive semidefinite, tested on all normalized states. -/
abbrev LocalTerm.IsPsd {n : ℕ} (t : LocalTerm n) : Prop :=
  ∀ ψ : BitString n → ℂ, 0 ≤ (∑ a, ∑ b, star (ψ a) * t.op a b * ψ b).re

/-- Every term of the Hamiltonian is Hermitian. -/
abbrev LocalHamiltonian.IsHermitian {n : ℕ} (H : LocalHamiltonian n) : Prop :=
  ∀ t ∈ H.terms, t.IsHermitian

/-- Every term is positive semidefinite. -/
abbrev LocalHamiltonian.IsPsd {n : ℕ} (H : LocalHamiltonian n) : Prop :=
  ∀ t ∈ H.terms, t.IsPsd

/-- The terms pairwise commute. -/
abbrev LocalHamiltonian.Commuting {n : ℕ} (H : LocalHamiltonian n) : Prop :=
  ∀ t₁ ∈ H.terms, ∀ t₂ ∈ H.terms, t₁.op * t₂.op = t₂.op * t₁.op

/-- The Hamiltonian is `k`-local: every term has support at most `k`. -/
abbrev LocalHamiltonian.IsLocal {n : ℕ} (k : ℕ) (H : LocalHamiltonian n) : Prop :=
  ∀ t ∈ H.terms, t.support.card ≤ k

/-- Frustration-free: a normalized state annihilates every local term. -/
abbrev LocalHamiltonian.IsFrustrationFree {n : ℕ} (H : LocalHamiltonian n) : Prop :=
  ∃ ψ : BitString n → ℂ,
    (∑ x, Complex.normSq (ψ x)) = 1 ∧
    ∀ t ∈ H.terms, (∑ a, ∑ b, star (ψ a) * t.op a b * ψ b).re = 0

/-- The number of local terms. -/
def LocalHamiltonian.numTerms {n : ℕ} (H : LocalHamiltonian n) : ℕ := H.terms.card

/-! ## Energies and circuit depth -/

/-- Expectation `⟨ψ| M |ψ⟩` of a matrix in a pure state. -/
def expectation {n : ℕ} (ψ : BitString n → ℂ)
    (M : Matrix (BitString n) (BitString n) ℂ) : ℂ :=
  ∑ a, ∑ b, star (ψ a) * M a b * ψ b

/-- Real energy `tr(H ψ)` of a pure state under a local Hamiltonian. -/
def LocalHamiltonian.energy {n : ℕ} (H : LocalHamiltonian n)
    (ψ : BitString n → ℂ) : ℝ :=
  (∑ t ∈ H.terms, expectation ψ t.op).re

/-- The minimal circuit depth of a state, as a source-level quantity.  The
paper's circuit complexity/depth lower bounds are stated through this interface. -/
structure CircuitComplexityModel (n : ℕ) where
  /-- Minimal circuit depth of a state. -/
  depth : (BitString n → ℂ) → ℕ

/-- Pointwise form of `depth ψ ≥ Ω(log n)`. -/
abbrev IsOmegaLog {n : ℕ} (CM : CircuitComplexityModel n)
    (ψ : BitString n → ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ c * Real.log (n : ℝ) ≤ (CM.depth ψ : ℝ)

/-- `f n = Θ(n)` in the asymptotic sense, with an explicit threshold. -/
abbrev IsThetaN (f : ℕ → ℕ) : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → c₁ * (n : ℝ) ≤ (f n : ℝ) ∧ (f n : ℝ) ≤ c₂ * (n : ℝ)

/-- Theorem 5 (p.5): the explicit threshold
`(1/(400c₁)) · (min{mx,mz}/n) · min{((k-1)/(4n))², δ₀, c₂/2}` on the energy
density `ε`.  Kept as a definition so the quantitative and the constant-rate
parts of Theorem 5 use the same expression. -/
def epsilonBound (n k mx mz : ℕ) (δ0 c1 c2 : ℝ) : ℝ :=
  (1 / (400 * c1)) * ((min mx mz : ℝ) / (n : ℝ)) *
    min ((((k : ℝ) - 1) / (4 * (n : ℝ))) ^ 2) (min δ0 (c2 / 2))

/-! ## Measurement distributions and Fact 3 -/

/-- A real-valued distribution on `n`-bit strings. -/
abbrev Distribution (n : ℕ) := BitString n → ℝ

/-- The total mass of a finite set of bit strings. -/
def Distribution.mass {n : ℕ} (D : Distribution n) (S : Finset (BitString n)) : ℝ :=
  ∑ x ∈ S, D x

/-- A probability distribution. -/
abbrev Distribution.IsProbability {n : ℕ} (D : Distribution n) : Prop :=
  (∀ x, 0 ≤ D x) ∧ ∑ x, D x = 1

/-- A pair of measurement distributions, in the standard and Hadamard bases. -/
structure MeasurementPair (n : ℕ) where
  /-- Distribution obtained by measuring in the Hadamard (`X`) basis. -/
  Dx : Distribution n
  /-- Distribution obtained by measuring in the standard (`Z`) basis. -/
  Dz : Distribution n

/-- Fact 3 (p.4): the standard/Hadamard-basis uncertainty relation for the two
measurement distributions of a state.  This is a proved fact of the paper
(Appendix), recorded here as a predicate on the pair of distributions. -/
abbrev HasHadamardUncertainty {n : ℕ} (Dx Dz : Distribution n) : Prop :=
  ∀ S T : Finset (BitString n),
    Dx.mass T ≤
      2 * Real.sqrt (1 - Dz.mass S) +
        Real.sqrt ((S.card : ℝ) * (T.card : ℝ) / (2 : ℝ) ^ n)

end Qatlib.Papers.NLTSAnshu23.MainResults.Model
