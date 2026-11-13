/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMA2Sep26.MainResults.SourceModel
import Qatlib.Papers.QMA2Sep26.MainResults.ProductValue.SourceProductValue

set_option backward.isDefEq.respectTransparency false

/-!
# Shared complexity-theoretic vocabulary for QMA(2) vs QMA

This module defines acceptance specifications inspired by `QMA` and `QMA(2)`, the antisymmetric
entangled-subspace (AESD) promise problem, approximate disentanglers, and unitary-oracle
interfaces used in Sections 5 and 6 of [Bostanci et al., 2026][BostanciEtAl2026].
The legacy verifier records do not certify queries, probabilities or circuits.
`QueryModel` and the realization predicates require an externally supplied
operational semantics, matching both acceptance and the number of oracle calls.
The class predicates below are conditional query specifications with explicit
language, uniformity and polynomial bounds; no operational model, uniform circuit
family, or oracle separation is constructed in this module.

## Main definitions

* `IsAESDYes`, `IsAESDNo`, `NofD`, `dJ`: the AESD promise problem predicates and dimension
  parameters.
* `QMAVerifier`, `QMA2Verifier`, `canonicalAESDVerifier2`, `DecidesAESD1`, `DecidesAESD2`:
  single-witness and product-witness verifier interfaces for AESD.
* `Disentangler`, `IsDisentangler`: approximate disentangler parameter specification.
* `UnitaryOracle`, `InQMAOracle`, `InQMA2Oracle`, `QMAClass`, `QMA2Class`:
  dimension data and conditional language specifications in a supplied model.

## References

* [Bostanci et al., 2026][BostanciEtAl2026]
-/

namespace Qatlib.Papers.QMA2Sep26.MainResults

set_option autoImplicit false

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection

noncomputable section

variable {d : ℕ}

/- ## The AESD promise problem (Definition 5.2) -/

/-- A projector on `(C^d)^{⊗4}` is a **YES** instance of AESD when it is a
rank-one product projector `|α⟩⟨α|_{12} ⊗ |β⟩⟨β|_{34}` (Definition 5.2, the set
`Y_D`). -/
def IsAESDYes (P : Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ) : Prop :=
  ∃ α β : QState (Fin 2 → Fin d),
    Normalized α ∧ Normalized β ∧ P = outerProduct (tensorPair α β)

/-- A projector is a **NO** instance of AESD when it has product value at most
`1/3` — the soundness-side characterization of the antisymmetric family
`{Π_{5j−1}}` established by Lemma 4.1 (Definition 5.2 / §5, `N_D`). -/
def IsAESDNo (P : Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ) : Prop :=
  productValue P ≤ 1 / 3

/-- `N(D) = max { j ∈ ℕ : (5j−1)² ≤ D }`, the number of NO instances
(Equation (7), p. 13). -/
def NofD (D : ℕ) : ℕ := (Nat.sqrt D - 1) / 5

/-- The antisymmetric dimension `d_j = 5j − 1` (Equation (7)). -/
def dJ (j : ℕ) : ℕ := 5 * j - 1

/- ## Verifiers -/

/-- Single-witness acceptance specification. Neither its budget nor its real-valued
acceptance map is certified by a circuit or probability-range proof. -/
structure QMAVerifier (d : ℕ) where
  /-- Witness space dimension (not its logarithm in qubits). -/
  witnessDim : ℕ
  /-- Declared query budget; requires a separate realization certificate. -/
  queries : ℕ
  /-- completeness threshold -/
  completeness : ℝ
  /-- soundness threshold -/
  soundness : ℝ
  /-- acceptance probability as a function of the oracle projector and witness -/
  accept : Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ → QState (Fin witnessDim) → ℝ

/-- Product-witness acceptance specification, with an uncertified query label.
No physical acceptance rule is required by this record. -/
structure QMA2Verifier (d : ℕ) where
  /-- Declared query budget; requires a separate realization certificate. -/
  queries : ℕ
  /-- completeness threshold -/
  completeness : ℝ
  /-- soundness threshold -/
  soundness : ℝ
  /-- acceptance probability on a product witness `a ⊗ b` -/
  accept : Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ →
    QState (Fin 2 → Fin d) → QState (Fin 2 → Fin d) → ℝ

/-- Quadratic-form specification from Proposition 5.3, labeled with one query.
The label is not a certified query bound: implementation is specified separately
by `canonicalAESDVerifier2_statement`. -/
def canonicalAESDVerifier2 (d : ℕ) : QMA2Verifier d where
  queries := 1
  completeness := 1
  soundness := 1 / 3
  accept := fun P a b => realQuadForm P (tensorPair a b)

/-- Semantic correctness only, independent of `queries` (QMA(2) form): on every YES instance
some product witness is accepted with probability at least `completeness`; on
every NO instance every product witness is accepted with probability at most
`soundness`. -/
def DecidesAESD2 {d : ℕ} (V : QMA2Verifier d) : Prop :=
  (∀ P, IsAESDYes P → ∃ a b : QState (Fin 2 → Fin d),
      Normalized a ∧ Normalized b ∧ V.completeness ≤ V.accept P a b) ∧
  (∀ P, IsAESDNo P → ∀ a b : QState (Fin 2 → Fin d),
      Normalized a → Normalized b → V.accept P a b ≤ V.soundness)

/-- Semantic correctness only, independent of `queries` (QMA form): on every YES instance some
witness is accepted with probability at least `completeness`; on every NO
instance every witness is accepted with probability at most `soundness`. -/
def DecidesAESD1 {d : ℕ} (V : QMAVerifier d) : Prop :=
  (∀ P, IsAESDYes P → ∃ ψ : QState (Fin V.witnessDim),
      Normalized ψ ∧ V.completeness ≤ V.accept P ψ) ∧
  (∀ P, IsAESDNo P → ∀ ψ : QState (Fin V.witnessDim),
      Normalized ψ → V.accept P ψ ≤ V.soundness)

/-- Supplied query semantics. `calls` must list all charged oracle invocations;
`accept` must be the acceptance rule of the supplied programs. Physical validity
and the absence of other oracle access are obligations of the model provider,
not established by this interface. -/
structure QueryModel (Oracle Witness : Type) where
  Program : Type
  Call : Type
  calls : Program → List Call
  accept : Program → Oracle → Witness → ℝ

/-- Realization of a single-witness specification in a supplied query model. -/
def RealizesQMA {d : ℕ} (V : QMAVerifier d)
    (M : QueryModel (Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ)
      (QState (Fin V.witnessDim))) : Prop :=
  ∃ p : M.Program, (M.calls p).length = V.queries ∧
    ∀ P ψ, M.accept p P ψ = V.accept P ψ

/-- Realization of a product-witness specification in a supplied query model. -/
def RealizesQMA2 {d : ℕ} (V : QMA2Verifier d)
    (M : QueryModel (Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ)
      (QState (Fin 2 → Fin d) × QState (Fin 2 → Fin d))) : Prop :=
  ∃ p : M.Program, (M.calls p).length = V.queries ∧
    ∀ P a b, M.accept p P (a, b) = V.accept P a b

/-- **Statement only — not proved in Qatlib.** One-query realization of the
canonical quadratic-form rule in the supplied reflection-oracle model. -/
def canonicalAESDVerifier2_statement (d : ℕ)
    (M : QueryModel (Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ)
      (QState (Fin 2 → Fin d) × QState (Fin 2 → Fin d))) : Prop :=
  RealizesQMA2 (canonicalAESDVerifier2 d) M

/- ## Disentanglers (Definition 2.1) -/

/-- An approximate disentangler in the query model: `inputQubits = m` input
qubits, local output dimension `outputDim = D` (output lives in
`B(C^D ⊗ C^D)`), and the `(ε, δ)`-disentangler guarantees (Definition 2.1).
The channel itself is not modeled (only its input/output sizes and error
parameters matter in the query model, as the paper notes in footnote 4). -/
structure Disentangler where
  /-- number of input qubits `m` -/
  inputQubits : ℕ
  /-- local output dimension `D` -/
  outputDim : ℕ
  /-- error `ε` on the "close to separable" side -/
  epsilon : ℝ
  /-- error `δ` on the "approximately surjective" side -/
  delta : ℝ

/-- Parameter matching only; this does not assert a channel or either
approximate-disentangler guarantee. -/
def IsDisentangler (Λ : Disentangler) (ε δ : ℝ) (D : ℕ) : Prop :=
  Λ.epsilon = ε ∧ Λ.delta = δ ∧ Λ.outputDim = D

/- ## Unitary oracles and relativized classes (Theorem 5.1) -/

/-- A unitary oracle `U = (U^{(n)})_{n ≥ 1}`: the `n`-th component acts on one
control qubit and two `n`-qubit registers, i.e. on a `2·(2^{2n+1})`-dimensional
space.  We record only its ambient dimension per input length. -/
structure UnitaryOracle where
  /-- ambient dimension of the `n`-th component -/
  dim : ℕ → ℕ

/-- External oracle interpretation and uniformity contracts. `projector n` must
interpret the actual oracle component, and `uniform1/2` must enforce uniform
polynomial circuit size and witness length. The dimension-only `UnitaryOracle`
record cannot establish these facts; no instance of this contract is built here. -/
structure OracleClassModel (U : UnitaryOracle) where
  projector : (n : ℕ) → Matrix (Fin 4 → Fin (2 ^ n)) (Fin 4 → Fin (2 ^ n)) ℂ
  single : (n w : ℕ) → QueryModel
    (Matrix (Fin 4 → Fin (2 ^ n)) (Fin 4 → Fin (2 ^ n)) ℂ) (QState (Fin w))
  product : (n : ℕ) → QueryModel
    (Matrix (Fin 4 → Fin (2 ^ n)) (Fin 4 → Fin (2 ^ n)) ℂ)
    (QState (Fin 2 → Fin (2 ^ n)) × QState (Fin 2 → Fin (2 ^ n)))
  uniform1 : ((n : ℕ) → QMAVerifier (2 ^ n)) → Prop
  uniform2 : ((n : ℕ) → QMA2Verifier (2 ^ n)) → Prop

/-- Conditional single-witness language specification relative to a supplied
oracle model. This is not an unconditional characterization of `QMA^U`. -/
def InQMAOracle (U : UnitaryOracle) (M : OracleClassModel U) (L : Set ℕ) : Prop :=
  ∃ V : (n : ℕ) → QMAVerifier (2 ^ n), M.uniform1 V ∧
    (∃ C k : ℕ, ∀ n, (V n).queries ≤ C * (n + 1) ^ k) ∧
    ∀ n, RealizesQMA (V n) (M.single n (V n).witnessDim) ∧
      (n ∈ L → ∃ ψ, Normalized ψ ∧ (2 : ℝ) / 3 ≤ (V n).accept (M.projector n) ψ) ∧
      (n ∉ L → ∀ ψ, Normalized ψ → (V n).accept (M.projector n) ψ ≤ 1 / 3)

/-- Conditional product-witness language specification in a supplied oracle model. -/
def InQMA2Oracle (U : UnitaryOracle) (M : OracleClassModel U) (L : Set ℕ) : Prop :=
  ∃ V : (n : ℕ) → QMA2Verifier (2 ^ n), M.uniform2 V ∧
    (∃ C k : ℕ, ∀ n, (V n).queries ≤ C * (n + 1) ^ k) ∧
    ∀ n, RealizesQMA2 (V n) (M.product n) ∧
      (n ∈ L → ∃ a b, Normalized a ∧ Normalized b ∧
        (2 : ℝ) / 3 ≤ (V n).accept (M.projector n) a b) ∧
      (n ∉ L → ∀ a b, Normalized a → Normalized b →
        (V n).accept (M.projector n) a b ≤ 1 / 3)

/-- Languages satisfying the conditional single-witness specification. -/
def QMAClass (U : UnitaryOracle) (M : OracleClassModel U) : Set (Set ℕ) :=
  { L | InQMAOracle U M L }

/-- Languages satisfying the conditional product-witness specification. -/
def QMA2Class (U : UnitaryOracle) (M : OracleClassModel U) : Set (Set ℕ) :=
  { L | InQMA2Oracle U M L }

end

end Qatlib.Papers.QMA2Sep26.MainResults
