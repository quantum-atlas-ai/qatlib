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

This module defines the `QMA` and `QMA(2)` query-model verifier interfaces, the antisymmetric
entangled-subspace (AESD) promise problem, approximate disentanglers, and unitary-oracle
relativized complexity classes used in Sections 5 and 6 of [Bostanci et al., 2026][BostanciEtAl2026].

## Main definitions

* `IsAESDYes`, `IsAESDNo`, `NofD`, `dJ`: the AESD promise problem predicates and dimension
  parameters.
* `QMAVerifier`, `QMA2Verifier`, `canonicalAESDVerifier2`, `DecidesAESD1`, `DecidesAESD2`:
  single-witness and product-witness verifier interfaces for AESD.
* `Disentangler`, `IsDisentangler`: approximate disentangler parameter specification.
* `UnitaryOracle`, `InQMAOracle`, `InQMA2Oracle`, `QMAClass`, `QMA2Class`: unitary-oracle
  relativized `QMA` and `QMA(2)` classes.

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

/-- A `QMA` verifier for the AESD promise problem on `(C^d)^{⊗4}`: an
`m`-qubit witness, `q` oracle queries, completeness/soundness thresholds, and a
Born-rule acceptance probability `accept P ψ ∈ [0,1]`. -/
structure QMAVerifier (d : ℕ) where
  /-- witness length in qubits -/
  witnessDim : ℕ
  /-- number of oracle queries -/
  queries : ℕ
  /-- completeness threshold -/
  completeness : ℝ
  /-- soundness threshold -/
  soundness : ℝ
  /-- acceptance probability as a function of the oracle projector and witness -/
  accept : Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ → QState (Fin witnessDim) → ℝ

/-- A `QMA(2)` verifier for AESD: a *pair* of unentangled witness registers
(each a `QState (Fin 2 → Fin d)`), `q` oracle queries, thresholds, and a
Born-rule acceptance probability on product witnesses. -/
structure QMA2Verifier (d : ℕ) where
  /-- number of oracle queries -/
  queries : ℕ
  /-- completeness threshold -/
  completeness : ℝ
  /-- soundness threshold -/
  soundness : ℝ
  /-- acceptance probability on a product witness `a ⊗ b` -/
  accept : Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ →
    QState (Fin 2 → Fin d) → QState (Fin 2 → Fin d) → ℝ

/-- The canonical one-query QMA(2) verifier for AESD: it measures the projector
`P` on the product witness `a ⊗ b` (Hadamard test), accepting with probability
`Re⟨a b| P |a b⟩` (proof of Proposition 5.3). -/
def canonicalAESDVerifier2 (d : ℕ) : QMA2Verifier d where
  queries := 1
  completeness := 1
  soundness := 1 / 3
  accept := fun P a b => realQuadForm P (tensorPair a b)

/-- `V` decides the AESD promise problem (QMA(2) form): on every YES instance
some product witness is accepted with probability at least `completeness`; on
every NO instance every product witness is accepted with probability at most
`soundness`. -/
def DecidesAESD2 {d : ℕ} (V : QMA2Verifier d) : Prop :=
  (∀ P, IsAESDYes P → ∃ a b : QState (Fin 2 → Fin d),
      Normalized a ∧ Normalized b ∧ V.completeness ≤ V.accept P a b) ∧
  (∀ P, IsAESDNo P → ∀ a b : QState (Fin 2 → Fin d),
      Normalized a → Normalized b → V.accept P a b ≤ V.soundness)

/-- `V` decides the AESD promise problem (QMA form): on every YES instance some
witness is accepted with probability at least `completeness`; on every NO
instance every witness is accepted with probability at most `soundness`. -/
def DecidesAESD1 {d : ℕ} (V : QMAVerifier d) : Prop :=
  (∀ P, IsAESDYes P → ∃ ψ : QState (Fin V.witnessDim),
      Normalized ψ ∧ V.completeness ≤ V.accept P ψ) ∧
  (∀ P, IsAESDNo P → ∀ ψ : QState (Fin V.witnessDim),
      Normalized ψ → V.accept P ψ ≤ V.soundness)

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

/-- The `(ε, δ)`-disentangler guarantee predicate: `Λ` is an `(ε, δ)`-disentangler
with the given output dimension and `m` input qubits. -/
def IsDisentangler (Λ : Disentangler) (ε δ : ℝ) (D : ℕ) : Prop :=
  Λ.epsilon = ε ∧ Λ.delta = δ ∧ Λ.outputDim = D

/- ## Unitary oracles and relativized classes (Theorem 5.1) -/

/-- A unitary oracle `U = (U^{(n)})_{n ≥ 1}`: the `n`-th component acts on one
control qubit and two `n`-qubit registers, i.e. on a `2·(2^{2n+1})`-dimensional
space.  We record only its ambient dimension per input length. -/
structure UnitaryOracle where
  /-- ambient dimension of the `n`-th component -/
  dim : ℕ → ℕ

/-- `L ∈ QMA^U`: a unary language decided by a family of `QMA` verifiers with
oracle access to `U`, one per input length, with the AESD-style decision
guarantee.  Modeled through the `QMAVerifier` interface. -/
def InQMAOracle (U : UnitaryOracle) (L : Set ℕ) : Prop :=
  ∃ (verifierOf : (n : ℕ) → QMAVerifier (2 ^ n)),
    (∀ n, DecidesAESD1 (verifierOf n)) ∧ (∀ n, n ∈ L → 1 ≤ U.dim n)

/-- `L ∈ QMA(2)^U`: decided by a family of `QMA(2)` verifiers with oracle access
to `U`. -/
def InQMA2Oracle (U : UnitaryOracle) (L : Set ℕ) : Prop :=
  ∃ (verifierOf : (n : ℕ) → QMA2Verifier (2 ^ n)),
    (∀ n, DecidesAESD2 (verifierOf n)) ∧ (∀ n, n ∈ L → 1 ≤ U.dim n)

/-- The class `QMA^U`, as a set of unary languages. -/
def QMAClass (U : UnitaryOracle) : Set (Set ℕ) := { L | InQMAOracle U L }

/-- The class `QMA(2)^U`, as a set of unary languages. -/
def QMA2Class (U : UnitaryOracle) : Set (Set ℕ) := { L | InQMA2Oracle U L }

end

end Qatlib.Papers.QMA2Sep26.MainResults
