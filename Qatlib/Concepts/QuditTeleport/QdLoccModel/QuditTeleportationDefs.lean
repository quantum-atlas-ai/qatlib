/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationProtocol

/-!
# A finite qudit teleportation model

`QdLoccTeleport` records a complete finite Kraus family on Alice's two registers, linear
corrections, and Boolean message codes. Separate predicates express perfect recovery, unitary
corrections, and consistency of corrections with messages.

The remaining definitions measure alphabet size and maximum code length, and assign weights to
fixed-message guesses, decoders, and uniform qudit outcomes. These results develop resource and
communication properties of teleportation [BennettEtAl1993Teleportation].

## Main statements

* `QdLoccTeleport`: A finite qudit teleportation model consisting of a complete Alice-side Kraus
  family, complex-linear correction maps, and Boolean message codes.
* `QdLoccPerfect`: The condition that the protocol's total output equals every input operator
  for resource `ω`.
* `QdLoccUnitaryCorr`: The condition that each correction matrix `U k` is unitary and implements
  the protocol's correction map by conjugation.
* `qdCommCost`: The maximum length of a protocol's Boolean message codes, with value zero for an
  empty outcome type.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.QuditTeleport.QdLoccModel

open Matrix
open scoped BigOperators

/-- The register equivalence moving Bob's qudit first and combining Alice's two qudit indices
into `Fin (n * n)`. -/
def qdBobFirstEquiv (n : ℕ) : (Fin n × Fin n) × Fin n ≃ Fin n × Fin (n * n) :=
  (Equiv.prodComm (Fin n × Fin n) (Fin n)).trans
    (Equiv.prodCongr (Equiv.refl (Fin n)) (finProdFinEquiv (m := n) (n := n)))

/-- Bob's unnormalized reduced operator after Alice applies `K` to the input and her resource
register, with resource operator `ω`. -/
noncomputable def qdBranchMarginal {n : ℕ}
    (K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (ρ : Operator n) : Operator n :=
  PartialTrace (relabelGate (qdBobFirstEquiv n)
    (TensorGate K (1 : Operator n) *
      relabelGate (Equiv.prodAssoc (Fin n) (Fin n) (Fin n)).symm (TensorGate ρ ω) *
      (TensorGate K (1 : Operator n)).conjTranspose))

/-- A finite qudit teleportation model consisting of a complete Alice-side Kraus family,
complex-linear correction maps, and Boolean message codes. -/
structure QdLoccTeleport (n : ℕ) (κ : Type) [Fintype κ] where

  kraus : κ → Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ

  krausComplete : ∑ k, (kraus k).conjTranspose * kraus k = 1

  corr : κ → (Operator n →ₗ[ℂ] Operator n)

  msgCode : κ → List Bool

/-- The sum of all branch marginals after application of the protocol's outcome-dependent
correction maps. -/
noncomputable def qdLoccOutput {n : ℕ} {κ : Type} [Fintype κ] (P : QdLoccTeleport n κ)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (ρ : Operator n) : Operator n :=
  ∑ k, P.corr k (qdBranchMarginal (P.kraus k) ω ρ)

/-- The condition that the protocol's total output equals every input operator for resource `ω`. -/
def QdLoccPerfect {n : ℕ} {κ : Type} [Fintype κ] (P : QdLoccTeleport n κ)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) : Prop :=
  ∀ ρ : Operator n, qdLoccOutput P ω ρ = ρ

/-- The condition that each correction matrix `U k` is unitary and implements the protocol's
correction map by conjugation. -/
def QdLoccUnitaryCorr {n : ℕ} {κ : Type} [Fintype κ] (P : QdLoccTeleport n κ)
    (U : κ → Operator n) : Prop :=
  (∀ k : κ, U k ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧
    ∀ (k : κ) (ρ : Operator n), P.corr k ρ = U k * ρ * (U k).conjTranspose

/-- The condition that any two outcomes with the same message code have identical correction
maps. -/
def QdLoccMsgConsistent {n : ℕ} {κ : Type} [Fintype κ] (P : QdLoccTeleport n κ) : Prop :=
  ∀ k k' : κ, P.msgCode k = P.msgCode k' → P.corr k = P.corr k'

/-- The condition that conjugation by `U` and by `V` agrees on every operator in dimension `n`. -/
def QdSameConjugation (n : ℕ) (U V : Operator n) : Prop :=
  ∀ ρ : Operator n, U * ρ * U.conjTranspose = V * ρ * V.conjTranspose

/-- For unitary correction implementations, message consistency implies that equal-message
outcomes induce the same conjugation map. -/
theorem qdMsgConsistent_sameConjugation {n : ℕ} {κ : Type} [Fintype κ]
    (P : QdLoccTeleport n κ) (U : κ → Operator n) (hU : QdLoccUnitaryCorr P U)
    (hc : QdLoccMsgConsistent P) {k k' : κ}
    (hm : P.msgCode k = P.msgCode k') : QdSameConjugation n (U k) (U k') := by
  intro ρ
  rw [← hU.2 k, ← hU.2 k', hc k k' hm]

/-- The ceiling base-two logarithm of the finite outcome alphabet's cardinality. -/
def qdMessageBits (κ : Type) [Fintype κ] : ℕ :=
  Nat.clog 2 (Fintype.card κ)

/-- The maximum length of a protocol's Boolean message codes, with value zero for an empty
outcome type. -/
def qdCommCost {n : ℕ} {κ : Type} [Fintype κ] (P : QdLoccTeleport n κ) : ℕ :=
  Finset.sup Finset.univ fun k => (P.msgCode k).length

/-- The outcome alphabet has cardinality at most `2 ^ qdMessageBits κ`. -/
theorem qdCard_le_pow_messageBits (κ : Type) [Fintype κ] :
    Fintype.card κ ≤ 2 ^ qdMessageBits κ :=
  Nat.le_pow_clog (by decide) _

/-- Every outcome's message-code length is at most the protocol's communication cost. -/
theorem qdMsgCodeLength_le {n : ℕ} {κ : Type} [Fintype κ] (P : QdLoccTeleport n κ)
    (k : κ) : (P.msgCode k).length ≤ qdCommCost P :=
  Finset.le_sup (f := fun j => (P.msgCode j).length) (Finset.mem_univ k)

/-- The sum of outcome weights over the fiber of the fixed message guess `g`. -/
def qdGuessMass {κ σ : Type} [Fintype κ] [DecidableEq σ]
    (p : κ → ℝ) (m : κ → σ) (g : σ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => m k = g), p k

/-- The maximum of zero and the weights of all fixed-message guesses. -/
noncomputable def qdBestGuessMass {κ σ : Type} [Fintype κ] [Fintype σ] [DecidableEq σ]
    (p : κ → ℝ) (m : κ → σ) : ℝ :=
  ((Finset.univ : Finset σ).toList.map (qdGuessMass p m)).foldl max 0

/-- The total outcome weight for which decoding the encoded message returns the original
outcome. -/
def qdDecodeMass {κ σ : Type} [Fintype κ] [DecidableEq κ] [DecidableEq σ]
    (p : κ → ℝ) (m : κ → σ) (g : σ → κ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => g (m k) = k), p k

/-- The constant weight `1 / n²` on pairs of qudit outcome indices. -/
noncomputable def qdUniform (n : ℕ) : (Fin n × Fin n) → ℝ :=
  fun _ => 1 / ((n * n : ℕ) : ℝ)

/-- For uniform qudit outcomes, a fixed-message guess has weight equal to its fiber cardinality
divided by `n²`. -/
theorem qdGuessMass_uniform (n : ℕ) {σ : Type} [DecidableEq σ]
    (m : Fin n × Fin n → σ) (g : σ) :
    qdGuessMass (qdUniform n) m g =
      ((Finset.univ.filter (fun k => m k = g)).card : ℕ) / ((n * n : ℕ) : ℝ) := by
  simp only [qdGuessMass, qdUniform]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- The teleportation model for a composite system of dimension `n ^ k`. -/
abbrev QdCompositeTeleport (n k : ℕ) (κ : Type) [Fintype κ] :=
  QdLoccTeleport (n ^ k) κ

/-- The type of `k`-tuples of outcomes in `κ`. -/
abbrev QdCompositeOutcomes (κ : Type) (k : ℕ) := Fin k → κ

/-- The cardinality of `k`-tuples of outcomes equals `Fintype.card κ ^ k`. -/
theorem qdCompositeOutcomes_card (κ : Type) [Fintype κ] (k : ℕ) :
    Fintype.card (QdCompositeOutcomes κ k) = Fintype.card κ ^ k := by
  simp [QdCompositeOutcomes, Fintype.card_pi]

end Qatlib.Concepts.QuditTeleport.QdLoccModel
