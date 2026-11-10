/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationProtocol
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.QuditTeleport.QdLoccModel

open Matrix
open scoped BigOperators

def qdBobFirstEquiv (n : ℕ) : (Fin n × Fin n) × Fin n ≃ Fin n × Fin (n * n) :=
  (Equiv.prodComm (Fin n × Fin n) (Fin n)).trans
    (Equiv.prodCongr (Equiv.refl (Fin n)) (finProdFinEquiv (m := n) (n := n)))

noncomputable def qdBranchMarginal {n : ℕ}
    (K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (ρ : Operator n) : Operator n :=
  PartialTrace (relabelGate (qdBobFirstEquiv n)
    (TensorGate K (1 : Operator n) *
      relabelGate (Equiv.prodAssoc (Fin n) (Fin n) (Fin n)).symm (TensorGate ρ ω) *
      (TensorGate K (1 : Operator n)).conjTranspose))

structure QdLoccTeleport (n : ℕ) (κ : Type) [Fintype κ] where

  kraus : κ → Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ

  krausComplete : ∑ k, (kraus k).conjTranspose * kraus k = 1

  corr : κ → (Operator n →ₗ[ℂ] Operator n)

  msgCode : κ → List Bool

noncomputable def qdLoccOutput {n : ℕ} {κ : Type} [Fintype κ] (P : QdLoccTeleport n κ)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (ρ : Operator n) : Operator n :=
  ∑ k, P.corr k (qdBranchMarginal (P.kraus k) ω ρ)

def QdLoccPerfect {n : ℕ} {κ : Type} [Fintype κ] (P : QdLoccTeleport n κ)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) : Prop :=
  ∀ ρ : Operator n, qdLoccOutput P ω ρ = ρ

def QdLoccUnitaryCorr {n : ℕ} {κ : Type} [Fintype κ] (P : QdLoccTeleport n κ)
    (U : κ → Operator n) : Prop :=
  (∀ k : κ, U k ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧
    ∀ (k : κ) (ρ : Operator n), P.corr k ρ = U k * ρ * (U k).conjTranspose

def QdLoccMsgConsistent {n : ℕ} {κ : Type} [Fintype κ] (P : QdLoccTeleport n κ) : Prop :=
  ∀ k k' : κ, P.msgCode k = P.msgCode k' → P.corr k = P.corr k'

def QdSameConjugation (n : ℕ) (U V : Operator n) : Prop :=
  ∀ ρ : Operator n, U * ρ * U.conjTranspose = V * ρ * V.conjTranspose

theorem qdMsgConsistent_sameConjugation {n : ℕ} {κ : Type} [Fintype κ]
    (P : QdLoccTeleport n κ) (U : κ → Operator n) (hU : QdLoccUnitaryCorr P U)
    (hc : QdLoccMsgConsistent P) {k k' : κ}
    (hm : P.msgCode k = P.msgCode k') : QdSameConjugation n (U k) (U k') := by
  intro ρ
  rw [← hU.2 k, ← hU.2 k', hc k k' hm]

def qdMessageBits (κ : Type) [Fintype κ] : ℕ :=
  Nat.clog 2 (Fintype.card κ)

def qdCommCost {n : ℕ} {κ : Type} [Fintype κ] (P : QdLoccTeleport n κ) : ℕ :=
  Finset.sup Finset.univ fun k => (P.msgCode k).length

theorem qdCard_le_pow_messageBits (κ : Type) [Fintype κ] :
    Fintype.card κ ≤ 2 ^ qdMessageBits κ :=
  Nat.le_pow_clog (by decide) _

theorem qdMsgCodeLength_le {n : ℕ} {κ : Type} [Fintype κ] (P : QdLoccTeleport n κ)
    (k : κ) : (P.msgCode k).length ≤ qdCommCost P :=
  Finset.le_sup (f := fun j => (P.msgCode j).length) (Finset.mem_univ k)

def qdGuessMass {κ σ : Type} [Fintype κ] [DecidableEq σ]
    (p : κ → ℝ) (m : κ → σ) (g : σ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => m k = g), p k

noncomputable def qdBestGuessMass {κ σ : Type} [Fintype κ] [Fintype σ] [DecidableEq σ]
    (p : κ → ℝ) (m : κ → σ) : ℝ :=
  ((Finset.univ : Finset σ).toList.map (qdGuessMass p m)).foldl max 0

def qdDecodeMass {κ σ : Type} [Fintype κ] [DecidableEq κ] [DecidableEq σ]
    (p : κ → ℝ) (m : κ → σ) (g : σ → κ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => g (m k) = k), p k

noncomputable def qdUniform (n : ℕ) : (Fin n × Fin n) → ℝ :=
  fun _ => 1 / ((n * n : ℕ) : ℝ)

theorem qdGuessMass_uniform (n : ℕ) {σ : Type} [DecidableEq σ]
    (m : Fin n × Fin n → σ) (g : σ) :
    qdGuessMass (qdUniform n) m g =
      ((Finset.univ.filter (fun k => m k = g)).card : ℕ) / ((n * n : ℕ) : ℝ) := by
  simp only [qdGuessMass, qdUniform]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]

abbrev QdCompositeTeleport (n k : ℕ) (κ : Type) [Fintype κ] :=
  QdLoccTeleport (n ^ k) κ

abbrev QdCompositeOutcomes (κ : Type) (k : ℕ) := Fin k → κ

theorem qdCompositeOutcomes_card (κ : Type) [Fintype κ] (k : ℕ) :
    Fintype.card (QdCompositeOutcomes κ k) = Fintype.card κ ^ k := by
  simp [QdCompositeOutcomes, Fintype.card_pi]

end Qatlib.Concepts.QuditTeleport.QdLoccModel
