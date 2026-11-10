/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QTeleport93.MainResults.QuditResourceCommunicationDefs
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportation
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Papers.QTeleport93.MainResults

theorem clause11_counting_reduce (n : ℕ) (κ : Type) [Fintype κ]
    (hcard : n * n ≤ Fintype.card κ) :
    n * n ≤ 2 ^ qdMessageBits κ :=
  clause4_clause2_counting_reduce n κ hcard

theorem clause11_guess_bound (n : ℕ) (h : NeZero n) (σ : Type) [Fintype σ]
    [DecidableEq σ] (m : Fin n × Fin n → σ) :
    (Function.Injective m →
      qdBestGuessMass (qdUniform n) m = 1 / ((n * n : ℕ) : ℝ)) ∧
    (¬ Function.Injective m →
      2 / ((n * n : ℕ) : ℝ) ≤ qdBestGuessMass (qdUniform n) m ∧
        qdBestGuessMass (qdUniform n) m ≤ 1) ∧
    ((∃ c : σ, ∀ o : Fin n × Fin n, m o = c) →
      qdBestGuessMass (qdUniform n) m = 1) ∧
    (∀ g : σ → Fin n × Fin n,
      qdDecodeMass (qdUniform n) m g ≤
        ((Fintype.card (Set.range m) : ℕ) : ℝ) / ((n * n : ℕ) : ℝ)) :=
  clause4_clause4 n h σ ‹Fintype σ› ‹DecidableEq σ› m

theorem clause11_actual_branch (n : ℕ) (h : NeZero n) :
    (∀ (rho : Operator n) (o : Fin n × Fin n),
      @quditActualBranchCore n h o rho = (1 / (n : ℂ) ^ 2) • rho) ∧
    (∀ rho : Operator n, (@quditCorrectedInstrument n h).forget.map rho = rho) ∧
    (∀ o : Fin n × Fin n,
      (quditMessage n (Nat.clog 2 n) o).length = 2 * Nat.clog 2 n ∧
        quditDecodeMessage n (Nat.clog 2 n) (quditMessage n (Nat.clog 2 n) o)
          = some o) ∧
    Function.Injective (quditMessage n (Nat.clog 2 n)) ∧
    n ≤ 2 ^ Nat.clog 2 n :=
  clause4_clause6 n h

theorem clause11_contract_bundle :
    (QuditResourceMarginalConverse ∧ QuditMaxEntCharacterization ∧
      QuditMaxEntResourceTeleportation ∧ QuditPureResourceMaxEntForm ∧
      RedundantCodingReliability) :=
  clause4_clause7

end Qatlib.Papers.QTeleport93.MainResults
