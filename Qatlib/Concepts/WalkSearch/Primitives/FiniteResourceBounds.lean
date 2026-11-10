/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.EquivFin
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib
open Qatlib

set_option autoImplicit false

namespace Qatlib.Concepts.WalkSearch.Primitives

theorem search_index_encoding (n : ℕ) :
    ∃ qenc : Fin n → Fin (2 ^ Nat.clog 2 n), Function.Injective qenc := by
  refine ⟨Fin.castLE (Nat.le_pow_clog (by decide) n), ?_⟩
  intro a b hab
  exact Fin.val_injective (congrArg (fun z : Fin (2 ^ Nat.clog 2 n) => z.val) hab)

theorem adjacency_table_encoding (n : ℕ) :
    ∃ cenc : (Fin n → Fin n → Bool) → Fin (2 ^ (n * n)), Function.Injective cenc := by
  classical
  have hc : Fintype.card (Fin n → Fin n → Bool) = 2 ^ (n * n) := by
    simp [pow_mul]
  let e := Fintype.equivFinOfCardEq hc
  exact ⟨e, e.injective⟩

theorem positive_empty_word_gate_bound (N : ℕ) (hN : 0 < N) :
    ∃ (C : Circuit (Fin N)) (ψ : QState (Fin N)),
      IsUnitaryCircuit C ∧ Normalized ψ ∧ GateCount C = 0 :=
  ⟨[], Ket ⟨0, hN⟩, isUnitaryCircuit_nil, normalized_ket _, rfl⟩

end Qatlib.Concepts.WalkSearch.Primitives
