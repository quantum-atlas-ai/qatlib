/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite encodings and empty circuits

This module constructs finite encodings for search indices and Boolean adjacency tables. It also
produces a normalized state and a unitary circuit with zero gates on every positive-dimensional
finite register, using the circuit model of quantum computation [NielsenChuang2010].

## Main statements

* `search_index_encoding`: encode `n` indices using `Nat.clog 2 n` bits.
* `adjacency_table_encoding`: encode an adjacency table using `n * n` bits.
* `positive_empty_word_gate_bound`: a zero-gate circuit on a nonempty register.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib
open Qatlib

set_option autoImplicit false

namespace Qatlib.Concepts.WalkSearch.Primitives

/-- There is an injective encoding of `Fin n` into `Fin (2 ^ Nat.clog 2 n)`. -/
theorem search_index_encoding (n : ℕ) :
    ∃ qenc : Fin n → Fin (2 ^ Nat.clog 2 n), Function.Injective qenc := by
  refine ⟨Fin.castLE (Nat.le_pow_clog (by decide) n), ?_⟩
  intro a b hab
  exact Fin.val_injective (congrArg (fun z : Fin (2 ^ Nat.clog 2 n) => z.val) hab)

/-- Boolean adjacency tables on `Fin n` inject into a register with `2 ^ (n * n)` values. -/
theorem adjacency_table_encoding (n : ℕ) :
    ∃ cenc : (Fin n → Fin n → Bool) → Fin (2 ^ (n * n)), Function.Injective cenc := by
  classical
  have hc : Fintype.card (Fin n → Fin n → Bool) = 2 ^ (n * n) := by
    simp [pow_mul]
  let e := Fintype.equivFinOfCardEq hc
  exact ⟨e, e.injective⟩

/-- For `N > 0`, there exist a unitary circuit on `Fin N` with zero gates and a normalized state
on that register. -/
theorem positive_empty_word_gate_bound (N : ℕ) (hN : 0 < N) :
    ∃ (C : Circuit (Fin N)) (ψ : QState (Fin N)),
      IsUnitaryCircuit C ∧ Normalized ψ ∧ GateCount C = 0 :=
  ⟨[], Ket ⟨0, hN⟩, isUnitaryCircuit_nil, normalized_ket _, rfl⟩

end Qatlib.Concepts.WalkSearch.Primitives
