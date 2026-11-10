/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable.Tabulate
import Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable.Value
set_option warningAsError false

set_option autoImplicit false
open scoped BigOperators

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable

def tabulateUsing {α : Type} {n : ℕ} (indices : List (Fin n))
    (h : indices = List.finRange n) (f : Fin n → Observed α) :
    Observed (Vector α n) :=
  let saved := generate f indices
  assemble saved (by simp [saved,generate_runs,h])

theorem tabulateUsing_eq {α : Type} {n : ℕ} (indices : List (Fin n))
    (h : indices = List.finRange n) (f : Fin n → Observed α) :
    tabulateUsing indices h f = tabulate f := by
  subst indices
  rfl

theorem tabulateUsing_arithmetic_eq {α : Type} {n : ℕ}
    (indices : List (Fin n)) (h : indices = List.finRange n)
    (f : Fin n → Observed α) :
    (tabulateUsing indices h f).arithmetic =
      Structural.tabulate (fun i => (f i).arithmetic) := by
  rw [tabulateUsing_eq,tabulate_arithmetic_eq]

theorem tabulateUsing_counts {α : Type} {n : ℕ}
    (indices : List (Fin n)) (h : indices = List.finRange n)
    (f : Fin n → Observed α) (e : Event) :
    (tabulateUsing indices h f).counts e =
      (∑ i : Fin n, (f i).counts e)+localCost n e := by
  rw [tabulateUsing_eq,tabulate_counts]

def tableUsing {α : Type} {r : ℕ} (states : List (Fin r))
    (h : states = List.finRange r)
    (f : Fin r → Fin r → Observed α) :
    Observed ((Vector (Vector α r) r)) :=
  tabulateUsing states h (fun i => tabulateUsing states h (f i))

theorem tableUsing_eq {α : Type} {r : ℕ} (states : List (Fin r))
    (h : states = List.finRange r)
    (f : Fin r → Fin r → Observed α) :
    tableUsing states h f = table f := by
  simp only [tableUsing,tabulateUsing_eq,table]

theorem tableUsing_arithmetic_eq {α : Type} {r : ℕ} (states : List (Fin r))
    (h : states = List.finRange r)
    (f : Fin r → Fin r → Observed α) :
    (tableUsing states h f).arithmetic =
      Structural.table (fun i l => (f i l).arithmetic) := by
  rw [tableUsing_eq,table_arithmetic_eq]

theorem tableUsing_counts {α : Type} {r : ℕ} (states : List (Fin r))
    (h : states = List.finRange r)
    (f : Fin r → Fin r → Observed α) (e : Event) :
    (tableUsing states h f).counts e =
      (∑ i : Fin r, ∑ l : Fin r, (f i l).counts e)+(r+1)*localCost r e := by
  rw [tableUsing_eq,table_counts]

theorem tabulateUsing_value_eq_plain {α : Type} {n : ℕ}
    (indices : List (Fin n)) (h : indices = List.finRange n)
    (f : Fin n → Observed α) :
    (tabulateUsing indices h f).arithmetic.value =
      Value.tabulate indices h (fun i => (f i).arithmetic.value) := by
  rw [tabulateUsing_arithmetic_eq, Value.tabulate_eq]
  apply Vector.ext
  intro i hi
  simp [Structural.tabulate]

theorem tabulateUsing_refines_value {α : Type} {n : ℕ}
    (indices : List (Fin n)) (h : indices = List.finRange n)
    (observed : Fin n → Observed α) (values : Fin n → α)
    (hv : ∀ i, (observed i).arithmetic.value = values i) :
    (tabulateUsing indices h observed).arithmetic.value =
      Value.tabulate indices h values := by
  rw [tabulateUsing_value_eq_plain, Value.tabulate_eq, Value.tabulate_eq]
  apply Vector.ext
  intro i hi
  simpa using hv ⟨i, hi⟩

theorem collect_value_eq_plain {α : Type} (xs : List α) (acc : Array α) :
    (collect xs acc).value = Value.collect xs acc := by
  apply Array.toList_inj.mp
  rw [(collect_spec xs acc).1, Value.collect_toList]

theorem finish_value_eq_plain {α : Type} {n : ℕ} (p : TailPacket α n) :
    (finish p).value = Value.finish p := by
  rw [(finish_spec p).1]
  apply Vector.toList_inj.mp
  simpa [Value.finish, TailPacket.toList] using
    (Value.collect_toList (p.head :: p.rest) (Array.emptyWithCapacity (n+1))).symm

end Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable
