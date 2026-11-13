/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable.Tabulate
import Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable.Value

/-!
# Saved-table construction from explicit indices

`tabulateUsing` and `tableUsing` construct observed vectors and square tables from explicit
index lists certified equal to `List.finRange`. They agree with the standard tabulation
operations and retain their arithmetic results and event counts.

The refinement lemmas identify the underlying values with the plain operations in `Value`. The
count formulas separate the contributions of the supplied computations from the local assembly
counts.

## Main statements

* `tabulateUsing_eq` and `tableUsing_eq`: agreement with standard tabulation.
* `tabulateUsing_counts` and `tableUsing_counts`: exact event-count formulas.
* `tabulateUsing_refines_value`: value refinement from entrywise equalities.

For background on classical computation and resource bounds, see [KitaevShenVyalyi2002].

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option autoImplicit false
open scoped BigOperators

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable

/-- Generate and assemble an observed vector using an explicit index list certified equal to
`List.finRange n`. -/
def tabulateUsing {α : Type} {n : ℕ} (indices : List (Fin n))
    (h : indices = List.finRange n) (f : Fin n → Observed α) :
    Observed (Vector α n) :=
  let saved := generate f indices
  assemble saved (by simp [saved,generate_runs,h])

/-- Tabulation using an explicit list equal to `List.finRange n` agrees with `tabulate`. -/
theorem tabulateUsing_eq {α : Type} {n : ℕ} (indices : List (Fin n))
    (h : indices = List.finRange n) (f : Fin n → Observed α) :
    tabulateUsing indices h f = tabulate f := by
  subst indices
  rfl

/-- The arithmetic component of explicit-index tabulation is the structural tabulation of the
entrywise arithmetic components. -/
theorem tabulateUsing_arithmetic_eq {α : Type} {n : ℕ}
    (indices : List (Fin n)) (h : indices = List.finRange n)
    (f : Fin n → Observed α) :
    (tabulateUsing indices h f).arithmetic =
      Structural.tabulate (fun i => (f i).arithmetic) := by
  rw [tabulateUsing_eq,tabulate_arithmetic_eq]

/-- For each event, explicit-index tabulation records the sum of the entry counts plus
`localCost n e`. -/
theorem tabulateUsing_counts {α : Type} {n : ℕ}
    (indices : List (Fin n)) (h : indices = List.finRange n)
    (f : Fin n → Observed α) (e : Event) :
    (tabulateUsing indices h f).counts e =
      (∑ i : Fin n, (f i).counts e)+localCost n e := by
  rw [tabulateUsing_eq,tabulate_counts]

/-- Construct an observed square table by nested tabulation over an explicit state list
certified equal to `List.finRange r`. -/
def tableUsing {α : Type} {r : ℕ} (states : List (Fin r))
    (h : states = List.finRange r)
    (f : Fin r → Fin r → Observed α) :
    Observed ((Vector (Vector α r) r)) :=
  tabulateUsing states h (fun i => tabulateUsing states h (f i))

/-- Square-table construction using the certified explicit state list agrees with `table`. -/
theorem tableUsing_eq {α : Type} {r : ℕ} (states : List (Fin r))
    (h : states = List.finRange r)
    (f : Fin r → Fin r → Observed α) :
    tableUsing states h f = table f := by
  simp only [tableUsing,tabulateUsing_eq,table]

/-- The arithmetic component of explicit-index square-table construction equals the structural
table of entrywise arithmetic components. -/
theorem tableUsing_arithmetic_eq {α : Type} {r : ℕ} (states : List (Fin r))
    (h : states = List.finRange r)
    (f : Fin r → Fin r → Observed α) :
    (tableUsing states h f).arithmetic =
      Structural.table (fun i l => (f i l).arithmetic) := by
  rw [tableUsing_eq,table_arithmetic_eq]

/-- For each event, explicit-index square-table construction records the sum of all entry counts
plus `(r + 1) * localCost r e`. -/
theorem tableUsing_counts {α : Type} {r : ℕ} (states : List (Fin r))
    (h : states = List.finRange r)
    (f : Fin r → Fin r → Observed α) (e : Event) :
    (tableUsing states h f).counts e =
      (∑ i : Fin r, ∑ l : Fin r, (f i l).counts e)+(r+1)*localCost r e := by
  rw [tableUsing_eq,table_counts]

/-- The underlying value of explicit-index observed tabulation agrees with plain
`Value.tabulate` on the entrywise values. -/
theorem tabulateUsing_value_eq_plain {α : Type} {n : ℕ}
    (indices : List (Fin n)) (h : indices = List.finRange n)
    (f : Fin n → Observed α) :
    (tabulateUsing indices h f).arithmetic.value =
      Value.tabulate indices h (fun i => (f i).arithmetic.value) := by
  rw [tabulateUsing_arithmetic_eq, Value.tabulate_eq]
  apply Vector.ext
  intro i hi
  simp [Structural.tabulate]

/-- Entrywise equality between observed arithmetic values and supplied values implies equality
of the resulting observed and plain tabulated vectors. -/
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

/-- The value returned by counted collection equals the array returned by plain `Value.collect`. -/
theorem collect_value_eq_plain {α : Type} (xs : List α) (acc : Array α) :
    (collect xs acc).value = Value.collect xs acc := by
  apply Array.toList_inj.mp
  rw [(collect_spec xs acc).1, Value.collect_toList]

/-- The value returned by counted packet finishing equals the vector returned by plain
`Value.finish`. -/
theorem finish_value_eq_plain {α : Type} {n : ℕ} (p : TailPacket α n) :
    (finish p).value = Value.finish p := by
  rw [(finish_spec p).1]
  apply Vector.toList_inj.mp
  simpa [Value.finish, TailPacket.toList] using
    (Value.collect_toList (p.head :: p.rest) (Array.emptyWithCapacity (n+1))).symm

end Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable
