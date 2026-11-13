/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable.Traversal
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

/-!
# Saved table tabulation and resource ledgers

This module constructs vectors and square tables from saved child runs. `Structural.tabulate`
sums arithmetic work and cell ledgers, while `tabulate` and `assemble` additionally count
generation, traversal, and array construction events.

The exact event formulas and suffix bounds support explicit resource accounting for finite
computations, with general computational background in [KitaevShenVyalyi2002]. `eventTotal`
excludes the separately recorded slot count.

## Main statements

* `tabulate_arithmetic_eq`: observed tabulation agrees with structural tabulation on arithmetic
  data.
* `table_counts`: square table counts are child counts plus the local row and outer traversal
  costs.
* `table_ledger_suffix_bound`: bounds suffix ledger values and their binary sizes.

## References

* [Kitaev, Shen and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open scoped BigOperators

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable.Structural

/-- Tabulates a finite family of runs into a vector, summing their work and cell ledgers. -/
def tabulate {α : Type} {n : ℕ} (f : Fin n → Run α) :
    Run (Vector α n) :=
  let runs := Vector.ofFn f
  ⟨runs.map (fun a => a.value), ∑ i : Fin n, runs[i].work,
    ∑ i : Fin n, runs[i].cells⟩

/-- The value at index `i` of structural tabulation is the value of the corresponding child run. -/
@[simp] theorem tabulate_value {α : Type} {n : ℕ}
    (f : Fin n → Run α) (i : Fin n) :
    (tabulate f).value[i]=(f i).value := by
  simp [tabulate]

/-- The work of structural tabulation is the sum of the child work ledgers. -/
@[simp] theorem tabulate_work {α : Type} {n : ℕ}
    (f : Fin n → Run α) :
    (tabulate f).work=∑ i : Fin n, (f i).work := by
  simp [tabulate]

/-- The cell count of structural tabulation is the sum of the child cell ledgers. -/
@[simp] theorem tabulate_cells {α : Type} {n : ℕ}
    (f : Fin n → Run α) :
    (tabulate f).cells=∑ i : Fin n, (f i).cells := by
  simp [tabulate]

/-- If each child has cells at most work and work at most `C`, tabulation has cells at most work
and work at most `n * C`. -/
theorem tabulate_bound {α : Type} {n : ℕ}
    (f : Fin n → Run α) (C : ℕ)
    (h : ∀ i, (f i).cells ≤ (f i).work ∧ (f i).work ≤ C) :
    (tabulate f).cells ≤ (tabulate f).work ∧ (tabulate f).work ≤ n*C := by
  simp only [tabulate_work,tabulate_cells]
  constructor
  · exact Finset.sum_le_sum (fun i _ => (h i).1)
  · calc
      (∑ i : Fin n, (f i).work) ≤ ∑ _i : Fin n, C :=
        Finset.sum_le_sum (fun i _ => (h i).2)
      _ = n*C := by simp

/-- Forms a square table of runs by tabulating each row and then the rows. -/
def table {α : Type} {r : ℕ} (f : Fin r → Fin r → Run α) :
    Run ((Vector (Vector α r) r)) :=
  tabulate (fun i => tabulate (f i))

/-- The value at row `i` and column `l` of a structural table is the corresponding child value. -/
@[simp] theorem table_value {α : Type} {r : ℕ}
    (f : Fin r → Fin r → Run α) (i l : Fin r) :
    (table f).value[i][l]=(f i l).value := by
  simp [table,tabulate]

/-- Uniform child work bounds give cells at most work and total work at most `r^2 * C` for a
square table. -/
theorem table_bound {α : Type} {r : ℕ}
    (f : Fin r → Fin r → Run α) (C : ℕ)
    (h : ∀ i l, (f i l).cells ≤ (f i l).work ∧ (f i l).work ≤ C) :
    (table f).cells ≤ (table f).work ∧ (table f).work ≤ r^2*C := by
  have hh := tabulate_bound (fun i => tabulate (f i)) (r*C)
    (fun i => tabulate_bound (f i) C (h i))
  simpa [table,pow_two,Nat.mul_assoc] using hh
end Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable.Structural

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable

/-- The event counts contributed locally by tabulating `n` children. -/
def localCost (n : ℕ) : Counts
  | .child => n
  | .check => 5*(n+1)
  | .cons => 2*n
  | .field => 3*n
  | .ledgerAdd => 2*n
  | .reserve => 1
  | .push => n
  | .slot => n

/-- Assembles saved runs into an observed vector, combining their arithmetic ledgers and
recording traversal and array construction events. -/
def assemble {α : Type} {n : ℕ} (saved : Generated α)
    (h : saved.runs.length = n) : Observed (Vector α n) :=
  let values := project saved.runs
  let work := sumField (fun q => q.work) saved.runs
  let cells := sumField (fun q => q.cells) saved.runs
  let out := collect values.values (Array.emptyWithCapacity n)
  let vector : Vector α n := ⟨out.value,by
    simp [out,values,collect_size,(project_spec saved.runs).1,h]⟩
  ⟨⟨vector,work.value,cells.value⟩,saved.nested + fun
    | .child => saved.items
    | .check => saved.checks+values.checks+work.checks+cells.checks+out.calls
    | .cons => saved.items+values.reads
    | .field => values.reads+work.reads+cells.reads
    | .ledgerAdd => work.reads+cells.reads
    | .reserve => 1
    | .push => out.pushes
    | .slot => n⟩

/-- Assembly preserves the ordered child values and sums the child work and cell ledgers. -/
theorem assemble_fields {α : Type} {n : ℕ} (saved : Generated α)
    (h : saved.runs.length = n) :
    (assemble saved h).arithmetic.value.toList = saved.runs.map (fun q => q.value) ∧
    (assemble saved h).arithmetic.work = (saved.runs.map (fun q => q.work)).sum ∧
    (assemble saved h).arithmetic.cells = (saved.runs.map (fun q => q.cells)).sum := by
  dsimp only [assemble]
  refine ⟨?_,(sumField_spec _ _).1,(sumField_spec _ _).1⟩
  change (collect (project saved.runs).values (Array.emptyWithCapacity n)).value.toList = _
  rw [(collect_spec _ _).1]
  simpa using (project_spec saved.runs).1

/-- With `n` saved items and `n + 1` generation checks, assembly adds `localCost n` to the
nested event counts. -/
theorem assemble_counts {α : Type} {n : ℕ} (saved : Generated α)
    (h : saved.runs.length = n) (hc : saved.checks = n+1) (hi : saved.items = n)
    (e : Event) :
    (assemble saved h).counts e = saved.nested e+localCost n e := by
  have hp := project_spec saved.runs
  have hw := sumField_spec (fun q => q.work) saved.runs
  have hs := sumField_spec (fun q => q.cells) saved.runs
  have ho := collect_spec (project saved.runs).values (Array.emptyWithCapacity n)
  have hl : (project saved.runs).values.length = n := by rw [hp.1,List.length_map,h]
  cases e <;> simp only [assemble,Pi.add_apply,localCost,hc,hi,hp.2.1,hp.2.2,
    hw.2.1,hw.2.2,hs.2.1,hs.2.2,ho.2.1,ho.2.2,hl,h] <;> omega

/-- Tabulates observed children by generating saved runs in index order and assembling them into
a vector. -/
def tabulate {α : Type} {n : ℕ} (f : Fin n → Observed α) :
    Observed (Vector α n) :=
  let saved := generate f (List.finRange n)
  assemble saved (by simp [saved,generate_runs])

/-- Runs are equal when their values, work ledgers, and cell ledgers agree. -/
private theorem run_ext {α : Type} (a b : Run α)
    (hv : a.value=b.value) (hw : a.work=b.work) (hc : a.cells=b.cells) : a=b := by
  cases a
  cases b
  simp_all

/-- The arithmetic component of observed tabulation equals structural tabulation of the child
arithmetic runs. -/
theorem tabulate_arithmetic_eq {α : Type} {n : ℕ} (f : Fin n → Observed α) :
    (tabulate f).arithmetic = Structural.tabulate (fun i => (f i).arithmetic) := by
  have h := assemble_fields (n := n) (generate f (List.finRange n))
    (by simp [generate_runs])
  apply run_ext
  · apply Vector.toList_inj.mp
    dsimp only [tabulate]
    rw [h.1]
    simp [Structural.tabulate,Vector.toList_ofFn,
      List.ofFn_eq_map,generate_runs,List.map_map]
  · rw [Structural.tabulate_work]
    simpa only [generate_runs,List.map_map,sum_finRange] using! h.2.1
  · rw [Structural.tabulate_cells]
    simpa only [generate_runs,List.map_map,sum_finRange] using! h.2.2

/-- Observed tabulation adds the local event cost to the sum of the child event counts. -/
theorem tabulate_counts {α : Type} {n : ℕ} (f : Fin n → Observed α) (e : Event) :
    (tabulate f).counts e = (∑ i : Fin n, (f i).counts e)+localCost n e := by
  have hg := generate_counts f (List.finRange n)
  have h := assemble_counts (n := n) (generate f (List.finRange n))
    (by simp [generate_runs]) (by simpa using hg.1) (by simpa using hg.2) e
  simpa only [tabulate,generate_nested,sum_finRange] using h

/-- Tabulates plain arithmetic runs after lifting them to observed runs with zero nested counts. -/
def plain {α : Type} {n : ℕ} (f : Fin n → Run α) :=
  tabulate (fun i => lift (f i))

/-- The arithmetic component of plain tabulation is structural tabulation. -/
theorem plain_arithmetic_eq {α : Type} {n : ℕ}
    (f : Fin n → Run α) :
    (plain f).arithmetic = Structural.tabulate f := by
  simpa only [plain,lift] using tabulate_arithmetic_eq (fun i => lift (f i))

/-- Plain tabulation has exactly the local event counts. -/
theorem plain_counts {α : Type} {n : ℕ}
    (f : Fin n → Run α) (e : Event) :
    (plain f).counts e = localCost n e := by
  simp [plain,tabulate_counts,lift]

/-- Forms an observed square table by tabulating rows and then tabulating the resulting row
vectors. -/
def table {α : Type} {r : ℕ} (f : Fin r → Fin r → Observed α) :
    Observed ((Vector (Vector α r) r)) :=
  tabulate (fun i => tabulate (f i))

/-- The arithmetic component of an observed table equals the corresponding structural table. -/
theorem table_arithmetic_eq {α : Type} {r : ℕ}
    (f : Fin r → Fin r → Observed α) :
    (table f).arithmetic = Structural.table (fun i l => (f i l).arithmetic) := by
  simp only [table,tabulate_arithmetic_eq,Structural.table]

/-- The event counts of a square table are the sum of its child counts plus `(r + 1) * localCost
r`. -/
theorem table_counts {α : Type} {r : ℕ} (f : Fin r → Fin r → Observed α)
    (e : Event) :
    (table f).counts e =
      (∑ i : Fin r, ∑ l : Fin r, (f i l).counts e)+(r+1)*localCost r e := by
  simp [table,tabulate_counts,Finset.sum_add_distrib,add_mul,Nat.add_assoc]

/-- Sums the child, check, cons, field, ledger addition, reserve, and push counts, excluding the
slot count. -/
def eventTotal (c : Counts) : ℕ :=
  c .child+c .check+c .cons+c .field+c .ledgerAdd+c .reserve+c .push

/-- The total local event count, excluding slots, is `14 * n + 6`. -/
theorem localCost_eventTotal (n : ℕ) : eventTotal (localCost n) = 14*n+6 := by
  simp only [eventTotal,localCost]
  omega

/-- The total event count of plain tabulation, excluding slots, is `14 * n + 6`. -/
theorem plain_eventTotal {α : Type} {n : ℕ}
    (f : Fin n → Run α) :
    eventTotal (plain f).counts = 14*n+6 := by
  simpa only [eventTotal,plain_counts] using localCost_eventTotal n

/-- Forms an observed square table from plain arithmetic runs with zero nested event counts. -/
def plainTable {α : Type} {r : ℕ} (f : Fin r → Fin r → Run α) :=
  table (fun i l => lift (f i l))

/-- The arithmetic component of a plain table equals the structural table. -/
theorem plainTable_arithmetic_eq {α : Type} {r : ℕ}
    (f : Fin r → Fin r → Run α) :
    (plainTable f).arithmetic = Structural.table f := by
  simpa only [plainTable,lift] using table_arithmetic_eq (fun i l => lift (f i l))

/-- Each event count of a plain square table is `(r + 1)` times the corresponding local row
cost. -/
theorem plainTable_counts {α : Type} {r : ℕ}
    (f : Fin r → Fin r → Run α) (e : Event) :
    (plainTable f).counts e = (r+1)*localCost r e := by
  simp [plainTable,table_counts,lift]

/-- The total event count of a plain square table, excluding slots, is `(r + 1) * (14 * r + 6)`. -/
theorem plainTable_eventTotal {α : Type} {r : ℕ}
    (f : Fin r → Fin r → Run α) :
    eventTotal (plainTable f).counts = (r+1)*(14*r+6) := by
  simp only [eventTotal,plainTable_counts,localCost]
  ring

/-- Uniform entry bounds give cells at most work and work at most `r^2 * C` for a plain square
table. -/
theorem plainTable_bound {α : Type} {r : ℕ}
    (f : Fin r → Fin r → Run α) (C : ℕ)
    (h : ∀ i l, (f i l).cells ≤ (f i l).work ∧ (f i l).work ≤ C) :
    (plainTable f).arithmetic.cells ≤ (plainTable f).arithmetic.work ∧
    (plainTable f).arithmetic.work ≤ r^2*C := by
  rw [plainTable_arithmetic_eq]
  exact Structural.table_bound f C h

/-- For any suffix of the generated runs, both ledger sums are at most `n * C`, and their binary
sizes are at most its binary size, under the stated child bounds. -/
theorem tabulate_ledger_suffix_bound {α : Type} {n : ℕ}
    (f : Fin n → Observed α) (C : ℕ)
    (h : ∀ i, (f i).arithmetic.cells ≤ (f i).arithmetic.work ∧
      (f i).arithmetic.work ≤ C)
    (suffix : List (Run α))
    (hSuffix : ∃ pre, pre++suffix=(generate f (List.finRange n)).runs) :
    ((sumField (fun q => q.work) suffix).value ≤ n*C ∧
      (sumField (fun q => q.work) suffix).value.size ≤ (n*C).size) ∧
    ((sumField (fun q => q.cells) suffix).value ≤ n*C ∧
      (sumField (fun q => q.cells) suffix).value.size ≤ (n*C).size) := by
  have hq : ∀ q ∈ (generate f (List.finRange n)).runs, q.cells ≤ q.work ∧ q.work ≤ C := by
    intro q hmem
    rw [generate_runs] at hmem
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hmem
    exact h i
  have hw := sumField_suffix_bound (fun q => q.work)
    (generate f (List.finRange n)).runs suffix C (fun q hmem => (hq q hmem).2) hSuffix
  have hc := sumField_suffix_bound (fun q => q.cells)
    (generate f (List.finRange n)).runs suffix C
    (fun q hmem => (hq q hmem).1.trans (hq q hmem).2) hSuffix
  have hl : (generate f (List.finRange n)).runs.length=n := by simp [generate_runs]
  simpa only [hl] using And.intro hw hc

/-- For any suffix of the generated row runs, both ledger sums are at most `r^2 * C`, with the
corresponding binary size bounds, under uniform entry bounds. -/
theorem table_ledger_suffix_bound {α : Type} {r : ℕ}
    (f : Fin r → Fin r → Observed α) (C : ℕ)
    (h : ∀ i l, (f i l).arithmetic.cells ≤ (f i l).arithmetic.work ∧
      (f i l).arithmetic.work ≤ C)
    (suffix : List (Run (Vector α r)))
    (hSuffix : ∃ pre,
      pre++suffix=(generate (fun i => tabulate (f i)) (List.finRange r)).runs) :
    ((sumField (fun q => q.work) suffix).value ≤ r^2*C ∧
      (sumField (fun q => q.work) suffix).value.size ≤ (r^2*C).size) ∧
    ((sumField (fun q => q.cells) suffix).value ≤ r^2*C ∧
      (sumField (fun q => q.cells) suffix).value.size ≤ (r^2*C).size) := by
  have hr : ∀ i, (tabulate (f i)).arithmetic.cells ≤ (tabulate (f i)).arithmetic.work ∧
      (tabulate (f i)).arithmetic.work ≤ r*C := by
    intro i
    rw [tabulate_arithmetic_eq]
    exact Structural.tabulate_bound (fun l => (f i l).arithmetic) C (h i)
  simpa only [pow_two,Nat.mul_assoc] using
    tabulate_ledger_suffix_bound (fun i => tabulate (f i)) (r*C) hr suffix hSuffix

end Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable
