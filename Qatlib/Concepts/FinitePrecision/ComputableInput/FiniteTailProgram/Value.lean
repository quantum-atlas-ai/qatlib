/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable.Value

/-!
# Plain finite-tail programs

`Kernel` supplies abstract scalar operations for square vector tables. The `Plain` program
builds conjugates and adjoints, applies a transfer step, and recursively collects finite tails
in a `SavedTable.TailPacket`; `Plain.driver` assembles these computations from a vector and a
family of tables.

For background on classical computation and its resource models, see [KitaevShenVyalyi2002].

## Main statements

* `Plain.step`: sums paired left and right table products.
* `Plain.run`: constructs the recursive tail packet with a terminal zero table.
* `Plain.driver`: constructs the initial outer table and returns all tails.

## References

* [Kitaev, Shen and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.FiniteTailProgram

/-- A collection of scalar zero, addition, multiplication, and conjugation operations, without
algebraic laws imposed. -/
structure Kernel (α : Type) where
  zero : α
  add : α → α → α
  mul : α → α → α
  conj : α → α

/-- A square table represented as a length-`r` vector of length-`r` vectors. -/
abbrev Table (α : Type) (r : ℕ) := Vector (Vector α r) r

namespace Plain

/-- Computes a right-associated list-indexed sum of products using the supplied kernel. -/
def dot {α ι : Type} (K : Kernel α) (x y : ι → α) : List ι → α
  | [] => K.zero
  | i::is =>
    let p := K.mul (x i) (y i)
    let tail := dot K x y is
    K.add p tail

/-- Computes a right-associated list-indexed sum using the supplied kernel. -/
def sum {α ι : Type} (K : Kernel α) (x : ι → α) : List ι → α
  | [] => K.zero
  | i::is => let tail := sum K x is; K.add (x i) tail

/-- Tabulates a square table using an index list certified equal to `List.finRange r`. -/
def table {α : Type} {r : ℕ} (is : List (Fin r)) (hi : is = List.finRange r)
    (f : Fin r → Fin r → α) : Table α r :=
  SavedTable.Value.tabulate is hi (fun i => SavedTable.Value.tabulate is hi (f i))

/-- The square table whose entries are all the kernel zero. -/
def zeroTable {α : Type} (K : Kernel α) (r : ℕ) : Table α r :=
  Vector.ofFn (fun _ : Fin r => Vector.ofFn (fun _ : Fin r => K.zero))

/-- Tabulates kernel conjugation of each vector entry over the full index list. -/
def conjugates {α : Type} {r : ℕ} (K : Kernel α)
    (is : List (Fin r)) (hi : is = List.finRange r) (v : Vector α r) : Vector α r :=
  SavedTable.Value.tabulate is hi (fun i => K.conj v[i])

/-- Forms each input table's conjugate transpose using the supplied kernel and full index lists. -/
def adjoints {α : Type} {k r : ℕ} (K : Kernel α)
    (is : List (Fin r)) (hi : is = List.finRange r)
    (js : List (Fin k)) (hj : js = List.finRange k)
    (A : Vector (Table α r) k) : Vector (Table α r) k :=
  SavedTable.Value.tabulate js hj (fun j => table is hi (fun i l => K.conj A[j][l][i]))

/-- Forms the table with entries obtained by multiplying an entry of `v` by an entry of `cv`. -/
def outer {α : Type} {r : ℕ} (K : Kernel α)
    (is : List (Fin r)) (hi : is = List.finRange r) (v cv : Vector α r) : Table α r :=
  table is hi (fun i l => K.mul v[i] cv[l])

/-- Computes the left-product tables obtained by multiplying each table in `A` by `Y`. -/
def lefts {α : Type} {k r : ℕ} (K : Kernel α)
    (is : List (Fin r)) (hi : is = List.finRange r)
    (js : List (Fin k)) (hj : js = List.finRange k)
    (A : Vector (Table α r) k) (Y : Table α r) : Vector (Table α r) k :=
  SavedTable.Value.tabulate js hj (fun j => table is hi (fun i l =>
    dot K (fun h => A[j][i][h]) (fun h => Y[h][l]) is))

/-- Computes the paired products of the supplied left and adjoint tables. -/
def products {α : Type} {k r : ℕ} (K : Kernel α)
    (is : List (Fin r)) (hi : is = List.finRange r)
    (js : List (Fin k)) (hj : js = List.finRange k)
    (left adj : Vector (Table α r) k) : Vector (Table α r) k :=
  SavedTable.Value.tabulate js hj (fun j => table is hi (fun i l =>
    dot K (fun h => left[j][i][h]) (fun h => adj[j][h][l]) is))

/-- Sums the corresponding entries of the supplied tables over the letter list `js`. -/
def letters {α : Type} {k r : ℕ} (K : Kernel α)
    (is : List (Fin r)) (hi : is = List.finRange r)
    (js : List (Fin k)) (terms : Vector (Table α r) k) : Table α r :=
  table is hi (fun i l => sum K (fun j => terms[j][i][l]) js)

/-- Forms left products with `Y`, multiplies them by the supplied adjoint tables, and sums the
resulting tables. -/
def step {α : Type} {k r : ℕ} (K : Kernel α)
    (is : List (Fin r)) (hi : is = List.finRange r)
    (js : List (Fin k)) (hj : js = List.finRange k)
    (A adj : Vector (Table α r) k) (Y : Table α r) : Table α r :=
  let left := lefts K is hi js hj A Y
  let terms := products K is hi js hj left adj
  letters K is hi js terms

/-- Adds two tables entrywise using the kernel addition operation. -/
def tailAdd {α : Type} {r : ℕ} (K : Kernel α)
    (is : List (Fin r)) (hi : is = List.finRange r) (X Y : Table α r) : Table α r :=
  table is hi (fun i l => K.add X[i][l] Y[i][l])

/-- Recursively builds a packet of finite tails by transfer steps and table addition, with a
zero table at depth zero. -/
def run {α : Type} {k r : ℕ} (K : Kernel α)
    (is : List (Fin r)) (hi : is = List.finRange r)
    (js : List (Fin k)) (hj : js = List.finRange k)
    (A adj : Vector (Table α r) k) :
    (n : ℕ) → Table α r → SavedTable.TailPacket (Table α r) n
  | 0, _ => ⟨zeroTable K r, [], rfl⟩
  | n+1, Y =>
    let next := step K is hi js hj A adj Y
    let child := run K is hi js hj A adj n next
    let head := tailAdd K is hi Y child.head
    child.prepend head
termination_by structural n _ => n

/-- The zero-depth plain run returns the zero table and an empty tail list. -/
@[simp] theorem run_zero {α : Type} {k r : ℕ} (K : Kernel α)
    (is : List (Fin r)) (hi : is = List.finRange r)
    (js : List (Fin k)) (hj : js = List.finRange k)
    (A adj : Vector (Table α r) k) (Y : Table α r) :
    run K is hi js hj A adj 0 Y = ⟨zeroTable K r, [], rfl⟩ := rfl

/-- A successor-depth plain run recurses from the next transfer table and prepends the current
table added to the child head. -/
theorem run_succ {α : Type} {k r : ℕ} (K : Kernel α)
    (is : List (Fin r)) (hi : is = List.finRange r)
    (js : List (Fin k)) (hj : js = List.finRange k)
    (A adj : Vector (Table α r) k) (n : ℕ) (Y : Table α r) :
    run K is hi js hj A adj (n+1) Y =
      let next := step K is hi js hj A adj Y
      let child := run K is hi js hj A adj n next
      child.prepend (tailAdd K is hi Y child.head) := rfl

/-- Computes vector conjugates, table adjoints, and the initial outer table, then returns the
vector of depth-`D` tails. -/
def driver {α : Type} {k r : ℕ} (K : Kernel α)
    (v : Vector α r) (A : Vector (Table α r) k) (D : ℕ) : Vector (Table α r) (D+1) :=
  let states := List.finRange r
  let letters := List.finRange k
  let cv := conjugates K states rfl v
  let adj := adjoints K states rfl letters rfl A
  let initial := outer K states rfl v cv
  let tails := run K states rfl letters rfl A adj D initial
  SavedTable.Value.finish tails

end Plain
end Qatlib.Concepts.FinitePrecision.ComputableInput.FiniteTailProgram
