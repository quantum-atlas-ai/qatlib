/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.FiniteTailProgram.Value
import Qatlib.Concepts.FinitePrecision.ComputableInput.SavedTable.Indices

/-!
# Observed finite-tail programs

`ObservedKernel` equips scalar operations with arithmetic and table observations, and `Refines`
records agreement with a plain `Kernel`. The `Metered` operations propagate these observations
through table products, transfer steps, and the construction of all finite tails.

For background on classical computation and its resource models, see [KitaevShenVyalyi2002].

## Main statements

* `Refines`: value agreement between observed and plain scalar operations.
* `Metered.run`: computes a vector of tails while retaining observations.
* `Metered.driver`: initializes the outer table and runs the observed computation.

## References

* [Kitaev, Shen and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.FiniteTailProgram

/-- Scalar zero, addition, multiplication, and conjugation operations, with observations
attached to the nonconstant operations. -/
structure ObservedKernel (α : Type) where
  zero : α
  add : α → α → SavedTable.Observed α
  mul : α → α → SavedTable.Observed α
  conj : α → SavedTable.Observed α

/-- Pointwise agreement of an observed kernel with a plain kernel after taking arithmetic
values, including agreement of their zero values. -/
structure Refines {α : Type} (K : Kernel α) (M : ObservedKernel α) : Prop where
  zero_eq : M.zero = K.zero
  add_eq : ∀ x y, (M.add x y).arithmetic.value = K.add x y
  mul_eq : ∀ x y, (M.mul x y).arithmetic.value = K.mul x y
  conj_eq : ∀ x, (M.conj x).arithmetic.value = K.conj x

namespace Metered

/-- Keeps the value of `out` while adding the arithmetic work, cell counts, and table counts
recorded by `child`. -/
def retain {α β : Type} (out : SavedTable.Observed α)
    (child : SavedTable.Observed β) : SavedTable.Observed α :=
  ⟨⟨out.arithmetic.value, child.arithmetic.work + out.arithmetic.work,
    child.arithmetic.cells + out.arithmetic.cells⟩, child.counts + out.counts⟩

/-- Wraps a value with zero arithmetic work, cell count, and table count. -/
def pure {α : Type} (a : α) : SavedTable.Observed α := ⟨⟨a,0,0⟩,0⟩

/-- Computes a list-indexed dot product while retaining the observations from each
multiplication and addition. -/
def dot {α ι : Type} (M : ObservedKernel α) (x y : ι → α) :
    List ι → SavedTable.Observed α
  | [] => pure M.zero
  | i::is =>
    let p := M.mul (x i) (y i)
    let tail := dot M x y is
    let out := M.add p.arithmetic.value tail.arithmetic.value
    retain (retain out tail) p

/-- Computes a list-indexed sum while retaining the observations from all additions. -/
def sum {α ι : Type} (M : ObservedKernel α) (x : ι → α) :
    List ι → SavedTable.Observed α
  | [] => pure M.zero
  | i::is =>
    let tail := sum M x is
    retain (M.add (x i) tail.arithmetic.value) tail

/-- Tabulates observed conjugation of each entry of a vector over the supplied full index list. -/
def conjugates {α : Type} {r : ℕ} (M : ObservedKernel α)
    (is : List (Fin r)) (hi : is = List.finRange r) (v : Vector α r) :=
  SavedTable.tabulateUsing is hi (fun i => M.conj v[i])

/-- Tabulates the conjugate-transpose entries of each input table, retaining their observations. -/
def adjoints {α : Type} {k r : ℕ} (M : ObservedKernel α)
    (is : List (Fin r)) (hi : is = List.finRange r)
    (js : List (Fin k)) (hj : js = List.finRange k) (A : Vector (Table α r) k) :=
  SavedTable.tabulateUsing js hj (fun j =>
    SavedTable.tableUsing is hi (fun i l => M.conj A[j][l][i]))

/-- Tabulates observed products of entries of `v` and `cv` to form an outer table. -/
def outer {α : Type} {r : ℕ} (M : ObservedKernel α)
    (is : List (Fin r)) (hi : is = List.finRange r) (v cv : Vector α r) :=
  SavedTable.tableUsing is hi (fun i l => M.mul v[i] cv[l])

/-- Computes and observes each left multiplication of `Y` by a table in `A`. -/
def lefts {α : Type} {k r : ℕ} (M : ObservedKernel α)
    (is : List (Fin r)) (hi : is = List.finRange r)
    (js : List (Fin k)) (hj : js = List.finRange k)
    (A : Vector (Table α r) k) (Y : Table α r) :=
  SavedTable.tabulateUsing js hj (fun j => SavedTable.tableUsing is hi (fun i l =>
    dot M (fun h => A[j][i][h]) (fun h => Y[h][l]) is))

/-- Computes and observes the paired products of the supplied left and adjoint tables. -/
def products {α : Type} {k r : ℕ} (M : ObservedKernel α)
    (is : List (Fin r)) (hi : is = List.finRange r)
    (js : List (Fin k)) (hj : js = List.finRange k)
    (left adj : Vector (Table α r) k) :=
  SavedTable.tabulateUsing js hj (fun j => SavedTable.tableUsing is hi (fun i l =>
    dot M (fun h => left[j][i][h]) (fun h => adj[j][h][l]) is))

/-- Computes the observed entrywise sum of the supplied letter tables over `js`. -/
def letters {α : Type} {k r : ℕ} (M : ObservedKernel α)
    (is : List (Fin r)) (hi : is = List.finRange r)
    (js : List (Fin k)) (terms : Vector (Table α r) k) :=
  SavedTable.tableUsing is hi (fun i l => sum M (fun j => terms[j][i][l]) js)

/-- Computes a transfer step from left products, paired right products, and their sum, retaining
all intermediate observations. -/
def step {α : Type} {k r : ℕ} (M : ObservedKernel α)
    (is : List (Fin r)) (hi : is = List.finRange r)
    (js : List (Fin k)) (hj : js = List.finRange k)
    (A adj : Vector (Table α r) k) (Y : Table α r) :=
  let left := lefts M is hi js hj A Y
  let terms := products M is hi js hj left.arithmetic.value adj
  let next := letters M is hi js terms.arithmetic.value
  retain (retain next terms) left

/-- Adds two tables entrywise using the observed scalar addition operation. -/
def tailAdd {α : Type} {r : ℕ} (M : ObservedKernel α)
    (is : List (Fin r)) (hi : is = List.finRange r) (X Y : Table α r) :=
  SavedTable.tableUsing is hi (fun i l => M.add X[i][l] Y[i][l])

/-- Recursively computes `n + 1` tail tables ending in a zero table, retaining observations from
transfer steps and tail additions. -/
def run {α : Type} {k r : ℕ} (M : ObservedKernel α)
    (is : List (Fin r)) (hi : is = List.finRange r)
    (js : List (Fin k)) (hj : js = List.finRange k)
    (A adj : Vector (Table α r) k) :
    (n : ℕ) → Table α r → SavedTable.Observed (Vector (Table α r) (n+1))
  | 0, _ => pure (Vector.singleton (Vector.ofFn (fun _ : Fin r =>
      Vector.ofFn (fun _ : Fin r => M.zero))))
  | n+1, Y =>
    let next := step M is hi js hj A adj Y
    let tails := run M is hi js hj A adj n next.arithmetic.value
    let head := tailAdd M is hi Y tails.arithmetic.value[0]
    let out : SavedTable.Observed (Vector (Table α r) (n+2)) :=
      ⟨⟨tails.arithmetic.value.insertIdx 0 head.arithmetic.value,
        head.arithmetic.work, head.arithmetic.cells⟩, head.counts⟩
    retain (retain out tails) next
termination_by structural n _ => n

/-- The zero-depth observed run has the singleton zero-table vector as its arithmetic value. -/
@[simp] theorem run_value_zero {α : Type} {k r : ℕ} (M : ObservedKernel α)
    (is : List (Fin r)) (hi : is = List.finRange r)
    (js : List (Fin k)) (hj : js = List.finRange k)
    (A adj : Vector (Table α r) k) (Y : Table α r) :
    (run M is hi js hj A adj 0 Y).arithmetic.value =
      Vector.singleton (Vector.ofFn (fun _ : Fin r =>
        Vector.ofFn (fun _ : Fin r => M.zero))) := rfl

/-- The successor-depth run prepends the sum of the current table and the first child tail to
the recursively computed tail vector. -/
theorem run_value_succ {α : Type} {k r : ℕ} (M : ObservedKernel α)
    (is : List (Fin r)) (hi : is = List.finRange r)
    (js : List (Fin k)) (hj : js = List.finRange k)
    (A adj : Vector (Table α r) k) (n : ℕ) (Y : Table α r) :
    (run M is hi js hj A adj (n+1) Y).arithmetic.value =
      let next := step M is hi js hj A adj Y
      let tails := run M is hi js hj A adj n next.arithmetic.value
      let head := tailAdd M is hi Y tails.arithmetic.value[0]
      tails.arithmetic.value.insertIdx 0 head.arithmetic.value := rfl

/-- Builds the observed conjugates, adjoints, and initial outer table, then computes the
depth-`D` tail vector while retaining their observations. -/
def driver {α : Type} {k r : ℕ} (M : ObservedKernel α)
    (v : Vector α r) (A : Vector (Table α r) k) (D : ℕ) :=
  let states := List.finRange r
  let letters := List.finRange k
  let cv := conjugates M states rfl v
  let adj := adjoints M states rfl letters rfl A
  let initial := outer M states rfl v cv.arithmetic.value
  let tails := run M states rfl letters rfl A adj.arithmetic.value D initial.arithmetic.value
  retain (retain (retain tails initial) adj) cv

end Metered
end Qatlib.Concepts.FinitePrecision.ComputableInput.FiniteTailProgram
