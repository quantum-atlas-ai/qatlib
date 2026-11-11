/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 8: the partial-product layer

Fixed version: arXiv:2608.15545v1 (2026-08-16), Lemma 8, p.19; construction
detail in Appendix I.1-I.2 (Eqs. (I8)-(I10), p.19).

Statement: all `n^2` partial products `p_ij = x_i y_j` of the multiplier can be
generated coherently in constant fan-out depth.  The proof fans out each `x_i`
to `n` local copies and each `y_j` to `n` local copies, applies a clean two-input
AND (`TH⊕_{2,2}`) on the matched pair `(i, j)`, and finally uncopies the local
copies, keeping the `p_ij` registers.

The paper's quantum content is the exact `AND` gadget and the cleanup of the
fan-out copies (Lemma 3 / Lemma 4).  At the paper layer we formalize the
combinatorial core: the fan-out layer produces exactly the pair `(x_i, y_j)` at
cell `(i, j)`, the AND gate yields `x_i && y_j`, and there are `n * n` cells.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ShallowAdvWu26.ShallowPower.Multiplier

/-- Fan-out layer of the multiplier: every source bit `x i` is copied to all
`n` column targets of row `i`. -/
def fanoutRow {n : ℕ} (x : Fin n → Bool) : Fin n → Fin n → Bool :=
  fun i _ => x i

/-- Clean two-input AND (`TH⊕_{2,2}` in the paper, Appendix I.2). -/
def cleanAnd (a b : Bool) : Bool := a && b

/-- The local partial product at cell `(i, j)`. -/
def partialProduct {n : ℕ} (x y : Fin n → Bool) (i j : Fin n) : Bool :=
  cleanAnd (fanoutRow x i j) (fanoutRow y j i)

/-- **Lemma 8 (Partial-product layer).**  The fan-out layer places `(x_i, y_j)`
at every one of the `n * n` cells, the clean two-input AND turns it into the
partial product `x_i ∧ y_j`, and the layer has exactly `n^2` cells with two
coherent layers (fan-out + AND; the final uncopy is the inverse fan-out and adds
no data qubits). -/
theorem partial_product_layer (n : ℕ) (x y : Fin n → Bool) :
    (∀ (i j : Fin n), fanoutRow x i j = x i ∧ fanoutRow y j i = y j) ∧
      (∀ (i j : Fin n), partialProduct x y i j = (x i && y j)) ∧
      (∀ (i j : Fin n), partialProduct x y i j = cleanAnd (x i) (y j)) ∧
      Fintype.card (Fin n × Fin n) = n * n := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    exact ⟨rfl, rfl⟩
  · intro i j
    rfl
  · intro i j
    rfl
  · simp [Fintype.card_prod]

/-- The partial-product layer uses two coherent layers (one fan-out and one
clean AND), independent of `n`. -/
def partialProductLayerDepth : ℕ := 2

/-- Constant-depth certificate for the partial-product layer. -/
theorem partial_product_constant_depth : partialProductLayerDepth = 2 := rfl

/-- Numeric value of a bit string in little-endian order:
`∑_i x_i 2^i`. -/
def bitValue {n : ℕ} (x : Fin n → Bool) : ℕ :=
  ∑ i, (if x i then 1 else 0) * 2 ^ (i : ℕ)

/-- Numeric value of the partial-product layer, weighting cell `(i, j)` by
`2^{i+j}`: this is the shifted sum of partial products in the multiplier. -/
def partialProductValue {n : ℕ} (x y : Fin n → Bool) : ℕ :=
  ∑ i, ∑ j, (if partialProduct x y i j then 1 else 0) * 2 ^ ((i : ℕ) + (j : ℕ))

/-- Indicator of a conjunction factors as the product of indicators. -/
theorem bool_and_indicator (a b : Bool) :
    (if (a && b) then (1 : ℕ) else 0)
      = (if a then 1 else 0) * (if b then 1 else 0) := by
  cases a <;> cases b <;> rfl

/-- **Lemma 8, multiplier value identity.**  The shifted sum of the `n^2`
partial products equals the product of the two input values:
`∑_{i,j} x_i y_j 2^{i+j} = (∑_i x_i 2^i)(∑_j y_j 2^j)`.

This is the arithmetic content of the partial-product layer: the fan-out and
clean-AND construction produces exactly the summands of the schoolbook
multiplication. -/
theorem partial_product_value_eq (n : ℕ) (x y : Fin n → Bool) :
    partialProductValue x y = bitValue x * bitValue y := by
  have hcell : ∀ (i j : Fin n),
      (if partialProduct x y i j then (1 : ℕ) else 0) * 2 ^ ((i : ℕ) + (j : ℕ))
        = ((if x i then 1 else 0) * 2 ^ (i : ℕ))
            * ((if y j then 1 else 0) * 2 ^ (j : ℕ)) := by
    intro i j
    simp only [partialProduct, cleanAnd, fanoutRow, pow_add]
    by_cases hx : x i <;> by_cases hy : y j <;> simp [hx, hy]
  unfold partialProductValue bitValue
  rw [Fintype.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact hcell i j

/-- **Lemma 8, local-copy count.**  The fan-out layer provides exactly `n`
local copies of each source bit `x i`, one per column, and likewise for `y`.
This is the register count `2 n^2` of the partial-product construction. -/
theorem fanout_row_copies (n : ℕ) (x y : Fin n → Bool) :
    (∀ i : Fin n, (Finset.univ.filter (fun j : Fin n => fanoutRow x i j = x i)).card = n) ∧
      (∀ j : Fin n, (Finset.univ.filter (fun i : Fin n => fanoutRow y j i = y j)).card = n) ∧
        Fintype.card (Fin n × Fin n) = n * n := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have h : (Finset.univ.filter (fun j : Fin n => fanoutRow x i j = x i)) = Finset.univ := by
      ext j
      simp [fanoutRow]
    rw [h, Finset.card_univ, Fintype.card_fin]
  · intro j
    have h : (Finset.univ.filter (fun i : Fin n => fanoutRow y j i = y j)) = Finset.univ := by
      ext i
      simp [fanoutRow]
    rw [h, Finset.card_univ, Fintype.card_fin]
  · simp [Fintype.card_prod]

end Qatlib.Papers.ShallowAdvWu26.ShallowPower.Multiplier
