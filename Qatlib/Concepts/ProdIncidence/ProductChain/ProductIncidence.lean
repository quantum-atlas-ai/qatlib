/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProdIncidence.ProductChain.ProductIncidenceDefs
import Mathlib.Data.Fintype.BigOperators
import Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
import Qatlib.Concepts.CodingDecoding.CssTesters.CssPauli

/-!
# Product incidence identities and CSS locality

Proves that the explicit binary boundary matrices of a product of finite directed multigraphs
form a chain complex. Bounds on their row and column weights give the check weight and qubit
incidence of `productCss`, in the CSS framework of [CalderbankShor1996]. Loops and parallel
edges are permitted; endpoint multiplicities are counted by `endpointLoad`.

## Main statements

* `product_boundary_squared_zero`: the product boundary maps compose to zero.
* `product_column_locality`: edge and face boundary columns have weights at most two and four.
* `product_css_locality`: bounds the size and locality parameters from endpoint loads.

## References

* [Calderbank and Shor, 1996][CalderbankShor1996]
-/

open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib
open Qatlib

set_option autoImplicit false

namespace Qatlib.Concepts.ProdIncidence.ProductChain

open scoped BigOperators

/-- The Hamming weight of a binary function is bounded by the sum of pointwise upper bounds on
its nonzero indicators. -/
private theorem weight_le_sum {α : Type*} [Fintype α]
    (f : α → ZMod 2) (w : α → ℕ)
    (hw : ∀ a, (if f a ≠ 0 then 1 else 0) ≤ w a) :
    bitWeight f ≤ ∑ a, w a := by
  classical
  have he : bitWeight f = ∑ a, if f a ≠ 0 then 1 else 0 := by
    exact (Finset.sum_boole (R := ℕ) (fun a => f a ≠ 0) Finset.univ).symm
  rw [he]
  exact Finset.sum_le_sum fun a _ => hw a

/-- The nonzero indicator of a sum in `ZMod 2` is bounded by the sum of the two nonzero
indicators. -/
private theorem indicator_add_le (x y : ZMod 2) :
    (if x + y ≠ 0 then 1 else 0 : ℕ) ≤
      (if x ≠ 0 then 1 else 0) + (if y ≠ 0 then 1 else 0) := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]
  split_ifs <;> omega

/-- The two explicit boundary matrices of a product of finite directed multigraphs compose to
zero over `ZMod 2`. -/
theorem product_boundary_squared_zero :
    ∀ (v₁ e₁ v₂ e₂ : ℕ) (p : Endpoints v₁ e₁) (q : Endpoints v₂ e₂),
      boundary₁ p q * boundary₂ p q = 0 := by
  intro v₁ e₁ v₂ e₂ p q
  ext a b
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
    boundary₁, boundary₂, mul_add, mul_ite, Finset.sum_add_distrib]
  split_ifs <;> decide

/-- Every column of `boundary₁` has Hamming weight at most two, and every column of `boundary₂`
has Hamming weight at most four. -/
theorem product_column_locality :
    ∀ (v₁ e₁ v₂ e₂ : ℕ) (p : Endpoints v₁ e₁) (q : Endpoints v₂ e₂),
      (∀ a : Edge v₁ e₁ v₂ e₂, bitWeight (fun b => boundary₁ p q b a) ≤ 2) ∧
        (∀ a : Face e₁ e₂, bitWeight (fun b => boundary₂ p q b a) ≤ 4) := by
  intro v₁ e₁ v₂ e₂ p q
  constructor
  · intro a
    cases a with
    | inl a =>
      let w : Vertex v₁ v₂ → ℕ := fun b =>
        (if b = (p.start a.1, a.2) then 1 else 0) +
          (if b = (p.finish a.1, a.2) then 1 else 0)
      have hw := weight_le_sum (fun b => boundary₁ p q b (.inl a)) w (by
        intro b
        by_cases h : b.2 = a.2
        · simpa [boundary₁, w, Prod.ext_iff, h] using
            indicator_add_le (if b.1 = p.start a.1 then 1 else 0)
              (if b.1 = p.finish a.1 then 1 else 0)
        · simp [boundary₁, w, Prod.ext_iff, h])
      simpa [w, Finset.sum_add_distrib] using hw
    | inr a =>
      let w : Vertex v₁ v₂ → ℕ := fun b =>
        (if b = (a.1, q.start a.2) then 1 else 0) +
          (if b = (a.1, q.finish a.2) then 1 else 0)
      have hw := weight_le_sum (fun b => boundary₁ p q b (.inr a)) w (by
        intro b
        by_cases h : b.1 = a.1
        · simpa [boundary₁, w, Prod.ext_iff, h] using
            indicator_add_le (if b.2 = q.start a.2 then 1 else 0)
              (if b.2 = q.finish a.2 then 1 else 0)
        · simp [boundary₁, w, Prod.ext_iff, h])
      simpa [w, Finset.sum_add_distrib] using hw
  · intro a
    let w : Edge v₁ e₁ v₂ e₂ → ℕ := Sum.elim
      (fun b => (if b = (a.1, q.start a.2) then 1 else 0) +
        (if b = (a.1, q.finish a.2) then 1 else 0))
      (fun b => (if b = (p.start a.1, a.2) then 1 else 0) +
        (if b = (p.finish a.1, a.2) then 1 else 0))
    have hw := weight_le_sum (fun b => boundary₂ p q b a) w (by
      intro b
      cases b with
      | inl b =>
        by_cases h : b.1 = a.1
        · simpa [boundary₂, w, Prod.ext_iff, h] using
            indicator_add_le (if b.2 = q.start a.2 then 1 else 0)
              (if b.2 = q.finish a.2 then 1 else 0)
        · simp [boundary₂, w, Prod.ext_iff, h]
      | inr b =>
        by_cases h : b.2 = a.2
        · simpa [boundary₂, w, Prod.ext_iff, h] using
            indicator_add_le (if b.1 = p.start a.1 then 1 else 0)
              (if b.1 = p.finish a.1 then 1 else 0)
        · simp [boundary₂, w, Prod.ext_iff, h])
    simpa [w, Fintype.sum_sum_type, Finset.sum_add_distrib] using hw

/-- The row weight of `boundary₁` at a product vertex is bounded by the sum of the endpoint
loads of its two coordinates. -/
private theorem vertex_row_bound {v₁ e₁ v₂ e₂ : ℕ}
    (p : Endpoints v₁ e₁) (q : Endpoints v₂ e₂) (a : Vertex v₁ v₂) :
    bitWeight (boundary₁ p q a) ≤ endpointLoad p a.1 + endpointLoad q a.2 := by
  classical
  let w : Edge v₁ e₁ v₂ e₂ → ℕ := Sum.elim
    (fun b => if a.2 = b.2 then
      (if p.start b.1 = a.1 then 1 else 0) +
        (if p.finish b.1 = a.1 then 1 else 0) else 0)
    (fun b => if a.1 = b.1 then
      (if q.start b.2 = a.2 then 1 else 0) +
        (if q.finish b.2 = a.2 then 1 else 0) else 0)
  have hw := weight_le_sum (boundary₁ p q a) w (by
    intro b
    cases b with
    | inl b =>
      by_cases h : a.2 = b.2
      · simpa [boundary₁, w, h, eq_comm] using
          indicator_add_le (if a.1 = p.start b.1 then 1 else 0)
            (if a.1 = p.finish b.1 then 1 else 0)
      · simp [boundary₁, w, h]
    | inr b =>
      by_cases h : a.1 = b.1
      · simpa [boundary₁, w, h, eq_comm] using
          indicator_add_le (if a.2 = q.start b.2 then 1 else 0)
            (if a.2 = q.finish b.2 then 1 else 0)
      · simp [boundary₁, w, h])
  simpa [w, Fintype.sum_sum_type, Fintype.sum_prod_type, Finset.sum_add_distrib,
    endpointLoad,
    Finset.sum_comm] using hw

/-- The number of faces incident to a product edge is bounded by the endpoint load in the other
graph factor. -/
private theorem face_incidence_bound {v₁ e₁ v₂ e₂ : ℕ}
    (p : Endpoints v₁ e₁) (q : Endpoints v₂ e₂) (a : Edge v₁ e₁ v₂ e₂) :
    bitWeight (fun b => boundary₂ p q a b) ≤
      match a with
      | .inl b => endpointLoad q b.2
      | .inr b => endpointLoad p b.1 := by
  classical
  cases a with
  | inl a =>
    let w : Face e₁ e₂ → ℕ := fun b => if a.1 = b.1 then
      (if q.start b.2 = a.2 then 1 else 0) +
        (if q.finish b.2 = a.2 then 1 else 0) else 0
    have hw := weight_le_sum (fun b => boundary₂ p q (.inl a) b) w (by
      intro b
      by_cases h : a.1 = b.1
      · simpa [boundary₂, w, h, eq_comm] using
          indicator_add_le (if a.2 = q.start b.2 then 1 else 0)
            (if a.2 = q.finish b.2 then 1 else 0)
      · simp [boundary₂, w, h])
    simpa [w, Fintype.sum_prod_type, Finset.sum_add_distrib,
      endpointLoad] using hw
  | inr a =>
    let w : Face e₁ e₂ → ℕ := fun b => if a.2 = b.2 then
      (if p.start b.1 = a.1 then 1 else 0) +
        (if p.finish b.1 = a.1 then 1 else 0) else 0
    have hw := weight_le_sum (fun b => boundary₂ p q (.inr a) b) w (by
      intro b
      by_cases h : a.2 = b.2
      · simpa [boundary₂, w, h, eq_comm] using
          indicator_add_le (if a.1 = p.start b.1 then 1 else 0)
            (if a.1 = p.finish b.1 then 1 else 0)
      · simp [boundary₂, w, h])
    simpa [w, Fintype.sum_prod_type, Finset.sum_add_distrib,
      endpointLoad] using hw

/-- For endpoint loads bounded by `d₁` and `d₂`, the product CSS data have `e₁ * v₂ + v₁ * e₂`
qubits, check weight at most `max (d₁ + d₂) 4`, and qubit incidence at most `2 + max d₁ d₂`. -/
theorem product_css_locality :
    ∀ (v₁ e₁ v₂ e₂ d₁ d₂ : ℕ) (p : Endpoints v₁ e₁) (q : Endpoints v₂ e₂)
        (h : boundary₁ p q * boundary₂ p q = 0),
      (∀ a, endpointLoad p a ≤ d₁) → (∀ a, endpointLoad q a ≤ d₂) →
      (productCss p q h).numQubits = e₁ * v₂ + v₁ * e₂ ∧
        (productCss p q h).checkWeight ≤ max (d₁ + d₂) 4 ∧
        (productCss p q h).qubitIncidence ≤ 2 + max d₁ d₂ := by
  intro v₁ e₁ v₂ e₂ d₁ d₂ p q h hp hq
  classical
  refine ⟨by simp [CssData.numQubits, Edge], ?_, ?_⟩
  · apply max_le
    · apply Finset.sup_le
      intro a _
      exact ((vertex_row_bound p q a).trans (Nat.add_le_add (hp _) (hq _))).trans
        (le_max_left _ _)
    · apply Finset.sup_le
      intro a _
      exact ((product_column_locality v₁ e₁ v₂ e₂ p q).2 a).trans (le_max_right _ _)
  · apply Finset.sup_le
    intro a _
    have hx := (product_column_locality v₁ e₁ v₂ e₂ p q).1 a
    have hz := face_incidence_bound p q a
    change bitWeight (fun b => boundary₁ p q b a) +
      bitWeight (fun b => boundary₂ p q a b) ≤ 2 + max d₁ d₂
    apply Nat.add_le_add hx
    cases a with
    | inl a => exact (hz.trans (hq _)).trans (le_max_right _ _)
    | inr a => exact (hz.trans (hp _)).trans (le_max_left _ _)

end Qatlib.Concepts.ProdIncidence.ProductChain
