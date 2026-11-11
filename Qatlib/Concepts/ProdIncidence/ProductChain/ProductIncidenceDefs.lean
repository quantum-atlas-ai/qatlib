/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CodingDecoding.CssTesters.CssCode

/-!
# Binary product incidence data

Defines product vertices, edges, and faces from the endpoint maps of two finite directed
multigraphs. The matrices `boundary₁` and `boundary₂` record incidence over `ZMod 2`, and
`productCss` packages them as CSS data given their compatibility identity. The CSS construction
is described in [CalderbankShor1996].

## Main statements

* `Endpoints`: records the start and finish of every edge.
* `boundary₁`: maps product edges to vertices.
* `boundary₂`: maps product faces to edges.
* `productCss`: forms CSS data from compatible boundary maps.

## References

* [Calderbank and Shor, 1996][CalderbankShor1996]
-/

open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib

set_option autoImplicit false
namespace Qatlib.Concepts.ProdIncidence.ProductChain

/-- Endpoint maps for a finite directed multigraph with `v` vertices and `e` edges. -/
structure Endpoints (v e : ℕ) where
  start : Fin e → Fin v
  finish : Fin e → Fin v

/-- The product vertex type `Fin v₁ × Fin v₂`. -/
abbrev Vertex (v₁ v₂ : ℕ) := Fin v₁ × Fin v₂
/-- The disjoint union of edges in the first graph paired with vertices in the second, and
vertices in the first paired with edges in the second. -/
abbrev Edge (v₁ e₁ v₂ e₂ : ℕ) := (Fin e₁ × Fin v₂) ⊕ (Fin v₁ × Fin e₂)
/-- The type of product faces, consisting of one edge from each graph. -/
abbrev Face (e₁ e₂ : ℕ) := Fin e₁ × Fin e₂

/-- The total number of starts and finishes at a vertex, counting a loop twice. -/
def endpointLoad {v e : ℕ} (p : Endpoints v e) (a : Fin v) : ℕ :=
  (Finset.univ.filter fun i => p.start i = a).card +
    (Finset.univ.filter fun i => p.finish i = a).card

/-- The binary incidence matrix from product edges to vertices, with each edge contributing its
two endpoints modulo two. -/
def boundary₁ {v₁ e₁ v₂ e₂ : ℕ} (p : Endpoints v₁ e₁) (q : Endpoints v₂ e₂) :
    Matrix (Vertex v₁ v₂) (Edge v₁ e₁ v₂ e₂) (ZMod 2)
  | a, .inl b => if a.2 = b.2 then
      (if a.1 = p.start b.1 then 1 else 0) +
        (if a.1 = p.finish b.1 then 1 else 0) else 0
  | a, .inr b => if a.1 = b.1 then
      (if a.2 = q.start b.2 then 1 else 0) +
        (if a.2 = q.finish b.2 then 1 else 0) else 0

/-- The binary incidence matrix from product faces to edges, obtained from the endpoints in each
graph factor. -/
def boundary₂ {v₁ e₁ v₂ e₂ : ℕ} (p : Endpoints v₁ e₁) (q : Endpoints v₂ e₂) :
    Matrix (Edge v₁ e₁ v₂ e₂) (Face e₁ e₂) (ZMod 2)
  | .inl a, b => if a.1 = b.1 then
      (if a.2 = q.start b.2 then 1 else 0) +
        (if a.2 = q.finish b.2 then 1 else 0) else 0
  | .inr a, b => if a.2 = b.2 then
      (if a.1 = p.start b.1 then 1 else 0) +
        (if a.1 = p.finish b.1 then 1 else 0) else 0

/-- CSS data with `boundary₁` as the X-check matrix and the transpose of `boundary₂` as the
Z-check matrix, using the supplied zero-composition identity. -/
def productCss {v₁ e₁ v₂ e₂ : ℕ} (p : Endpoints v₁ e₁) (q : Endpoints v₂ e₂)
    (h : boundary₁ p q * boundary₂ p q = 0) :
    CssData (Edge v₁ e₁ v₂ e₂) (Vertex v₁ v₂) (Face e₁ e₂) where
  hX := boundary₁ p q
  hZ := (boundary₂ p q).transpose
  hcompat := by simpa only [Matrix.transpose_transpose] using h

end Qatlib.Concepts.ProdIncidence.ProductChain
