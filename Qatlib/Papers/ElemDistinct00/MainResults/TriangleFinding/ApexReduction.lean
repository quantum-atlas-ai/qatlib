/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemDistinct00.MainResults.Defs
import Qatlib.Papers.ElemDistinct00.MainResults.TriangleFinding.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Apex graphs and triangle cost algebra

The graph `apexGraph G` adds a new vertex adjacent to every original vertex while preserving the
original edges. The equivalence `hasTriangle_apexGraph_iff` proves that this enlarged graph
contains a triangle exactly when `G` has an edge, giving the graph construction used in the
triangle-finding setting of [BuhrmanEtAl2005].

The separate identity `triangle_cost_identity` simplifies the product of square-root cost terms
to `n + sqrt (n * m)` for positive natural parameters. It records the algebraic cost scale
associated with Theorem 10.

The graph equivalence and scalar identity are separate results. This module
does not simulate graph-query circuits or prove triangle-finding upper or lower
query bounds.

## Main statements

* `hasTriangle_apexGraph_iff`: adding a universal apex converts edge existence into triangle
  existence.
* `triangle_cost_identity`: `(sqrt (n^2 / m) + sqrt n) * sqrt m = n + sqrt (n * m)` for positive
  `n` and `m`.

## References

* [Buhrman et al., 2005][BuhrmanEtAl2005], *Quantum Algorithms for Element Distinctness*,
  arXiv:quant-ph/0007016 (2000 preprint).
-/

set_option autoImplicit false
noncomputable section

open scoped Classical

namespace Qatlib.Papers.ElemDistinct00.MainResults.TriangleFinding

open Qatlib.Papers.ElemDistinct00.MainResults.Defs

/-- Adjoin an apex vertex to `G`, represented by `none`, and join it to every original vertex
`some v` while retaining all original edges. -/
def apexGraph {n : ℕ} (G : SimpleGraph (Fin n)) : SimpleGraph (Option (Fin n)) where
  Adj a b :=
    match a, b with
    | none, none => False
    | none, some _ => True
    | some _, none => True
    | some u, some v => G.Adj u v
  symm := ⟨by
    intro a b h
    cases a with
    | none => cases b with
      | none => exact h
      | some _ => trivial
    | some u => cases b with
      | none => trivial
      | some v => exact G.adj_symm h⟩
  loopless := ⟨fun a => by
    cases a with
    | none => exact id
    | some u => exact G.loopless.irrefl u⟩

/-- Two original vertices are adjacent in the apex graph exactly when they are adjacent in `G`. -/
@[simp] theorem apexGraph_adj_some_some {n : ℕ} (G : SimpleGraph (Fin n))
    (u v : Fin n) : (apexGraph G).Adj (some u) (some v) ↔ G.Adj u v := Iff.rfl

/-- The new apex is adjacent to every original vertex. -/
@[simp] theorem apexGraph_adj_none_some {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    (apexGraph G).Adj none (some v) := trivial

/-- The apex vertex has no loop in the apex graph. -/
@[simp] theorem apexGraph_not_adj_none_none {n : ℕ} (G : SimpleGraph (Fin n)) :
    ¬ (apexGraph G).Adj none none := id

/-- The graph obtained by adjoining a universal apex contains a triangle exactly when the
original graph has an edge. This is the graph-construction component of the triangle-finding
reduction in [BuhrmanEtAl2005]. -/
theorem hasTriangle_apexGraph_iff {n : ℕ} (G : SimpleGraph (Fin n)) :
    HasTriangle (apexGraph G) ↔ ∃ a b : Fin n, G.Adj a b := by
  constructor
  · rintro ⟨a, b, c, hab, hbc, hac, eab, ebc, eac⟩

    cases a with
    | none =>
      cases b with
      | none => exact absurd rfl hab
      | some b' =>
        cases c with
        | none => exact absurd eac (apexGraph_not_adj_none_none G)
        | some c' => exact ⟨b', c', ebc⟩
    | some a' =>
      cases b with
      | none =>
        cases c with
        | none => exact absurd rfl hbc
        | some c' => exact ⟨a', c', eac⟩
      | some b' => exact ⟨a', b', eab⟩
  · rintro ⟨a, b, hab⟩
    refine ⟨some a, some b, none, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      exact G.loopless.irrefl b (Option.some.inj h ▸ hab)
    · exact Option.some_ne_none b
    · exact Option.some_ne_none a
    · exact hab
    · exact trivial
    · exact trivial

/-- For positive natural `n` and `m`, the expression `(sqrt (n^2 / m) + sqrt n) * sqrt m` equals
`n + sqrt (n * m)`. This is the algebraic simplification of the triangle cost scale in
[BuhrmanEtAl2005]. -/
theorem triangle_cost_identity {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (Real.sqrt ((n : ℝ) ^ 2 / (m : ℝ)) + Real.sqrt (n : ℝ)) * Real.sqrt (m : ℝ)
      = (n : ℝ) + Real.sqrt ((n : ℝ) * (m : ℝ)) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnm : Real.sqrt ((n : ℝ) ^ 2 / (m : ℝ)) * Real.sqrt (m : ℝ) = (n : ℝ) := by
    rw [← Real.sqrt_mul (div_nonneg (sq_nonneg _) hm0.le)]
    rw [show (n : ℝ) ^ 2 / (m : ℝ) * (m : ℝ) = (n : ℝ) ^ 2 by field_simp]
    exact Real.sqrt_sq hn0
  have hcross : Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) = Real.sqrt ((n : ℝ) * (m : ℝ)) :=
    (Real.sqrt_mul hn0 (m : ℝ)).symm
  calc (Real.sqrt ((n : ℝ) ^ 2 / (m : ℝ)) + Real.sqrt (n : ℝ)) * Real.sqrt (m : ℝ)
      = Real.sqrt ((n : ℝ) ^ 2 / (m : ℝ)) * Real.sqrt (m : ℝ)
        + Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) := by ring
    _ = (n : ℝ) + Real.sqrt ((n : ℝ) * (m : ℝ)) := by rw [hnm, hcross]

end Qatlib.Papers.ElemDistinct00.MainResults.TriangleFinding
