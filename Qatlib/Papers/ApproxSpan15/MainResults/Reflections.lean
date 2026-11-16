/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ApproxSpan15.MainResults.Source.SpanProgramModel

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 3.1 — implementing the reflection `2Π_{H(x)} − I`

Ito--Jeffery, *Approximate Span Programs*, arXiv:1507.00432v1, Lemma 3.1 (p. 13).

The source constructs the reflection about `H(x)` from the input-independent
reflections `R_{i,a} = I − 2Π_{H_i^⊥ ∩ H_{i,a}}` and two oracle queries per
register `i`: one query maps `|i⟩|ψ_{i,j}⟩ ↦ |i⟩|x_i⟩|ψ_{i,j}⟩`, the conditioned
reflection is free, and one further query uncomputes the input register.

This module proves the action of the actual continuous linear reflection on a
sum of selected input components, the true component, and a rejected orthogonal
component. The two-query circuit implementation remains an open bridge.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ApproxSpan15.MainResults.Reflections

open Qatlib.Papers.ApproxSpan15.MainResults

variable {q n : ℕ} {H V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- Algebraic reflection decomposition underlying Lemma 3.1. Selected
components in `H_{i,x_i}` and `H_true` are fixed, while the orthogonal rejected
component changes sign. This is an operator identity, with no dummy query-cost
witness; realizing it with two oracle calls still requires circuit semantics. -/
theorem source_lemma_3_1 (P : SpanProgram q n H V) (x : Fin n → Fin q)
    (v : Fin n → H) (t f : H)
    (hv : ∀ i, v i ∈ P.Hja i (x i)) (ht : t ∈ P.Htrue)
    (hf : f ∈ (P.Hx x)ᗮ) :
    SpanProgram.reflectionAbout (P.Hx x) ((∑ i, v i) + t + f) =
      (∑ i, v i) + t - f := by
  have hs : (∑ i, v i) + t ∈ P.Hx x := by
    apply Submodule.add_mem
    · apply Submodule.sum_mem
      intro i _
      exact (le_sup_left : (⨆ j, P.Hja j (x j)) ≤ P.Hx x)
        ((le_iSup (fun j => P.Hja j (x j)) i) (hv i))
    · exact (le_sup_right : P.Htrue ≤ P.Hx x) ht
  have hp : (P.Hx x).starProjection ((∑ i, v i) + t) = (∑ i, v i) + t :=
    Submodule.starProjection_eq_self_iff.mpr hs
  have hz : (P.Hx x).starProjection f = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff (P.Hx x)).mpr hf
  change (2 : ℝ) • (P.Hx x).starProjection ((∑ i, v i) + t + f) -
    ((∑ i, v i) + t + f) = _
  rw [map_add, hp, hz, add_zero]
  module

end Qatlib.Papers.ApproxSpan15.MainResults.Reflections
