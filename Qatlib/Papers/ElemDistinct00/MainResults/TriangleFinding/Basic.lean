/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemDistinct00.MainResults.Defs
import Mathlib.Data.Real.Sqrt

/-!
# Symmetry of triangle witnesses

A triangle witness consists of three distinct vertices with all three connecting edges. The
theorem `isTriangle_swap` shows that exchanging the first two vertices preserves this predicate,
using symmetry of adjacency in a simple graph.

This witness symmetry is a basic tool for the triangle-finding framework associated with Theorem
10 of [BuhrmanEtAl2005].

## Main statements

* `isTriangle_swap`: `IsTriangle G a b c` is equivalent to `IsTriangle G b a c`.

## References

* [Buhrman et al., 2005][BuhrmanEtAl2005], *Quantum Algorithms for Element Distinctness*,
  arXiv:quant-ph/0007016 (2000 preprint).
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ElemDistinct00.MainResults.TriangleFinding

open Qatlib.Papers.ElemDistinct00.MainResults.Defs

/-- Exchanging the first two vertices preserves the triangle predicate in a simple graph. This
is a witness-symmetry helper for the triangle-finding setting of [BuhrmanEtAl2005]. -/
theorem isTriangle_swap {V : Type*} (G : SimpleGraph V) (a b c : V) :
    IsTriangle G a b c ↔ IsTriangle G b a c := by
  unfold IsTriangle
  constructor
  · rintro ⟨hab, hbc, hac, eab, ebc, eac⟩
    exact ⟨Ne.symm hab, hac, hbc, G.adj_symm eab, eac, ebc⟩
  · rintro ⟨hba, hac, hbc, eba, eac, ebc⟩
    exact ⟨Ne.symm hba, hbc, hac, G.adj_symm eba, ebc, eac⟩

end Qatlib.Papers.ElemDistinct00.MainResults.TriangleFinding
