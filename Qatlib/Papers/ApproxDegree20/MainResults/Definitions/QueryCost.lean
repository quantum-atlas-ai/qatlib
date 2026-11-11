/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds.Support
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery

set_option backward.isDefEq.respectTransparency false

/-!
# Query complexity measures used in the paper's introduction

Source: arXiv:2010.12629v1, Section 1 (pages 1–3).  The paper states its headline
results (`D(f) = O(Q(f)^4)`, `Q(f) = Ω(n)` for monotone graph properties) in terms
of the *optimal* measures `D(f)` and `Q(f)`.  Neither measure is defined in the
paper (they are standard), so we fix them here as infima:

* `detQueryCost f` — deterministic decision-tree depth `D(f)`, the least worst-case
  query count of a finite adaptive Boolean decision tree that computes `f` on every
  input (`BoolQueryTree` of the frozen `ClassicalQuery` module);
* `quantumQueryCost f` — bounded-error quantum query complexity `Q(f)`, the least
  query count of a unitary circuit over an arbitrary finite workspace that computes
  `f` with two-sided error `1/3`, in the same fixed-word workspace bit-oracle model
  used by the frozen per-circuit statements (`Run`, `QueryCount`, `MeasureProb`,
  `workspaceBitOracle`);
* `MonotoneGraphProperty f` — nontrivial monotone graph property of an `n`-vertex
  graph given by its edge set `Sym2 (Fin n) → Bool` (Theorem 5, page 3).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ApproxDegree20.MainResults.Definitions

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch

/-- Deterministic query complexity `D(f)`: the least worst-case query count of a
finite adaptive Boolean decision tree computing `f` (page 2). -/
def detQueryCost {I : Type} [Fintype I] [DecidableEq I] (f : (I → Bool) → Bool) : ℕ :=
  sInf {m : ℕ | ∃ T : BoolQueryTree I Bool,
    (∀ x, (BoolQueryTree.Run x T).1 = f x) ∧ BoolQueryTree.MaxQueries T = m}

/-- Bounded-error quantum query complexity `Q(f)`: the least query count of a
unitary circuit over an arbitrary finite workspace deciding `f` with two-sided
error `1/3` through a fixed basis readout event (page 2). -/
def quantumQueryCost {I : Type} [Fintype I] [DecidableEq I] (f : (I → Bool) → Bool) : ℕ :=
  sInf {m : ℕ | ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
    (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W))
    (E : Finset ((I × Bool) × W)),
    IsUnitaryCircuit C ∧ Normalized ψ ∧
    (∀ g : I → Bool,
      2 / 3 ≤ MeasureProb (Run (workspaceBitOracle (W := W) g) C ψ)
        (if f g then E else Eᶜ)) ∧
    QueryCount C = m}

/-- A nontrivial monotone graph property of an `n`-vertex graph, edges indexed
by `Sym2 (Fin n)` (Theorem 5, page 3): monotone under adding edges, neither always
true nor always false. -/
def MonotoneGraphProperty {n : ℕ} (f : (Sym2 (Fin n) → Bool) → Bool) : Prop :=
  (∀ G H : Sym2 (Fin n) → Bool, (∀ e, G e = true → H e = true) → f G = true → f H = true) ∧
  (∃ G, f G = true) ∧ (∃ G, f G = false)

end Qatlib.Papers.ApproxDegree20.MainResults.Definitions
