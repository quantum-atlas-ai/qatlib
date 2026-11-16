/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.DegreeBounds.Theorem3DegreeLeQueryCountSqDegr
public import Qatlib.Concepts.QueryComplexity.DegreeBounds.CorollaryF2DegreeLeQueryCountSqDegr

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Bridges for the abstract-level claims (ABKRT 2020)

Source: arXiv:2010.12629v1, page 1 (abstract) and Section 5 (page 18).
These claims appear in the paper as *locations* rather than
as single formal propositions:

* The abstract-level claim — "the total-function D–Q upper bound and monotone
  graph-property quantum lower bound" — points at the two headline
  consequences Theorem 2 (`D(f) = O(Q(f)^4)`) and Theorem 5 (`Q(f) = Ω(n)` for
  nontrivial monotone graph properties);
* The Section 5 claim — "the mod-two degree/query combination supporting
  Theorem 5" — points at the mechanical combination
  `deg₂(f) ≤ (6(3+2√2) T)^2` used together
  with Dodis–Khanna's `deg₂ = Ω(n^2)` to derive Theorem 5.

The fixed public library supplies the per-circuit halves of both consequences; the
theorems below state exactly those fixed per-circuit facts and cite their
fully-qualified names.  The optimal-measure formulations `D(f) = O(Q(f)^4)` and
`Q(f) = Ω(n)` (defined from `detQueryCost`/`quantumQueryCost`) are stated
separately in their own claim files and are not reproved here, because the
deterministic decision-tree side (`D(f) ≤ bs(f)·deg(f)`, Midrijanis) and Dodis–Khanna's
`deg₂ = Ω(n^2)` for monotone graph properties are citations in the paper and are
not part of the fixed public library.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ApproxDegree20.MainResults.Bridges

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds
open Qatlib.Concepts.QueryComplexity.DegreeBounds
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open scoped Matrix.Norms.L2Operator

/-- **ABKRT 2020, abstract / Theorems 2–3 and 5 (support).**  Per fixed unitary
bit-query circuit deciding a total `f` with error `1/3`: both the exact-degree
bound `deg(f) ≤ (6(3+2√2) T)^2` (Theorem 3) and the mod-two bound
`deg₂(f) ≤ (6(3+2√2) T)^2` (Section 5 combination behind Theorem 5).

Bridge to `theorem3DegreeLeQueryCountSq` and
`corollaryF2DegreeLeQueryCountSq` of the fixed public library. -/
theorem abstract_degree_and_deg2_le_queryCount_sq
    (N : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (C : Circuit ((Fin N × Bool) × W)) (ψ : QState ((Fin N × Bool) × W))
    (E : Finset ((Fin N × Bool) × W)) (f : (Fin N → Bool) → Bool)
    (hC : IsUnitaryCircuit C) (hψ : Normalized ψ)
    (hs : ∀ g : Fin N → Bool,
      2 / 3 ≤ MeasureProb (Run (workspaceBitOracle (W := W) g) C ψ)
        (if f g then E else Eᶜ)) :
    (exactDegree f : ℝ) ≤
        (6 * (3 + 2 * Real.sqrt 2) * (QueryCount C : ℝ)) ^ 2 ∧
    (gf2Degree f : ℝ) ≤
        (6 * (3 + 2 * Real.sqrt 2) * (QueryCount C : ℝ)) ^ 2 :=
  ⟨theorem3DegreeLeQueryCountSq N W C ψ E f hC hψ hs,
   corollaryF2DegreeLeQueryCountSq N W C ψ E f hC hψ hs⟩

/-- **ABKRT 2020, Section 5 (page 18): mod-two degree vs. query count.**
Per fixed unitary bit-query circuit deciding a total `f` with error `1/3`,
`deg₂(f) ≤ (6(3+2√2) T)^2`; feeding Dodis–Khanna's `deg₂ = Ω(n^2)` for
nontrivial monotone graph properties yields `Q(f) = Ω(n)` (Theorem 5).

Bridge to `TriangleQuery.DegreeBounds.corollaryF2DegreeLeQueryCountSq`. -/
theorem section5_deg2_le_queryCount_sq
    (N : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (C : Circuit ((Fin N × Bool) × W)) (ψ : QState ((Fin N × Bool) × W))
    (E : Finset ((Fin N × Bool) × W)) (f : (Fin N → Bool) → Bool)
    (hC : IsUnitaryCircuit C) (hψ : Normalized ψ)
    (hs : ∀ g : Fin N → Bool,
      2 / 3 ≤ MeasureProb (Run (workspaceBitOracle (W := W) g) C ψ)
        (if f g then E else Eᶜ)) :
    (gf2Degree f : ℝ) ≤
      (6 * (3 + 2 * Real.sqrt 2) * (QueryCount C : ℝ)) ^ 2 :=
  corollaryF2DegreeLeQueryCountSq N W C ψ E f hC hψ hs

end Qatlib.Papers.ApproxDegree20.MainResults.Bridges
