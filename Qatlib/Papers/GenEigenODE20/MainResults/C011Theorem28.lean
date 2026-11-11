/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GenEigenODE20.MainResults.SourceModel
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryLowerBounds

set_option backward.isDefEq.respectTransparency false

/-!
# c011 — Theorem 28 (query lower bound for singular generalized eigenproblems)

Shao--Liu, arXiv:2010.15027v2, Theorem 28, p. 23.

> Suppose we are given access to copies of a quantum state `|ψ⟩` and query
> access to the entries of `n × n` matrices `A` and `B`.  If `A|ψ⟩ = λ B|ψ⟩`
> and `B` is singular, then finding `λ` requires at least `Ω(√n)` quantum
> queries to `A` and `B`.

The singular case is a search problem: the null right-hand side hides which
generalized eigenvalue a marked instance carries, and a decoder must identify
the mark.  The frozen `workspace_search_query_lower_bound` is precisely the
bounded-error adversary bound for that setting: a fixed unitary circuit and a
decoder that identifies every mark with success at least `2/3` force
`Fintype.card I ≤ 64 · (QueryCount C)²`.

This module instantiates that theorem at the paper's `n` marked instances
(`I = Fin n`, with `n ≥ 6`), and derives the advertised square-root bound
`√n ≤ 8 · QueryCount C`, i.e. `QueryCount C ≥ √n / 8`.  The GEP data are
carried by `SingularGEPQuerySetup`, which records the generalized eigenvector
relation and the singularity of `B`; the lower bound itself is a property of
the query problem and is proved from the frozen adversary theorem.
-/

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout
open Qatlib.Concepts.SketchArith.GramAction
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.GenEigenODE20.MainResults

/-- A singular generalized eigenproblem instance at fixed matrix dimension `n`:
`A v = λ B v` with `B` not invertible, as in Theorem 28. -/
structure SingularGEPQuerySetup (n : ℕ) where
  /-- The left-hand matrix `A`. -/
  A : Matrix (Fin n) (Fin n) ℂ
  /-- The right-hand matrix `B`, required singular. -/
  B : Matrix (Fin n) (Fin n) ℂ
  /-- The generalized eigenvalue carried by the instance. -/
  lam : ℂ
  /-- The witness state `|ψ⟩` (as a coordinate vector). -/
  eigenvector : Fin n → ℂ
  /-- `B` is singular. -/
  B_singular : ¬ IsUnit B
  /-- `A|ψ⟩ = λ B|ψ⟩`. -/
  eigen_relation : Matrix.mulVec A eigenvector = lam • Matrix.mulVec B eigenvector

variable {W : Type} [Fintype W] [DecidableEq W]

/-- **Theorem 28, squared form.**  For a bounded-error quantum algorithm that
identifies one of the `n` marked singular-GEP instances, the number of queries
is at least `√n / 8`. -/
theorem theorem28_sqrt_query_lower_bound
    (n : ℕ) (hn : 6 ≤ n)
    (G : Fin n → SingularGEPQuerySetup n)
    (C : Circuit ((Fin n × Bool) × W)) (ψ : QState ((Fin n × Bool) × W))
    (decode : ((Fin n × Bool) × W) → Option (Fin n))
    (hC : IsUnitaryCircuit C) (hψ : Normalized ψ)
    (hmark : ∀ x : Fin n, MeasureProb
        (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ)
        (Finset.univ.filter (fun p => decode p = some x)) ≥ 2 / 3) :
    Real.sqrt (n : ℝ) ≤ 8 * (QueryCount C : ℝ) := by
  have hcard : 6 ≤ Fintype.card (Fin n) := by simpa using hn
  have h := workspace_search_query_lower_bound C ψ decode hC hψ hcard hmark
  have h' : Real.sqrt (n : ℝ) ≤ Real.sqrt (64 * (QueryCount C : ℝ) ^ 2) := by
    have hsq := Real.sqrt_le_sqrt (by simpa [Fintype.card_fin] using h)
    simpa [Fintype.card_fin] using hsq
  have hq : (0 : ℝ) ≤ (QueryCount C : ℝ) := by exact_mod_cast Nat.zero_le _
  have hsqrt : Real.sqrt (64 * (QueryCount C : ℝ) ^ 2)
      = 8 * (QueryCount C : ℝ) := by
    rw [show (64 : ℝ) = 8 ^ 2 by norm_num,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 8 ^ 2),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8), Real.sqrt_sq hq]
  linarith [h', hsqrt]

/-- **Theorem 28 in query-count form.**  A bounded-error algorithm for the
singular GEP must make at least `√n / 8` queries to `A` and `B`. -/
theorem theorem28_query_lower_bound
    (n : ℕ) (hn : 6 ≤ n)
    (G : Fin n → SingularGEPQuerySetup n)
    (C : Circuit ((Fin n × Bool) × W)) (ψ : QState ((Fin n × Bool) × W))
    (decode : ((Fin n × Bool) × W) → Option (Fin n))
    (hC : IsUnitaryCircuit C) (hψ : Normalized ψ)
    (hmark : ∀ x : Fin n, MeasureProb
        (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ)
        (Finset.univ.filter (fun p => decode p = some x)) ≥ 2 / 3) :
    Real.sqrt (n : ℝ) / 8 ≤ (QueryCount C : ℝ) := by
  have h := theorem28_sqrt_query_lower_bound n hn G C ψ decode hC hψ hmark
  linarith

end Qatlib.Papers.GenEigenODE20.MainResults
