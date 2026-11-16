/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
# SubHypergraph13 — main query complexity (Theorem 5)

Fixed source: Guerreschi--Magniez--Santha, "Quantum Algorithms for Finding
Constant-sized Sub-hypergraphs", arXiv:1310.4127 (2013), **Theorem 5, page 5**.

For a constant-sized 3-uniform `H` with a valid loading schedule `σ` and an
admissible parameter set `P`, there is a quantum algorithm that decides
`HasCopy H G` with probability at least some constant using

  `Õ( S + Σₜ (Π_{r≤t} 1/√ε_r)(1/√δₜ) Uₜ )`  queries,

where `S = Σ e_{ijk}` and `δₜ, εₜ, Uₜ` take the paper's case values (see
`SourceModel.lean`: `setupCost`, `deltaAt`, `epsAt`, `updateAt`,
`nestedWalkCost`).  The algorithm is a nested quantum walk over the loading
schedule (§3--§4).
-/

module

public import Qatlib.Papers.SubHypergraph13.MainResults.SourceModel

@[expose] public section


/-!
# MainQueryComplexity

Paper-specific definitions and results for SubHypergraph13.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Papers.SubHypergraph13.MainResults

namespace Qatlib.Papers.SubHypergraph13.MainResults.MainQueryComplexity
open Qatlib.Papers.SubHypergraph13.MainResults

/-- The hypergraph oracle `|{u,v,w},b⟩ ↦ |{u,v,w}, b ⊕ χ_G({u,v,w})⟩` is a
unitary permutation matrix on the algorithm register.  This is the
well-definedness obligation for every query step of the Theorem 5 algorithm. -/
theorem hypergraphOracleMatrix_mem_unitaryGroup {n κ : ℕ} (G : Hypergraph3 n) :
    hypergraphOracleMatrix (n := n) (κ := κ) G ∈
      Matrix.unitaryGroup (HypergraphState n κ) ℂ := by
  unfold hypergraphOracleMatrix
  exact boolOracleMatrix_mem_unitaryGroup _

/-! The remaining paper theorem requires unformalized probabilistic/circuit machinery and is intentionally omitted from this verified leaf. -/

end Qatlib.Papers.SubHypergraph13.MainResults.MainQueryComplexity
