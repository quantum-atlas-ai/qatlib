/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
# SubHypergraph13 — associativity testing (Theorem 12)

Fixed source: Guerreschi--Magniez--Santha, "Quantum Algorithms for Finding
Constant-sized Sub-hypergraphs", arXiv:1310.4127 (2013), **Theorem 12, page 15**.

There is a quantum algorithm that decides whether a ternary operation
`F : X³ → X` (with `|X| = n`) is associative with high probability using
`Õ(n^{169/80}) = Õ(n^{2.1125})` queries.  It reduces to finding a `K₇` in an
associated 5-uniform hypergraph (the `7`-vertex certificate), then invokes the
sub-hypergraph algorithm.  `IsAssociative`, `AssocState`, `assocOracleMatrix`,
`assocSuccessSet` are from `SourceModel.lean`.
-/

module

public import Qatlib.Papers.SubHypergraph13.MainResults.SourceModel

@[expose] public section


/-!
# Associativity

Paper-specific definitions and results for SubHypergraph13.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Papers.SubHypergraph13.MainResults

namespace Qatlib.Papers.SubHypergraph13.MainResults.Associativity
open Qatlib.Papers.SubHypergraph13.MainResults

/-- The associativity exponent is exactly `2.1125`: `169/80 = 2.1125`. -/
theorem assoc_exponent_eq : (169 : ℝ) / 80 = 2.1125 := by norm_num

/-- The associativity exponent is below `2.113`. -/
theorem assoc_exponent_lt : (169 : ℝ) / 80 < 2.113 := by norm_num

/-! The remaining paper theorem requires unformalized probabilistic/circuit machinery and is intentionally omitted from this verified leaf. -/

end Qatlib.Papers.SubHypergraph13.MainResults.Associativity
