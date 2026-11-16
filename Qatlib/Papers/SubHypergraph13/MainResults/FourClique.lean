/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
# SubHypergraph13 — 4-clique detection (Theorem 11)

Fixed source: Guerreschi--Magniez--Santha, "Quantum Algorithms for Finding
Constant-sized Sub-hypergraphs", arXiv:1310.4127 (2013), **Theorem 11, page 15**.

There is a quantum algorithm that detects whether a 3-uniform hypergraph on `n`
vertices contains a `K₄` (a copy of `completeHypergraph 4`) with high
probability using `Õ(n^{241/128}) = O(n^{1.883})` queries.  The paper obtains it
by instantiating Theorem 5 with the explicit loading schedule
`(1,2,3,4,{1,2},{1,3},{1,4},{2,3},{2,4},{3,4},{1,2,3},{1,2,4},{1,3,4},{2,3,4})`
and parameters `r₁=n^{1/2}, r₂=n^{3/4}, r₃=n^{7/8}, r₄=n^{3/4}`,
`f₁₂=f₁₃=n^{5/4}, f₁₄=n^{147/128}, f₂₃=n^{193/128}, f₂₄=n^{83/64}, f₃₄=n^{181/128}`,
`e₁₂₃=n^{241/128}, e₁₂₄=n^{217/128}, e₁₃₄=n^{211/128}, e₂₃₄=n^{193/128}`.
-/

module

public import Qatlib.Papers.SubHypergraph13.MainResults.SourceModel

@[expose] public section


/-!
# FourClique

Paper-specific definitions and results for SubHypergraph13.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Papers.SubHypergraph13.MainResults

namespace Qatlib.Papers.SubHypergraph13.MainResults.FourClique
open Qatlib.Papers.SubHypergraph13.MainResults

/-- The 4-clique exponent is strictly below `1.883`: `241/128 < 1.883`. -/
theorem four_clique_exponent_lt : (241 : ℝ) / 128 < 1.883 := by norm_num

/-- The 4-clique exponent equals `1.8828125`. -/
theorem four_clique_exponent_value : (241 : ℝ) / 128 = 1.8828125 := by norm_num

/-! The remaining paper theorem requires unformalized probabilistic/circuit machinery and is intentionally omitted from this verified leaf. -/

end Qatlib.Papers.SubHypergraph13.MainResults.FourClique
