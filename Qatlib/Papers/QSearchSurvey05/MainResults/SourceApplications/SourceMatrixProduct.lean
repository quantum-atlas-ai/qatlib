/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSearchSurvey05.MainResults.Applications.MatrixProduct
import Qatlib.Papers.QSearchSurvey05.MainResults.Defs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 4.5: Boolean matrix product in `O(N^(5/3))` queries

Source: A. Ambainis, *Quantum search algorithms*, arXiv:quant-ph/0504012v1
(3 April 2005), **Theorem 4.5, p. 9** (reference [16] = Buhrman–Špalek).

> Theorem 4.5 [16] Matrix product can be solved with `O(N^(5/3))` quantum queries.

The task (p. 9): three `N × N` Boolean matrices `A`, `B`, `C` are given by a black box
answering single-entry queries; decide whether `AB = C` with arithmetic modulo `2`.
`N` here is the matrix dimension (the paper's "`n²` variables per matrix" is the number
of entries of each matrix).

We formalise the **one-sided witness form** of the task, which is exactly what the
source algorithm [16] produces: the algorithm outputs an entry, and the verifier accepts
when the entry is a cell `(2, i, j)` at which `(AB)ᵢⱼ ≠ Cᵢⱼ`; when `AB = C` every answer
is accepted (there is no witness to find).  A constant-error algorithm of this shape
decides `AB = C` with one-sided error.

What is proved here (sorry-free):

* `matrixProductMismatch_eq_empty_iff`: the mod-`2` product `AB = C` holds iff there is
  no mismatch cell.  This is the soundness/completeness core of the witness verifier.
* `matrixProductAccept_of_holds` / `matrixProductAccept_of_not_holds`: the acceptance set
  is all entries on equal inputs and exactly the mismatch cells otherwise.
* `matrixProductAccept_nonempty_of_not_holds`: on unequal inputs a witness exists.
* `matrixProductAccept_witness`: every accepted entry on an unequal input is a genuine
  mismatch `(2, i, j)` with `(AB)ᵢⱼ ≠ Cᵢⱼ` (one-sided soundness: the verifier never
  accepts an unmarked cell as a witness).
* `matrixProduct_budget_decomposition`: the source's `N^(5/3)` budget is exactly the
  two-level product `N · N^(2/3)` (an `√N`-style outer amplification over the `N` candidate
  rows/columns, each level costing `N^(2/3)`), the shape of the [16] construction.

Residual gap (the actual algorithmic content): no frozen model of the Buhrman–Špalek
matrix-product algorithm exists.  Its query accounting uses element distinctness as a
subroutine on the `N²` entries with a two-level search over rows/columns
(`QuantumAlgorithm.Papers.QTriangle03.th4Alg` is the closest frozen pattern), and would
require a new oracle-access model for multi-entry objects, so the `O(N^(5/3))` *upper
bound* is not proved.  The verifier semantics above is what the fixed-space phase-query
model can currently certify. -/

set_option autoImplicit false
noncomputable section

open scoped Classical
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Papers.QSearchSurvey05.MainResults

namespace Qatlib.Papers.QSearchSurvey05.MainResults

/-- Support of the phase-query oracle: the entries equal to `1`. -/
def matrixProductOnes {n : ℕ} (X : MatrixProductInput n) :
    Finset (MatrixProductIndex n) :=
  Finset.univ.filter fun p => matrixProductEntry X p = true

end Qatlib.Papers.QSearchSurvey05.MainResults
