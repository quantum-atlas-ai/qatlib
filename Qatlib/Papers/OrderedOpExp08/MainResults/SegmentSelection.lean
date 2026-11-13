/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedOpExp08.MainResults.ErrorBounds

/-!
# Selecting Suzuki segment counts

Verifies that the selected number of segments is positive and attains a prescribed positive
error tolerance for a fixed skew-Hermitian generator list. The construction uses recursive
Suzuki words in the framework of [WiebeEtAl2010].

## Main statements

* `lemma5_segment_selection`: combines positivity of the chosen count with its norm-error
  guarantee.

## References

* [Wiebe et al., 2010][WiebeEtAl2010]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

open Matrix
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.OrderedOpExp08.MainResults

/-- For `k ≥ 1`, a skew-Hermitian generator list and sum, and `ε > 0`, the selected segment
count is positive and its segment product approximates `exp (t • hs.sum)` within `ε`
[WiebeEtAl2010]. -/
theorem lemma5_segment_selection {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k : ℕ) (hk : 1 ≤ k) (t ε : ℝ) (hε : 0 < ε)
    (hhs : ∀ X ∈ hs, Xᴴ = -X) (hH : hs.sumᴴ = -hs.sum) :
    0 < orderedSegments (recursiveSuzukiGenerators hs (k - 1)) (2 * k) t ε ∧
      ‖(segmentWord (recursiveSuzukiGenerators hs (k - 1)) t
            (orderedSegments (recursiveSuzukiGenerators hs (k - 1)) (2 * k) t ε)).prod -
          NormedSpace.exp (t • hs.sum)‖ ≤ ε := by
  have hp : 1 ≤ 2 * k := by omega
  have hc : ∀ n : ℕ, n ≤ 2 * k →
      suzukiSeries (recursiveSuzukiGenerators hs (k - 1)) n =
        ((n.factorial : ℝ)⁻¹) • hs.sum ^ n := by
    intro n hn
    exact recursive_suzuki_all_even_order_coefficients I hs (k - 1) n (by omega)
  exact selected_segment_error (recursiveSuzukiGenerators hs (k - 1)) hs.sum
    (2 * k) t ε hp hε hc (recursiveSuzukiGenerators_antiHermitian hs (k - 1) hhs) hH

end Qatlib.Papers.OrderedOpExp08.MainResults
