/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedOpExp08.MainResults.TaylorRemainder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Matrix
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option warningAsError false

namespace Qatlib.Papers.OrderedOpExp08.MainResults

theorem theorem2_suzuki_recursion_order {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k : ℕ) (t : ℝ)
    (hhs : ∀ X ∈ hs, Xᴴ = -X) (hH : hs.sumᴴ = -hs.sum) :
    ‖suzukiExponentialWord (recursiveSuzukiGenerators hs k) t -
        NormedSpace.exp (t • hs.sum)‖ ≤
      prefixMultinomial (recursiveSuzukiGenerators hs k) (2 * (k + 1)) *
        |t| ^ (2 * (k + 1) + 1) / ((2 * (k + 1) + 1).factorial : ℝ) := by
  have hp : 1 ≤ 2 * (k + 1) := by omega
  have hc : ∀ n : ℕ, n ≤ 2 * (k + 1) →
      suzukiSeries (recursiveSuzukiGenerators hs k) n =
        ((n.factorial : ℝ)⁻¹) • hs.sum ^ n :=
    fun n hn => recursive_suzuki_all_even_order_coefficients I hs k n hn
  have h := matched_segmented_ordered (recursiveSuzukiGenerators hs k) hs.sum
    (2 * (k + 1)) 1 t hp (by norm_num) hc
    (recursiveSuzukiGenerators_antiHermitian hs k hhs) hH
  simpa using! h

theorem corollary1_lts_order {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k : ℕ) (hk : 1 ≤ k) (t : ℝ)
    (hhs : ∀ X ∈ hs, Xᴴ = -X) (hH : hs.sumᴴ = -hs.sum) :
    ‖suzukiExponentialWord (recursiveSuzukiGenerators hs (k - 1)) t -
        NormedSpace.exp (t • hs.sum)‖ ≤
      prefixMultinomial (recursiveSuzukiGenerators hs (k - 1)) (2 * k) *
        |t| ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := by
  have hp : 1 ≤ 2 * k := by omega
  have hc : ∀ n : ℕ, n ≤ 2 * k →
      suzukiSeries (recursiveSuzukiGenerators hs (k - 1)) n =
        ((n.factorial : ℝ)⁻¹) • hs.sum ^ n := by
    intro n hn
    exact recursive_suzuki_all_even_order_coefficients I hs (k - 1) n (by omega)
  have h := matched_segmented_ordered (recursiveSuzukiGenerators hs (k - 1)) hs.sum
    (2 * k) 1 t hp (by norm_num) hc
    (recursiveSuzukiGenerators_antiHermitian hs (k - 1) hhs) hH
  simpa using! h

end Qatlib.Papers.OrderedOpExp08.MainResults
