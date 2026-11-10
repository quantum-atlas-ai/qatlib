/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedOpExp08.MainResults.SegmentSelection
set_option warningAsError false

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

theorem main_decomposition_theorem {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k : ℕ) (hk : 1 ≤ k) (t ε : ℝ)
    (hε : 0 < ε) (hhs : ∀ X ∈ hs, Xᴴ = -X) (hH : hs.sumᴴ = -hs.sum) :
    ∃ L : List (Matrix I I ℂ),
      ‖suzukiExponentialWord L
            (t / (orderedSegments (recursiveSuzukiGenerators hs (k - 1)) (2 * k) t ε : ℝ)) -
          NormedSpace.exp (t • hs.sum)‖ ≤ ε ∧
        L.length = orderedSegments (recursiveSuzukiGenerators hs (k - 1)) (2 * k) t ε *
          (2 * hs.length * 5 ^ (k - 1)) := by
  cases Subsingleton.elim ‹DecidableEq I› (Classical.decEq I)
  obtain ⟨-, herr⟩ := lemma5_segment_selection hs k hk t ε hε hhs hH
  refine ⟨(List.replicate
      (orderedSegments (recursiveSuzukiGenerators hs (k - 1)) (2 * k) t ε)
      (recursiveSuzukiGenerators hs (k - 1))).flatten, ?_, ?_⟩
  · have hprod : (segmentWord (recursiveSuzukiGenerators hs (k - 1)) t
        (orderedSegments (recursiveSuzukiGenerators hs (k - 1)) (2 * k) t ε)).prod =
        suzukiExponentialWord
          ((List.replicate
            (orderedSegments (recursiveSuzukiGenerators hs (k - 1)) (2 * k) t ε)
            (recursiveSuzukiGenerators hs (k - 1))).flatten)
          (t / (orderedSegments (recursiveSuzukiGenerators hs (k - 1)) (2 * k) t ε : ℝ)) := by
      simp only [segmentWord, suzukiExponentialWord, List.map_flatten, List.map_replicate,
        List.prod_flatten]
    rw [← hprod]
    exact herr
  · have hlen := (recursive_suzuki_length_and_mass I hs (k - 1)).1
    rw [List.length_flatten, List.map_replicate, List.sum_replicate, hlen, smul_eq_mul]

end Qatlib.Papers.OrderedOpExp08.MainResults
