/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MUBCompletion26.Completion.MUB6GraphGramGap
import Qatlib.Concepts.UnbiasedBases.ThreeBasis.MutuallyUnbiasedGauge
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Gram gaps for labeled and rephased rays

This module transfers the graph Gram-gap estimate of [Sun2026] to six rays chosen from a labeled
family. The construction `positionGraph` pulls adjacency back along the labels, and `chosenRays`
multiplies the chosen states by phases.

Unit phases preserve squared overlap norms. For a normalized family separated on graph nonedges,
`chosenRays_gram_gap` proves a squared Gram defect greater than 1/1200, including choices with
repeated labels.

## Main statements

* `positionGraph_triangleFree`: Pulling back adjacency preserves triangle-freeness.
* `chosenRays_overlap`: Unit rephasing preserves squared overlaps.
* `chosenRays_gram_gap`: Any six selected and rephased rays satisfy the uniform Gram gap.

## References

* [Sun, 2026][Sun2026]
-/

open Qatlib.Concepts.UnbiasedBases.ThreeBasis
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.MUBCompletion26.Completion

/-- The simple graph on six positions obtained by pulling back `G` along `label`. -/
def positionGraph {ι : Type*} (G : SimpleGraph ι) (label : Fin 6 → ι) :
    SimpleGraph (Fin 6) where
  Adj i j := G.Adj (label i) (label j)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun i => G.loopless.irrefl (label i)⟩

/-- Pulling back a triangle-free graph along any labeling of six positions gives a triangle-free
graph. -/
theorem positionGraph_triangleFree {ι : Type*} (G : SimpleGraph ι)
    (hG : G.CliqueFree 3) (label : Fin 6 → ι) :
    (positionGraph G label).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  exact hG _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hac,hbc⟩)

/-- The six states obtained by selecting labels from `V` and multiplying each selected state by
its assigned phase. -/
noncomputable def chosenRays {ι : Type*} {d : ℕ} (V : ι → QState (Fin d))
    (label : Fin 6 → ι) (phase : Fin 6 → ℂ) : Fin 6 → QState (Fin d) :=
  fun j i => phase j * V (label j) i

/-- If each phase has squared norm one, squared inner-product norms between chosen rays equal
those between the corresponding labeled states. -/
theorem chosenRays_overlap {ι : Type*} {d : ℕ} (V : ι → QState (Fin d))
    (label : Fin 6 → ι) (phase : Fin 6 → ℂ) (hp : ∀ i, Complex.normSq (phase i) = 1)
    (i j : Fin 6) : Complex.normSq (Qatlib.Foundations.PureStateMath.Inner (chosenRays V label phase i)
      (chosenRays V label phase j)) = Complex.normSq (Qatlib.Foundations.PureStateMath.Inner (V (label i)) (V (label j))) := by
  change Complex.normSq (Qatlib.Foundations.PureStateMath.Inner (fun t => phase i * V (label i) t)
    (fun t => phase j * V (label j) t)) = _
  rw [Qatlib.Concepts.UnbiasedBases.ThreeBasis.inner_rephase, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_conj, hp i, hp j, one_mul, one_mul]

/-- For a normalized family with overlap norms greater than 1/120 on distinct nonadjacent labels
of a triangle-free graph, any six labeled rays with unit phases have squared Gram defect
greater than 1/1200. -/
theorem chosenRays_gram_gap {ι : Type*} {d : ℕ} (G : SimpleGraph ι)
    (hG : G.CliqueFree 3) (V : ι → QState (Fin d)) (hn : ∀ a, Normalized (V a))
    (hsep : ∀ a b, a ≠ b → ¬ G.Adj a b →
      (1 : ℝ) / 120 < ‖Qatlib.Foundations.PureStateMath.Inner (V a) (V b)‖)
    (label : Fin 6 → ι) (phase : Fin 6 → ℂ) (hp : ∀ i, Complex.normSq (phase i) = 1) :
    (1 : ℝ) / 1200 < gramDefectSquared (chosenRays V label phase) := by
  classical
  have hs (i j : Fin 6) (_hij : i ≠ j) (hno : ¬ (positionGraph G label).Adj i j) :
      (1 : ℝ) / 14400 < Complex.normSq
        (Qatlib.Foundations.PureStateMath.Inner (chosenRays V label phase i) (chosenRays V label phase j)) := by
    rw [chosenRays_overlap V label phase hp]
    by_cases he : label i = label j
    · rw [he, (normalized_iff_inner_self (V (label j))).mp (hn (label j))]
      norm_num
    · have h := hsep (label i) (label j) he hno
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (Qatlib.Foundations.PureStateMath.Inner (V (label i)) (V (label j)))]
  have h := gram_gap_of_triangleFree (chosenRays V label phase)
    (positionGraph G label) (positionGraph_triangleFree G hG label)
    ((1 : ℝ) / 14400) (by norm_num) hs
  norm_num at h ⊢
  exact h

end Qatlib.Papers.MUBCompletion26.Completion
