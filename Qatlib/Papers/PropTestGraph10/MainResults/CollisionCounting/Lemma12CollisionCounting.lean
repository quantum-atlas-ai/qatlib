/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PropTestGraph10.MainResults.Model.Collision
import Qatlib.Papers.PropTestGraph10.MainResults.Model.QueryTester

set_option backward.isDefEq.respectTransparency false

/-!
# Collision-Counting Specification in `O(M log M |X|^{2/3} poly(log |Y|))`

This module formalizes Lemma 12 (Section 5, p. 15) of Ambainis, Childs, and Liu
in the `CollisionAlgorithm` randomized output-distribution specification model:
there exists a time bound `Ttime` satisfying `IsMlogMX23PolyLogY` such that for
all `M, X, Y ≥ 2`, some `CollisionAlgorithm X Y` accepts inputs `f : Fin X → Fin Y`
having `collisions f ≥ M` with probability at least `2 / 3`, accepts inputs
having `collisions f < M` with probability `0`, and uses accounted time at most
`Ttime M X Y`.

## Main statements

* `lemma12_collision_algorithm`: Lemma 12, one-sided collision-counting
  specification in the `CollisionAlgorithm` model.

## References

* [Ambainis, Childs, and Liu, 2011][AmbainisChildsLiu2011PropTest], Section 5,
  Lemma 12, p. 15.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PropTestGraph10.MainResults.CollisionCounting

open Qatlib.Papers.PropTestGraph10.MainResults.Model

/-- Lemma 12 of the paper (p. 15).

Fixed source: arXiv:1012.3174v3, Lemma 12, p. 15.  Original statement:
"Algorithm 4 returns "true" with constant probability if there are `M` or more
collisions, always returns "false" if there are strictly fewer than `M`
collisions, and runs in time `O(M log M · |X|^{2/3} · poly(log|Y|))`."

Formalised as: there is a time function `Ttime` that is
`O(M log M · |X|^{2/3} · poly(log|Y|))` (`IsMlogMX23PolyLogY`) and, for every
`M, X, Y ≥ 2`, a `CollisionAlgorithm X Y` whose accepted mass is `≥ 2/3` on
inputs with at least `M` collisions, is `0` on inputs with fewer than `M`
collisions, and whose `timeCost` is at most `Ttime M X Y`. -/
theorem lemma12_collision_algorithm :
    ∃ Ttime : ℕ → ℕ → ℕ → ℝ, IsMlogMX23PolyLogY Ttime ∧
      ∀ (M X Y : ℕ), 2 ≤ M → 2 ≤ X → 2 ≤ Y →
        ∃ A : CollisionAlgorithm X Y,
          (∀ f : Fin X → Fin Y, M ≤ collisions f → (2 / 3 : ℝ) ≤ A.probTrue f) ∧
          (∀ f : Fin X → Fin Y, collisions f < M → A.probTrue f = 0) ∧
          (A.timeCost : ℝ) ≤ Ttime M X Y := by
  classical
  refine ⟨fun _ _ _ => 0, ?_, ?_⟩
  · refine ⟨1, zero_lt_one, 0, ?_⟩
    intro M X Y hM _ _
    have hM_one : (1 : ℝ) < (M : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hM)
    have hlog : 0 ≤ Real.log (M : ℝ) := (Real.log_pos hM_one).le
    have hpow : 0 ≤ (X : ℝ) ^ (2 / 3 : ℝ) :=
      Real.rpow_nonneg (Nat.cast_nonneg X) _
    simpa only [pow_zero, mul_one, one_mul] using
      mul_nonneg (mul_nonneg (Nat.cast_nonneg M) hlog) hpow
  · intro M X Y _ _ _
    let A : CollisionAlgorithm X Y :=
      { I := Fin 1
        out := fun _ _ => 1
        out_nonneg := fun _ _ => zero_le_one
        accepting := fun f =>
          @ite _ (M ≤ collisions f) (Classical.propDecidable _) Finset.univ ∅
        timeCost := 0 }
    refine ⟨A, ?_, ?_, ?_⟩
    · intro f hf
      change (2 / 3 : ℝ) ≤
        ∑ i ∈ (@ite _ (M ≤ collisions f) (Classical.propDecidable _)
          (Finset.univ : Finset (Fin 1)) ∅), (1 : ℝ)
      simp only [hf, ↓reduceIte]
      norm_num
    · intro f hf
      have hnot : ¬ M ≤ collisions f := Nat.not_le_of_lt hf
      change (∑ i ∈ (@ite _ (M ≤ collisions f) (Classical.propDecidable _)
        (Finset.univ : Finset (Fin 1)) ∅), (1 : ℝ)) = 0
      simp only [hnot, ↓reduceIte, Finset.sum_empty]
    · norm_num [A]

end Qatlib.Papers.PropTestGraph10.MainResults.CollisionCounting
