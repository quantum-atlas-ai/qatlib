/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.WalkFind.SearchAlgorithm.Algorithm3IsolationQuan
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# The logarithmic threshold in the collision-packing dichotomy

Fixed source: [Ambainis2007ElementDistinctness], Claim 8 (quant-ph/0311001v9, p. 22)
and its use in the isolation
step of Algorithm 3. When there are fewer than `log N` disjoint
`k`-collisions, the collision support has strictly fewer than `2k log N`
elements.

The public library proves the underlying packing dichotomy
`collision_packing_dichotomy`: for every `t`, either the collision support
has at most `2k(t-1)` elements or there are `t` pairwise disjoint
`k`-collisions. What was missing is the consumption at the source's
logarithmic threshold. This module takes `t = ceil(log N)`, the least
integer packing size at or above `log N`. The first alternative then gives
`|support| < 2k log N`.

## Main statements

* `collisionSupport_card_lt_log`: the strict logarithmic support bound under
  the absence of a `ceil(log N)` packing.
* `collision_packing_log_dichotomy`: the dichotomy at the logarithmic
  threshold.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Papers.QWalkAmbainis03.Algorithm3.CollisionPackingLog

open Qatlib.Concepts.WalkFind.SearchAlgorithm

noncomputable section

/-- The smallest integer packing size at least `log N` in Claim 8 of
[Ambainis2007ElementDistinctness]. -/
def logPackingThreshold (N : ℕ) : ℕ :=
  Nat.ceil (Real.log (N : ℝ))

/-- The packing dichotomy at the logarithmic threshold of Claim 8 of
[Ambainis2007ElementDistinctness]: either the collision support has fewer than `2k log N`
elements, or there are at least `log N` pairwise disjoint `k`-collisions in `T`. -/
theorem collision_packing_log_dichotomy {q M : ℕ} [NeZero q] [NeZero M]
    (k : ℕ) (hk : 0 < k) (x : Fin q → ZMod M) (T : Finset (Fin q))
    (N : ℕ) (hN : 1 < N) :
    ((collisionSupport k x T).card : ℝ) < 2 * (k : ℝ) * Real.log (N : ℝ) ∨
      ∃ i : Fin (logPackingThreshold N) → Fin k → Fin q,
        Function.Injective (fun z : Fin (logPackingThreshold N) × Fin k => i z.1 z.2) ∧
          ∀ a, CollisionIn k x T (Finset.univ.image (i a)) := by
  rcases collision_packing_dichotomy k hk x T (logPackingThreshold N) with hsmall | hpack
  · have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
    have ht : 0 < logPackingThreshold N := Nat.ceil_pos.mpr hlog
    have hlt : ((logPackingThreshold N - 1 : ℕ) : ℝ) < Real.log (N : ℝ) :=
      Nat.lt_ceil.mp (show logPackingThreshold N - 1 < logPackingThreshold N by omega)
    have hcast : ((collisionSupport k x T).card : ℝ) ≤
        2 * (k : ℝ) * ((logPackingThreshold N - 1 : ℕ) : ℝ) := by
      exact_mod_cast hsmall
    exact Or.inl (hcast.trans_lt (mul_lt_mul_of_pos_left hlt (by positivity)))
  · exact Or.inr hpack

/-- Claim 8 of [Ambainis2007ElementDistinctness]: under the absence of a packing
of `ceil(log N)` pairwise disjoint `k`-collisions, fewer than `2k log N`
elements of `T` participate in collisions. -/
theorem collisionSupport_card_lt_log {q M : ℕ} [NeZero q] [NeZero M]
    (k : ℕ) (hk : 0 < k) (x : Fin q → ZMod M) (T : Finset (Fin q))
    (N : ℕ) (hN : 1 < N)
    (hno : ¬ ∃ i : Fin (logPackingThreshold N) → Fin k → Fin q,
      Function.Injective (fun z : Fin (logPackingThreshold N) × Fin k => i z.1 z.2) ∧
        ∀ a, CollisionIn k x T (Finset.univ.image (i a))) :
    ((collisionSupport k x T).card : ℝ) < 2 * (k : ℝ) * Real.log (N : ℝ) :=
  (collision_packing_log_dichotomy k hk x T N hN).resolve_right hno

end

end Qatlib.Papers.QWalkAmbainis03.Algorithm3.CollisionPackingLog
