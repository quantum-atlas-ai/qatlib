/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Lemma41
import Qatlib.Papers.QLattice03.MainResults.Reductions

/-!
# Partial matchings for subset sum success sets

This module defines partial matching predicates, two gap-based candidate functions, and their
finite family `matchingFamily`. The predicate `IsGoodMatching` quantifies how often many
vertices of a subset sum success set remain paired within that set. See [Regev2004] for the
paper context.

## Main statements

* `IsQMatching`: A partial matching whose paired endpoint differences equal `q` or `-q`.
* `matchingFamily`: The union of the two candidate families with gaps `k * q` for `1 ≤ k ≤ L`.
* `IsGoodMatching`: The property that a fraction at least `1 / log(N)^cm` of input vectors have
  at least `N / log(N)^cm` success-set vertices whose partners also lie in that success set.

## References

* [Regev, 2004][Regev2004]
-/

set_option autoImplicit false

open scoped Classical BigOperators

namespace Qatlib.Papers.QLattice03.MainResults

/-- The set of targets for which the subset sum routine returns some subset on the fixed input
vector `A`. -/
noncomputable def successSet (S : SubsetSumRoutine) (N r : ℕ) [NeZero N]
    (A : Fin r → ZMod N) : Finset (ZMod N) :=
  Finset.univ.filter (fun t => (S N r A t).isSome)

/-- The condition that every defined pair has distinct endpoints and is reciprocated by the
partial map. -/
def IsMatching (N : ℕ) [NeZero N] (f : ZMod N → Option (ZMod N)) : Prop :=
  ∀ i j, f i = some j → j ≠ i ∧ f j = some i

/-- A partial matching whose paired endpoint differences equal `q` or `-q`. -/
def IsQMatching (N : ℕ) [NeZero N] (q : ZMod N) (f : ZMod N → Option (ZMod N)) : Prop :=
  IsMatching N f ∧ ∀ i j, f i = some j → j - i = q ∨ j - i = -q

/-- The first gap-`q` candidate partial map, selecting addition or subtraction of `q` by the
residue modulo `2q` and boundary conditions. -/
noncomputable def qMatching1 (N : ℕ) [NeZero N] (q : ℕ) (t : ZMod N) : Option (ZMod N) :=
  if t.val % (2 * q) < q ∧ t.val + q < N then some (t + (q : ZMod N))
  else if q ≤ t.val % (2 * q) ∧ q ≤ t.val then some (t - (q : ZMod N))
  else none

/-- The second gap-`q` candidate partial map, reversing the addition and subtraction choices
subject to its boundary conditions. -/
noncomputable def qMatching2 (N : ℕ) [NeZero N] (q : ℕ) (t : ZMod N) : Option (ZMod N) :=
  if t.val % (2 * q) < q ∧ q ≤ t.val then some (t - (q : ZMod N))
  else if q ≤ t.val % (2 * q) ∧ t.val + q < N then some (t + (q : ZMod N))
  else none

/-- The union of the two candidate families with gaps `k * q` for `1 ≤ k ≤ L`. -/
noncomputable def matchingFamily (N : ℕ) [NeZero N] (q L : ℕ) :
    Finset (ZMod N → Option (ZMod N)) :=
  (Finset.Icc 1 L).image (fun k => qMatching1 N (k * q)) ∪
    (Finset.Icc 1 L).image (fun k => qMatching2 N (k * q))

/-- The elements of `T` on which the partial map is defined and whose image also belongs to `T`. -/
noncomputable def matchingIntersection (N : ℕ) [NeZero N] (f : ZMod N → Option (ZMod N))
    (T : Finset (ZMod N)) : Finset (ZMod N) :=
  T.filter (fun t => (f t).isSome ∧ ∀ j, f t = some j → j ∈ T)

/-- The natural floor of the `cm`th power of `log N`. -/
noncomputable def logPow (N cm : ℕ) : ℕ := ⌊(Real.log (N : ℝ)) ^ (cm : ℕ)⌋₊

/-- The property that a fraction at least `1 / log(N)^cm` of input vectors have at least `N /
log(N)^cm` success-set vertices whose partners also lie in that success set. -/
noncomputable def IsGoodMatching (N : ℕ) [NeZero N] (S : SubsetSumRoutine) (r : ℕ) (cm : ℕ)
    (f : ZMod N → Option (ZMod N)) : Prop :=
  (1 / (Real.log (N : ℝ)) ^ (cm : ℝ)) ≤
    (((Finset.univ.filter (fun A : Fin r → ZMod N =>
        (N : ℝ) / (Real.log (N : ℝ)) ^ (cm : ℝ) ≤
          ((matchingIntersection N f (successSet S N r A)).card : ℝ))).card : ℝ) /
      (Fintype.card (Fin r → ZMod N) : ℝ))

end Qatlib.Papers.QLattice03.MainResults
