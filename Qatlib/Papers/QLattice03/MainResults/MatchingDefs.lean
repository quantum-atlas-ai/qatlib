/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Lemma41
import Qatlib.Papers.QLattice03.MainResults.Reductions
set_option warningAsError false

set_option autoImplicit false

open scoped Classical BigOperators

namespace Qatlib.Papers.QLattice03.MainResults

noncomputable def successSet (S : SubsetSumRoutine) (N r : ℕ) [NeZero N]
    (A : Fin r → ZMod N) : Finset (ZMod N) :=
  Finset.univ.filter (fun t => (S N r A t).isSome)

def IsMatching (N : ℕ) [NeZero N] (f : ZMod N → Option (ZMod N)) : Prop :=
  ∀ i j, f i = some j → j ≠ i ∧ f j = some i

def IsQMatching (N : ℕ) [NeZero N] (q : ZMod N) (f : ZMod N → Option (ZMod N)) : Prop :=
  IsMatching N f ∧ ∀ i j, f i = some j → j - i = q ∨ j - i = -q

noncomputable def qMatching1 (N : ℕ) [NeZero N] (q : ℕ) (t : ZMod N) : Option (ZMod N) :=
  if t.val % (2 * q) < q ∧ t.val + q < N then some (t + (q : ZMod N))
  else if q ≤ t.val % (2 * q) ∧ q ≤ t.val then some (t - (q : ZMod N))
  else none

noncomputable def qMatching2 (N : ℕ) [NeZero N] (q : ℕ) (t : ZMod N) : Option (ZMod N) :=
  if t.val % (2 * q) < q ∧ q ≤ t.val then some (t - (q : ZMod N))
  else if q ≤ t.val % (2 * q) ∧ t.val + q < N then some (t + (q : ZMod N))
  else none

noncomputable def matchingFamily (N : ℕ) [NeZero N] (q L : ℕ) :
    Finset (ZMod N → Option (ZMod N)) :=
  (Finset.Icc 1 L).image (fun k => qMatching1 N (k * q)) ∪
    (Finset.Icc 1 L).image (fun k => qMatching2 N (k * q))

noncomputable def matchingIntersection (N : ℕ) [NeZero N] (f : ZMod N → Option (ZMod N))
    (T : Finset (ZMod N)) : Finset (ZMod N) :=
  T.filter (fun t => (f t).isSome ∧ ∀ j, f t = some j → j ∈ T)

noncomputable def logPow (N cm : ℕ) : ℕ := ⌊(Real.log (N : ℝ)) ^ (cm : ℕ)⌋₊

noncomputable def IsGoodMatching (N : ℕ) [NeZero N] (S : SubsetSumRoutine) (r : ℕ) (cm : ℕ)
    (f : ZMod N → Option (ZMod N)) : Prop :=
  (1 / (Real.log (N : ℝ)) ^ (cm : ℝ)) ≤
    (((Finset.univ.filter (fun A : Fin r → ZMod N =>
        (N : ℝ) / (Real.log (N : ℝ)) ^ (cm : ℝ) ≤
          ((matchingIntersection N f (successSet S N r A)).card : ℝ))).card : ℝ) /
      (Fintype.card (Fin r → ZMod N) : ℝ))

end Qatlib.Papers.QLattice03.MainResults
