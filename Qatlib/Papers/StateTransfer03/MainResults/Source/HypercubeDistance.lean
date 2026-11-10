/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq

namespace Qatlib.Papers.StateTransfer03.MainResults.Source

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

def twolinkSiteCount (d : ℕ) : ℕ := 3 ^ d

def coordinateDistance3 (x y : Fin 3) : ℕ :=
  if x = y then 0
  else if (x = 0 ∧ y = 2) ∨ (x = 2 ∧ y = 0) then 2
  else 1

def twolinkDistance {d : ℕ} (x y : Fin d → Fin 3) : ℕ :=
  ∑ i, coordinateDistance3 (x i) (y i)

def twolinkFirst (d : ℕ) : Fin d → Fin 3 := fun _ => 0

def twolinkLast (d : ℕ) : Fin d → Fin 3 := fun _ => 2

theorem twolink_antipodal_distance (d : ℕ) :
    twolinkDistance (twolinkFirst d) (twolinkLast d) = 2 * d := by
  unfold twolinkDistance twolinkFirst twolinkLast coordinateDistance3
  simp
  omega

theorem twolink_max_distance (d : ℕ) :
    twolinkDistance (twolinkFirst d) (twolinkLast d) =
      2 * Nat.log 3 (twolinkSiteCount d) := by
  rw [twolink_antipodal_distance]
  unfold twolinkSiteCount
  rw [Nat.log_pow (by norm_num : 1 < 3)]

theorem twolink_distance_of_site_count (d : ℕ) :
    twolinkDistance (twolinkFirst d) (twolinkLast d) =
      2 * Nat.log 3 (3 ^ d) :=
  twolink_max_distance d

end

end Qatlib.Papers.StateTransfer03.MainResults.Source
