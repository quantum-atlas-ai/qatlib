/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QChemImprove14.MainResults.SourceModel
import Mathlib.Analysis.Asymptotics.Theta

set_option backward.isDefEq.respectTransparency false

/-!
# Claim c005 — gate depth improves from `N^9` to `O(N^7)`

Hastings--Wecker--Bauer--Troyer, fixed arXiv:1403.1539v2, Sec. 6
("Discussion"), and the abstract.

Ref. 17 reported gate depth scaling as `N^9`.  Cancelling Jordan–Wigner
strings removes one factor of `N` (`N^9 → N^8`); nesting/parallelizing the
rotations removes another (`N^8 → N^7`).  The resulting depth is `O(N^7)`,
an `Θ(N²)` improvement.  Even treating Clifford operations as free, the
previous circuits scale as `N^8` and the present ones as `N^7`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Qatlib.Papers.QChemImprove14.MainResults

/-- **Claim c005 (`N^9 → N^8`)**: cancelling the Jordan–Wigner strings removes
one factor of `N`. -/
theorem jwCancellation_factor (N : ℕ) (hN : 0 < N) :
    refGateDepth N / jwCancelledDepth N = (N : ℝ) := by
  unfold refGateDepth jwCancelledDepth
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hpow : (N : ℝ) ^ 9 = (N : ℝ) ^ 8 * (N : ℝ) := by ring
  rw [hpow]; field_simp

/-- **Claim c005 (`N^8 → N^7`)**: nesting the rotations removes one more
factor of `N`.  This is the "even if Clifford operations are free" step. -/
theorem nesting_factor (N : ℕ) (hN : 0 < N) :
    jwCancelledDepth N / nestedGateDepth N = (N : ℝ) := by
  unfold jwCancelledDepth nestedGateDepth
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hpow : (N : ℝ) ^ 8 = (N : ℝ) ^ 7 * (N : ℝ) := by ring
  rw [hpow]; field_simp

/-- **Claim c005 (combined `N^9 → N^7`)**: the two cancellation steps compose
to a factor `N² = Θ(N²)`, i.e. Ref. 17's `N^9` becomes `N^7`. -/
theorem combined_factor (N : ℕ) (hN : 0 < N) :
    refGateDepth N / nestedGateDepth N = (N : ℝ) ^ 2 := by
  unfold refGateDepth nestedGateDepth
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hpow : (N : ℝ) ^ 9 = (N : ℝ) ^ 7 * (N : ℝ) ^ 2 := by ring
  rw [hpow]; field_simp

/-- **Claim c005 (`O(N^7)`)**: the resulting gate depth is `O(N^7)`. -/
theorem nestedGateDepth_isBigO :
    Asymptotics.IsBigO Filter.atTop nestedGateDepth (fun N : ℕ => (N : ℝ) ^ 7) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards with N
  simp [nestedGateDepth]

end Qatlib.Papers.QChemImprove14.MainResults
