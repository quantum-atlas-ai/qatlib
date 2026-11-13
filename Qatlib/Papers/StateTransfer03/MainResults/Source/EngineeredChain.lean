/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StateTransfer03.MainResults.Defs

/-!
# Engineered nearest-neighbor chain

`engineeredCoupling` defines the couplings `lam / 2 * sqrt (n * (N - n))`, and `engineeredAdj`
places them on neighboring entries of a path matrix. The file establishes positivity of interior
couplings, reflection symmetry, and vanishing entries away from neighboring sites. See
[ChristandlEtAl2004].

## Main statements

* `engineeredCoupling_pos`: interior couplings are positive for positive `lam`.
* `engineeredCoupling_reflect`: couplings are invariant under `n ↦ N - n`.
* `engineeredAdj_diag`: all diagonal entries vanish.

## References

* [Christandl et al., 2004][ChristandlEtAl2004]
-/

namespace Qatlib.Papers.StateTransfer03.MainResults.Source

open Matrix
open scoped BigOperators
open Qatlib.Papers.StateTransfer03.MainResults.Defs

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

/-- The engineered chain coupling `lam / 2 * sqrt (n * (N - n))`. -/
def engineeredCoupling (N : ℕ) (lam : ℝ) (n : ℕ) : ℝ :=
  lam / 2 * Real.sqrt ((n : ℝ) * ((N : ℝ) - (n : ℝ)))

/-- The real matrix with engineered couplings between consecutive sites and zero entries
elsewhere. -/
def engineeredAdj (N : ℕ) (lam : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    if i.val + 1 = j.val then engineeredCoupling N lam (i.val + 1)
    else if j.val + 1 = i.val then engineeredCoupling N lam (j.val + 1)
    else 0

/-- The engineered coupling is positive when `lam > 0` and `1 ≤ n < N`. See
[ChristandlEtAl2004]. -/
theorem engineeredCoupling_pos (N : ℕ) (lam : ℝ) (hlam : 0 < lam)
    (n : ℕ) (hn : 1 ≤ n) (hnN : n < N) :
    0 < engineeredCoupling N lam n := by
  unfold engineeredCoupling
  have h1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h2 : (0 : ℝ) < (N : ℝ) - (n : ℝ) := by
    have : (n : ℝ) < (N : ℝ) := by exact_mod_cast hnN
    linarith
  have hprod : 0 < (n : ℝ) * ((N : ℝ) - (n : ℝ)) := mul_pos h1 h2
  have hsqrt : 0 < Real.sqrt ((n : ℝ) * ((N : ℝ) - (n : ℝ))) :=
    Real.sqrt_pos.mpr hprod
  have : 0 < lam / 2 := by positivity
  exact mul_pos this hsqrt

/-- For `n ≤ N`, reflecting the edge index from `n` to `N - n` preserves the engineered
coupling. See [ChristandlEtAl2004]. -/
theorem engineeredCoupling_reflect (N : ℕ) (lam : ℝ) (n : ℕ) (hn : n ≤ N) :
    engineeredCoupling N lam n = engineeredCoupling N lam (N - n) := by
  unfold engineeredCoupling
  have hcast : ((N - n : ℕ) : ℝ) = (N : ℝ) - (n : ℝ) := by
    rw [Nat.cast_sub hn]
  rw [hcast]
  rw [show ((N : ℝ) - (n : ℝ)) * ((N : ℝ) - ((N : ℝ) - (n : ℝ))) =
      (n : ℝ) * ((N : ℝ) - (n : ℝ)) by ring]

/-- An entry of the engineered chain matrix vanishes when its two sites are not consecutive in
either order. See [ChristandlEtAl2004]. -/
theorem engineeredAdj_eq_zero (N : ℕ) (lam : ℝ) (i j : Fin N)
    (hij : i.val + 1 ≠ j.val) (hji : j.val + 1 ≠ i.val) :
    engineeredAdj N lam i j = 0 := by
  unfold engineeredAdj
  rw [ite_eq_right hij, ite_eq_right hji]

/-- Every diagonal entry of the engineered chain matrix is zero. See [ChristandlEtAl2004]. -/
theorem engineeredAdj_diag (N : ℕ) (lam : ℝ) (i : Fin N) :
    engineeredAdj N lam i i = 0 := by
  unfold engineeredAdj
  have h1 : ¬ i.val + 1 = i.val := by omega
  rw [ite_eq_right h1, ite_eq_right h1]

end

end Qatlib.Papers.StateTransfer03.MainResults.Source
