/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Aperiodic autocorrelation energy

This module defines the aperiodic `correlation` of a finite real sequence and its
`squaredSidelobe` energy. It evaluates the final-lag correlation and obtains a lower bound on
the energy from the endpoint product. The correlation sum is a finite inner product of
overlapping shifted segments; see [HornJohnson2013] for the matrix and inner-product background.

## Main statements

* `squaredSidelobe_nonneg`: the energy is nonnegative.
* `correlation_last`: the last correlation is the endpoint product.
* `endpoint_sq_le_sidelobe`: the endpoint product gives an energy lower bound.

## References

* [Horn and Johnson, 2013][HornJohnson2013]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.SequenceEnergy.Aperiodic
open scoped Classical

/-- The aperiodic autocorrelation at lag `k`, summing products only where both sequence indices
lie below `N`. -/
def correlation {N : ℕ} (s : Fin N → ℝ) (k : Fin N) : ℝ :=
  ∑ i : Fin N, if h : i.val+k.val<N then s i*s ⟨i.val+k.val,h⟩ else 0

/-- The sum of the squared aperiodic autocorrelations over all positive lags below `N`. -/
def squaredSidelobe {N : ℕ} (s : Fin N → ℝ) : ℝ :=
  ∑ k : Fin N, if 0<k.val then correlation s k^2 else 0

/-- The squared sidelobe sum is nonnegative. -/
theorem squaredSidelobe_nonneg {N : ℕ} (s : Fin N → ℝ) : 0≤squaredSidelobe s := by
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact sq_nonneg _
  · exact le_refl 0

/-- For a nonempty sequence, autocorrelation at the final lag is the product of the first and
last entries. -/
theorem correlation_last {N : ℕ} (hN : 0<N) (s : Fin N → ℝ) :
    correlation s ⟨N-1,by omega⟩=s ⟨0,hN⟩*s ⟨N-1,by omega⟩ := by
  unfold correlation
  rw [Finset.sum_eq_single (⟨0,hN⟩ : Fin N)]
  · simp [hN]
  · intro i _ hi
    have hv : i.val≠0 := fun h => hi (Fin.ext h)
    apply dif_neg
    change ¬i.val+(N-1)<N
    omega
  · simp

/-- For a sequence of length at least two, the squared endpoint product is bounded by the
squared sidelobe sum. -/
theorem endpoint_sq_le_sidelobe {N : ℕ} (hN : 2≤N) (s : Fin N → ℝ) :
    (s ⟨0,by omega⟩*s ⟨N-1,by omega⟩)^2≤squaredSidelobe s := by
  let k : Fin N:=⟨N-1,by omega⟩
  have hk : 0<k.val := by dsimp [k]; omega
  have hsum:=Finset.single_le_sum (f:=fun k : Fin N => if 0<k.val then correlation s k^2 else 0)
    (fun j _ => by (try dsimp only); split_ifs; exact sq_nonneg _; exact le_refl 0) (Finset.mem_univ k)
  try dsimp only at hsum
  rw [if_pos hk] at hsum
  change correlation s ⟨N-1,by omega⟩^2≤squaredSidelobe s at hsum
  rwa [correlation_last (by omega)] at hsum
end Qatlib.Foundations.SequenceEnergy.Aperiodic
