/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QChemistry14.ScalarModels.Definitions

/-!
# Nuclear-attraction size scaling

This module factors the scalar uniform-ball nuclear-entry bound into a prefactor and `N^(2/3)`.
It also transports a bound in nuclear count to the same real-power scaling in a proportionally
related basis size. See [McCleanEtAl2014].

## Main statements

* `nuclear_attraction_scaling`: For nonnegative charge and nuclear count and positive density,
  the scalar nuclear-entry bound equals `betaAB ρ S Z * N^(2/3)`.
* `max_oei_scaling`: If `M = c * N` with `c > 0` and `N ≥ 0`, a bound `hmax ≤ β * N^(2/3)`
  implies `hmax ≤ (β * c^(-2/3)) * M^(2/3)` under the stated sign assumptions.

## References

* [McClean et al., 2014][McCleanEtAl2014]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.QChemistry14.ScalarModels.SparseLocality

open Qatlib.Papers.QChemistry14.ScalarModels.Definitions

/-- For nonnegative charge and nuclear count and positive density, the scalar nuclear-entry
bound equals `betaAB ρ S Z * N^(2/3)`. -/
theorem nuclear_attraction_scaling (Z N ρ S : ℝ)
    (hZ : 0 ≤ Z) (hN : 0 ≤ N) (hρ : 0 < ρ) (_hS : 0 ≤ S) :
    nuclearEntryBound ρ S Z N = betaAB ρ S Z * N ^ (2 / 3 : ℝ) := by
  unfold nuclearEntryBound betaAB rMax
  have h2 : ∀ x : ℝ, x ^ 2 = x ^ (2 : ℝ) := fun x => (Real.rpow_natCast x 2).symm
  try rw [h2]
  have hA : 0 ≤ 3 * Z / (4 * Real.pi * ρ) := by positivity
  have hsplit : 3 * Z * N / (4 * Real.pi * ρ) = (3 * Z / (4 * Real.pi * ρ)) * N := by
    field_simp
  rw [hsplit]
  rw [← Real.rpow_mul (mul_nonneg hA hN) (1 / 3) 2]
  norm_num
  rw [Real.mul_rpow hA hN]
  ring

/-- If `M = c * N` with `c > 0` and `N ≥ 0`, a bound `hmax ≤ β * N^(2/3)` implies `hmax ≤ (β *
c^(-2/3)) * M^(2/3)` under the stated sign assumptions. See [McCleanEtAl2014]. -/
theorem max_oei_scaling (hmax β M c N : ℝ)
    (hc : 0 < c) (hN : 0 ≤ N) (_hβ : 0 ≤ β) (hM : M = c * N)
    (hbound : hmax ≤ β * N ^ (2 / 3 : ℝ)) :
    hmax ≤ (β * c ^ (-(2 / 3 : ℝ))) * M ^ (2 / 3 : ℝ) := by
  subst hM
  have hc0 : 0 ≤ c := le_of_lt hc
  have hcpow : (c * N) ^ (2 / 3 : ℝ) = c ^ (2 / 3 : ℝ) * N ^ (2 / 3 : ℝ) := by
    rw [Real.mul_rpow hc0 hN]
  rw [hcpow]
  have hcc : c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) = 1 := by
    rw [← Real.rpow_add hc]
    norm_num
  have hcoef : (β * c ^ (-(2 / 3 : ℝ))) * (c ^ (2 / 3 : ℝ) * N ^ (2 / 3 : ℝ))
      = β * N ^ (2 / 3 : ℝ) := by
    calc
      (β * c ^ (-(2 / 3 : ℝ))) * (c ^ (2 / 3 : ℝ) * N ^ (2 / 3 : ℝ))
          = β * (c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) * N ^ (2 / 3 : ℝ) := by
            ring
      _ = β * N ^ (2 / 3 : ℝ) := by rw [hcc]; ring
  rw [hcoef]
  exact hbound

end Qatlib.Papers.QChemistry14.ScalarModels.SparseLocality
