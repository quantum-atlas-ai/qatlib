/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.MPFRootBound
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MPFRootStep

open Matrix
open scoped BigOperators Classical Matrix.Norms.L2Operator
open CommutatorProducts MPFRootProfile MPFRootBound MPFMomentSeries
open Qatlib.Concepts.TrotterFormula.GeneralOrder

variable {I : Type} [Fintype I] [DecidableEq I]

def step (xs : List (Matrix I I ℂ)) (m : ℕ) : ℝ :=
  if 0 < mu xs m then 1 / (2 * mu xs m) else 1

omit [DecidableEq I] in

theorem step_pos (xs : List (Matrix I I ℂ)) (m : ℕ) : 0 < step xs m := by
  unfold step
  split_ifs with h
  · positivity
  · norm_num

theorem step_control (xs : List (Matrix I I ℂ)) (m : ℕ) (hm : 0 < m) :
    mu xs m * step xs m ≤ 1 / 2 := by
  unfold step
  split_ifs with h
  · have hn : mu xs m ≠ 0 := ne_of_gt h
    field_simp
    norm_num
  · have hz : mu xs m = 0 := le_antisymm (le_of_not_gt h) (mu_nonneg xs m hm)
    rw [hz]
    norm_num

theorem time_control (xs : List (Matrix I I ℂ)) (m : ℕ) (hm : 0 < m)
    (t : ℝ) (ht : |t| ≤ step xs m) : mu xs m * |t| ≤ 1 / 2 :=
  (mul_le_mul_of_nonneg_left ht (mu_nonneg xs m hm)).trans (step_control xs m hm)

theorem chebyshev_step_error (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (m : ℕ) (hm : 0 < m) (t : ℝ) (ht : |t| ≤ step xs m) :
    ‖actualMPF xs (ChebyshevNodes.node m) (ChebyshevNodes.weight m) t -
      NormedSpace.exp (t • ((-Complex.I) • xs.sum))‖ ≤
        ((16 / 3 : ℝ) * (harmonic m : ℝ) * mu xs m ^ (2 * m + 1)) * |t| ^ (2 * m + 1) :=
  chebyshev_time_power xs hxs m hm t (time_control xs m hm t ht)

theorem mu_eq_zero_of_profile_zero (xs : List (Matrix I I ℂ)) (m : ℕ) (hm : 0 < m)
    (hz : ∀ n, 3 ≤ n → pfCommAlphaSelf xs n = 0) : mu xs m = 0 := by
  apply le_antisymm _ (mu_nonneg xs m hm)
  apply csSup_le (rootSet_nonempty xs m hm)
  rintro z ⟨j, l, heven, hj, hl, hlm, rfl⟩
  have hp : positiveProduct xs j l = 0 := by
    unfold positiveProduct
    apply Finset.sum_eq_zero
    intro v hv
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨0, by omega⟩ : Fin l))
    exact hz _ (by have h := (Finset.mem_filter.mp hv).2 (⟨0, by omega⟩ : Fin l); omega)
  rw [rootCoefficient, hp, Real.zero_rpow (by positivity)]

theorem chebyshev_exact_of_mu_zero (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (m : ℕ) (hm : 0 < m) (hz : mu xs m = 0) (t : ℝ) :
    actualMPF xs (ChebyshevNodes.node m) (ChebyshevNodes.weight m) t =
      NormedSpace.exp (t • ((-Complex.I) • xs.sum)) := by
  have h := chebyshev_root_error xs hxs m hm t (by rw [hz]; norm_num)
  rw [hz, zero_mul, zero_pow (by omega), mul_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

end Qatlib.Papers.CommutLCHS26.MainResults.MPFRootStep
