/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QWalkConnect06.MainResults

@[expose] public section

/-!
# Left branch of the classical persistent walk limit

Equation (21) gives two directional rates using opposite lattice shifts. Reflecting the
lattice coordinate and exchanging the probability profiles identifies the left difference
quotient with the existing right difference quotient.
-/

set_option autoImplicit false

open Filter Qatlib.Papers.QWalkConnect06.MainResults
open scoped Topology

namespace Qatlib.Papers.QWalkConnect06.MainResults

/-- Reflection interchanges the two directional increments in Eq. (21).
The scaled left increment has the stated limit for fixed probability profiles. -/
theorem eq21_left_continuum (γ : ℝ) (pR pL : ℤ → ℝ) (n : ℤ) :
    Tendsto (fun Δt : ℝ =>
        ((2 * γ * Δt) ^ 2 * pL (n + 2)
          + (2 * γ * Δt) * (1 - 2 * γ * Δt) * (pR (n + 2) + pR n)
          + ((1 - 2 * γ * Δt) ^ 2 - 1) * pL n) / (2 * Δt))
      (𝓝[>] (0 : ℝ))
      (𝓝 (γ * (pR (n + 2) + pR n) - 2 * γ * pL n)) := by
  have hreflect : -(-n - 2) = n + 2 := by ring
  have hrate : γ * (pR (n + 2) + pR n) + (-2) * γ * pL n =
      γ * (pR (n + 2) + pR n) - 2 * γ * pL n := by ring
  simpa only [hreflect, neg_neg, hrate] using
    eq21_continuum γ (fun j => pL (-j)) (fun j => pR (-j)) (-n)

end Qatlib.Papers.QWalkConnect06.MainResults
