/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpatialSearch03.MainResults.Claims
public import Qatlib.Papers.SpatialSearch03.MainResults.SpectralAnalysis.TimeBound

@[expose] public section

/-!
# Lattice volume in spatial search

Section IV A uses a periodic lattice with n choices in each of d
coordinate directions. Its volume identifies the dimension of the
walk space and sets the normalization of the uniform initial state.
The same count appears in the lower time bound for the marked amplitude.
-/

set_option autoImplicit false

open Qatlib.Papers.SpatialSearch03.MainResults
open Qatlib.Papers.SpatialSearch03.MainResults.Claims

namespace Qatlib.Papers.SpatialSearch03.MainResults

/-- The periodic lattice in Section IV A has one choice among n sites
in each of its d coordinate directions. -/
theorem card_latticeVertex (d n : ℕ) :
    Fintype.card (LatticeVertex d n) = n ^ d := by
  simpa only [LatticeVertex, Fintype.card_fin] using Fintype.card_pi_const (Fin n) d

/-- The walk's initial probability is the reciprocal of the lattice volume. -/
theorem initial_probability_lattice (d n : ℕ) (γ : ℝ) (w : LatticeVertex d n) :
    successProbability d n γ w 0 = ((n ^ d : ℕ) : ℝ)⁻¹ := by
  simpa only [card_latticeVertex] using successProbability_zero d n γ w

/-- The actual evolution's amplitude lower bound on time, with the
square root of the lattice volume substituted for the vertex count. -/
theorem time_ge_lattice_amplitude (d n : ℕ) (hn : 0 < n) (γ : ℝ)
    (w : LatticeVertex d n) {t : ℝ} (ht : 0 ≤ t) :
    ‖successAmplitude d n γ w t‖ * Real.sqrt ((n ^ d : ℕ) : ℝ) - 1 ≤ t := by
  simpa only [card_latticeVertex] using time_ge_amplitude d n hn γ w ht

end Qatlib.Papers.SpatialSearch03.MainResults
