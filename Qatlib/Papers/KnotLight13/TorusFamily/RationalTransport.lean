/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.RationalLineGeometry

/-!
# Poynting-flow transport kernel of the rational Bateman field

[Kedia2013TyingKnots], p150404-3 (field lines transported by the normalized
Poynting flow), [DOI](https://doi.org/10.1103/physrevlett.111.150404).
For a null Maxwell field `F = E + iB` the paper describes the electric and
magnetic field lines as frozen-in curves carried by the normalized Poynting
flow `v = S / u` (with `S = E × B` the Poynting vector and `u` the energy
density, which for null fields equals `|E|²`). This module proves the
pointwise algebraic kernel of that picture for the explicit rational pair:
the transport velocity field is defined everywhere and, wherever the field
is nonzero, the freezing relations `v × B = -E` and `v × E = B` hold exactly.
They are the algebraic core of the induction equation in transport form;
the flow, the ODE-level line preservation and the topological invariance
statement of the paper are not claimed here.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnotLight13.TorusFamily (radialAux rationalAlpha rationalBeta
  pairDenominator pair_denominator_pos)
open Qatlib.Papers.KnottedLight08.HopfField (cross3 dot3 squaredLength)

/-! ### Real vector algebra -/

/-- The real dot product is symmetric. -/
theorem dot3_comm_real (a b : Fin 3 → ℝ) : dot3 a b = dot3 b a := by
  show a 0 * b 0 + a 1 * b 1 + a 2 * b 2 = b 0 * a 0 + b 1 * a 1 + b 2 * a 2
  ring

/-- The squared length is the dot product with itself. -/
theorem dot3_self_eq_squaredLength (u : Fin 3 → ℝ) :
    dot3 u u = squaredLength u := rfl

/-- Vector triple product, outer arrangement: `(a × b) × c` expands by the
`bac − cab` rule. -/
theorem cross3_cross3_real (a b c : Fin 3 → ℝ) :
    cross3 (cross3 a b) c = fun j => dot3 a c * b j - dot3 b c * a j := by
  funext j
  fin_cases j
  · show (a 2 * b 0 - a 0 * b 2) * c 2 - (a 0 * b 1 - a 1 * b 0) * c 1 =
      (a 0 * c 0 + a 1 * c 1 + a 2 * c 2) * b 0 -
        (b 0 * c 0 + b 1 * c 1 + b 2 * c 2) * a 0
    ring
  · show (a 0 * b 1 - a 1 * b 0) * c 0 - (a 1 * b 2 - a 2 * b 1) * c 2 =
      (a 0 * c 0 + a 1 * c 1 + a 2 * c 2) * b 1 -
        (b 0 * c 0 + b 1 * c 1 + b 2 * c 2) * a 1
    ring
  · show (a 1 * b 2 - a 2 * b 1) * c 1 - (a 2 * b 0 - a 0 * b 2) * c 0 =
      (a 0 * c 0 + a 1 * c 1 + a 2 * c 2) * b 2 -
        (b 0 * c 0 + b 1 * c 1 + b 2 * c 2) * a 2
    ring

/-- The cross product is homogeneous in the first argument: dividing the
first vector through by a common scalar divides the cross product. -/
theorem cross3_div_left (u v : Fin 3 → ℝ) (k : ℝ) :
    cross3 (fun j => u j / k) v = fun j => cross3 u v j / k := by
  funext j
  fin_cases j
  · show u 1 / k * v 2 - u 2 / k * v 1 = (u 1 * v 2 - u 2 * v 1) / k
    ring
  · show u 2 / k * v 0 - u 0 / k * v 2 = (u 2 * v 0 - u 0 * v 2) / k
    ring
  · show u 0 / k * v 1 - u 1 / k * v 0 = (u 0 * v 1 - u 1 * v 0) / k
    ring

/-! ### The transport velocity field -/

/-- The electric part `E` of the rational Riemann–Silberstein field. -/
noncomputable def electricField (x y z t : ℝ) : Fin 3 → ℝ :=
  fun j => (rationalField x y z t j).re

/-- The magnetic part `B` of the rational Riemann–Silberstein field. -/
noncomputable def magneticField (x y z t : ℝ) : Fin 3 → ℝ :=
  fun j => (rationalField x y z t j).im

/-- The normalized Poynting flow `v = S / u = E × B / |E|²` of the rational
field; for a null field the energy density is `u = |E|² = |B|²`. -/
noncomputable def poyntingFlow (x y z t : ℝ) : Fin 3 → ℝ :=
  fun j => cross3 (electricField x y z t) (magneticField x y z t) j /
    squaredLength (electricField x y z t)

/-- The null invariants of the rational field give equal electric and
magnetic energy and orthogonality, unconditionally in space-time. -/
theorem poyntingFlow_null_invariants (x y z t : ℝ) :
    squaredLength (magneticField x y z t) =
      squaredLength (electricField x y z t) ∧
      dot3 (electricField x y z t) (magneticField x y z t) = 0 := by
  obtain ⟨hEB, hL⟩ := rational_field_real_invariants x y z t
  exact ⟨hL.symm, hEB⟩

/-- Freezing relation, magnetic part: wherever the field does not vanish,
the transport velocity satisfies `v × B = -E`. -/
theorem poyntingFlow_cross_magnetic (x y z t : ℝ)
    (h : squaredLength (electricField x y z t) ≠ 0) :
    cross3 (poyntingFlow x y z t) (magneticField x y z t) =
      fun j => -(electricField x y z t j) := by
  obtain ⟨hL, hEB⟩ := poyntingFlow_null_invariants x y z t
  unfold poyntingFlow
  rw [cross3_div_left, cross3_cross3_real, hEB, dot3_self_eq_squaredLength, hL]
  funext j
  field_simp
  ring

/-- Freezing relation, electric part: wherever the field does not vanish,
the transport velocity satisfies `v × E = B`. -/
theorem poyntingFlow_cross_electric (x y z t : ℝ)
    (h : squaredLength (electricField x y z t) ≠ 0) :
    cross3 (poyntingFlow x y z t) (electricField x y z t) =
      magneticField x y z t := by
  obtain ⟨hL, hEB⟩ := poyntingFlow_null_invariants x y z t
  have hBE : dot3 (magneticField x y z t) (electricField x y z t) = 0 := by
    rw [dot3_comm_real]; exact hEB
  unfold poyntingFlow
  rw [cross3_div_left, cross3_cross3_real, hBE, dot3_self_eq_squaredLength]
  funext j
  field_simp
  ring
