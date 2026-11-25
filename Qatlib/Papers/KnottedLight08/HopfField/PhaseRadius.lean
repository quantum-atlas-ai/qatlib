/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.HopfField.NullAlgebra

@[expose] public section

/-!
# Radius preservation along a Hopf fibre

The real four-coordinate form of a common unit phase rotates two
coordinate planes. It preserves the sphere on which the fibre lies.
-/

set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.HopfField

open Qatlib.Papers.KnottedLight08.HopfField

/-- Unit phase action preserves the squared four-coordinate radius. -/
theorem phase_radius (c s : ℝ) (q : Fin 4 → ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    square4 (phaseRotate c s q) = square4 q := by
  simp [square4, phaseRotate]
  linear_combination (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2) * h

end Qatlib.Papers.KnottedLight08.HopfField
