/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.NullLinking.ElectricLinking
public import Qatlib.Papers.KnottedLight08.NullLinking.CompactifiedAxes

/-!
# Pole-circle representatives and zero-fiber compactification

[IrvineBouwmeester2008KnottedLight], p. 717, [DOI](https://doi.org/10.1038/nphys1056).

The affine zero fibers are lines whose one-point compactifications are circles.  The representatives
below are aliases for the existing pole circles.  The conjunctions record the actual zero-fiber
compactification and these alias equalities separately; they do not establish an orientation-compatible
ambient map, transport the other fiber, or prove linking invariance.  The Gauss integral results
therefore concern the chosen pole-circle representatives, not yet the actual compactified zero fibers.

At time zero the magnetic pole circle contains `(0, 1, 0)`, while the magnetic zero fiber is
the x-axis. Adding the point at infinity to the axis does not identify those embedded images.
Linking for the actual compactified pair can be proved directly in the compactification or
transported using a map that tracks both oriented curves and preserves their linking number.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.KnottedLight08.NullLinking

open Qatlib.Papers.SuperfluidHel18.CenterlineCL (gaussLinking)

/-- The chosen magnetic pole-circle representative.  Its identification with the
actual compactified zero fiber still requires a geometric transport theorem. -/
def magneticZeroCompactifiedRepresentative (t : ℝ) : ℝ → (Fin 3 → ℝ) :=
  cartesianCoordinates ∘ magneticPoleCircleAt t

/-- The chosen electric pole-circle representative.  Its identification with the
actual compactified zero fiber still requires a geometric transport theorem. -/
def electricZeroCompactifiedRepresentative (t : ℝ) : ℝ → (Fin 3 → ℝ) :=
  cartesianCoordinates ∘ electricPoleCircleAt t

/-- The actual magnetic zero-fiber closure is a circle, and the chosen
representative is definitionally the pole circle.  This conjunction asserts
no compatibility between the homeomorphism and the representative. -/
theorem magnetic_zero_compactified_circle_bridge (t : ℝ) :
    Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ
      closure (((↑) : ℝ × ℝ × ℝ → OnePoint (ℝ × ℝ × ℝ)) '' magneticFiberAt t 0)) ∧
      magneticZeroCompactifiedRepresentative t =
        cartesianCoordinates ∘ magneticPoleCircleAt t := by
  exact ⟨⟨compactifiedMagneticZeroFiberHomeo t⟩, rfl⟩

/-- The actual electric zero-fiber closure is a circle, and the chosen
representative is definitionally the electric pole circle.  This conjunction
asserts no compatibility between the homeomorphism and the representative. -/
theorem electric_zero_compactified_circle_bridge (t : ℝ) :
    Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ
      closure (((↑) : ℝ × ℝ × ℝ → OnePoint (ℝ × ℝ × ℝ)) '' electricFiberAt t 0)) ∧
      electricZeroCompactifiedRepresentative t =
        cartesianCoordinates ∘ electricPoleCircleAt t := by
  exact ⟨⟨compactifiedElectricZeroFiberHomeo t⟩, rfl⟩

/-- Every finite nonzero magnetic fiber links once with the chosen pole-circle representative on every
physical time slice.  This does not yet transport the result to the actual compactified zero fiber. -/
theorem gaussLinking_magnetic_circle_compactified_zero_eq_one (u v t : ℝ)
    (huv : 0 < u ^ 2 + v ^ 2) :
    gaussLinking (cartesianCoordinates ∘ magneticCircleAt u v t)
      (magneticZeroCompactifiedRepresentative t) = 1 := by
  exact gaussLinking_magnetic_circle_pole_eq_one u v t huv

/-- Every finite nonzero electric fiber links once with the chosen pole-circle representative on every
physical time slice.  This does not yet transport the result to the actual compactified zero fiber. -/
theorem gaussLinking_electric_circle_compactified_zero_eq_one (u v t : ℝ)
    (huv : 0 < u ^ 2 + v ^ 2) :
    gaussLinking (cartesianCoordinates ∘ electricCircleAt u v t)
      (electricZeroCompactifiedRepresentative t) = 1 := by
  exact gaussLinking_electric_circle_pole_eq_one u v t huv

end Qatlib.Papers.KnottedLight08.NullLinking
