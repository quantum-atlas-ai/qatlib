/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.JohnsonWalk

/-!
# Statement of Grover interpolation

`GroverInterpolation` specifies a quantitative search guarantee for a real unitary walk combined
with a target reflection. It records the normalization, overlap, fixed-vector, and spectral
phase hypotheses together with the desired iteration and target-overlap bounds.

The mathematical background is developed in [Ambainis2007ElementDistinctness].

## Main statements

* `GroverInterpolation`: states the search guarantee with explicit constants.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option warningAsError false
set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.GroverInterp

open Qatlib.Concepts.WalkFind.UniqueCollision

open Matrix

/-- The proposition that the stated unitary, reality, reflection, and phase-gap hypotheses yield
target overlap at least `ε^3 / 1000` in at most `8 / (ε * α)` iterations. -/
def GroverInterpolation : Prop :=
  ∀ (m : ℕ) (ε α : ℝ), 0 < ε → ε ≤ 1 → 0 < α → α ≤ 1 →
    ∀ (Uf Uw : Matrix (Fin m) (Fin m) ℂ) (start good : Fin m → ℂ),
      (star Uf * Uf) = 1 →
      (star Uw * Uw) = 1 →
      (∀ i j, (Uw i j).im = 0) →
      (∀ i, (start i).im = 0) →
      (∀ i, (good i).im = 0) →
      (∑ i, ‖start i‖ ^ 2) = 1 →
      (∑ i, ‖good i‖ ^ 2) = 1 →
      (∑ i, star (good i) * start i) = (α : ℂ) →
      Uf *ᵥ good = -good →
      (∀ v : Fin m → ℂ, (∑ i, star (v i) * good i) = 0 → Uf *ᵥ v = v) →
      Uw *ᵥ start = start →
      (∀ (ν : ℂ) (v : Fin m → ℂ), Uw *ᵥ v = ν • v →
          (∑ i, star (v i) * start i) = 0 → v ≠ 0 →
          ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ θ ≠ Real.pi ∧
            ν = Complex.exp (Complex.I * θ)) →
      ∃ t : ℕ, (t : ℝ) ≤ 8 / (ε * α) ∧
        ε ^ 3 / 1000 ≤
          ‖∑ i, star (good i) * ((Uw * Uf) ^ t *ᵥ start) i‖

end Qatlib.Concepts.WalkFind.GroverInterp
