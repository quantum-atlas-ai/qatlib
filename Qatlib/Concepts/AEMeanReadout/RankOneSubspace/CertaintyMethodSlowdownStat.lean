/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma2RestrictedStat
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

/-!
# Phase-adjustment certainty specification

`CertaintyMethodSlowdown` specifies the final phase adjustment in the certainty method of
[BrassardHoyerTapp1998Counting]. In the nonintegral stopping case it requires unit-modulus
phases satisfying the cancellation equations and producing marked mass one after the ordinary
iterations.

## Main statements

* `CertaintyMethodSlowdown`: the phase equations and exact marked-mass specification.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

open Qatlib.Concepts.AEMeanReadout.RankOneSubspace.RankOneReflection

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace

open scoped Classical BigOperators

/-- Specifies unit-modulus phases satisfying the slowdown equations and producing marked mass
one after the floored ordinary-iteration count when that count is strictly below the ideal
stopping value. -/
def CertaintyMethodSlowdown : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool),
    (hA : A * A.conjTranspose = 1) →
    let a : ℝ := ∑ i, Complex.normSq (RankOneReflection.goodPart g (fun i => A i 0) i)
    ∀ (θ : ℝ), (hθ0 : 0 < θ) → (hθ1 : θ < Real.pi / 2) →
      (hmass : Real.sin θ ^ 2 = a) →
      let m₀ : ℕ := Nat.floor (Real.pi / (4 * θ) - 1 / 2)
      (hfloor : (m₀ : ℝ) < Real.pi / (4 * θ) - 1 / 2) →
      ∃ (φ ϕ : ℂ),
        ‖φ‖ = 1 ∧
        ‖ϕ‖ = 1 ∧
        (Real.cos ((2 * (m₀ : ℝ) + 1) * θ) / Real.sqrt (1 - a)) ^ 2 =
          2 * a * (1 - Complex.re φ) ∧
        ϕ * (1 - φ) * (a : ℂ) *
            (Real.sin ((2 * (m₀ : ℝ) + 1) * θ) / Real.sqrt a) =
          ((1 - φ) * (a : ℂ) + φ) *
            (Real.cos ((2 * (m₀ : ℝ) + 1) * θ) / Real.sqrt (1 - a)) ∧
        ∑ i, Complex.normSq (RankOneReflection.goodPart g
            ((RankOneReflection.iterate A g φ ϕ).mulVec
              (((RankOneReflection.iterate A g (-1) (-1)) ^ m₀).mulVec
                (fun i => A i 0))) i) = 1

end Qatlib.Concepts.AEMeanReadout.RankOneSubspace
