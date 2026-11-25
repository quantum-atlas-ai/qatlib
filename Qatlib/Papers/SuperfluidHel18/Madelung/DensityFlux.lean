/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.Madelung.PolarEquations

import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Ring

/-!
# Cartesian divergence of the Madelung density flux

The spatial operator in the polar density balance is the divergence of the
actual product of density and phase-gradient velocity.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.Madelung

open scoped BigOperators

/-- The divergence of a vector field with respect to the three Cartesian directions. -/
noncomputable def gpeDivergence (F : GpeSpace → Fin 3 → ℝ) (x : GpeSpace) : ℝ :=
  ∑ i : Fin 3, gpePartial (fun y => F y i) x i

/-- Cartesian displacements along a single coordinate add on the same affine line. -/
private theorem gpeCoordinateLine_add (x : GpeSpace) (i : Fin 3) (s r : ℝ) :
    gpeCoordinateLine (gpeCoordinateLine x i s) i r = gpeCoordinateLine x i (r + s) := by
  simp [gpeCoordinateLine, add_smul, add_assoc, add_comm]

/-- The coordinate partial at a translated point is the derivative of
the fixed line section at that translation. -/
private theorem gpePartial_line (f : GpeSpace → ℝ) (x : GpeSpace) (i : Fin 3) (s : ℝ) :
    gpePartial f (gpeCoordinateLine x i s) i = deriv (f ∘ gpeCoordinateLine x i) s := by
  have he : f ∘ gpeCoordinateLine (gpeCoordinateLine x i s) i =
      fun r => (f ∘ gpeCoordinateLine x i) (r + s) := by
    funext r
    simp only [Function.comp_apply, gpeCoordinateLine_add]
  rw [gpePartial, he, deriv_comp_add_const, zero_add]

/-- Expanding the divergence of density times phase-gradient velocity
gives exactly the spatial term in the Gross–Pitaevskii density balance. -/
theorem gpeDivergence_densityVelocity (ν : ℝ) (A θ : GpeSpace → ℝ) (x : GpeSpace)
    (hA : ContDiff ℝ 1 A) (hθ : ContDiff ℝ 2 θ) :
    gpeDivergence (fun y i => A y ^ 2 * (ν * gpePartial θ y i)) x =
      ν * (2 * A x * gpeGradDot A θ x + A x ^ 2 * gpeLaplacian θ x) := by
  have hp (i : Fin 3) :
      gpePartial (fun y => A y ^ 2 * (ν * gpePartial θ y i)) x i =
        ν * (2 * A x * gpePartial A x i * gpePartial θ x i +
          A x ^ 2 * deriv (deriv (θ ∘ gpeCoordinateLine x i)) 0) := by
    let c := gpeCoordinateLine x i
    have hc : ContDiff ℝ ⊤ c := by
      unfold c gpeCoordinateLine
      fun_prop
    have hc₀ : c 0 = x := by simp [c, gpeCoordinateLine]
    have hA₁ := ((hA.comp (hc.of_le le_top)).differentiable (by norm_num) 0).hasDerivAt
    have hθ₂ := ((hθ.comp (hc.of_le le_top)).differentiable_deriv_two 0).hasDerivAt
    have hder := ((hA₁.fun_pow 2).fun_mul (hθ₂.const_mul ν)).deriv
    have he : (fun y => A y ^ 2 * (ν * gpePartial θ y i)) ∘ c =
        fun s => ((A ∘ c) s) ^ 2 * (ν * deriv (θ ∘ c) s) := by
      funext s
      simp only [c, Function.comp_apply, gpePartial_line]
    change deriv ((fun y => A y ^ 2 * (ν * gpePartial θ y i)) ∘ c) 0 = _
    rw [he, hder]
    simp only [Function.comp_apply, hc₀, gpePartial, c]
    ring
  unfold gpeDivergence gpeGradDot gpeLaplacian
  simp_rw [hp]
  simp only [Fin.sum_univ_three]
  ring

end Qatlib.Papers.SuperfluidHel18.Madelung
