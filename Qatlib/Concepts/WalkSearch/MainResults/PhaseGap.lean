/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Phase gap and approximate reflection estimates

`phaseGap` converts a real spectral parameter to an angular gap. The module bounds the phase
estimation register size and zero outcome overlap, then controls reflection error using a
decomposition into fixed and negated components, as needed in the quantum walk reflection
analysis. For background on search via quantum walks, see [MagniezNayakRolandSantha2011].

## Main statements

* `phaseGap`: The angular gap `2 * Real.arccos lam` associated with a real spectral parameter
  `lam`.
* `reflection_error_bound`: If `ψ = ψ₀ + ψ₁`, `R` fixes `ψ₀`, negates `ψ₁`, and `‖ψ₀‖ ≤ (1 /
  2)^k`, then `‖R ψ + ψ‖ ≤ 2 * (1 / 2)^k`; see [Magniez et al., Theorem
  6][MagniezNayakRolandSantha2011].

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.WalkSearch.MainResults.PhaseGap

open scoped BigOperators

/-- The angular gap `2 * Real.arccos lam` associated with a real spectral parameter `lam`. -/
noncomputable def phaseGap (lam : ℝ) : ℝ := 2 * Real.arccos lam

/-- For `0 < δ ≤ 1`, the angular gap at `1 - δ` is at least `2 * Real.sqrt δ`. -/
theorem phaseGap_ge_two_sqrt_gap {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    2 * Real.sqrt δ ≤ phaseGap (1 - δ) := by
  have hc1 : -1 ≤ 1 - δ := by linarith
  have harg : 1 - (1 - δ) ^ 2 = 2 * δ - δ ^ 2 := by ring
  have hnonneg : 0 ≤ 2 * δ - δ ^ 2 := by nlinarith
  have hsqrt : Real.sqrt δ ≤ Real.sqrt (2 * δ - δ ^ 2) := by
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hsin_eq : Real.sqrt (2 * δ - δ ^ 2) = Real.sin (Real.arccos (1 - δ)) := by
    rw [Real.sin_arccos (1 - δ), harg]
  have hsin_le : Real.sin (Real.arccos (1 - δ)) ≤ Real.arccos (1 - δ) :=
    Real.sin_le (Real.arccos_nonneg (1 - δ))
  unfold phaseGap
  linarith only [hsqrt, hsin_eq, hsin_le]

/-- A phase estimation precision exponent satisfying `2^(s - 1) < 2 * π / Δ` and `1 ≤ s` obeys
`2^s ≤ 4 * π / Δ`; see [Magniez et al., Theorem 6][MagniezNayakRolandSantha2011]. -/
theorem qpeCopies_le {Δ : ℝ} (hΔ : 0 < Δ) {s : ℕ} (hs : 1 ≤ s)
    (hmin : (2 : ℝ) ^ (s - 1) < 2 * Real.pi / Δ) :
    (2 : ℝ) ^ s ≤ 4 * Real.pi / Δ := by
  have hstep : (2 : ℝ) ^ s = 2 * (2 : ℝ) ^ (s - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hs, pow_succ']
  rw [hstep]
  have hpos : 0 < (2 * Real.pi / Δ) := by positivity
  have h2 : 2 * (2 : ℝ) ^ (s - 1) < 2 * (2 * Real.pi / Δ) := by
    linarith only [hmin]
  have h3 : 2 * (2 * Real.pi / Δ) = 4 * Real.pi / Δ := by ring
  linarith only [h2, h3]

/-- If `2^s ≥ 2 * π / Δ` and `Δ / 2 ≤ θ ≤ π / 2`, the absolute sine ratio for the zero phase
estimation outcome is at most `1 / 2`; see [Magniez et al., Theorem
6][MagniezNayakRolandSantha2011]. -/
theorem qpeZeroOverlap_le_half {Δ θ : ℝ} (hΔ : 0 < Δ) {s : ℕ}
    (hlo : 2 * Real.pi / Δ ≤ (2 : ℝ) ^ s)
    (hθlo : Δ / 2 ≤ θ) (hθhi : θ ≤ Real.pi / 2) :
    |Real.sin ((2 : ℝ) ^ s * θ) / ((2 : ℝ) ^ s * Real.sin θ)| ≤ 1 / 2 := by
  have hθ0 : 0 ≤ θ := le_trans (by linarith) hθlo
  have hsin_ge : 2 / Real.pi * θ ≤ Real.sin θ := Real.mul_le_sin hθ0 hθhi
  have h2sθ : Real.pi ≤ (2 : ℝ) ^ s * θ := by
    have h1 : (2 : ℝ) ^ s * (Δ / 2) ≤ (2 : ℝ) ^ s * θ :=
      mul_le_mul_of_nonneg_left hθlo (by positivity)
    have h2 : (2 * Real.pi / Δ) * (Δ / 2) ≤ (2 : ℝ) ^ s * (Δ / 2) :=
      mul_le_mul_of_nonneg_right hlo (by linarith)
    have h3 : (2 * Real.pi / Δ) * (Δ / 2) = Real.pi := by
      field_simp
    linarith only [h1, h2, h3]
  have hden : 2 ≤ (2 : ℝ) ^ s * Real.sin θ := by
    have h1 : (2 : ℝ) ^ s * (2 / Real.pi * θ) ≤ (2 : ℝ) ^ s * Real.sin θ :=
      mul_le_mul_of_nonneg_left hsin_ge (by positivity)
    have h2 : (2 : ℝ) ^ s * (2 / Real.pi * θ) = (2 / Real.pi) * ((2 : ℝ) ^ s * θ) := by
      ring
    have hpi := Real.pi_pos
    have h4 : 2 ≤ (2 / Real.pi) * ((2 : ℝ) ^ s * θ) := by
      have h5 : (2 / Real.pi) * Real.pi = 2 := by field_simp
      have h6 := mul_le_mul_of_nonneg_left h2sθ (by positivity : (0 : ℝ) ≤ 2 / Real.pi)
      linarith only [h5, h6]
    linarith only [h1, h2, h4]
  have hpos : 0 < (2 : ℝ) ^ s * Real.sin θ := by linarith
  have hnum : |Real.sin ((2 : ℝ) ^ s * θ)| ≤ 1 := Real.abs_sin_le_one _
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  nlinarith only [hnum, hden]

/-- If `ψ = ψ₀ + ψ₁`, `R` fixes `ψ₀`, negates `ψ₁`, and `‖ψ₀‖ ≤ (1 / 2)^k`, then `‖R ψ + ψ‖ ≤ 2
* (1 / 2)^k`; see [Magniez et al., Theorem 6][MagniezNayakRolandSantha2011]. -/
theorem reflection_error_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (R : H ≃ₗᵢ[ℂ] H) (ψ ψ₀ ψ₁ : H) (k : ℕ)
    (hdecomp : ψ = ψ₀ + ψ₁) (hR0 : R ψ₀ = ψ₀) (hR1 : R ψ₁ = -ψ₁)
    (hsmall : ‖ψ₀‖ ≤ (1 / 2 : ℝ) ^ k) :
    ‖R ψ + ψ‖ ≤ 2 * (1 / 2 : ℝ) ^ k := by
  have hsum : R ψ + ψ = (2 : ℂ) • ψ₀ := by
    rw [hdecomp, map_add, hR0, hR1]
    module
  rw [hsum, norm_smul]
  norm_num
  linarith only [hsmall]

end Qatlib.Concepts.WalkSearch.MainResults.PhaseGap
