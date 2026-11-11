/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.SinhWidth

/-!
# Finite error bounds for sinh quadrature

This module combines strip mesh estimates with discarded lattice tails for the finite sinh
quadrature rule in [AftabAnTrivisa2026]. It supplies bounds with the actual lattice tail and,
for sufficiently large endpoints, complementary-error-function and exponential tail estimates.

The final formulations replace explicit pole gaps with a half-width below `analyticWidth`.

## Main statements

* `finite_error`: the mesh-plus-lattice-tail bound.
* `original_error_bounds`: analytic-width estimates with explicit tail bounds.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhError
open Complex Matrix Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.L2Operator ComplexOrder
open Qatlib.Papers.CommutLCHS26.MainResults.KernelStrip
open Qatlib.Papers.CommutLCHS26.MainResults.SinhStrip
open Qatlib.Papers.CommutLCHS26.MainResults.SinhWidth (analyticWidth original_mesh_error)
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhRule
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.Trapezoid (cutoff)
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget (tailConstant)
open Qatlib.Concepts.QsvtCore.ApproxToolkit (erf)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local instance : ContinuousENorm (Matrix ι ι ℂ) :=
  SeminormedAddGroup.toESeminormedAddMonoid.toContinuousENorm

/-- Under the stated strip and pole-gap conditions, the finite sinh quadrature error is at most
the exponential mesh bound plus the discarded lattice tail; see [Aftab et al., Proposition
4.17][AftabAnTrivisa2026]. -/
theorem finite_error (n : ℕ) (b c d η β : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hη : 0 < η) (hβ₀ : 0 < β) (hβ : β < Real.pi / 4)
    (hgap : η * Real.sin β < 1) (hbn : n = 0 ∨ η * Real.sin β < b)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T h : ℝ} (hT : 0 ≤ T) (hh : 0 < h) (Y : ℝ) :
    ‖(∫ k : ℝ, integrand n b c d T H L (k : ℂ)) -
        finiteIdeal n b c d T η h H L (cutoff Y h)‖ ≤
      2 * stripMass n b c d η β (T * ‖L‖) / (Real.exp (2 * Real.pi * β / h) - 1) +
        latticeTail n b c d T η h H L (cutoff Y h) := by
  have hs := finite_error_split n b c d hb hc H L hH hL hT hη hh (cutoff Y h)
  have hm := transformed_mesh_error n b c d η β hb hc hη hβ₀ hβ hgap hbn H L hH hL hT hh
  exact hs.trans (_root_.add_le_add hm (le_refl _))

/-- When the scaled endpoint is at least one, the finite sinh quadrature error is bounded by the
mesh term plus the explicit complementary-error-function tail under the stated hypotheses. -/
theorem finite_error_erfc (n : ℕ) (b c d η β : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hη : 0 < η) (hβ₀ : 0 < β) (hβ : β < Real.pi / 4)
    (hgap : η * Real.sin β < 1) (hbn : n = 0 ∨ η * Real.sin β < b)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T h : ℝ} (hT : 0 ≤ T) (hh : 0 < h) (Y : ℝ)
    (hlarge : 1 ≤ η / (2 * c) * Real.sinh (h * cutoff Y h)) :
    ‖(∫ k : ℝ, integrand n b c d T H L (k : ℂ)) -
        finiteIdeal n b c d T η h H L (cutoff Y h)‖ ≤
      2 * stripMass n b c d η β (T * ‖L‖) / (Real.exp (2 * Real.pi * β / h) - 1) +
        tailConstant n b c d * (1 - erf (η * Real.sinh (h * cutoff Y h) / (2 * c))) := by
  exact (finite_error n b c d η β hb hc hη hβ₀ hβ hgap hbn H L hH hL hT hh Y).trans
    (_root_.add_le_add (le_refl _)
      (actual_tail_bounds n b c d hb hc H L hH hL hT hη hh Y hlarge).1)

/-- When the scaled endpoint is at least one, the finite sinh quadrature error is bounded by the
mesh term plus the explicit exponential tail under the stated hypotheses. -/
theorem finite_error_exp (n : ℕ) (b c d η β : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hη : 0 < η) (hβ₀ : 0 < β) (hβ : β < Real.pi / 4)
    (hgap : η * Real.sin β < 1) (hbn : n = 0 ∨ η * Real.sin β < b)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T h : ℝ} (hT : 0 ≤ T) (hh : 0 < h) (Y : ℝ)
    (hlarge : 1 ≤ η / (2 * c) * Real.sinh (h * cutoff Y h)) :
    ‖(∫ k : ℝ, integrand n b c d T H L (k : ℂ)) -
        finiteIdeal n b c d T η h H L (cutoff Y h)‖ ≤
      2 * stripMass n b c d η β (T * ‖L‖) / (Real.exp (2 * Real.pi * β / h) - 1) +
        tailConstant n b c d * Real.exp (-(η / (2 * c)) ^ 2 * Real.sinh (h * cutoff Y h) ^ 2) := by
  exact (finite_error_erfc n b c d η β hb hc hη hβ₀ hβ hgap hbn H L hH hL hT hh Y hlarge).trans
    (_root_.add_le_add (le_refl _)
      (actual_tail_bounds n b c d hb hc H L hH hL hT hη hh Y hlarge).2)

/-- A half-width below `analyticWidth` and `π / 4` gives a finite sinh quadrature error bound by
the mesh term plus the discarded lattice tail under the stated hypotheses. -/
theorem original_finite_error (n : ℕ) (b c d η β : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hη : 0 < η) (hβ₀ : 0 < β) (hβ : β < Real.pi / 4)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T h : ℝ} (hT : 0 ≤ T) (hh : 0 < h) (Y : ℝ)
    (hw : (β : EReal) < analyticWidth n b c d T η H L) :
    ‖(∫ k : ℝ, integrand n b c d T H L (k : ℂ)) -
        finiteIdeal n b c d T η h H L (cutoff Y h)‖ ≤
      2 * stripMass n b c d η β (T * ‖L‖) / (Real.exp (2 * Real.pi * β / h) - 1) +
        latticeTail n b c d T η h H L (cutoff Y h) := by
  exact (finite_error_split n b c d hb hc H L hH hL hT hη hh (cutoff Y h)).trans
    (_root_.add_le_add (original_mesh_error n b c d η β hb hc hη hβ₀ hβ H L hH hL hT hh hw)
      (le_refl _))

/-- Below `analyticWidth`, the finite sinh error is bounded by mesh error plus lattice tail, and
a sufficiently large endpoint bounds that tail first by the complementary-error-function
expression and then by an exponential; see [Aftab et al., Proposition
4.17][AftabAnTrivisa2026]. -/
theorem original_error_bounds (n : ℕ) (b c d η β : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hη : 0 < η) (hβ₀ : 0 < β) (hβ : β < Real.pi / 4)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T h : ℝ} (hT : 0 ≤ T) (hh : 0 < h) (Y : ℝ)
    (hw : (β : EReal) < analyticWidth n b c d T η H L) :
    (‖(∫ k : ℝ, integrand n b c d T H L (k : ℂ)) -
        finiteIdeal n b c d T η h H L (cutoff Y h)‖ ≤
      2 * stripMass n b c d η β (T * ‖L‖) / (Real.exp (2 * Real.pi * β / h) - 1) +
        latticeTail n b c d T η h H L (cutoff Y h)) ∧
      (1 ≤ η / (2 * c) * Real.sinh (h * cutoff Y h) →
        latticeTail n b c d T η h H L (cutoff Y h) ≤
          tailConstant n b c d * (1 - erf (η * Real.sinh (h * cutoff Y h) / (2 * c))) ∧
        tailConstant n b c d * (1 - erf (η * Real.sinh (h * cutoff Y h) / (2 * c))) ≤
          tailConstant n b c d * Real.exp (-(η / (2 * c)) ^ 2 * Real.sinh (h * cutoff Y h) ^ 2)) := by
  exact ⟨original_finite_error n b c d η β hb hc hη hβ₀ hβ H L hH hL hT hh Y hw,
    fun hlarge => actual_tail_bounds n b c d hb hc H L hH hL hT hη hh Y hlarge⟩

end Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhError
