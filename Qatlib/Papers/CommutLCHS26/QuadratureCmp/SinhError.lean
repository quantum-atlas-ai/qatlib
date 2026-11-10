/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.SinhWidth
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
