/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.InhomLeftGrid.InhomogeneousSourceScheduleStat
import Qatlib.Concepts.LchsSimulation.InhomLeftGrid.InhomogeneousSourceQuadratureLine

/-!
# Explicit schedules for left-grid source approximation

`inhomogeneousSourceSchedule` chooses the window cutoff, LCHS node count, and source time-grid
size to meet the prescribed accuracy. The resulting schedule also bounds the coefficient spacing
and the sampled source mass. See [AnLiuLin2023] for the mathematical setting.

## Main statements

* `inhomogeneousSourceSchedule`: The prescribed cutoff, LCHS node count, and positive time-grid
  size achieve source error at most `ε / 2`, together with the stated spacing, raw-budget, and
  source-mass bounds.

## References

* [An, Liu, and Lin, 2023][AnLiuLin2023]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

open Qatlib.Concepts.LchsSimulation.WindowLchs

namespace Qatlib.Concepts.LchsSimulation.InhomLeftGrid

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The prescribed cutoff, LCHS node count, and positive time-grid size achieve source error at
most `ε / 2`, together with the stated spacing, raw-budget, and source-mass bounds. See
[AnLiuLin2023]. -/
theorem inhomogeneousSourceSchedule : InhomogeneousSourceSchedule := by
  intro I _ _ L H b b' s t ε Λ β lamL lamH bmax hL hH hb hPSD hHerm hst hε hbmax0
    hd hβ hbmax hlL hlH hΛ
  (try dsimp only)
  let δ := min (ε/2) (ε/(4*(t-s)*bmax))
  let K := timeDependentLchsWindowCutoff δ
  let N := timeDependentLchsWindowNodes δ Λ
  let C := (lamL+lamH)*bmax+β
  let Mt := max 1 (Nat.ceil (2*C*(t-s)^2/ε))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hs := inh_schedule_raw_bound δ Λ (2/Real.pi+∫ u in s..t, ‖L u‖) hδ hΛ
  have hMt : 0 < Mt := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hMr : 0 < (Mt : ℝ) := by exact_mod_cast hMt
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ s le_rfl hst.le)
  have hL0 : 0 ≤ lamL := (norm_nonneg _).trans (hlL s)
  have hH0 : 0 ≤ lamH := (norm_nonneg _).trans (hlH s)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hceil : 2*C*(t-s)^2/ε ≤ (Mt : ℝ) :=
    (Nat.le_ceil _).trans (by
      have hmceil : Nat.ceil (2*C*(t-s)^2/ε) ≤ Mt := le_max_right _ _
      exact_mod_cast hmceil)
  have htime : (t-s)*inhStep Mt s t*C/2 ≤ ε/4 := by
    have hc := (div_le_iff₀ hε).mp hceil
    have heq : (t-s)*inhStep Mt s t*C/2 = C*(t-s)^2/(2*(Mt : ℝ)) := by
      dsimp [inhStep]; field_simp
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < 2*(Mt : ℝ))).mpr
    nlinarith only [hc]
  have hk : (t-s)*bmax*(2/(Real.pi*(K : ℝ))+(2*(K : ℝ)/N)*
      (2/Real.pi+∫ u in s..t, ‖L u‖)) ≤ ε/4 := by
    have hr := hs.2.2.2.trans (min_le_right (ε/2) (ε/(4*(t-s)*bmax)))
    have hr' := (le_div_iff₀ (by positivity : 0 < 4*(t-s)*bmax)).mp hr
    nlinarith only [hr']
  refine ⟨hMt, hs.2.2.1, hs.2.2.2, ?_, ?_⟩
  · have he := inhomogeneousSourceQuadrature I L H b b' s t K N Mt β lamL lamH bmax
      hL hH hb hPSD hHerm hst.le hs.1 hs.2.1 hMt hd hβ hbmax hlL hlH
    exact he.trans (by change (t-s)*inhStep Mt s t*C/2+_ ≤ _; linarith only [htime, hk])
  · exact inh_source_mass_quadrature b b' s t β Mt hb hst.le hMt hd hβ

end Qatlib.Concepts.LchsSimulation.InhomLeftGrid
