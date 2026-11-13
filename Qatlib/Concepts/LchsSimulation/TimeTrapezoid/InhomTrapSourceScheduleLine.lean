/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.TimeTrapezoid.InhomTrapSourceScheduleStat
import Qatlib.Concepts.LchsSimulation.TimeTrapezoid.InhomogeneousTrapezoidSourceQuadrature

/-!
# A computed trapezoidal source schedule

`inhomogeneousTrapezoidSourceSchedule` establishes the computed source quadrature schedule. The
schedule chooses the Cauchy cutoff and node count together with a positive time subdivision
count to control the source approximation and weighted source mass.

The mathematical background is described in [AnLiuLin2023].

## Main statements

* `inhomogeneousTrapezoidSourceSchedule`: proves the source schedule error and mass bounds.

## References

* [An et al., 2023][AnLiuLin2023]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

open Qatlib.Concepts.LchsSimulation.InhomLeftGrid
open Qatlib.Concepts.LchsSimulation.WindowLchs

namespace Qatlib.Concepts.LchsSimulation.TimeTrapezoid

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The computed trapezoidal source schedule has positive time subdivision count, grid width at
most `1 / 2`, source error at most `ε / 2`, and the specified source-mass bound for the
Duhamel representation [AnLiuLin2023]. -/
theorem inhomogeneousTrapezoidSourceSchedule : InhomogeneousTrapezoidSourceSchedule := by
  intro I _ _ L L' H H' b b' b'' s t ε Λ β β₂ lamL lamH lamLd lamHd bmax
    hL hH hb hPSD hHerm hst hε hbmax0 hdL hdH hnLd hnHd hd hd' hβ hβ₂ hbmax hlL hlH hΛ
  (try dsimp only)
  let δ := min (ε/2) (ε/(4*(t-s)*bmax))
  let K := timeDependentLchsWindowCutoff δ
  let N := timeDependentLchsWindowNodes δ Λ
  let C := ((lamL+lamH)^2+(lamLd+lamHd))*bmax+2*(lamL+lamH)*β+β₂
  let Mt := max 1 (Nat.ceil (Real.sqrt (C*(t-s)^3/(3*ε))))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hs := inh_schedule_raw_bound δ Λ (2/Real.pi+∫ u in s..t, ‖L u‖) hδ hΛ
  have hMt : 0 < Mt := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hMr : 0 < (Mt : ℝ) := by exact_mod_cast hMt
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ s le_rfl hst.le)
  have hL0 : 0 ≤ lamL := (norm_nonneg _).trans (hlL s)
  have hH0 : 0 ≤ lamH := (norm_nonneg _).trans (hlH s)
  have hβ₂0 : 0 ≤ β₂ := (norm_nonneg _).trans (hβ₂ s le_rfl hst.le)
  have hLd0 : 0 ≤ lamLd := (norm_nonneg _).trans (hnLd s le_rfl hst.le)
  have hHd0 : 0 ≤ lamHd := (norm_nonneg _).trans (hnHd s le_rfl hst.le)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hceil : Real.sqrt (C*(t-s)^3/(3*ε)) ≤ (Mt : ℝ) :=
    (Nat.le_ceil _).trans (by
      have hmceil : Nat.ceil (Real.sqrt (C*(t-s)^3/(3*ε))) ≤ Mt := le_max_right _ _
      exact_mod_cast hmceil)
  have htime : (t-s)*(inhStep Mt s t)^2*C/12 ≤ ε/4 := by
    have hz : 0 ≤ C*(t-s)^3/(3*ε) := by positivity
    have hsquare := mul_self_le_mul_self (Real.sqrt_nonneg _) hceil
    rw [← pow_two, ← pow_two, Real.sq_sqrt hz] at hsquare
    have hraw := (div_le_iff₀ (by positivity : 0 < 3*ε)).1 hsquare
    have heq : (t-s)*(inhStep Mt s t)^2*C/12 = C*(t-s)^3/(12*(Mt : ℝ)^2) := by
      dsimp [inhStep]; field_simp
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < 12*(Mt : ℝ)^2)).2
    nlinarith only [hraw]
  have hk : (t-s)*bmax*(2/(Real.pi*(K : ℝ))+(2*(K : ℝ)/N)*
      (2/Real.pi+∫ u in s..t, ‖L u‖)) ≤ ε/4 := by
    have hr := hs.2.2.2.trans (min_le_right (ε/2) (ε/(4*(t-s)*bmax)))
    have hr' := (le_div_iff₀ (by positivity : 0 < 4*(t-s)*bmax)).mp hr
    nlinarith only [hr']
  refine ⟨hMt, hs.2.2.1, hs.2.2.2, ?_, ?_⟩
  · have he := inhomogeneousTrapezoidSourceQuadrature I L L' H H' b b' b'' s t K N Mt
      β β₂ lamL lamH lamLd lamHd bmax hL hH hb hPSD hHerm hst.le hs.1 hs.2.1 hMt
      hdL hdH hnLd hnHd hd hd' hβ hβ₂ hbmax hlL hlH
    exact he.trans (by change (t-s)*(inhStep Mt s t)^2*C/12+_ ≤ _; linarith only [htime, hk])
  · exact inh_trap_source_mass_quadrature b b' s t β Mt hb hst.le hMt hd hβ

end Qatlib.Concepts.LchsSimulation.TimeTrapezoid
