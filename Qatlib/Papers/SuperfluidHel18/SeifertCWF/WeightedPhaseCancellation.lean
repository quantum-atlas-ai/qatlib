/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.SeifertCWF.RibbonRegularCWF

import Mathlib.Tactic.Ring

/-!
# Weighted phase-defect cancellation for a regular Seifert ribbon

[Kedia2018SuperfluidHelicity], Section IV and Eq. (5), writes the phase
defect carried by a narrow Seifert ribbon as a sum of off-diagonal linking,
writhe, and twist.  This file keeps the circulation of every component
explicit.  The phase-jump and boundary-flux fields are hypotheses because
the existence of a particular Gross–Pitaevskii phase chart is a separate
punctured-domain problem.

The resulting theorem is the weighted identity
`Σ i, Σ j ≠ i, κᵢκⱼ Lᵢⱼ + Σ i, κᵢ² (Wrᵢ + Twᵢ) = 0`.
It applies when each regular component has the stated phase jump, its
normalized punctured-domain boundary flux equals the component defect, and
the total outer boundary flux vanishes.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.SeifertCWF

open Set
open scoped BigOperators Real

local notation "Circulation" => ℝ

/-- The circulation-weighted Călugăreanu–White–Fuller defect of one
component.  The first term contains all links to distinct components and the
second term is the component's writhe plus twist contribution. -/
def weightedCWFComponent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ι → Circulation) (link : ι → ι → ℝ) (writhe twist : ι → ℝ) (i : ι) : ℝ :=
  κ i * (∑ j, if i ≠ j then κ j * link i j else 0) +
    κ i ^ 2 * (writhe i + twist i)

/-- The total weighted Călugăreanu–White–Fuller defect of a finite ribbon
bundle. -/
def weightedCWFDefect {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ι → Circulation) (link : ι → ι → ℝ) (writhe twist : ι → ℝ) : ℝ :=
  ∑ i, weightedCWFComponent κ link writhe twist i

/-- Data supplied by a regular Seifert phase chart on a punctured domain.
`phaseJump` is the jump around the component, `boundaryFlux` is the flux
through the boundary of the punctured domain, and `component_flux` is the
phase-normalized defect identity. -/
structure RegularSeifertPhaseJumpData {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ι → Circulation) (link : ι → ι → ℝ) (writhe twist : ι → ℝ) where
  phaseJump : ι → ℝ
  boundaryFlux : ι → ℝ
  regular_phase_jump : ∀ i, phaseJump i = 2 * π * κ i
  nonzero_phase_jump : ∀ i, phaseJump i ≠ 0
  component_flux : ∀ i,
    boundaryFlux i =
      (phaseJump i / (2 * π)) *
        ((∑ j, if i ≠ j then κ j * link i j else 0) +
          (phaseJump i / (2 * π)) * (writhe i + twist i))
  punctured_boundary_flux_zero : ∑ i, boundaryFlux i = 0

/-- The regular phase-jump and punctured-domain boundary-flux hypotheses
force cancellation of the fully circulation-weighted Călugăreanu–White–Fuller
defect. -/
theorem weighted_cwf_phase_defect_cancel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ι → Circulation) (link : ι → ι → ℝ) (writhe twist : ι → ℝ)
    (hdata : RegularSeifertPhaseJumpData κ link writhe twist) :
    weightedCWFDefect κ link writhe twist = 0 := by
  unfold weightedCWFDefect weightedCWFComponent
  calc
    ∑ i, (κ i * (∑ j, if i ≠ j then κ j * link i j else 0) +
        κ i ^ 2 * (writhe i + twist i)) = ∑ i, hdata.boundaryFlux i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hdata.component_flux i, hdata.regular_phase_jump i]
      have hpi : (2 * π : ℝ) ≠ 0 := by positivity
      field_simp [hpi]
    _ = 0 := hdata.punctured_boundary_flux_zero

end Qatlib.Papers.SuperfluidHel18.SeifertCWF
