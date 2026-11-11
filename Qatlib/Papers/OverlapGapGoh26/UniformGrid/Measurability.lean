/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.UniformGrid.AdaptiveEnergy
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Measurability of continuum AMP energy events

Continuity of `energyPath` and compactness of the parameter interval make its continuum
threshold events closed. These events are therefore measurable, as required by the probability
bounds for the AMP dynamics associated with [GohMuller2026].

## Main statements

* `isClosed_actual_continuum_energy`: existence of an interpolated energy above a fixed
  threshold defines a closed set.
* `measurableSet_actual_continuum_energy`: the same continuum event is measurable.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open MeasureTheory
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Gaussian
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.AdaptiveEnergy

namespace Qatlib.Papers.OverlapGapGoh26.UniformGrid.Measurability

/-- The set of samples whose AMP energy path reaches or exceeds `c` at some parameter in `[0,
1]` is closed. -/
theorem isClosed_actual_continuum_energy {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ) (c : ℝ) :
    IsClosed {w : Sample r N | ∃ τ∈Set.Icc (0:ℝ) 1,c≤energyPath M s T w τ} := by
  let I := Set.Icc (0:ℝ) 1
  letI : CompactSpace I := isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1))
  have hc : Continuous (fun p : Sample r N × I => energyPath M s T p.1 p.2) :=
    (continuous_energyPath M s T).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hclosed : IsClosed {p : Sample r N × I | c≤energyPath M s T p.1 p.2} :=
    isClosed_le continuous_const hc
  have hp := isClosedMap_fst_of_compactSpace _ hclosed
  have he : Prod.fst '' {p : Sample r N × I | c≤energyPath M s T p.1 p.2}=
      {w : Sample r N | ∃ τ∈Set.Icc (0:ℝ) 1,c≤energyPath M s T w τ} := by
    ext w
    constructor
    · rintro ⟨⟨w,τ⟩,hc,rfl⟩
      exact ⟨τ,τ.property,hc⟩
    · rintro ⟨τ,hτ,hc⟩
      exact ⟨(w,⟨τ,hτ⟩),hc,rfl⟩
  rw [he] at hp
  exact hp

/-- The set of samples whose AMP energy path reaches or exceeds `c` somewhere on `[0, 1]` is
measurable. -/
theorem measurableSet_actual_continuum_energy {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ) (c : ℝ) :
    MeasurableSet {w : Sample r N | ∃ τ∈Set.Icc (0:ℝ) 1,c≤energyPath M s T w τ} :=
  (isClosed_actual_continuum_energy M s T c).measurableSet

end Qatlib.Papers.OverlapGapGoh26.UniformGrid.Measurability
