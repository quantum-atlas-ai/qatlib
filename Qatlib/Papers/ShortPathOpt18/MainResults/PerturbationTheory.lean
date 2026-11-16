/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ShortPathOpt18.MainResults.SourceModel
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

@[expose] public section


/-! Closed source mathematics; paper algorithm claims retain their separate obligations. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.ShortPathOpt18.MainResults
open Qatlib.Papers.ShortPathOpt18.MainResults

/-- `⟨0|(X/N)^K|0⟩`, the basis-state moment appearing in Eqs. (24)–(27). -/
def zeroMoment (N K : ℕ) : ℝ := xPowExp N K (basisVec (zeroConfig N))

/-- A real series dominated termwise in absolute value by `2 ^ (-t)` converges. Obtaining this bound for the Brillouin-Wigner coefficients is a separate spectral obligation. -/
theorem source_lemma5_series_converges (bwTerm : ℕ → ℝ)
    (hgeom : ∀ t, |bwTerm t| ≤ (1 / 2 : ℝ) ^ t) :
    ∃ L : ℝ, HasSum bwTerm L := by
  have habs : Summable (fun t => |bwTerm t|) :=
    Summable.of_nonneg_of_le (fun t => abs_nonneg _) hgeom
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have hsum : Summable bwTerm := habs.of_abs
  exact ⟨∑' t, bwTerm t, hsum.hasSum⟩

/-- An assumed energy identity with a bounded scalar correction implies the corresponding lower energy bound. The resolvent identity and the correction estimate are hypotheses, not conclusions of this theorem. -/
theorem source_lemma5_energy_shift {N : ℕ} (E0 E01 B : ℝ) (K : ℕ)
    (hcorr : ∃ c : ℝ, |c| ≤ 2 * B ^ 2 * zeroMoment N (2 * K) ∧
      E01 = E0 - B * zeroMoment N K + c) :
    E0 - B * zeroMoment N K - 2 * B ^ 2 * zeroMoment N (2 * K) ≤ E01 := by
  obtain ⟨c, hc, hE⟩ := hcorr
  rw [hE]
  linarith [(abs_le.mp hc).1]

/-- An assumed squared-norm identity with a bounded scalar correction implies its upper norm bound. Constructing the perturbative state and proving the correction estimate remain separate obligations. -/
theorem source_lemma5_norm {N : ℕ} (φ01 : Config N → ℝ) (B : ℝ) (K : ℕ)
    (hcorr : ∃ c : ℝ, |c| ≤ 4 * B ^ 2 * zeroMoment N (2 * K) ∧
      normSq φ01 = 1 + c) :
    normSq φ01 ≤ 1 + 4 * B ^ 2 * zeroMoment N (2 * K) := by
  obtain ⟨c, hc, hφ⟩ := hcorr
  rw [hφ]
  linarith [(abs_le.mp hc).2]

/-- A vanishing supplied moment and the assumed energy and norm correction bounds imply `E0 - 1 <= E01` and `phiSq <= 4` under the smallness condition. This is scalar postprocessing; oddness of a matrix moment and the perturbation estimates are not derived here. -/
theorem source_lemma5_odd {E0 E01 B mK m2K φsq : ℝ}
    (hmoment : mK = 0) (hsmall : B ^ 2 * m2K ≤ 1 / 2)
    (hE : E0 - B * mK - 2 * B ^ 2 * m2K ≤ E01)
    (hφ : φsq ≤ 1 + 4 * B ^ 2 * m2K) :
    E0 - 1 ≤ E01 ∧ φsq ≤ 4 := by
  constructor
  · rw [hmoment, mul_zero, sub_zero] at hE
    nlinarith [hsmall, hE]
  · nlinarith [hsmall, hφ]

end Qatlib.Papers.ShortPathOpt18.MainResults
