/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LocalHam06.MainResults.ProjectionLemma

/-!
# Energy estimates for history-Hamiltonian constructions

This module applies the projection estimate to the energy thresholds appearing in Lemmas 2 and 3
of [KempeKitaevRegev2006]. Under the stated symmetric decomposition and penalty-gap assumptions,
`kitaev_lemma2` and `two_local_lemma3` combine a low-energy witness implication with a
conditional ground-energy lower bound.

## Main statements

* `kitaev_lemma2`: Uses the section-energy threshold based on `3 / 4 - ε`.
* `two_local_lemma3`: Uses the section-energy threshold based on `1 / 2 - ε`.

## References

* [Kempe et al., 2006][KempeKitaevRegev2006]
-/

noncomputable section

open scoped ComplexOrder
open InnerProductSpace

namespace Qatlib.Papers.LocalHam06.MainResults.KitaevConstruction

open Qatlib.Papers.LocalHam06.MainResults.OperatorDefs
open Qatlib.Papers.LocalHam06.MainResults.ProjectionLemma

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Nontrivial E]

/-- Under the stated projection hypotheses, a unit witness of energy below `ε` forces ground
energy below `ε`, and the given section-energy bound forces ground energy at least `3 / 4 -
ε`. These are the abstract energy estimates used for Lemma 2 of [KempeKitaevRegev2006]. -/
theorem kitaev_lemma2
    (H H1 H2 : E →L[ℂ] E) (S : Submodule ℂ E) (J ε : ℝ)
    (hH : H = H1 + H2)
    (hH1 : (H1 : E →ₗ[ℂ] E).IsSymmetric)
    (hH2 : (H2 : E →ₗ[ℂ] E).IsSymmetric)
    (hS : S ≠ ⊥)
    (hJ : 2 * ‖H1‖ < J)
    (hH2zero : ∀ v ∈ S, H2 v = 0)
    (hgap : ∀ v ∈ Sᗮ, J * ‖v‖ ^ 2 ≤ rayleigh H2 v)
    : ((∃ η : E, ‖η‖ = 1 ∧ rayleigh H η < ε) → groundEnergy H < ε) ∧
      (3 / 4 - ε + ‖H1‖ ^ 2 / (J - 2 * ‖H1‖) ≤ sectionEnergy S H1 →
        3 / 4 - ε ≤ groundEnergy H) := by
  have hpl := projection_lemma S H1 H2 J hH1 hH2 hS hJ hH2zero hgap
  constructor
  · intro hyes
    rw [hH] at hyes ⊢
    rw [groundEnergy]
    exact lt_of_le_of_lt
      (csInf_le (bddBelow_rect (H1 + H2)) ⟨hyes.choose, hyes.choose_spec.1, rfl⟩)
      hyes.choose_spec.2
  · intro hsec
    rw [hH]
    have hlower := hpl.1
    linarith

/-- Under the stated projection hypotheses, a unit witness of energy below `ε` forces ground
energy below `ε`, and the given section-energy bound forces ground energy at least `1 / 2 -
ε`. These are the abstract energy estimates used for Lemma 3 of [KempeKitaevRegev2006]. -/
theorem two_local_lemma3
    (H H1 H2 : E →L[ℂ] E) (S : Submodule ℂ E) (J ε : ℝ)
    (hH : H = H1 + H2)
    (hH1 : (H1 : E →ₗ[ℂ] E).IsSymmetric)
    (hH2 : (H2 : E →ₗ[ℂ] E).IsSymmetric)
    (hS : S ≠ ⊥)
    (hJ : 2 * ‖H1‖ < J)
    (hH2zero : ∀ v ∈ S, H2 v = 0)
    (hgap : ∀ v ∈ Sᗮ, J * ‖v‖ ^ 2 ≤ rayleigh H2 v)
    : ((∃ η : E, ‖η‖ = 1 ∧ rayleigh H η < ε) → groundEnergy H < ε) ∧
      (1 / 2 - ε + ‖H1‖ ^ 2 / (J - 2 * ‖H1‖) ≤ sectionEnergy S H1 →
        1 / 2 - ε ≤ groundEnergy H) := by
  have hpl := projection_lemma S H1 H2 J hH1 hH2 hS hJ hH2zero hgap
  constructor
  · intro hyes
    rw [hH] at hyes ⊢
    rw [groundEnergy]
    exact lt_of_le_of_lt
      (csInf_le (bddBelow_rect (H1 + H2)) ⟨hyes.choose, hyes.choose_spec.1, rfl⟩)
      hyes.choose_spec.2
  · intro hsec
    rw [hH]
    have hlower := hpl.1
    linarith

end Qatlib.Papers.LocalHam06.MainResults.KitaevConstruction
