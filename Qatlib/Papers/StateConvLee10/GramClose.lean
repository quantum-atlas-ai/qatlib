/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredCert.FilteredGamma2

/-!
# Gram closeness and common unitary alignment

This module connects pointwise overlap of normalized state families with an all-ones filtered
certificate for the difference of their Gram matrices. Conversely, a Gram certificate yields a
common unitary on a finite enlarged space that aligns the padded families to the stated overlap
accuracy, as used in [LeeEtAl2011].

## Main statements

* `source_overlap_to_gram`: pointwise real overlap gives a Gram certificate with budget `2 *
  sqrt ε`.
* `source_padded_unitary_overlap`: a Gram certificate yields a common padded unitary alignment.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.GramQueryCore.GramRealization
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

open Qatlib.Concepts.GramQueryCore.FilteredCert

namespace Qatlib.Papers.StateConvLee10.GramClose

/-- For normalized state families and `0 ≤ ε ≤ 1`, real overlaps at least `sqrt (1 - ε)` yield
an all-ones filtered Gram certificate with budget `2 * sqrt ε` [LeeEtAl2011]. -/
theorem source_overlap_to_gram {H X : Type} [Fintype H] [Fintype X]
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ρ σ : X → QState H)
    (hρ : ∀ x, Normalized (ρ x)) (hσ : ∀ x, Normalized (σ x))
    (hov : ∀ x, Real.sqrt (1 - ε) ≤ (Qatlib.Foundations.PureStateMath.Inner (ρ x) (σ x)).re) :
    gramFilteredCert (gramStateMatrix ρ - gramStateMatrix σ)
      (fun _ : Fin 1 => gramFilterAllOnes) (2 * Real.sqrt ε) := by
  exact Qatlib.Concepts.GramQueryCore.FilteredCert.gramFilteredCert_of_realPart_overlap (H := H)
      (X := X) (ε := ε) (hε := hε) (hε1 := hε1) (ρ := ρ) (σ := σ) (hρ := hρ) (hσ := hσ) (hov := hov)

/-- For normalized state families, a nonnegative all-ones Gram certificate budget `ε` yields a
unitary on a finite enlarged space with padded real overlaps at least `1 - sqrt (2 * ε)`
[LeeEtAl2011]. -/
theorem source_padded_unitary_overlap {H X : Type}
    [Fintype H] [DecidableEq H] [Fintype X] [DecidableEq X]
    {ε : ℝ} (hε : 0 ≤ ε) (ρ σ : X → QState H)
    (hρ : ∀ x, Normalized (ρ x)) (hσ : ∀ x, Normalized (σ x))
    (hcert : gramFilteredCert (gramStateMatrix ρ - gramStateMatrix σ)
      (fun _ : Fin 1 => gramFilterAllOnes) ε) :
    ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K) (U : Matrix (H ⊕ K) (H ⊕ K) ℂ),
      U ∈ Matrix.unitaryGroup (H ⊕ K) ℂ ∧
      ∀ x, 1 - Real.sqrt (2 * ε) ≤ (Qatlib.Foundations.PureStateMath.Inner
        (ApplyGate U (Sum.elim (ρ x) (0 : K → ℂ)))
        (Sum.elim (σ x) (0 : K → ℂ))).re := by
  exact Qatlib.Concepts.GramQueryCore.FilteredCert.gram_unitary_overlap_of_filteredCert (H := H)
      (X := X) (ε := ε) (hε := hε) (ρ := ρ) (σ := σ) (hρ := hρ) (hσ := hσ) (hcert := hcert)

end Qatlib.Papers.StateConvLee10.GramClose
