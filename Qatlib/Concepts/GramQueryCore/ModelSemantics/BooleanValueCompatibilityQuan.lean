/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.ModelSemantics.BooleanValueCompatibilityStat
import Qatlib.Concepts.GramQueryCore.FilteredNorm.RectangularBudgetRealizationQuan
import Qatlib.Concepts.GramQueryCore.ModelSemantics.CoherentValueFeasibleBoundaryQuan

/-!
# Compatibility of Boolean Gram optimization values

Identifies square instances of the rectangular witness model with `gramFilteredCert` and
`filteredGamma2`. Encoding Boolean symbols as a two-symbol alphabet preserves the coordinate
difference filters.

These identifications prove compatibility of the source filtered value, coherent approximation
value, and adversary value with their Boolean definitions in the framework of [LeeEtAl2011].

## Main statements

* `sourceSquareCert_iff`: identifies the two certificate formulations.
* `sourceSquareValue_eq`: identifies the square optimization values.
* `booleanValueCompatibility`: proves all Boolean value compatibility identities.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.ModelSemantics
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- For square finite matrices, the rectangular source certificate is equivalent to the filtered
Gram certificate with the same budget. -/
theorem sourceSquareCert_iff {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ) (w : ℝ) :
    sourceRectCert n A Z w ↔ gramFilteredCert A Z w := by
  constructor
  · rintro ⟨m,u,v,heq,hu,hv⟩
    refine ⟨Fin m,inferInstance,fun j x => u x j,fun j x => v x j,?_,?_,?_⟩
    · intro x
      simpa only [Complex.normSq_eq_norm_sq,← norm_toEuclidean_fromVec_sq] using! hu x
    · intro x
      simpa only [Complex.normSq_eq_norm_sq,← norm_toEuclidean_fromVec_sq] using! hv x
    · simpa only [dotProduct,Pi.star_apply] using! heq
  · rintro ⟨Q,hQ,u,v,hu,hv,heq⟩
    obtain ⟨u',v',hi,hm,hv'⟩ := rectangularWitness_compress u v
    refine ⟨Fintype.card X+Fintype.card X,u',v',?_,?_,?_⟩
    · intro x y
      simpa only [dotProduct,Pi.star_apply,hi] using! heq x y
    · intro x
      simp_rw [hm]
      exact hu x
    · intro x
      simp_rw [hv']
      exact hv x

/-- For square finite matrices, `sourceRectValue` equals `filteredGamma2` for the same filter
family. -/
theorem sourceSquareValue_eq {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ) : sourceRectValue A Z=filteredGamma2 A Z := by
  unfold sourceRectValue filteredGamma2
  congr 1
  ext b
  constructor
  · rintro ⟨w,_,hb,hc⟩
    exact ⟨w,hb,(sourceSquareCert_iff A Z w).mp hc⟩
  · rintro ⟨w,hb,hc⟩
    refine ⟨max w 0,le_max_right _ _,?_,(sourceSquareCert_iff A Z _).mpr
      (gramFilteredCert_mono hc (le_max_left _ _))⟩
    rw [hb,ENNReal.ofReal_max]
    simp

/-- Encoding Boolean inputs as alphabet symbols leaves the coordinate difference filters
unchanged. -/
theorem sourceBooleanDelta_eq {X : Type} {n : ℕ} (input : X → Fin n → Bool) :
    sourceAlphabetDelta (fun x j => sourceBooleanSymbol (input x j))=gramFilterDelta input := by
  ext j x y
  cases hx : input x j <;> cases hy : input y j <;>
    simp [sourceAlphabetDelta,sourceBooleanSymbol,gramFilterDelta,hx,hy]

/-- Proves that Boolean alphabet encoding preserves filtered Gram values, the coherent state
conversion optimization for nonnegative tolerance, and general adversary values
[LeeEtAl2011]. -/
theorem booleanValueCompatibility : BooleanValueCompatibility := by
  intro X _ _ n input R S δ
  have hΔ := sourceBooleanDelta_eq input
  refine ⟨?_,?_,?_⟩
  · rw [hΔ,sourceSquareValue_eq]
  · intro hδ
    rw [coherentValueFeasibleBoundary X n input δ R S hδ]
    unfold sourceQDelta
    apply le_antisymm
    · apply le_iInf
      intro T
      have hb : sourceUnfiltered (T.1-S)≤ENNReal.ofReal δ := by
        unfold sourceUnfiltered
        rw [sourceSquareValue_eq]
        exact T.2.2
      apply iInf_le_of_le ⟨T.1,T.2.1,hb⟩
      rw [hΔ,sourceSquareValue_eq]
    · apply le_iInf
      intro T
      have hb : filteredGamma2 (T.1-S) (fun _ : Fin 1 => gramFilterAllOnes)≤ENNReal.ofReal δ := by
        have ht := T.2.2
        unfold sourceUnfiltered at ht
        rw [sourceSquareValue_eq] at ht
        exact ht
      apply iInf_le_of_le ⟨T.1,T.2.1,hb⟩
      rw [hΔ,sourceSquareValue_eq]
  · intro E _ _ f
    rw [generalAdversaryValue_eq_real_sup]
    unfold sourceAdversary
    rw [hΔ]
    apply le_antisymm
    · apply iSup_le
      intro Γ
      have hc : ∀ j, ‖gramFilterDelta input j ⊙ Γ.1‖≤1 := by
        intro j
        simpa only [Matrix.hadamard_comm] using! Γ.2.2.2.2 j
      exact le_iSup_of_le (⟨Γ.1,Γ.2.1,Γ.2.2.2.1,hc,Γ.2.2.1⟩ :
        {M : Matrix X X ℂ // M.IsHermitian ∧ (∀ x y, f x=f y → M x y=0) ∧
          (∀ j, ‖gramFilterDelta input j ⊙ M‖≤1) ∧ ∀ x y,(M x y).im=0}) le_rfl
    · apply iSup_le
      intro Γ
      have hc : ∀ j, ‖Γ.1 ⊙ gramFilterDelta input j‖≤1 := by
        intro j
        simpa only [Matrix.hadamard_comm] using! Γ.2.2.2.1 j
      exact le_iSup_of_le (⟨Γ.1,Γ.2.1,Γ.2.2.2.2,Γ.2.2.1,hc⟩ :
        {M : Matrix X X ℂ // M.IsHermitian ∧ (∀ x y,(M x y).im=0) ∧
          (∀ x y, f x=f y → M x y=0) ∧ ∀ j, ‖M ⊙ gramFilterDelta input j‖≤1}) le_rfl

end Qatlib.Concepts.GramQueryCore.ModelSemantics
