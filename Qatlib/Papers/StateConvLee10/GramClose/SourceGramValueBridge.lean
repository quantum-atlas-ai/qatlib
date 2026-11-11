/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.RectangularBudgetRealizationQuan
import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Value
import Qatlib.Concepts.GramQueryCore.FilteredCert.FilteredGamma2

set_option backward.isDefEq.respectTransparency false

/-!
# GramClose — Lemma 4.8 in the printed γ₂-value form

Lee--Mittal--Reichardt--Spalek--Szegedy, fixed arXiv:1011.3020v2.
PDF SHA-256 edb6a9db14e47b34a18a5b54610041c680bbe090084e81ca1822eddd990228f1.

Printed Lemma 4.8 (p. 9) is stated with the γ₂ *value*: the hypotheses are
`Re ⟨ρ_x | σ_x⟩ ≥ √(1 − ε)` and `γ₂(ρ − σ) ≤ ε`, and the conclusions are
`γ₂(ρ − σ) ≤ 2√ε` and `1 − √(2ε) ≤ Re ⟨ρ_x | U σ_x⟩`.  The shared
implementation of the paper's γ₂ (Definition 2.3 and the unfiltered instance of
Definition 3.1) is the rectangular value `sourceUnfiltered`, while the existing
output-condition lemmas consume the finite witness predicate
`gramFilteredCert` (`SourceGramClose`).  This module supplies the missing
representation bridge between the two: a square rectangular certificate is
exactly a Gram-filtered certificate on the same matrix and filter, hence the
printed value bounds and the printed value hypothesis are the ones the paper
actually reads off.

Boundary: the second direction still yields the paper's own proof object, a
unitary on the padded space `H ⊕ K`; no same-space `U ∈ L(H)` statement is
claimed here.  Constants are the printed `2√ε` and `1 − √(2ε)`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

namespace Qatlib.Papers.StateConvLee10.GramClose

/-- The inner product of a starred vector with a vector is the plain sum of
`star (a q) * b q`. -/
private theorem dotProduct_star_apply {Q : Type} [Fintype Q] (a b : Q → ℂ) :
    star a ⬝ᵥ b = ∑ q, star (a q) * b q := by
  simp [dotProduct]

/-- Square rectangular certificates are Gram-filtered certificates for the same
matrix and filters: the only difference is how the finite witness space is
indexed. -/
theorem gramFilteredCert_of_sourceRectCert {X : Type} [Fintype X]
    {n : ℕ} {A : Matrix X X ℂ} {Z : Fin n → Matrix X X ℂ} {w : ℝ}
    (h : sourceRectCert n A Z w) :
    gramFilteredCert A Z w := by
  obtain ⟨m, u, v, heq, hu, hv⟩ := h
  refine ⟨Fin m, inferInstance, fun j x => u x j, fun j y => v y j, ?_, ?_, ?_⟩
  · intro x
    calc ∑ j, ∑ q, Complex.normSq (u x j q)
        = ∑ j, ∑ q, ‖u x j q‖ ^ 2 := by
          simp only [Complex.normSq_eq_norm_sq]
      _ = ∑ j, ‖toEuclidean_fromVec (u x j)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          exact (norm_toEuclidean_fromVec_sq (u x j)).symm
      _ ≤ w := hu x
  · intro y
    calc ∑ j, ∑ q, Complex.normSq (v y j q)
        = ∑ j, ∑ q, ‖v y j q‖ ^ 2 := by
          simp only [Complex.normSq_eq_norm_sq]
      _ = ∑ j, ‖toEuclidean_fromVec (v y j)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          exact (norm_toEuclidean_fromVec_sq (v y j)).symm
      _ ≤ w := hv y
  · intro x y
    rw [heq x y]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1

/-- Gram-filtered certificates on a square matrix are rectangular certificates
for the same matrix and filters. -/
theorem sourceRectCert_of_gramFilteredCert {X : Type} [Fintype X]
    {n : ℕ} {A : Matrix X X ℂ} {Z : Fin n → Matrix X X ℂ} {w : ℝ}
    (h : gramFilteredCert A Z w) : sourceRectCert n A Z w := by
  obtain ⟨Q, hQ, u, v, hu, hv, heq⟩ := h
  let e : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  refine ⟨Fintype.card Q, fun x j k => u j x (e.symm k),
    fun y j k => v j y (e.symm k), ?_, ?_, ?_⟩
  · intro r s
    rw [heq r s]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dotProduct_star_apply]
    congr 1
    exact (Equiv.sum_comp e.symm (fun q => star (u j r q) * v j s q)).symm
  · intro r
    calc ∑ j, ‖toEuclidean_fromVec (fun k => u j r (e.symm k))‖ ^ 2
        = ∑ j, ∑ k, ‖u j r (e.symm k)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => norm_toEuclidean_fromVec_sq _
      _ = ∑ j, ∑ q, ‖u j r q‖ ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          exact Equiv.sum_comp e.symm (fun q => ‖u j r q‖ ^ 2)
      _ = ∑ j, ∑ q, Complex.normSq (u j r q) := by
          simp only [Complex.normSq_eq_norm_sq]
      _ ≤ w := hu r
  · intro s
    calc ∑ j, ‖toEuclidean_fromVec (fun k => v j s (e.symm k))‖ ^ 2
        = ∑ j, ∑ k, ‖v j s (e.symm k)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => norm_toEuclidean_fromVec_sq _
      _ = ∑ j, ∑ q, ‖v j s q‖ ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          exact Equiv.sum_comp e.symm (fun q => ‖v j s q‖ ^ 2)
      _ = ∑ j, ∑ q, Complex.normSq (v j s q) := by
          simp only [Complex.normSq_eq_norm_sq]
      _ ≤ w := hv s

/-- A Gram-filtered certificate bounds the paper's unfiltered γ₂ value. -/
theorem sourceUnfiltered_le_of_gramFilteredCert {X : Type} [Fintype X]
    [DecidableEq X] {A : Matrix X X ℂ} {W : ℝ} (hW : 0 ≤ W)
    (h : gramFilteredCert A (fun _ : Fin 1 => gramFilterAllOnes) W) :
    sourceUnfiltered A ≤ ENNReal.ofReal W := by
  have hrect : sourceRectCert 1 A (fun _ : Fin 1 => fun _ _ => (1 : ℂ)) W :=
    sourceRectCert_of_gramFilteredCert h
  have hb := (sourceRectValue_budget_boundary A
    (fun _ : Fin 1 => fun _ _ => (1 : ℂ)) W hW).mpr hrect
  simpa only [sourceUnfiltered, gramFilterAllOnes] using hb

/-- The paper's unfiltered γ₂ value yields a Gram-filtered certificate. -/
theorem gramFilteredCert_of_sourceUnfiltered_le {X : Type} [Fintype X]
    [DecidableEq X] {A : Matrix X X ℂ} {W : ℝ} (hW : 0 ≤ W)
    (h : sourceUnfiltered A ≤ ENNReal.ofReal W) :
    gramFilteredCert A (fun _ : Fin 1 => gramFilterAllOnes) W := by
  have hb := (sourceRectValue_budget_boundary A
    (fun _ : Fin 1 => fun _ _ => (1 : ℂ)) W hW).mp
    (by simpa only [sourceUnfiltered, gramFilterAllOnes] using h)
  exact gramFilteredCert_of_sourceRectCert hb

/-- Fixed arXiv:1011.3020v2. Lemma4.8, first direction, printed γ₂-value form: normalized states with pointwise real overlap at least sqrt(1−ε) have unfiltered γ₂ distance at most2sqrt(ε). -/
theorem source_lemma48_overlap_to_value {H X : Type} [Fintype H] [DecidableEq H]
    [Fintype X] [DecidableEq X] {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ρ σ : X → QState H) (hρ : ∀ x, Normalized (ρ x))
    (hσ : ∀ x, Normalized (σ x))
    (hov : ∀ x, Real.sqrt (1 - ε) ≤
      (Qatlib.Foundations.PureStateMath.Inner (ρ x) (σ x)).re) :
    sourceUnfiltered (gramStateMatrix ρ - gramStateMatrix σ) ≤
      ENNReal.ofReal (2 * Real.sqrt ε) := by
  have hcert := gramFilteredCert_of_realPart_overlap (X := X) (H := H) (ε := ε)
    hε hε1 ρ σ hρ hσ hov
  exact sourceUnfiltered_le_of_gramFilteredCert (by positivity) hcert

/-- Fixed arXiv:1011.3020v2. Lemma4.8, second direction, printed γ₂-value hypothesis: unfiltered γ₂ distance at most ε yields one unitary on H⊕K with real overlap at least1−sqrt(2ε). This is the paper's own padded proof object, not a same-space U∈L(H). -/
theorem source_lemma48_value_to_unitary {H X : Type} [Fintype H] [DecidableEq H]
    [Fintype X] [DecidableEq X] {ε : ℝ} (hε : 0 ≤ ε) (ρ σ : X → QState H)
    (hρ : ∀ x, Normalized (ρ x)) (hσ : ∀ x, Normalized (σ x))
    (hval : sourceUnfiltered (gramStateMatrix ρ - gramStateMatrix σ) ≤
      ENNReal.ofReal ε) :
    ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K)
      (U : Matrix (H ⊕ K) (H ⊕ K) ℂ),
      U ∈ Matrix.unitaryGroup (H ⊕ K) ℂ ∧
      ∀ x, 1 - Real.sqrt (2 * ε) ≤
        (Qatlib.Foundations.PureStateMath.Inner
          (ApplyGate U (Sum.elim (ρ x) (0 : K → ℂ)))
          (Sum.elim (σ x) (0 : K → ℂ))).re := by
  have hcert : gramFilteredCert (gramStateMatrix ρ - gramStateMatrix σ)
      (fun _ : Fin 1 => gramFilterAllOnes) ε :=
    gramFilteredCert_of_sourceUnfiltered_le hε hval
  exact gram_unitary_overlap_of_filteredCert (X := X) (H := H) (ε := ε)
    hε ρ σ hρ hσ hcert

end Qatlib.Papers.StateConvLee10.GramClose
