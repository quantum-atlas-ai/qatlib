/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecodingDefs
public import Qatlib.Concepts.ErrorCorrection.CssBuild.Classical
public import Qatlib.Papers.CssCodeCS96.Construction.Hamming
public import Qatlib.Papers.CssCodeCS96.Construction.Steane
import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The Hamming-to-Steane representation bridge

The `m = 3` Hamming code, reindexed by the Steane column order, is exactly
the classical check underlying the seven-qubit Steane code: the
self-orthogonal Hamming checks build, through the shared classical-to-CSS
bridge, the very `Qatlib.Concepts.CodingDecoding.CssTesters.steaneData`
consumed by the Steane consumer.

The seven-column example is from [Calderbank and Shor, 1996][CalderbankShor1996],
fixed version `quant-ph/9512032v2`. The general Hamming family is an additional
consumer of the shared components.
-/

namespace Qatlib.Papers.CssCodeCS96.Construction

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.ErrorCorrection.CssBuild
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open scoped Matrix

/-- Every Steane parity-check column is a nonzero binary vector. -/
theorem steaneCol_ne (j : Fin 7) : steaneCol j ≠ 0 := by
  fin_cases j <;> decide

/-- Column map pulling the Hamming columns into the Steane order. -/
def hamToSteane (j : Fin 7) : {v : Fin 3 → ZMod 2 // v ≠ 0} :=
  ⟨steaneCol j, steaneCol_ne j⟩

/-- The seven distinct Steane columns enumerate every nonzero Hamming column. -/
theorem ham_col_bij : Function.Bijective hamToSteane := by
  apply (Fintype.bijective_iff_injective_and_card hamToSteane).mpr
  refine ⟨fun i j h => steaneCol_injective i j (congrArg Subtype.val h), ?_⟩
  rw [Fintype.card_fin, hamCard]
  norm_num

/-- The explicit column map, equipped with its inverse on all nonzero columns. -/
noncomputable def hamSteaneEquiv : Fin 7 ≃ {v : Fin 3 → ZMod 2 // v ≠ 0} :=
  Equiv.ofBijective hamToSteane ham_col_bij

/-- Extending a Steane-ordered vector along the inverse column bijection. -/
noncomputable def hamVector (v : Fin 7 → ZMod 2) :
    {w : Fin 3 → ZMod 2 // w ≠ 0} → ZMod 2 :=
  fun w => v (hamSteaneEquiv.symm w)

/-- The inverse coordinate transport preserves every syndrome component. -/
theorem ham_syn_trans (v : Fin 7 → ZMod 2) :
    hamCheck 3 *ᵥ hamVector v = steaneH *ᵥ v := by
  funext i
  change (∑ w, hamCheck 3 i w * hamVector v w) = ∑ j, steaneH i j * v j
  rw [← Equiv.sum_comp hamSteaneEquiv]
  simp only [hamVector, Equiv.symm_apply_apply]
  rfl

/-- Kernel membership is transported in both directions by the column bijection. -/
theorem ham_words_iff (v : Fin 7 → ZMod 2) :
    hamVector v ∈ codeWords (hamCode 3) ↔ steaneH *ᵥ v = 0 := by
  rw [mem_words]
  change hamCheck 3 *ᵥ hamVector v = 0 ↔ steaneH *ᵥ v = 0
  rw [ham_syn_trans]

/-- The reindexed Hamming checks are exactly the Steane parity checks. -/
theorem ham3_eq_steane : (hamCheck 3).submatrix id hamToSteane = steaneH := by
  ext i j
  rfl

/-- The reindexed Hamming checks are self-orthogonal. -/
theorem ham3_self :
    (hamCheck 3).submatrix id hamToSteane
      * ((hamCheck 3).submatrix id hamToSteane)ᵀ = 0 := by
  rw [ham3_eq_steane, steaneH_mul_transpose]

/-- The length-seven classical code shared with the Steane construction. -/
def ham3Code : ClCode (Fin 7) (Fin 3) where
  h := (hamCheck 3).submatrix id hamToSteane

/-- The CSS code from the reindexed Hamming checks is exactly the Steane data. -/
theorem ham3_to_steane : toCss ham3Code ham3_self = steaneData := rfl

/-- Reindexing by the full column bijection preserves the Hamming check rank. -/
theorem ham3_rank : Matrix.rank ham3Code.h = 3 := by
  change Matrix.rank ((hamCheck 3).submatrix (Equiv.refl _) hamSteaneEquiv) = 3
  rw [Matrix.rank_submatrix, hamRank]

/-- Rank-nullity transports the classical dimension to the Steane coordinate order. -/
theorem ham3_dim : codeDim ham3Code = 4 := by
  have h := dim_add_rank ham3Code
  rw [ham3_rank, Fintype.card_fin] at h
  omega

/-- The transported classical Hamming code has exact distance three in Steane order. -/
theorem ham3_dist : minDist ham3Code = (3 : ℕ∞) := by
  apply dist_eq ham3Code 3 (w := logicalWord)
  · apply (mem_words ham3Code logicalWord).mpr
    simpa only [ham3Code, ham3_eq_steane] using word_syndrome
  · decide
  · exact word_weight
  · intro v hv hn
    by_contra h
    apply hn
    apply small_kernel v (by omega)
    simpa only [ham3Code, ham3_eq_steane] using (mem_words ham3Code v).mp hv

/-- All classical parameters survive the explicit Hamming-to-Steane column transport. -/
theorem ham3_params : Fintype.card (Fin 7) = 7 ∧ codeDim ham3Code = 4 ∧
    minDist ham3Code = (3 : ℕ∞) :=
  ⟨Fintype.card_fin 7, ham3_dim, ham3_dist⟩

/-- The self-orthogonal Hamming presentation inherits the proved Steane parameters. -/
theorem ham3_css_params : (toCss ham3Code ham3_self).numQubits = 7 ∧
    (toCss ham3Code ham3_self).encodedQubits = 1 ∧
      cssDistance (toCss ham3Code ham3_self) = 3 := by
  rw [ham3_to_steane]
  exact steane_params

end Qatlib.Papers.CssCodeCS96.Construction
