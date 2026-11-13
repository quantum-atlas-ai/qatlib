/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.TwirlChannel
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic

/-!
# Unnormalized Young subgroup operators

This module defines row-subgroup sums and column-subgroup alternating sums for the symmetry
constructions discussed in [Whitfield2013]. The operator `youngOp` applies `rowSym` first and
then `colAlt`; each subgroup sum is unnormalized, and applying it twice introduces the subgroup
cardinality.

The invariance statements distinguish the action on the input from the action on the output:
`youngOp_row_invariant` concerns row actions on the input, whereas `youngOp_col_antisym`
concerns column actions on the output. Explicit subgroups on five labels give the corresponding
tableau examples.

## Main statements

* `rowSym_idem` and `colAlt_idem`: subgroup-cardinality scaling under repeated application.
* `youngOp_row_invariant` and `youngOp_col_antisym`: input invariance and output antisymmetry.
* `fiveElectron_T1_column_antisymmetric`: the selected column transposition negates the
  five-label output.

## References

* [Whitfield, 2013][Whitfield2013]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.SpinFreeSim13.YoungModels

open Classical
open Qatlib.Concepts.ChannelTheory.TwirlChannel

variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The sign of a finite permutation, viewed as a complex scalar. -/
noncomputable def sgnC {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) : ℂ := ((Equiv.Perm.sign σ).val : ℂ)

/-- The complex permutation sign preserves multiplication. -/
theorem sgnC_mul {α : Type*} [Fintype α] [DecidableEq α]
    (σ τ : Equiv.Perm α) : sgnC (σ * τ) = sgnC σ * sgnC τ := by
  unfold sgnC
  rw [map_mul, Units.val_mul]
  push_cast
  ring

/-- A permutation and its inverse have the same complex sign. -/
theorem sgnC_inv {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) : sgnC σ⁻¹ = sgnC σ := by
  unfold sgnC
  rw [Equiv.Perm.sign_inv]

/-- The transposition of two distinct elements has complex sign minus one. -/
theorem sgnC_swap {α : Type*} [Fintype α] [DecidableEq α]
    {x y : α} (h : x ≠ y) : sgnC (Equiv.swap x y) = -1 := by
  unfold sgnC
  rw [Equiv.Perm.sign_swap h]
  norm_num

variable (ρ : Equiv.Perm (Fin N) →* Module.End ℂ V)

/-- The unnormalized sum of the represented subgroup actions on the input vector. -/
noncomputable def rowSym (H : Subgroup (Equiv.Perm (Fin N))) (ψ : V) : V :=
  ∑ σ : H, ρ (σ : Equiv.Perm (Fin N)) ψ

/-- The unnormalized sum of the represented subgroup actions weighted by their complex
permutation signs. -/
noncomputable def colAlt (H : Subgroup (Equiv.Perm (Fin N))) (ψ : V) : V :=
  ∑ κ : H, sgnC (κ : Equiv.Perm (Fin N)) • ρ (κ : Equiv.Perm (Fin N)) ψ

/-- Applies the row-subgroup sum first and then the column-subgroup alternating sum. -/
noncomputable def youngOp (Hr Hc : Subgroup (Equiv.Perm (Fin N))) (ψ : V) : V :=
  colAlt ρ Hc (rowSym ρ Hr ψ)

/-- Successive represented actions agree with the action of the product permutation. -/
theorem rep_mul_apply (σ τ : Equiv.Perm (Fin N)) (ψ : V) :
    ρ σ (ρ τ ψ) = ρ (σ * τ) ψ := by
  rw [← Module.End.mul_apply, ← map_mul]

/-- Applying the unnormalized subgroup symmetrizer twice multiplies its output by the subgroup
cardinality. -/
theorem rowSym_idem (H : Subgroup (Equiv.Perm (Fin N))) (ψ : V) :
    rowSym ρ H (rowSym ρ H ψ) = (Fintype.card H : ℂ) • rowSym ρ H ψ := by
  have hmul : ∀ σ τ : H,
      ρ (σ : Equiv.Perm (Fin N)) (ρ (τ : Equiv.Perm (Fin N)) ψ)
        = ρ ((σ * τ : H) : Equiv.Perm (Fin N)) ψ :=
    fun σ τ => rep_mul_apply ρ (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin N)) ψ
  unfold rowSym
  simp only [map_sum, hmul]
  have hinner : ∀ σ : H,
      (∑ τ : H, ρ ((σ * τ : H) : Equiv.Perm (Fin N)) ψ)
        = ∑ k : H, ρ (k : Equiv.Perm (Fin N)) ψ :=
    fun σ => sum_mul_left_reindex (G := H)
      (W := fun g : H => ρ (g : Equiv.Perm (Fin N)) ψ) σ
  simp only [hinner]
  exact sum_const_card_smul (∑ k : H, ρ (k : Equiv.Perm (Fin N)) ψ)

/-- Applying the unnormalized subgroup antisymmetrizer twice multiplies its output by the
subgroup cardinality. -/
theorem colAlt_idem (H : Subgroup (Equiv.Perm (Fin N))) (ψ : V) :
    colAlt ρ H (colAlt ρ H ψ) = (Fintype.card H : ℂ) • colAlt ρ H ψ := by
  have hmul : ∀ κ μ : H,
      (sgnC (κ : Equiv.Perm (Fin N)) * sgnC (μ : Equiv.Perm (Fin N)))
          • ρ (κ : Equiv.Perm (Fin N)) (ρ (μ : Equiv.Perm (Fin N)) ψ)
        = sgnC ((κ * μ : H) : Equiv.Perm (Fin N))
            • ρ ((κ * μ : H) : Equiv.Perm (Fin N)) ψ := by
    intro κ μ
    rw [rep_mul_apply ρ (κ : Equiv.Perm (Fin N)) (μ : Equiv.Perm (Fin N)) ψ]
    rw [show ((κ * μ : H) : Equiv.Perm (Fin N))
          = (κ : Equiv.Perm (Fin N)) * (μ : Equiv.Perm (Fin N)) from rfl]
    rw [sgnC_mul]
  unfold colAlt
  simp only [map_sum, map_smul, Finset.smul_sum, smul_smul, hmul]
  have hinner : ∀ κ : H,
      (∑ μ : H, sgnC ((κ * μ : H) : Equiv.Perm (Fin N))
          • ρ ((κ * μ : H) : Equiv.Perm (Fin N)) ψ)
        = ∑ k : H, sgnC (k : Equiv.Perm (Fin N))
            • ρ (k : Equiv.Perm (Fin N)) ψ :=
    fun κ => sum_mul_left_reindex (G := H)
      (W := fun g : H => sgnC (g : Equiv.Perm (Fin N))
        • ρ (g : Equiv.Perm (Fin N)) ψ) κ
  simp only [hinner, mul_smul]
  rw [sum_const_card_smul (∑ k : H, sgnC (k : Equiv.Perm (Fin N))
    • ρ (k : Equiv.Perm (Fin N)) ψ)]
  rw [← Finset.smul_sum]

/-- Acting on an antisymmetrized vector by a subgroup element multiplies it by that element's
sign. -/
theorem colAlt_conj (H : Subgroup (Equiv.Perm (Fin N))) (κ : H) (φ : V) :
    ρ (κ : Equiv.Perm (Fin N)) (colAlt ρ H φ)
      = sgnC (κ : Equiv.Perm (Fin N)) • colAlt ρ H φ := by
  have hmul : ∀ μ : H,
      ρ (κ : Equiv.Perm (Fin N)) (ρ (μ : Equiv.Perm (Fin N)) φ)
        = ρ ((κ * μ : H) : Equiv.Perm (Fin N)) φ :=
    fun μ => rep_mul_apply ρ (κ : Equiv.Perm (Fin N)) (μ : Equiv.Perm (Fin N)) φ
  unfold colAlt
  simp only [map_sum, map_smul, hmul]
  calc
    ∑ μ : H, sgnC (μ : Equiv.Perm (Fin N))
        • ρ ((κ * μ : H) : Equiv.Perm (Fin N)) φ
        = ∑ ν : H, sgnC ((κ⁻¹ * ν : H) : Equiv.Perm (Fin N))
            • ρ ((κ * (κ⁻¹ * ν) : H) : Equiv.Perm (Fin N)) φ := by
          symm
          exact sum_mul_left_reindex (G := H)
            (W := fun ν : H => sgnC (ν : Equiv.Perm (Fin N))
              • ρ ((κ * ν : H) : Equiv.Perm (Fin N)) φ) κ⁻¹
    _ = ∑ ν : H, sgnC ((κ⁻¹ * ν : H) : Equiv.Perm (Fin N))
            • ρ (ν : Equiv.Perm (Fin N)) φ := by
          apply Finset.sum_congr rfl
          intro ν _
          have harg : (κ * (κ⁻¹ * ν) : H) = ν := by group
          rw [harg]
    _ = ∑ ν : H, (sgnC (κ : Equiv.Perm (Fin N)) * sgnC (ν : Equiv.Perm (Fin N)))
            • ρ (ν : Equiv.Perm (Fin N)) φ := by
          apply Finset.sum_congr rfl
          intro ν _
          rw [show ((κ⁻¹ * ν : H) : Equiv.Perm (Fin N))
                = ((κ : Equiv.Perm (Fin N)))⁻¹ * (ν : Equiv.Perm (Fin N)) from rfl,
            sgnC_mul, sgnC_inv]
    _ = sgnC (κ : Equiv.Perm (Fin N))
            • ∑ ν : H, sgnC (ν : Equiv.Perm (Fin N)) • ρ (ν : Equiv.Perm (Fin N)) φ := by
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro ν _
          rw [smul_smul]

/-- The row-subgroup sum is unchanged when its input is acted on by an element of that subgroup. -/
theorem rowSym_invariant (H : Subgroup (Equiv.Perm (Fin N))) (σ : H) (φ : V) :
    rowSym ρ H (ρ (σ : Equiv.Perm (Fin N)) φ) = rowSym ρ H φ := by
  have hmul : ∀ τ : H,
      ρ (τ : Equiv.Perm (Fin N)) (ρ (σ : Equiv.Perm (Fin N)) φ)
        = ρ ((τ * σ : H) : Equiv.Perm (Fin N)) φ :=
    fun τ => rep_mul_apply ρ (τ : Equiv.Perm (Fin N)) (σ : Equiv.Perm (Fin N)) φ
  unfold rowSym
  simp only [hmul]
  exact sum_mul_right_reindex (G := H)
    (W := fun k : H => ρ (k : Equiv.Perm (Fin N)) φ) σ

/-- The Young operator is unchanged when its input is acted on by an element of the row
subgroup. See [Whitfield2013]. -/
theorem youngOp_row_invariant (Hr Hc : Subgroup (Equiv.Perm (Fin N)))
    (σ : Hr) (ψ : V) :
    youngOp ρ Hr Hc (ρ (σ : Equiv.Perm (Fin N)) ψ) = youngOp ρ Hr Hc ψ := by
  unfold youngOp
  rw [rowSym_invariant ρ Hr σ ψ]

/-- The output of the Young operator transforms by the permutation sign under the column
subgroup. See [Whitfield2013]. -/
theorem youngOp_col_antisym (Hr Hc : Subgroup (Equiv.Perm (Fin N)))
    (κ : Hc) (ψ : V) :
    ρ (κ : Equiv.Perm (Fin N)) (youngOp ρ Hr Hc ψ)
      = sgnC (κ : Equiv.Perm (Fin N)) • youngOp ρ Hr Hc ψ := by
  unfold youngOp
  exact colAlt_conj ρ Hc κ (rowSym ρ Hr ψ)

/-- The subgroup of permutations of five labels generated by the row transpositions `(0, 1)` and
`(2, 3)`. -/
def t1RowGroup : Subgroup (Equiv.Perm (Fin 5)) :=
  Subgroup.closure {Equiv.swap (0 : Fin 5) 1, Equiv.swap 2 3}

/-- The subgroup of permutations of five labels generated by the transpositions within `{0, 2,
4}` and within `{1, 3}`. -/
def t1ColGroup : Subgroup (Equiv.Perm (Fin 5)) :=
  Subgroup.closure {Equiv.swap (0 : Fin 5) 2, Equiv.swap 0 4, Equiv.swap 2 4,
    Equiv.swap (1 : Fin 5) 3}

/-- The five-label Young-operator output changes sign under the column transposition
interchanging labels zero and two. See [Whitfield2013]. -/
theorem fiveElectron_T1_column_antisymmetric
    (ρ5 : Equiv.Perm (Fin 5) →* Module.End ℂ V) (ψ : V) :
    ρ5 (Equiv.swap (0 : Fin 5) 2) (youngOp ρ5 t1RowGroup t1ColGroup ψ)
      = - youngOp ρ5 t1RowGroup t1ColGroup ψ := by
  have hmem : Equiv.swap (0 : Fin 5) 2 ∈ t1ColGroup :=
    Subgroup.subset_closure (by simp)
  rw [youngOp_col_antisym ρ5 t1RowGroup t1ColGroup ⟨Equiv.swap 0 2, hmem⟩ ψ,
    sgnC_swap (by decide : (0 : Fin 5) ≠ 2)]
  norm_num

/-- Applying the row transposition interchanging labels zero and one to the input leaves the
five-label Young-operator result unchanged. -/
theorem fiveElectron_T1_row_invariant
    (ρ5 : Equiv.Perm (Fin 5) →* Module.End ℂ V) (ψ : V) :
    youngOp ρ5 t1RowGroup t1ColGroup (ρ5 (Equiv.swap (0 : Fin 5) 1) ψ)
      = youngOp ρ5 t1RowGroup t1ColGroup ψ := by
  have hmem : Equiv.swap (0 : Fin 5) 1 ∈ t1RowGroup :=
    Subgroup.subset_closure (by simp)
  exact youngOp_row_invariant ρ5 t1RowGroup t1ColGroup ⟨Equiv.swap 0 1, hmem⟩ ψ

end Qatlib.Papers.SpinFreeSim13.YoungModels
