/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.QramData.SquaredNormTree.Storage
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Amplitude preparation from cached square sums

A branch contributes the square root of the child-to-parent mass ratio. At the leaf,
the signed entry divided by its absolute value supplies the terminal sign. The product
of these factors is the normalized signed entry, including zero entries. A state
requires positive root mass. The module accounts for the exact amplitudes, with
cached real arithmetic interpreted exactly.

See [KerenidisPrakash2017], Appendix A, [KerenidisLandmanPrakash2020], Appendix F.2,
and [ChenXueChenEtAl2022], Appendix E.
-/

set_option autoImplicit false

namespace Qatlib.Concepts.QRAM.AmplitudeAccess

open scoped BigOperators
open Qatlib.Foundations.QramData.SquaredNormTree

variable {depth : ℕ}

/-- The mass of a valid tree is nonnegative. -/
theorem mass_nonneg (tree : Tree ℝ depth) (h : Valid tree) : 0 ≤ mass tree := by
  rw [mass_eq_sum tree h]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- A valid tree of zero mass contains only zero entries. -/
theorem read_eq_zero_of_mass_eq_zero (tree : Tree ℝ depth) (h : Valid tree)
    (hZero : mass tree = 0) (address : Address depth) : read tree address = 0 := by
  have hBound : read tree address ^ 2 ≤ mass tree := by
    rw [mass_eq_sum tree h]
    exact Finset.single_le_sum (f := fun a => read tree a ^ 2)
      (fun a _ => sq_nonneg _) (Finset.mem_univ address)
  rw [hZero] at hBound
  exact sq_eq_zero_iff.mp (le_antisymm hBound (sq_nonneg _))

/-- The magnitude contributed by the addressed branch in the preparation. -/
noncomputable def branchAmplitude (tree : Tree ℝ (depth + 1)) (bit : Bool) : ℝ :=
  Real.sqrt (mass (child tree bit) / mass tree)

/-- Compute the output amplitude as the product of branch factors and the signed leaf factor. -/
noncomputable def pathAmplitude : {depth : ℕ} → Tree ℝ depth → Address depth → ℝ
  | 0, tree, address => read tree address / Real.sqrt (mass tree)
  | _ + 1, tree, address =>
      branchAmplitude tree (address 0) * pathAmplitude (child tree (address 0)) (Fin.tail address)

/-- The branch square-root ratios telescope to the normalized signed entries. -/
theorem path_amplitude_eq (tree : Tree ℝ depth) (h : Valid tree) (address : Address depth) :
    pathAmplitude tree address = read tree address / Real.sqrt (mass tree) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      let selected := child tree (address 0)
      have hSelected : Valid selected := valid_child tree (address 0) h
      rw [pathAmplitude, ih selected hSelected]
      change Real.sqrt (mass selected / mass tree) *
        (read selected (Fin.tail address) / Real.sqrt (mass selected)) =
          read selected (Fin.tail address) / Real.sqrt (mass tree)
      by_cases hZero : mass selected = 0
      · simp [read_eq_zero_of_mass_eq_zero selected hSelected hZero]
      rw [Real.sqrt_div (mass_nonneg selected hSelected)]
      have hSqrt : Real.sqrt (mass selected) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 (lt_of_le_of_ne (mass_nonneg selected hSelected) (Ne.symm hZero)))
      rw [div_mul_div_comm, mul_comm (Real.sqrt (mass tree)), mul_div_mul_left _ _ hSqrt]

/-- Positive root mass gives a unit vector, so squared amplitudes form a sampling law. -/
theorem sum_path_amplitude_sq (tree : Tree ℝ depth) (h : Valid tree) (hPos : 0 < mass tree) :
    ∑ address : Address depth, pathAmplitude tree address ^ 2 = 1 := by
  simp_rw [path_amplitude_eq tree h, div_pow, Real.sq_sqrt hPos.le]
  rw [← Finset.sum_div, ← mass_eq_sum tree h, div_self hPos.ne']

/-- Top-level preparation ending at a prefix while leaving the lower tree unopened. -/
noncomputable def prefixAmplitude {remaining : ℕ} : (levels : ℕ) →
    Tree ℝ (remaining + levels) → Address levels → ℝ
  | 0, _, _ => 1
  | levels + 1, tree, address =>
      branchAmplitude tree (address 0) *
        prefixAmplitude levels (child tree (address 0)) (Fin.tail address)

/-- Multiplying the prefix amplitude by the root norm recovers the selected subtree norm. -/
theorem sqrt_mass_mul_prefix_amplitude {remaining : ℕ} (levels : ℕ)
    (tree : Tree ℝ (remaining + levels)) (h : Valid tree) (address : Address levels) :
    Real.sqrt (mass tree) * prefixAmplitude levels tree address =
      Real.sqrt (mass (subtree levels tree address)) := by
  induction levels with
  | zero => simp [prefixAmplitude, subtree]
  | succ levels ih =>
      have hChild := valid_child tree (address 0) h
      have hNonneg := mass_nonneg _ hChild
      have hBound : mass (child tree (address 0)) ≤ mass tree := by
        rw [mass_eq_children tree h]
        have hLeft := mass_nonneg _ (valid_child tree false h)
        have hRight := mass_nonneg _ (valid_child tree true h)
        cases address 0
        · simp only [le_add_iff_nonneg_right, hRight]
        · simp only [le_add_iff_nonneg_left, hLeft]
      have hScale : Real.sqrt (mass tree) * branchAmplitude tree (address 0) =
          Real.sqrt (mass (child tree (address 0))) := by
        unfold branchAmplitude
        rw [Real.sqrt_div hNonneg]
        by_cases hZero : mass tree = 0
        · have hZeroChild := le_antisymm (hZero ▸ hBound) hNonneg
          simp [hZero, hZeroChild]
        · have hn := ne_of_gt (Real.sqrt_pos.2 (lt_of_le_of_ne (mass_nonneg tree h) (Ne.symm hZero)))
          rw [mul_comm, div_mul_cancel₀ _ hn]
      rw [prefixAmplitude, ← mul_assoc, hScale, ih _ hChild, subtree]

/-- A positive root makes each prefix amplitude the selected norm divided by the root norm. -/
theorem prefix_amplitude_eq {remaining : ℕ} (levels : ℕ) (tree : Tree ℝ (remaining + levels))
    (h : Valid tree) (hPos : 0 < mass tree) (address : Address levels) :
    prefixAmplitude levels tree address =
      Real.sqrt (mass (subtree levels tree address)) / Real.sqrt (mass tree) := by
  apply (eq_div_iff (Real.sqrt_pos.2 hPos).ne').2
  rw [mul_comm]
  exact sqrt_mass_mul_prefix_amplitude levels tree h address

end Qatlib.Concepts.QRAM.AmplitudeAccess
