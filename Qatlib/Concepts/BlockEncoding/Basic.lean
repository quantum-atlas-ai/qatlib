/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding

/-!
# Approximate block encodings

`BlockEncoding` expresses approximation of a matrix by a positively scaled compression of a
unitary between two isometric frames. Its error is measured in the matrix operator norm.

The basic laws transport encodings across larger error budgets, perturbations of the target, and
adjoints. Norm estimates show that isometric compression does not increase operator norm.

For background, see [GilyenSuLowWiebe2019].

## Main statements

* `BlockEncoding`: a scaled compression with a nonnegative error bound.
* `BlockEncoding.perturb`: adds target perturbation to the encoding error.
* `compress_sub_norm_le`: compression is nonexpansive on matrix differences.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.Execution.WorkspaceCP

namespace Qatlib.Concepts.BlockEncoding

open Matrix
open scoped Matrix.Norms.L2Operator

variable {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
  [DecidableEq H] [DecidableEq I] [DecidableEq O]

/-- An approximate block encoding of `A` by a unitary `U` between isometric frames `L` and `R`,
with positive scale `α` and operator-norm error at most `ε`. -/
structure BlockEncoding (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (α ε : ℝ) : Prop where
  unitary : U ∈ Matrix.unitaryGroup H ℂ
  left_isometry : IsIsometry L
  right_isometry : IsIsometry R
  normalization_pos : 0 < α
  error_nonneg : 0 ≤ ε
  error_le : ‖A - α • compress L U R‖ ≤ ε

/-- An exact projected unitary encoding gives a block encoding with scale one and zero error. -/
theorem ProjectedUnitaryEncoding.toBlockEncoding {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ} (h : ProjectedUnitaryEncoding A U L R) :
    BlockEncoding A U L R 1 0 := by
  refine ⟨h.unitary, h.left_isometry, h.right_isometry, by norm_num, le_rfl, ?_⟩
  simp [h.encoded]

/-- A block encoding remains valid after increasing its error allowance. -/
theorem BlockEncoding.mono {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ} {α ε δ : ℝ}
    (h : BlockEncoding A U L R α ε) (hεδ : ε ≤ δ) : BlockEncoding A U L R α δ :=
  ⟨h.unitary, h.left_isometry, h.right_isometry, h.normalization_pos,
    h.error_nonneg.trans hεδ, h.error_le.trans hεδ⟩

/-- Perturbing the target matrix by operator-norm distance at most `δ` increases the
block-encoding error by at most `δ`. -/
theorem BlockEncoding.perturb {A B : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ} {α ε δ : ℝ}
    (h : BlockEncoding A U L R α ε) (hδ : 0 ≤ δ) (hAB : ‖B - A‖ ≤ δ) :
    BlockEncoding B U L R α (ε + δ) := by
  refine ⟨h.unitary, h.left_isometry, h.right_isometry, h.normalization_pos,
    add_nonneg h.error_nonneg hδ, ?_⟩
  calc
    ‖B - α • compress L U R‖ = ‖(B - A) + (A - α • compress L U R)‖ := by
      congr 1
      abel
    _ ≤ ‖B - A‖ + ‖A - α • compress L U R‖ := norm_add_le _ _
    _ ≤ δ + ε := add_le_add hAB h.error_le
    _ = ε + δ := add_comm _ _

end Qatlib.Concepts.BlockEncoding

open Matrix Polynomial
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]
namespace Qatlib.Concepts.BlockEncoding.Encoding
open Matrix
open scoped Matrix.Norms.L2Operator

/-- Taking conjugate transposes and swapping the left and right frames preserves block-encoding
scale and error. -/
theorem BlockEncoding.adjoint {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
    [DecidableEq H] [DecidableEq I] [DecidableEq O]
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    {α ε : ℝ} (h : BlockEncoding A U L R α ε) : BlockEncoding Aᴴ Uᴴ R L α ε := by
  refine ⟨adjoint_unitary h.unitary, h.right_isometry, h.left_isometry,
    h.normalization_pos, h.error_nonneg, ?_⟩
  have he : Aᴴ - α • compress R Uᴴ L = (A - α • compress L U R)ᴴ := by
    simp [compress_adjoint]
  rw [he, Matrix.l2_opNorm_conjTranspose]
  exact h.error_le
end Qatlib.Concepts.BlockEncoding.Encoding

open Matrix
open scoped Matrix.Norms.L2Operator
namespace Qatlib.Concepts.BlockEncoding.Encoding

/-- The operator norm of the identity matrix is at most one, including for an empty index type. -/
theorem matrix_one_norm_le {I : Type*} [Fintype I] [DecidableEq I] :
    ‖(1 : Matrix I I ℂ)‖ ≤ 1 := by
  change ‖(Matrix.diagonal (fun _ : I => (1 : ℂ)) : Matrix I I ℂ)‖ ≤ 1
  rw [Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun _ => by simp)

/-- The operator norm of an isometric matrix is at most one. -/
theorem IsIsometry.norm_le_one {H I : Type*} [Fintype H] [Fintype I]
    [DecidableEq I] {V : Matrix H I ℂ} (hV : IsIsometry V) : ‖V‖ ≤ 1 := by
  rw [← sq_le_one_iff₀ (norm_nonneg V), pow_two,
    ← Matrix.l2_opNorm_conjTranspose_mul_self, show Vᴴ * V = 1 from hV]
  exact matrix_one_norm_le

/-- The operator norm of a unitary matrix is at most one. -/
theorem unitary_norm_le_one {H : Type*} [Fintype H] [DecidableEq H]
    {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) : ‖U‖ ≤ 1 := by
  apply IsIsometry.norm_le_one
  change Uᴴ * U = 1
  simpa only [Matrix.star_eq_conjTranspose] using hU.1

/-- Compression between isometric frames does not increase the operator norm. -/
theorem compress_norm_le {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
    [DecidableEq H] [DecidableEq I] [DecidableEq O]
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (hL : IsIsometry L) (hR : IsIsometry R) (U : Matrix H H ℂ) :
    ‖compress L U R‖ ≤ ‖U‖ := by
  have hLa : ‖Lᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact IsIsometry.norm_le_one hL
  have hleft : ‖Lᴴ * U‖ ≤ ‖U‖ := by
    calc
      ‖Lᴴ * U‖ ≤ ‖Lᴴ‖ * ‖U‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ‖U‖ := mul_le_mul_of_nonneg_right hLa (norm_nonneg U)
      _ = ‖U‖ := one_mul _
  calc
    ‖compress L U R‖ ≤ ‖Lᴴ * U‖ * ‖R‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖U‖ * 1 := mul_le_mul hleft (IsIsometry.norm_le_one hR) (norm_nonneg R) (norm_nonneg U)
    _ = ‖U‖ := mul_one _

/-- The norm of the difference of two isometric compressions is at most the norm of the original
matrix difference. -/
theorem compress_sub_norm_le {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
    [DecidableEq H] [DecidableEq I] [DecidableEq O]
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (hL : IsIsometry L) (hR : IsIsometry R) (U V : Matrix H H ℂ) :
    ‖compress L U R - compress L V R‖ ≤ ‖U - V‖ := by
  simpa only [compress, Matrix.mul_sub, Matrix.sub_mul] using
    compress_norm_le hL hR (U - V)
end Qatlib.Concepts.BlockEncoding.Encoding
