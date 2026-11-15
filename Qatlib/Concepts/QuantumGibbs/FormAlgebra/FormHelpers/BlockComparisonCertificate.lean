/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra.BlockComparisonCertificate
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

def gap (c : ℝ) (M G : Matrix I I ℂ) : Matrix I I ℂ := (c:ℂ) • M-G

omit [DecidableEq I] [DecidableEq J] in

/-- Compression by `U` preserves positive semidefiniteness of the comparison gap between `M` and
`G`. -/
theorem compress (c : ℝ) (M G : Matrix I I ℂ) (U : Matrix I J ℂ)
    (h : (gap c M G).PosSemidef) :
    (gap c (Uᴴ*M*U) (Uᴴ*G*U)).PosSemidef := by
  have ht := h.conjTranspose_mul_mul_same U
  simpa only [gap,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul] using ht

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in

/-- The comparison gap of two Hermitian block matrices is the block matrix of their diagonal
gaps and scaled off-diagonal difference. -/
theorem gap_blocks (c : ℝ) (M00 G00 : Matrix I I ℂ) (M11 Clause11 : Matrix J J ℂ)
    (M01 G01 : Matrix I J ℂ) :
    gap c (fromBlocks M00 M01 M01ᴴ M11) (fromBlocks G00 G01 G01ᴴ Clause11) =
      fromBlocks (gap c M00 G00) ((c:ℂ) • M01-G01)
        (((c:ℂ) • M01-G01)ᴴ) (gap c M11 Clause11) := by
  ext x y
  cases x <;> cases y <;>
    simp [gap,Matrix.fromBlocks,Matrix.conjTranspose_apply]

omit [DecidableEq I] in

/-- When the lower diagonal gap is positive definite and invertible, positivity of the full gap
is equivalent to positivity of its Schur complement. -/
theorem full_iff_schur (c : ℝ) (M00 G00 : Matrix I I ℂ) (M11 Clause11 : Matrix J J ℂ)
    (M01 G01 : Matrix I J ℂ)
    (hD : (gap c M11 Clause11).PosDef) [Invertible (gap c M11 Clause11)] :
    (gap c (fromBlocks M00 M01 M01ᴴ M11) (fromBlocks G00 G01 G01ᴴ Clause11)).PosSemidef ↔
      (gap c M00 G00-((c:ℂ) • M01-G01)*(gap c M11 Clause11)⁻¹*
        (((c:ℂ) • M01-G01)ᴴ)).PosSemidef := by
  rw [gap_blocks]
  exact hD.fromBlocks₂₂ _ _

omit [DecidableEq I] in

/-- A positive definite lower gap and positive semidefinite Schur complement imply the full
quadratic form of `G` is bounded by `c` times that of `M`. -/
theorem full_form_bound (c : ℝ) (M00 G00 : Matrix I I ℂ) (M11 Clause11 : Matrix J J ℂ)
    (M01 G01 : Matrix I J ℂ)
    (hD : (gap c M11 Clause11).PosDef) [Invertible (gap c M11 Clause11)]
    (hS : (gap c M00 G00-((c:ℂ) • M01-G01)*(gap c M11 Clause11)⁻¹*
        (((c:ℂ) • M01-G01)ᴴ)).PosSemidef) (v : I ⊕ J → ℂ) :
    (star v ⬝ᵥ (fromBlocks G00 G01 G01ᴴ Clause11 *ᵥ v)).re ≤
      c*(star v ⬝ᵥ (fromBlocks M00 M01 M01ᴴ M11 *ᵥ v)).re := by
  have h := ((full_iff_schur c M00 G00 M11 Clause11 M01 G01 hD).mpr hS).dotProduct_mulVec_nonneg v
  have hr := (Complex.nonneg_iff.mp h).1
  simpa [gap,Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,dotProduct_smul,
    Complex.sub_re,Complex.mul_re] using hr

end
end Qatlib.Concepts.QuantumGibbs.FormAlgebra.BlockComparisonCertificate
