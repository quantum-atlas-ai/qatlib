/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.Measurements.POVM
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# Two-outcome instruments for contractions

For a contraction `B`, `failure` is the positive square root of `1 - Bᴴ * B`. Together with `B`,
it forms a complete two-element Kraus family, defining a trace-preserving channel and a Boolean
POVM `readout`. The success probability is the real trace of the success completely positive
branch.

The mathematical background is described in [Kraus1971].

## Main statements

* `kraus_complete`: success and failure satisfy Kraus completeness.
* `successCP_matrix`: the success branch is conjugation by `B`.
* `success_probability_trace`: the readout probability equals the success branch trace.

## References

* [Kraus, 1971][Kraus1971]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open Matrix
open scoped Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

namespace Qatlib.Concepts.ChannelTheory.Naimark.ContractionInstrument
variable {I : Type} [Fintype I] [DecidableEq I]

section DefectOrder
noncomputable local instance matrixCStar : CStarAlgebra (Matrix I I ℂ) where

/-- For a contraction `B`, the defect matrix `1 - Bᴴ * B` is positive semidefinite. -/
theorem defect_posSemidef (B : Matrix I I ℂ) (hB : ‖B‖≤1) : (1-Bᴴ*B).PosSemidef := by
  have hs := CStarAlgebra.star_mul_le_algebraMap_norm_sq (a:=B)
  rw [Matrix.star_eq_conjTranspose] at hs
  have hn : algebraMap ℝ (Matrix I I ℂ) (‖B‖^2)≤1 := by
    rw [← map_one (algebraMap ℝ (Matrix I I ℂ)),← sub_nonneg,← map_sub]
    rw [Algebra.algebraMap_eq_smul_one]
    exact (Matrix.PosSemidef.one.smul (by nlinarith [norm_nonneg B] : (0:ℝ)≤1-‖B‖^2)).nonneg
  exact Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr (hs.trans hn))

end DefectOrder

/-- The positive square root of the defect matrix `1 - Bᴴ * B` of a contraction. -/
def failure (B : Matrix I I ℂ) (hB : ‖B‖≤1) : Matrix I I ℂ :=
  (HermitianMat.sqrt (⟨1-Bᴴ*B,(defect_posSemidef B hB).isHermitian⟩ : HermitianMat I ℂ)).mat

/-- The failure matrix of a contraction is Hermitian. -/
theorem failure_hermitian (B : Matrix I I ℂ) (hB : ‖B‖≤1) : (failure B hB)ᴴ=failure B hB :=
  (HermitianMat.sqrt (⟨1-Bᴴ*B,(defect_posSemidef B hB).isHermitian⟩ : HermitianMat I ℂ)).H

/-- The square of the failure matrix equals `1 - Bᴴ * B`. -/
theorem failure_square (B : Matrix I I ℂ) (hB : ‖B‖≤1) : failure B hB*failure B hB=1-Bᴴ*B :=
  HermitianMat.sqrt_sq (HermitianMat.zero_le_iff.mpr (defect_posSemidef B hB))

/-- The Boolean Kraus family using `B` for success and its defect square root for failure. -/
def kraus (B : Matrix I I ℂ) (hB : ‖B‖≤1) (b : Bool) : Matrix I I ℂ :=
  if b then B else failure B hB

/-- The success and failure Kraus matrices of a contraction satisfy the completeness identity.
See [Kraus1971]. -/
theorem kraus_complete (B : Matrix I I ℂ) (hB : ‖B‖≤1) : ∑ b : Bool,(kraus B hB b)ᴴ*kraus B hB b=1 := by
  simp only [Fintype.sum_bool,kraus,Bool.false_eq_true,ite_false,ite_true,failure_hermitian,failure_square]
  abel

/-- The trace-preserving completely positive map defined by the success and failure Kraus
matrices of a contraction. -/
def channel (B : Matrix I I ℂ) (hB : ‖B‖≤1) : CPTPMap I I ℂ :=
  CPTPMap.of_kraus_CPTPMap (kraus B hB) (kraus_complete B hB)

/-- The completely positive map with the single Kraus matrix `B`. -/
def successCP (B : Matrix I I ℂ) : CPMap I I ℂ :=
  CPMap.of_kraus_CPMap (fun _ : Unit => B)

/-- The success completely positive map acts on a matrix as `B * ρ * Bᴴ`. -/
theorem successCP_matrix (B ρ : Matrix I I ℂ) : (successCP B).map ρ=B*ρ*Bᴴ := by
  simp [successCP,CPMap.of_kraus_CPMap,HPMap.map,MatrixMap.of_kraus]

/-- The Boolean POVM with effects equal to the adjoint products of the success and failure Kraus
matrices. -/
def readout (B : Matrix I I ℂ) (hB : ‖B‖≤1) : POVM Bool I where
  mats b := ⟨(kraus B hB b)ᴴ*kraus B hB b,Matrix.isHermitian_conjTranspose_mul_self _⟩
  nonneg b := HermitianMat.zero_le_iff.mpr (Matrix.posSemidef_conjTranspose_mul_self _)
  normalized := by
    apply HermitianMat.ext
    simpa only [HermitianMat.mat_finset_sum,HermitianMat.mat_one] using! kraus_complete B hB

/-- The success probability of the Boolean contraction readout equals the real trace of the
success branch applied to the input state. -/
theorem success_probability_trace (B : Matrix I I ℂ) (hB : ‖B‖≤1) (ρ : MState I) :
    (((readout B hB).measure ρ) true : ℝ)=((successCP B).map ρ.m).trace.re := by
  change (RCLike.re (((readout B hB).mats true).mat*ρ.m).trace)=_
  rw [successCP_matrix]
  change ((Bᴴ*B*ρ.m).trace).re=(B*ρ.m*Bᴴ).trace.re
  exact congrArg Complex.re (Matrix.trace_mul_cycle B ρ.m Bᴴ).symm

end Qatlib.Concepts.ChannelTheory.Naimark.ContractionInstrument
