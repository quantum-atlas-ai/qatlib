/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import Mathlib.Data.Matrix.Basic

/-!
# Matrix approximation and frame ledger data

This module defines rational precision scales, approximation records, and symbolic frame
preparation data. `CauchyComplexMatrix` stores entrywise rational approximations with certified
error, while `FrameData` stores a Gram matrix, a nonnegative defect, and resource counts for
later perturbation estimates; matrix analysis background is provided by [Bhatia1997].

## Main statements

* `CauchyReal` and `CauchyComplexMatrix`: record rational approximation data.
* `matrixReadBits`: records a dimension and precision dependent read cost.
* `FrameData.prepareWord`: constructs the symbolic frame preparation word.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option autoImplicit false

open Qatlib.Concepts.PhaseGeometry.Phase

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb
namespace MatrixComputation

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The real precision scale `1 / 2 ^ p`. -/
noncomputable def ratUnitR (p : ℕ) : ℝ := 1 / (2 : ℝ) ^ p

/-- The rational precision scale `1 / 2 ^ p`. -/
def ratUnit (p : ℕ) : ℚ := 1 / (2 : ℚ) ^ p

/-- A sequence of rational approximations whose pairwise differences are bounded by the sum of
their real precision scales. -/
structure CauchyReal where

  approx : ℕ → ℚ

  cauchy : ∀ p q, (↑|approx p - approx q| : ℝ) ≤ ratUnitR p + ratUnitR q

/-- A finite approximation record containing a rational value, a real error value, and a natural
bit count. -/
structure FiniteReal where

  value : ℚ

  error : ℝ

  bits : ℕ

/-- The precision choice `k + 1` for a requested index `k`. -/
def digitsFor (k : ℕ) : ℕ := k + 1

/-- A complex square matrix with rational entry approximations whose error at precision `p` is
bounded by `ratUnitR p`. -/
structure CauchyComplexMatrix (I : Type) [Fintype I] [DecidableEq I] where

  data : Matrix I I ℂ

  approx : ℕ → I → I → ℚ

  error : ∀ p i j, ‖((approx p i j : ℚ) - data i j)‖ ≤ ratUnitR p

/-- The matrix approximation record for a rational matrix, using its exact entries at every
precision. -/
def CauchyComplexMatrix.ofRational (M : Matrix I I ℚ) : CauchyComplexMatrix I where
  data := fun i j => (M i j : ℂ)
  approx := fun _ i j => M i j
  error := by
    intro p i j
    have h : ((M i j : ℚ) : ℂ) - (M i j : ℂ) = 0 := by
      simp
    rw [h, norm_zero]
    unfold ratUnitR
    positivity

/-- A complex square matrix together with a recorded bit count. -/
structure FiniteComplexMatrix (I : Type) [Fintype I] [DecidableEq I] where

  data : Matrix I I ℂ

  bits : ℕ

/-- The read cost `D * D * p` for a square matrix of dimension `D` at precision `p`. -/
def matrixReadBits (D p : ℕ) : ℕ := D * D * p

/-- The symbolic gate kinds used by the frame preparation ledger. -/
inductive FrameGateKind where

  | gramCorrection

  | reflection

  | phaseRotation

  | ancillaSwap

  | uncompute

/-- The fixed list of all symbolic frame gate kinds. -/
def FrameGateSet.all : List FrameGateKind :=
  [.gramCorrection, .reflection, .phaseRotation, .ancillaSwap, .uncompute]

/-- A rational Gram matrix together with a nonnegative rational defect and a recorded entry
count. -/
structure FrameData (m : ℕ) where

  gram : Fin m → Fin m → ℚ

  defect : ℚ

  entries : ℕ

  defect_nonneg : 0 ≤ defect

/-- The frame preparation word consisting of `F.entries + 1` Gram correction gates followed by
reflection, phase rotation, ancilla swap, and uncomputation. -/
def FrameData.prepareWord {m : ℕ} (F : FrameData m) : List FrameGateKind :=
  List.replicate (F.entries + 1) .gramCorrection
    ++ [.reflection, .phaseRotation, .ancillaSwap, .uncompute]

/-- The frame read time cost, defined as the recorded entry count. -/
def FrameData.readBitTime {m : ℕ} (F : FrameData m) : ℕ := F.entries

/-- The frame ancilla count `F.entries + 1`. -/
def FrameData.ancillas {m : ℕ} (F : FrameData m) : ℕ := F.entries + 1

end MatrixComputation
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb
