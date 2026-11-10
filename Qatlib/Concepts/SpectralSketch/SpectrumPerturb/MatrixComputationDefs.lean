/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import Mathlib.Data.Matrix.Basic
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.PhaseGeometry.Phase

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb
namespace MatrixComputation

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def ratUnitR (p : ℕ) : ℝ := 1 / (2 : ℝ) ^ p

def ratUnit (p : ℕ) : ℚ := 1 / (2 : ℚ) ^ p

structure CauchyReal where

  approx : ℕ → ℚ

  cauchy : ∀ p q, (↑|approx p - approx q| : ℝ) ≤ ratUnitR p + ratUnitR q

structure FiniteReal where

  value : ℚ

  error : ℝ

  bits : ℕ

def digitsFor (k : ℕ) : ℕ := k + 1

structure CauchyComplexMatrix (I : Type) [Fintype I] [DecidableEq I] where

  data : Matrix I I ℂ

  approx : ℕ → I → I → ℚ

  error : ∀ p i j, ‖((approx p i j : ℚ) - data i j)‖ ≤ ratUnitR p

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

structure FiniteComplexMatrix (I : Type) [Fintype I] [DecidableEq I] where

  data : Matrix I I ℂ

  bits : ℕ

def matrixReadBits (D p : ℕ) : ℕ := D * D * p

inductive FrameGateKind where

  | gramCorrection

  | reflection

  | phaseRotation

  | ancillaSwap

  | uncompute

def FrameGateSet.all : List FrameGateKind :=
  [.gramCorrection, .reflection, .phaseRotation, .ancillaSwap, .uncompute]

structure FrameData (m : ℕ) where

  gram : Fin m → Fin m → ℚ

  defect : ℚ

  entries : ℕ

  defect_nonneg : 0 ≤ defect

def FrameData.prepareWord {m : ℕ} (F : FrameData m) : List FrameGateKind :=
  List.replicate (F.entries + 1) .gramCorrection
    ++ [.reflection, .phaseRotation, .ancillaSwap, .uncompute]

def FrameData.readBitTime {m : ℕ} (F : FrameData m) : ℕ := F.entries

def FrameData.ancillas {m : ℕ} (F : FrameData m) : ℕ := F.entries + 1

end MatrixComputation
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb
