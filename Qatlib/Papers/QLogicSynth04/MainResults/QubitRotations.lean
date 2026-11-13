/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownQubitEuler

/-!
# Qubit rotations for circuit synthesis

The matrices `paperRz` and `paperRy` implement the paper's single-qubit rotation conventions.
Their composition, unitarity, and bit-flip identities support multiplexor synthesis;
`theorem2_preparation` prepares any normalized qubit state from `ket0` using three Euler
rotations. See [ShendeBullockMarkov2006] for the paper's setting.

## Main statements

* `paperRz`: The qubit Z rotation at angle `θ`, defined as `qubitEulerPhase (-θ)`.
* `theorem2_preparation`: Every qubit vector with amplitudes `a, b` satisfying `normSq a +
  normSq b = 1` can be prepared from `ket0` by a Z-Y-Z rotation product.

## References

* [Shende et al., 2006][ShendeBullockMarkov2006]
-/

set_option backward.isDefEq.respectTransparency false

open scoped Matrix
open Matrix
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLogicSynth04.MainResults

/-- The qubit Z rotation at angle `θ`, defined as `qubitEulerPhase (-θ)`. -/
def paperRz (θ : ℝ) : Matrix Bool Bool ℂ := qubitEulerPhase (-θ)

/-- The qubit Y rotation at angle `θ`, defined as `qubitEulerRotation θ`. -/
def paperRy (θ : ℝ) : Matrix Bool Bool ℂ := qubitEulerRotation θ

/-- The Pauli X matrix, which exchanges the two computational basis states. -/
def bitFlip : Matrix Bool Bool ℂ := PauliX

/-- The computational basis vector with amplitude one at `false` and zero at `true`. -/
def ket0 : Bool → ℂ := fun b => if b then 0 else 1

/-- Composing two `paperRz` rotations adds their angles. -/
theorem paperRz_mul (s t : ℝ) : paperRz s * paperRz t = paperRz (s + t) := by
  simp only [paperRz]
  rw [qubitEulerPhase_mul]
  congr 1
  ring

/-- Composing two `paperRy` rotations adds their angles. -/
theorem paperRy_mul (s t : ℝ) : paperRy s * paperRy t = paperRy (s + t) := by
  unfold paperRy; exact qubitEulerRotation_mul s t

/-- Conjugating `paperRz θ` by `bitFlip` reverses its angle. -/
theorem bitFlip_mul_paperRz (θ : ℝ) : bitFlip * paperRz θ * bitFlip = paperRz (-θ) := by
  simpa [bitFlip, paperRz] using! pauliX_mul_qubitEulerPhase (-θ)

/-- Conjugating `paperRy θ` by `bitFlip` reverses its angle. -/
theorem bitFlip_mul_paperRy (θ : ℝ) : bitFlip * paperRy θ * bitFlip = paperRy (-θ) := by
  simpa [bitFlip, paperRy] using! pauliX_mul_qubitEulerRotation θ

/-- Every `paperRz` rotation is unitary. -/
theorem paperRz_unitary (θ : ℝ) : paperRz θ ∈ Matrix.unitaryGroup Bool ℂ :=
  qubitEulerPhase_unitary (-θ)

/-- Every `paperRy` rotation is unitary. -/
theorem paperRy_unitary (θ : ℝ) : paperRy θ ∈ Matrix.unitaryGroup Bool ℂ :=
  qubitEulerRotation_unitary θ

/-- The zero-angle Z rotation is the identity. -/
theorem paperRz_zero : paperRz 0 = 1 := by
  simpa [paperRz] using! qubitEulerPhase_zero

/-- The conjugate transpose of `paperRz θ` is the rotation at angle `-θ`. -/
theorem paperRz_conjTranspose (θ : ℝ) : (paperRz θ)ᴴ = paperRz (-θ) := by
  simp [paperRz, qubitEulerPhase_conjTranspose]

/-- The conjugate transpose of `paperRy θ` is the rotation at angle `-θ`. -/
theorem paperRy_conjTranspose (θ : ℝ) : (paperRy θ)ᴴ = paperRy (-θ) := by
  simp [paperRy, qubitEulerRotation_conjTranspose]

/-- Multiplying a qubit matrix by `ket0` selects its column indexed by `false`. -/
theorem mulVec_ket0 (M : Matrix Bool Bool ℂ) : M *ᵥ ket0 = fun i : Bool => M i false := by
  ext i; simp [Matrix.mulVec, ket0, dotProduct]

/-- The action of `paperRz θ` on `ket0` multiplies its nonzero amplitude by `exp (-θ*I/2)`. -/
theorem paperRz_mulVec_ket0 (θ : ℝ) :
    paperRz θ *ᵥ ket0 = fun i : Bool => if i then 0 else Complex.exp ((-(θ/2) : ℝ) * Complex.I) := by
  rw [mulVec_ket0]
  ext i
  rcases i with _ | _
  · have harg : ((-θ)/2 : ℝ) = -(θ/2) := by ring
    simp [paperRz, qubitEulerPhase_apply, harg]
  · simp [paperRz, qubitEulerPhase_apply]

/-- Every qubit vector with amplitudes `a, b` satisfying `normSq a + normSq b = 1` can be
prepared from `ket0` by a Z-Y-Z rotation product. See [ShendeBullockMarkov2006]. -/
theorem theorem2_preparation (a b : ℂ) (hab : Complex.normSq a + Complex.normSq b = 1) :
    ∃ α θ β : ℝ, (paperRz α * paperRy θ * paperRz β) *ᵥ ket0 =
      (fun i : Bool => if i then b else a) := by
  let bb : ℂ := -((starRingEnd ℂ) b)
  have hbb : Complex.normSq a + Complex.normSq bb = 1 := by
    dsimp [bb]; rw [Complex.normSq_neg, Complex.normSq_conj]; exact hab
  have h := euler_angles_reconstruct a bb hbb
  refine ⟨-(Complex.arg a + Complex.arg bb), 2 * Real.arccos ‖a‖,
          -(Complex.arg a - Complex.arg bb), ?_⟩
  rw [show paperRz (-(Complex.arg a + Complex.arg bb))
        = qubitEulerPhase (Complex.arg a + Complex.arg bb) from by simp [paperRz]]
  rw [show paperRy (2 * Real.arccos ‖a‖)
        = qubitEulerRotation (2 * Real.arccos ‖a‖) from rfl]
  rw [show paperRz (-(Complex.arg a - Complex.arg bb))
        = qubitEulerPhase (Complex.arg a - Complex.arg bb) from by simp [paperRz]]
  rw [h, mulVec_ket0]
  ext i
  rcases i with _ | _
  · simp [Matrix.of_apply]
  · simp [Matrix.of_apply, bb]

end Qatlib.Papers.QLogicSynth04.MainResults
