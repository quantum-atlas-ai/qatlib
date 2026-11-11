/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.Checkerboard
import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.SharedPhases
import Mathlib.Data.ZMod.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Grid Parity

The actual periodic-grid checkerboard residue, transported through the canonical ZMod map.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib.Concepts.SpinorSampling.Model

/-- The actual periodic-grid checkerboard residue, transported through the canonical ZMod map. -/
def gridParityResidue (d N : ℕ) [NeZero N] (hN : 2 ∣ N)
    (x : Fin d → Fin N) : ZMod 2 :=
  ZMod.castHom hN (ZMod 2) (∑ k, (ZMod.finEquiv N) (x k))

/-- The actual dyadic-grid checkerboard bit; the modular definition includes every wrap edge. -/
def gridParity (d N : ℕ) [NeZero N] (hN : 2 ∣ N)
    (x : Fin d → Fin N) : Bool := decide (gridParityResidue d N hN x = 1)

/-- Every canonical periodic unit shift increases the checkerboard residue by one, including at the boundary. -/
theorem gridParityResidue_unit_shift (d N : ℕ) [NeZero N] (hN : 2 ∣ N)
    (j : Fin d) (x : Fin d → Fin N) :
    gridParityResidue d N hN (periodicUnitShift d N j x) = gridParityResidue d N hN x + 1 := by
  unfold gridParityResidue
  simp_rw [periodic_unit_shift_coordinates]
  rw [Finset.sum_add_distrib, map_add]
  have hs : (∑ k : Fin d, if k = j then (1 : ZMod N) else 0) = 1 := by simp
  rw [hs, map_one]

/-- The residue-to-bit map turns addition by one into the actual Boolean parity flip. -/
theorem zmod_two_parity_flip (q : ZMod 2) : decide (q+1=1) = !(decide (q=1)) := by
  fin_cases q <;> decide

/-- The generic full-loss null construction applies to the actual canonical periodic grid without a supplied routing or parity-flip certificate. -/
theorem gridParity_unit_shift (d N : ℕ) [NeZero N] (hN : 2 ∣ N)
    (j : Fin d) (x : Fin d → Fin N) :
    gridParity d N hN (periodicUnitShift d N j x) = !(gridParity d N hN x) := by
  unfold gridParity
  rw [gridParityResidue_unit_shift]
  exact zmod_two_parity_flip _

/-- Every actual fourth-root phase has unit physical norm square. -/
theorem fourthPhase_normSq (k : Fin 4) : Complex.normSq (fourthPhase k) = 1 := by
  fin_cases k <;> norm_num [fourthPhase, pow_succ, Complex.I_mul_I, Complex.normSq_apply]

/-- The periodic input family has zero complete original loss for every hidden phase assignment, with the actual canonical shifts and physical mesh width. -/
theorem phased_periodic_full_original_loss_zero (d N : ℕ) [NeZero N] (hN : 2 ∣ N)
    (basis : Bool → Bool → ℂ)
    (hb : ∀ b, Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.overlap
      (basis b) (basis (!b)) = 0) (ω : (Fin d → Fin N) → Fin 4) (lam : ℝ) :
    spinorDiscreteLoss
      (real0 (checkerboardSpinor (gridParity d N hN) (fun x => fourthPhase (ω x)) basis))
      (imag0 (checkerboardSpinor (gridParity d N hN) (fun x => fourthPhase (ω x)) basis))
      (real1 (checkerboardSpinor (gridParity d N hN) (fun x => fourthPhase (ω x)) basis))
      (imag1 (checkerboardSpinor (gridParity d N hN) (fun x => fourthPhase (ω x)) basis))
      (fun _ _ => 0) (periodicUnitShift d N) (2*Real.pi/N) 1 lam = 0 := by
  exact checkerboard_full_original_loss_zero (gridParity d N hN)
    (fun x => fourthPhase (ω x)) basis (periodicUnitShift d N)
    (fun x => fourthPhase_normSq (ω x)) hb (gridParity_unit_shift d N hN) _ lam

/-- The same actual periodic hidden-phase inputs satisfy the source's pointwise normalization contract. -/
theorem phased_periodic_source_normalization (d N : ℕ) [NeZero N] (hN : 2 ∣ N)
    (basis : Bool → Bool → ℂ)
    (hb : ∀ b, Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.qubitMass (basis b) = 1)
    (ω : (Fin d → Fin N) → Fin 4) (x : Fin d → Fin N) :
    real0 (checkerboardSpinor (gridParity d N hN) (fun x => fourthPhase (ω x)) basis) x^2 +
      imag0 (checkerboardSpinor (gridParity d N hN) (fun x => fourthPhase (ω x)) basis) x^2 +
        real1 (checkerboardSpinor (gridParity d N hN) (fun x => fourthPhase (ω x)) basis) x^2 +
          imag1 (checkerboardSpinor (gridParity d N hN) (fun x => fourthPhase (ω x)) basis) x^2 = 1 := by
  exact checkerboard_source_normalization (gridParity d N hN) (fun x => fourthPhase (ω x))
    basis (fun x => fourthPhase_normSq (ω x)) hb x

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
