/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.TensorRegisters.SwapReadout

/-!
# Three-flag SWAP readout and overlap recovery

The unitary `readout` lifts a SWAP readout circuit to three success flags. On the all-true flag
branch, the difference of the two ancilla Born weights recovers the squared overlap times the
preparation weight; the module also substitutes the three sine preparation factors. See
[SchererEtAl2017] for the paper context.

## Main statements

* `readout_unitary`: The flag-lifted SWAP readout matrix is unitary.
* `actual_good_born_difference`: The false-ancilla weight minus the true-ancilla weight on the
  good branch equals `normSq a` times the squared overlap of `x` and `R`.
* `actual_source_overlap_eq`: If the product of squared preparation sines is nonzero, dividing
  the good-branch weight difference by that product recovers the squared overlap of `R` and `x`.

## References

* [Scherer et al., 2017][SchererEtAl2017]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace Qatlib.Papers.QLSAScatter15.SwapReadout
open Qatlib.Foundations.TensorRegisters

/-- The register of three Boolean preparation flags. -/
abbrev Flags := Bool × (Bool × Bool)

/-- The SWAP readout circuit lifted to act with the three preparation flags. -/
def readout {I : Type*} [Fintype I] [DecidableEq I] :
    Matrix (Flags × (Bool × (I × I))) (Flags × (Bool × (I × I))) ℂ :=
  SwapReadout.flagLift SwapReadout.circuit

/-- The flag-lifted SWAP readout matrix is unitary. See [SchererEtAl2017]. -/
theorem readout_unitary {I : Type*} [Fintype I] [DecidableEq I] :
    readout (I:=I) ∈ Matrix.unitaryGroup (Flags × (Bool × (I × I))) ℂ :=
  SwapReadout.flagLift_unitary _ SwapReadout.circuit_unitary

/-- A state with false SWAP ancilla, amplitude `a` times the product of `x` and `R` on the
all-true flag branch, and the supplied junk amplitudes on other flag branches. -/
def prepared {I : Type*} (a : ℂ) (x R : I→ℂ) (junk : Flags→I×I→ℂ)
    (z : Flags × (Bool × (I × I))) : ℂ :=
  if z.2.1 then 0 else
    if z.1=(true,(true,true)) then a*(x z.2.2.1*R z.2.2.2) else junk z.1 z.2.2

/-- Restricting `prepared` to the all-true flag branch gives `a` times the SWAP readout input
for `x` and `R`. -/
theorem prepared_good {I : Type*} (a : ℂ) (x R : I→ℂ) (junk : Flags→I×I→ℂ) :
    (fun z => prepared a x R junk ((true,(true,true)),z)) = a • SwapReadout.input x R := by
  funext z
  rcases z with ⟨b,i,j⟩
  cases b <;> simp [prepared,SwapReadout.input]

/-- The output amplitude on the all-true flag branch equals the SWAP circuit amplitude on the
scaled good input. See [SchererEtAl2017]. -/
theorem readout_good_amplitude {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℂ) (x R : I→ℂ) (junk : Flags→I×I→ℂ) (b : Bool) (i j : I) :
    (readout *ᵥ prepared a x R junk) ((true,(true,true)),(b,(i,j))) =
      (SwapReadout.circuit *ᵥ (a • SwapReadout.input x R)) (b,(i,j)) := by
  rw [readout,SwapReadout.flagLift_apply,prepared_good]

/-- The sum of squared output amplitudes for all-true preparation flags and the specified SWAP
ancilla value. -/
def P111 {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℂ) (x R : I→ℂ) (junk : Flags→I×I→ℂ) (b : Bool) : ℝ :=
  ∑ i, ∑ j, Complex.normSq ((readout *ᵥ prepared a x R junk) ((true,(true,true)),(b,(i,j))))

/-- The all-true flag output weight equals the scaled SWAP readout weight, independently of the
junk amplitudes. -/
theorem P111_eq_scaledWeight {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℂ) (x R : I→ℂ) (junk : Flags→I×I→ℂ) (b : Bool) :
    P111 a x R junk b = SwapReadout.scaledWeight a x R b := by
  simp only [P111,SwapReadout.scaledWeight,readout_good_amplitude]

/-- The false-ancilla weight minus the true-ancilla weight on the good branch equals `normSq a`
times the squared overlap of `x` and `R`. See [SchererEtAl2017]. -/
theorem actual_good_born_difference {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℂ) (x R : I→ℂ) (junk : Flags→I×I→ℂ) :
    P111 a x R junk false - P111 a x R junk true =
      Complex.normSq a * Complex.normSq (star x ⬝ᵥ R) := by
  rw [P111_eq_scaledWeight,P111_eq_scaledWeight,SwapReadout.actual_scaled_born_overlap]

/-- For preparation amplitude equal to the product of three sines, the good-branch weight
difference is the product of their squares times the squared overlap. See [SchererEtAl2017]. -/
theorem actual_source_born_difference {I : Type*} [Fintype I] [DecidableEq I]
    (phib phix phir : ℝ) (x R : I→ℂ) (junk : Flags→I×I→ℂ) :
    let a : ℂ := (Real.sin phib * Real.sin phix * Real.sin phir : ℝ)
    P111 a x R junk false - P111 a x R junk true =
      (Real.sin phib ^ 2 * Real.sin phix ^ 2 * Real.sin phir ^ 2) *
        Complex.normSq (star x ⬝ᵥ R) := by
  dsimp
  rw [actual_good_born_difference]
  simp only [Complex.normSq_ofReal]
  ring

/-- If the product of squared preparation sines is nonzero, dividing the good-branch weight
difference by that product recovers the squared overlap of `R` and `x`. See
[SchererEtAl2017]. -/
theorem actual_source_overlap_eq {I : Type*} [Fintype I] [DecidableEq I]
    (phib phix phir : ℝ) (x R : I→ℂ) (junk : Flags→I×I→ℂ)
    (hden : Real.sin phib ^ 2 * Real.sin phix ^ 2 * Real.sin phir ^ 2 ≠ 0) :
    let a : ℂ := (Real.sin phib * Real.sin phix * Real.sin phir : ℝ)
    Complex.normSq (star R ⬝ᵥ x) =
      (P111 a x R junk false - P111 a x R junk true) /
        (Real.sin phib ^ 2 * Real.sin phix ^ 2 * Real.sin phir ^ 2) := by
  dsimp
  rw [actual_source_born_difference]
  rw [SwapReadout.overlap_symm R x]
  exact (mul_div_cancel_left₀ _ hden).symm
end Qatlib.Papers.QLSAScatter15.SwapReadout
