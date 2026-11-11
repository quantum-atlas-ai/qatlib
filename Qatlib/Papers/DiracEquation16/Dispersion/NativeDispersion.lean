/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.CliffordWalk.TwoAxis
import Qatlib.Papers.DiracEquation16.SpinGates.Spin
import Qatlib.Papers.DiracEquation16.Dispersion.ScalarPhase

/-!
# Zero modes of the half-CFL Dirac walk

`halfCflMatrix` is the two-axis walk formed from `alphaY4` and `alphaZ4` at half-CFL phases. The
module proves unitarity and characterizes its nonzero fixed vectors in the first Brillouin zone:
such a vector exists exactly at zero momentum.

This development follows [FillionGourdeauMacLeanLaflamme2017].

## Main statements

* `halfCflMatrix_unitary`: the two-axis matrix is unitary.
* `halfbox_zero_mode_iff`: a nonzero fixed vector exists exactly when both momenta vanish.

## References

* [Fillion-Gourdeau et al., 2017][FillionGourdeauMacLeanLaflamme2017]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Qatlib.Papers.DiracEquation16.Dispersion
open Qatlib.Foundations.MatrixAlgebra.CliffordWalk
open Qatlib.Papers.DiracEquation16.Dispersion
open Qatlib.Papers.DiracEquation16.SpinGates Qatlib.Papers.DiracEquation16.SpinGates.FourD

/-- The two-axis Dirac walk matrix with generators `alphaY4` and `alphaZ4` at half-CFL
dispersion phases. -/
def halfCflMatrix (ℓ py pz : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  walk alphaY4 alphaZ4 (dispersionPhase (1 / 2) ℓ py) (dispersionPhase (1 / 2) ℓ pz)

/-- The half-CFL two-axis walk matrix is unitary. -/
theorem halfCflMatrix_unitary (ℓ py pz : ℝ) :
    halfCflMatrix ℓ py pz ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
  walk_unitary _ _ alphaY4_hermitian alphaZ4_hermitian _ _

/-- For positive lattice spacing and momentum in the first Brillouin zone, the half-CFL phase
lies in `[-π / 2, π / 2]`. -/
theorem half_phase_bounds (ℓ p : ℝ) (hℓ : 0 < ℓ) (hp : firstBZ ℓ p) :
    dispersionPhase (1 / 2) ℓ p ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have hl : -Real.pi < p * ℓ :=
    (div_lt_iff₀ hℓ).mp (by simpa only [neg_div] using hp.1)
  have hu : p * ℓ ≤ Real.pi := (le_div_iff₀ hℓ).mp hp.2
  unfold dispersionPhase
  constructor <;> nlinarith

/-- A nonzero fixed vector of the half-CFL walk in the first Brillouin zone forces both momenta
to vanish. -/
theorem halfbox_no_zero_2d (ℓ py pz : ℝ) (hℓ : 0 < ℓ)
    (hy : firstBZ ℓ py) (hz : firstBZ ℓ pz) (v : Fin 4 → ℂ) (hv : v ≠ 0)
    (hzero : halfCflMatrix ℓ py pz *ᵥ v = v) : py = 0 ∧ pz = 0 := by
  have h := angles_zero_of_fixed alphaY4 alphaZ4 alphaY4_hermitian alphaZ4_hermitian
    alphaY4_sq alphaZ4_sq alphaY4_alphaZ4_anticomm _ _
    (half_phase_bounds ℓ py hℓ hy) (half_phase_bounds ℓ pz hℓ hz) v hv hzero
  have hn : (1 / 2 : ℝ) * ℓ ≠ 0 := by positivity
  exact ⟨(mul_eq_zero.mp h.1).resolve_left hn, (mul_eq_zero.mp h.2).resolve_left hn⟩

/-- For positive lattice spacing and momenta in the first Brillouin zone, a nonzero fixed vector
of the half-CFL walk exists exactly when both momenta vanish. See
[FillionGourdeauMacLeanLaflamme2017]. -/
theorem halfbox_zero_mode_iff (ℓ py pz : ℝ) (hℓ : 0 < ℓ)
    (hy : firstBZ ℓ py) (hz : firstBZ ℓ pz) :
    (∃ v : Fin 4 → ℂ, v ≠ 0 ∧ halfCflMatrix ℓ py pz *ᵥ v = v) ↔ py = 0 ∧ pz = 0 := by
  constructor
  · rintro ⟨v, hv, he⟩
    exact halfbox_no_zero_2d ℓ py pz hℓ hy hz v hv he
  · rintro ⟨rfl, rfl⟩
    refine ⟨Pi.single 0 1, ?_, ?_⟩
    · intro h
      have hc := congrFun h 0
      simp at hc
    · simp [halfCflMatrix, walk, Qatlib.Foundations.MatrixAlgebra.CliffordWalk.rotation, dispersionPhase,
        Matrix.col]
      ext i
      fin_cases i <;> rfl
