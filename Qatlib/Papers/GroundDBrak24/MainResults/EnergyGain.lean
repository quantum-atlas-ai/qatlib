/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Tactic

@[expose] public section


set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.GroundDBrak24.MainResults.EnergyGain

/-- `2 ^ 10` is positive, so `Fin (2 ^ 10)` has a zero (the `L = 10` chain). -/
instance : NeZero (2 ^ 10) := ⟨by norm_num⟩

/-- Energy expectation of a pure state `ψ` under a Hamiltonian `H`. -/
def energyExpectation {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (ψ : Fin d → ℂ) : ℝ :=
  (star ψ ⬝ᵥ (H *ᵥ ψ)).re

/-- The improvement factor of one DB-DOI step: the ratio of the warm-start
energy error to the post-step energy error. -/
def energyGainFactor (E0 Ew Ea : ℝ) : ℝ := (Ew - E0) / (Ea - E0)

/-- Arithmetic core: if one step shrinks the energy error `E - E_0` by
at least a factor of ten, the gain factor is at least ten. This makes the
"order of magnitude" statement precise as a ratio, independent of the numerics. -/
theorem energyGainFactor_ge_ten (E0 Ew Ea : ℝ)
    (_hEw : E0 < Ew) (hEa : E0 < Ea)
    (hstep : Ea - E0 ≤ (Ew - E0) / 10) :
    10 ≤ energyGainFactor E0 Ew Ea := by
  unfold energyGainFactor
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < Ea - E0)]
  nlinarith

/-- An identity step preserves the energy of every input vector. -/
theorem identity_step_energy {d : ℕ} (H U : Matrix (Fin d) (Fin d) ℂ)
    (v : Fin d → ℂ) :
    energyExpectation H (((1 : Matrix (Fin d) (Fin d) ℂ) * U) *ᵥ v) =
      energyExpectation H (U *ᵥ v) := by
  rw [one_mul]

/-- The identity Hamiltonian has energy one on a computational basis state. -/
theorem identity_basis_energy {d : ℕ} (i : Fin d) :
    energyExpectation (1 : Matrix (Fin d) (Fin d) ℂ) (Pi.single i 1) = 1 := by
  simp [energyExpectation, dotProduct, Pi.single_apply]

/-- The legacy numerical contract fails for the constant identity step family. -/
theorem identity_step_no_gain :
    ¬ ∃ (_r Ea : ℝ),
      energyExpectation (1 : Matrix (Fin (2 ^ 10)) (Fin (2 ^ 10)) ℂ)
        (((1 : Matrix (Fin (2 ^ 10)) (Fin (2 ^ 10)) ℂ) * 1) *ᵥ
          Pi.single (0 : Fin (2 ^ 10)) (1 : ℂ)) = Ea ∧
        0 < Ea ∧ Ea ≤ 1 / 10 := by
  rintro ⟨_r, Ea, henergy, _, hbound⟩
  have hone : Ea = 1 := by
    simpa only [one_mul, Matrix.one_mulVec, identity_basis_energy] using henergy.symm
  linarith

end Qatlib.Papers.GroundDBrak24.MainResults.EnergyGain
