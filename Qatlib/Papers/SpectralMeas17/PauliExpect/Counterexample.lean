/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Identifiability boundary for Equation (8)

This module records the exact premise missing from the final sentence following
Equation (8) of [PoulinEtAl2018], Eq. (8). If

F(E, Gamma) = 1 / 2 * (1 + (Gamma - E^2) / (1 - E^2)),

then the equation has the form walk = F(E, Gamma) * target. The displayed
identity is valid for the interior range E^2 < 1, but the target expectation
is recoverable from it only when F(E, Gamma) is nonzero. The concrete scalar
witness E = 0, Gamma = -1, target = 1, and walk = 0 satisfies the source
equation and the interior energy premise while making F = 0. It therefore
refutes the unqualified access claim without changing the scope of Equation
(8).

The values arise in the physical Pauli instance with one qubit, two
coefficients +1 and -1 on the same X word, observable Z, and input |0>.
The normalized Hamiltonian is zero, the energy is E = 0, every word
anticommutes with Z, so Gamma = -1, and the original Z expectation is 1.

The existing physical Pauli-LCU development proves Equation (8) for the
actual walk. The declarations here isolate its scalar identifiability contract
so that the zero-response boundary is kernel checked independently of any
division-by-zero convention.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpectralMeas17.PauliExpect

/-- The scalar response multiplying the static expectation in Equation (8). -/
def eq8Factor (E Gamma : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (1 + (Gamma - E ^ 2) / (1 - E ^ 2))

/-- The literal scalar content of Equation (8), with its interior energy premise. -/
def eq8Observation (E Gamma target walk : ℝ) : Prop :=
  E ^ 2 < 1 ∧ walk = eq8Factor E Gamma * target

/-- The zero-response value in the concrete boundary witness. -/
theorem eq8Factor_zero_response : eq8Factor 0 (-1) = 0 := by
  norm_num [eq8Factor]

/-- The concrete witness satisfies the source equation while retaining a nonzero
target expectation. -/
theorem eq8_zero_response_witness :
    eq8Observation 0 (-1) 1 0 ∧ (1 : ℝ) ≠ 0 / eq8Factor 0 (-1) := by
  constructor
  · constructor
    · norm_num
    · rw [eq8Factor_zero_response]
      norm_num
  · rw [eq8Factor_zero_response]
    norm_num

/-- The unguarded reconstruction sentence after Equation (8) is false. -/
theorem eq8_unqualified_access_false :
    ¬ (∀ E Gamma target walk : ℝ, eq8Observation E Gamma target walk →
      target = walk / eq8Factor E Gamma) := by
  intro h
  have hw := (eq8_zero_response_witness).2
  have hrec := h 0 (-1) 1 0 (eq8_zero_response_witness).1
  exact hw hrec

/-- Correct inversion of Equation (8) under the necessary nonzero-response
premise. -/
theorem eq8_recover_of_nonzero_factor
    (E Gamma target walk : ℝ) (hobs : eq8Observation E Gamma target walk)
    (hfactor : eq8Factor E Gamma ≠ 0) :
    target = walk / eq8Factor E Gamma := by
  rcases hobs with ⟨_, hwalk⟩
  rw [hwalk]
  field_simp [hfactor]

end Qatlib.Papers.SpectralMeas17.PauliExpect
