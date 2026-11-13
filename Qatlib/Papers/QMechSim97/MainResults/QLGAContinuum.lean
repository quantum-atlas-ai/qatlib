/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMechSim97.MainResults.OneDimContinuum
import Mathlib.Tactic

/-!
# Lattice gas potential and mass identities

Proves algebraic identities supporting the quantum lattice gas model of [BoghosianTaylor1998].
Occupation counts are invariant under index permutations, the one-dimensional phase-based mass
matches `particleMass1D`, and the external and pair potential matrices satisfy the unitary
matrix identity.

## Main statements

* `pairPotential_unitary`: The pair potential matrix has conjugate transpose times itself equal
  to the identity.
* `potential_and_mass_fragments`: Collects the one-dimensional mass identity and the unitary
  matrix identities for the external and pair potentials [BoghosianTaylor1998].

## References

* [Boghosian and Taylor, 1998][BoghosianTaylor1998]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QMechSim97.MainResults.QLGAContinuum

open Qatlib.Papers.QMechSim97.MainResults.Defs
open Qatlib.Papers.QMechSim97.MainResults.OneDimContinuum

/-- Reindexing a finite Boolean occupation configuration by an equivalence preserves its
occupation count. -/
theorem occupationCount_perm {ι : Type*} [Fintype ι] (occ : ι → Bool) (σ : ι ≃ ι) :
    occupationCount (fun i => occ (σ i)) = occupationCount occ :=
  Fintype.card_congr (Equiv.subtypeEquivOfSubtype (p := fun i => occ i = true) σ)

/-- For nonzero `a` and `b`, the one-dimensional mass obtained from phases `a + b` and `a - b`
equals `particleMass1D a b`. -/
theorem massFromPhases_oneDim (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    massFromPhases 1 (a + b) (a - b) = particleMass1D a b := by
  have h2b : (2 : ℂ) * b ≠ 0 := mul_ne_zero (by norm_num) hb
  have hμν : a + b - (a - b) = 2 * b := by ring
  unfold massFromPhases particleMass1D
  rw [hμν, div_one]
  have hR : (a - b) / (2 * b) + 1 / 2 = a / (2 * b) := by
    field_simp [h2b]
    ring
  rw [hR]
  have hD : (2 : ℂ) * (a / (2 * b)) = a / b := by
    field_simp [h2b, hb]
  rw [hD]
  field_simp [ha, hb]

/-- The external potential matrix has conjugate transpose times itself equal to the identity. -/
theorem externalPotential_unitary (θ : ℝ) :
    Matrix.conjTranspose (externalPotential θ) * externalPotential θ = 1 := by
  unfold externalPotential
  apply diagonal_phase_unitary
  have hphase := normSq_exp_pure_imaginary (-θ)
  simp only [Complex.ofReal_neg, neg_mul] at hphase
  intro i
  fin_cases i <;> simp [hphase, Complex.normSq_one]

/-- The pair potential matrix has conjugate transpose times itself equal to the identity. -/
theorem pairPotential_unitary (θ : ℝ) :
    Matrix.conjTranspose (pairPotential θ) * pairPotential θ = 1 := by
  unfold pairPotential
  apply diagonal_phase_unitary
  have hphase := normSq_exp_pure_imaginary (-θ)
  simp only [Complex.ofReal_neg, neg_mul] at hphase
  intro i
  fin_cases i <;> simp [hphase, Complex.normSq_one]

/-- Collects the one-dimensional mass identity and the unitary matrix identities for the
external and pair potentials [BoghosianTaylor1998]. -/
theorem potential_and_mass_fragments
    (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (θ : ℝ) :
    massFromPhases 1 (a + b) (a - b) = particleMass1D a b ∧
    Matrix.conjTranspose (externalPotential θ) * externalPotential θ = 1 ∧
    Matrix.conjTranspose (pairPotential θ) * pairPotential θ = 1 :=
  ⟨massFromPhases_oneDim a b ha hb, externalPotential_unitary θ, pairPotential_unitary θ⟩

end Qatlib.Papers.QMechSim97.MainResults.QLGAContinuum
