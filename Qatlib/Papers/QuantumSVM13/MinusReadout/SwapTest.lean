/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Papers.QuantumSVM13.MinusReadout

/-!
# Classification by swap test (QuantumSVM13, claim c004)

Source: P. Rebentrost, M. Mohseni, S. Lloyd, "Quantum support vector machine for
big data classification", arXiv:1307.0471v3 (10 Jul 2014), p. 3 left column:
construct the ancilla state `|ψ⟩ = (1/√2)(|0⟩|ũ⟩ + |1⟩|x̃⟩)` and measure the
ancilla in `|φ⟩ = (1/√2)(|0⟩ − |1⟩)`; the success probability is

`P = |⟨ψ|φ⟩|² = (1/2)(1 - ⟨ũ|x̃⟩)`,

`P` is obtained to accuracy `ε` by iterating `O(P(1-P)/ε²)` times, and
`P < 1/2` classifies the query as `+1`, otherwise `−1`.

Expanding `⟨φ|ψ⟩ = (1/2)(⟨ũ| - ⟨x̃|)` gives the ancilla-branch amplitude
`(ũ_i - x̃_i)/2` on each basis vector `i`, so for real-amplitude states
`P = (1/4)‖ũ - x̃‖²`. This file proves the probability identity, the
classification rule, the Bernoulli variance bound, and the repetition budget.
The concrete Eq. (8)/(9) preparations and actual ancilla circuit are not implemented here.
This is real-amplitude branch algebra, not a physical SWAP-test or confidence theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open scoped BigOperators

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.QuantumSVM13.MinusReadout

open Qatlib.Papers.QuantumSVM13.MinusReadout


variable {n : ℕ}

/-! ## Frozen Qubit bridge

The scalar `minusBranchWeight` is the mass of an (in general unnormalised)
real-amplitude branch.  The definitions below embed that branch into Frozen's
`QState` carrier and identify its mass with the corresponding finite Born-rule
sum.  No circuit or state-preparation claim is made by this bridge.
-/

/-- Embed a finite real amplitude vector into Frozen's complex `QState` carrier. -/
noncomputable def realQState (v : Fin n → ℝ) : QState (Fin n) :=
  fun i => (v i : ℂ)

/-- Born probability of a real amplitude is its ordinary real square. -/
theorem bornProb_realQState (v : Fin n → ℝ) (i : Fin n) :
    BornProb (realQState v) i = (v i) ^ 2 := by
  simp [BornProb, realQState, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- A real amplitude vector is Frozen-normalized exactly when its real squares sum to one. -/
theorem normalized_realQState_iff (v : Fin n → ℝ) :
    Normalized (realQState v) ↔ (∑ i, (v i) ^ 2) = 1 := by
  unfold Normalized
  simp_rw [show ∀ i : Fin n, ‖realQState v i‖ ^ 2 = (v i) ^ 2 by
    intro i
    simp [realQState, Complex.norm_real, Real.norm_eq_abs, sq_abs]]

/-- The real amplitudes of the minus branch, viewed as a Frozen `QState`. -/
noncomputable def minusBranchState (ψ φ : Fin n → ℝ) : QState (Fin n) :=
  realQState (fun i => (ψ i - φ i) / 2)

/-- The Frozen Born probability of a minus-branch coordinate is its real branch square. -/
theorem bornProb_minusBranchState (ψ φ : Fin n → ℝ) (i : Fin n) :
    BornProb (minusBranchState ψ φ) i = ((ψ i - φ i) / 2) ^ 2 := by
  exact bornProb_realQState (fun i => (ψ i - φ i) / 2) i

/-- The scalar minus-branch weight is the sum of its finite Frozen Born probabilities. -/
theorem minusBranchWeight_eq_bornProb_sum (ψ φ : Fin n → ℝ) :
    minusBranchWeight ψ φ = ∑ i, BornProb (minusBranchState ψ φ) i := by
  unfold minusBranchWeight
  apply Eq.symm
  apply Finset.sum_congr rfl
  intro i hi
  exact bornProb_minusBranchState ψ φ i

/-- The scalar minus-branch weight is the Frozen event probability of all coordinates. -/
theorem minusBranchWeight_eq_measureProb_univ (ψ φ : Fin n → ℝ) :
    minusBranchWeight ψ φ = MeasureProb (minusBranchState ψ φ) Finset.univ := by
  simpa [MeasureProb] using minusBranchWeight_eq_bornProb_sum ψ φ

/-- The minus branch is Frozen-normalized exactly when its scalar weight is one. -/
theorem normalized_minusBranchState_iff (ψ φ : Fin n → ℝ) :
    Normalized (minusBranchState ψ φ) ↔ minusBranchWeight ψ φ = 1 := by
  change Normalized (realQState (fun i => (ψ i - φ i) / 2)) ↔ minusBranchWeight ψ φ = 1
  rw [normalized_realQState_iff]
  rfl

/-! ## A concrete finite real-amplitude consumer -/

/-- The two computational basis states used by the finite consumer below. -/
def classicalZero2 : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0

/-- The second computational basis state used by the finite consumer below. -/
def classicalOne2 : Fin 2 → ℝ := fun i => if i = 1 then 1 else 0

/-- The concrete zero state is unit norm. -/
theorem classicalZero2_norm : (∑ i, (classicalZero2 i) ^ 2) = 1 := by
  simp [classicalZero2, Fin.sum_univ_two]

/-- The concrete one state is unit norm. -/
theorem classicalOne2_norm : (∑ i, (classicalOne2 i) ^ 2) = 1 := by
  simp [classicalOne2, Fin.sum_univ_two]

/-- The finite consumer instantiates the minus branch at two orthogonal basis
states: the scalar branch probability is exactly `1/2`. -/
theorem classical_basis_minusBranchWeight :
    minusBranchWeight classicalZero2 classicalOne2 = (1 / 2 : ℝ) := by
  rw [minusBranchWeight_formula classicalZero2 classicalOne2
    classicalZero2_norm classicalOne2_norm]
  simp [overlap, classicalZero2, classicalOne2, Fin.sum_univ_two]

end Qatlib.Papers.QuantumSVM13.MinusReadout
