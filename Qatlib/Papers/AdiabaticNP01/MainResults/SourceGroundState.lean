/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticNP01.MainResults.SourceExactCover

set_option backward.isDefEq.respectTransparency false

/-!
# AdiabaticNP01 — ground state of `H_P` and minimum-violation readout (Claim `c002`)

Source: E. Farhi, J. Goldstone, S. Gutmann, J. Lapan, A. Lundgren, D. Preda,
arXiv:quant-ph/0104129v1 (2001), §2 Eqs. (5)–(6) (p. 4) and §11 (pp. 9–10).

Claim `c002` of the paper: *"The quantum adiabatic algorithm is designed to find the
ground state of `H_P`, which corresponds to the minimum of the classical energy cost
`h`, whether the instance has satisfying assignments or not."*

The Lean model here makes that sentence precise in the diagonal `z`-basis:

* `stateEnergy I ψ` is `⟨ψ|H_P|ψ⟩ = ∑_z ψ(z)² h(z)` (real amplitudes; `H_P` is real
  diagonal, see `SourceExactCover.lean`);
* `stateEnergy_ge_minViolation`: every normalised state has energy at least the
  minimum violation count `min_z h(z)` — the ground-state energy of `H_P`;
* `stateEnergy_eq_minViolation_imp_support_minimizers`: a state whose energy equals
  the ground energy has support only on minimum-violation assignments;
* `measurement_minViolation_probability_eq_one`: consequently, measuring such a
  state (the adiabatic limit `T → ∞`, §11 p. 9) outputs a minimum-violation
  assignment with probability one;
* `satisfiable_measurement_outputs_satisfying`: when the instance has a satisfying
  assignment (`minViolation = 0`), every output is a satisfying assignment.

No `sorry`, no `admit`, no additional axioms.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticNP01.MainResults

variable {n : ℕ}

/-- The adiabatic theorem gives the ground state of `H_P` in the limit of infinite
running time (§11, p. 9).  Every normalised state has expected energy at least the
minimum classical energy `min_z h(z)`, so the ground energy equals `minViolation`. -/
theorem stateEnergy_ge_minViolation (I : ExactCoverInstance n) (ψ : Bitstring n → ℝ)
    (hψ0 : ∀ z, 0 ≤ ψ z ^ 2) (hψ1 : ∑ z, ψ z ^ 2 = 1) :
    (I.minViolation : ℝ) ≤ I.stateEnergy ψ := by
  have hm : ∀ z, (I.minViolation : ℝ) ≤ (I.violationCount z : ℝ) := fun z =>
    by exact_mod_cast minViolation_le I z
  have h1 : (I.minViolation : ℝ)
      = ∑ z, (I.minViolation : ℝ) * ψ z ^ 2 := by
    rw [← Finset.mul_sum, hψ1, mul_one]
  rw [ExactCoverInstance.stateEnergy, h1]
  apply Finset.sum_le_sum
  intro z _
  calc (I.minViolation : ℝ) * ψ z ^ 2
      ≤ (I.violationCount z : ℝ) * ψ z ^ 2 :=
        mul_le_mul_of_nonneg_right (hm z) (hψ0 z)
    _ = ψ z ^ 2 * (I.violationCount z : ℝ) := by ring

/-- If the expected energy of `ψ` equals the ground energy `minViolation I`, then
every basis vector on which `ψ` has nonzero amplitude is a minimum-violation
assignment.  This is the precise content of "the ground state of `H_P` encodes the
assignments violating the fewest clauses" (§11, p. 9–10). -/
theorem stateEnergy_eq_minViolation_imp_support_minimizers
    (I : ExactCoverInstance n) (ψ : Bitstring n → ℝ)
    (hψ0 : ∀ z, 0 ≤ ψ z ^ 2) (hψ1 : ∑ z, ψ z ^ 2 = 1)
    (hen : I.stateEnergy ψ = (I.minViolation : ℝ)) :
    ∀ z, ψ z ≠ 0 → I.IsMinViolation z := by
  have hm : ∀ z, (I.minViolation : ℝ) ≤ (I.violationCount z : ℝ) := fun z =>
    by exact_mod_cast minViolation_le I z
  -- The energy equals the ground energy; subtract the ground energy termwise.
  have hsum : (∑ z, ψ z ^ 2 * ((I.violationCount z : ℝ) - (I.minViolation : ℝ)))
      = 0 := by
    have hsplit : (∑ z, ψ z ^ 2 * ((I.violationCount z : ℝ) - (I.minViolation : ℝ)))
        = (∑ z, ψ z ^ 2 * (I.violationCount z : ℝ))
          - (I.minViolation : ℝ) * (∑ z, ψ z ^ 2) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro z _
      ring
    rw [hsplit, hψ1, mul_one]
    exact sub_eq_zero.mpr hen
  have hnonneg : ∀ z ∈ (Finset.univ : Finset (Bitstring n)),
      0 ≤ ψ z ^ 2 * ((I.violationCount z : ℝ) - (I.minViolation : ℝ)) := by
    intro z _
    exact mul_nonneg (hψ0 z) (sub_nonneg.mpr (hm z))
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
  intro z hz
  have hz2 : 0 < ψ z ^ 2 := by positivity
  have hterm := hzero z (Finset.mem_univ z)
  rcases mul_eq_zero.mp hterm with h | h
  · exact absurd h (ne_of_gt hz2)
  · unfold ExactCoverInstance.IsMinViolation
    have hcast : (I.violationCount z : ℝ) = (I.minViolation : ℝ) := by linarith
    exact_mod_cast hcast

/-- Measurement probability of the basis outcome `z` for the real amplitude vector
`ψ`: the Born weight `|ψ(z)|²` (real amplitudes, so the square). -/
def outcomeProb (ψ : Bitstring n → ℝ) (z : Bitstring n) : ℝ :=
  ψ z ^ 2

/-- A state at the ground energy gives probability zero to every assignment that is
not a minimum-violation assignment.  Hence measuring the adiabatic-limit state
produces a minimum-violation assignment with probability one (§11, p. 9). -/
theorem outcomeProb_eq_zero_of_not_isMinViolation (I : ExactCoverInstance n)
    (ψ : Bitstring n → ℝ) (hψ0 : ∀ z, 0 ≤ ψ z ^ 2) (hψ1 : ∑ z, ψ z ^ 2 = 1)
    (hen : I.stateEnergy ψ = (I.minViolation : ℝ))
    (z : Bitstring n) (hz : ¬ I.IsMinViolation z) :
    outcomeProb ψ z = 0 := by
  by_contra hprob
  apply hz
  apply stateEnergy_eq_minViolation_imp_support_minimizers I ψ hψ0 hψ1 hen z
  intro hz0
  exact hprob (by rw [outcomeProb, hz0]; ring)

/-- The measurement distribution of a ground-energy state is supported entirely on
the minimum-violation assignments; its total mass there is one.  This is the Lean
form of "a measurement produces a bit assignment that has the minimum number of
violated clauses" (§11, p. 9). -/
theorem measurement_minViolation_probability_eq_one (I : ExactCoverInstance n)
    (ψ : Bitstring n → ℝ) (hψ0 : ∀ z, 0 ≤ ψ z ^ 2) (hψ1 : ∑ z, ψ z ^ 2 = 1)
    (hen : I.stateEnergy ψ = (I.minViolation : ℝ)) :
    (∑ z ∈ (Finset.univ.filter fun z => I.IsMinViolation z), outcomeProb ψ z) = 1 := by
  rw [Finset.sum_subset (Finset.subset_univ _)]
  · simpa [outcomeProb] using hψ1
  · intro x _ hx
    have hx' : ¬ I.IsMinViolation x := by simpa using hx
    exact outcomeProb_eq_zero_of_not_isMinViolation I ψ hψ0 hψ1 hen x hx'

/-- On a satisfiable instance (`minViolation = 0`) the ground state of `H_P` puts
all measurement weight on satisfying assignments, so the algorithm solves the
original USA problem there as well (§11, p. 9). -/
theorem satisfiable_measurement_outputs_satisfying (I : ExactCoverInstance n)
    (ψ : Bitstring n → ℝ) (hψ0 : ∀ z, 0 ≤ ψ z ^ 2) (hψ1 : ∑ z, ψ z ^ 2 = 1)
    (hen : I.stateEnergy ψ = (I.minViolation : ℝ)) (hmin : I.minViolation = 0) :
    (∑ z ∈ (Finset.univ.filter fun z => ∀ C ∈ I.clauses, exactlyOneTrue z C),
        outcomeProb ψ z) = 1 := by
  rw [Finset.sum_subset (Finset.subset_univ _)]
  · simpa [outcomeProb] using hψ1
  · intro x _ hx
    have hx' : ¬ ∀ C ∈ I.clauses, exactlyOneTrue x C := by simpa using hx
    have hnotmin : ¬ I.IsMinViolation x := by
      intro hminx
      apply hx'
      have hv : I.violationCount x = I.minViolation := hminx
      exact (violationCount_eq_zero_iff I x).mp (by rw [hv, hmin])
    exact outcomeProb_eq_zero_of_not_isMinViolation I ψ hψ0 hψ1 hen x hnotmin

end Qatlib.Papers.AdiabaticNP01.MainResults
