/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HadamardAnn19.NativeReduction.Actual

/-!
# Checks on Reported Hadamard Formulas

This module gives explicit consistency checks for formulas reported in [SuksmonoMinato2019].
`abstract_count_mismatch` compares the printed abstract count with the actual carrier at order
four, while `printed_spin_map_failure`, `printed_spin_ancilla_failure`, and `printed22_mismatch`
exhibit failures of the printed transformations or coefficients.

The penalty example `badFive` has energy −8 at coefficient 5 for two rows. Since every valid
configuration has nonnegative paper energy, `bare_threshold_counterexample` proves that a
coefficient merely exceeding the squared row count can still have an invalid ground
configuration.

## Main statements

* `abstract_count_mismatch` and `rectangular_count` compute concrete variable counts.
* `corrected_transform` verifies the inverse of the corrected affine spin map.
* `printed22_mismatch` detects the changed coupling coefficient in the reported scalar
  expression.
* `badFive_energy`, `valid_paper_nonneg`, and `bare_threshold_counterexample` establish the
  penalty counterexample.

## References

* [Suksmono and Minato, 2019][SuksmonoMinato2019]
-/

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Papers.HadamardAnn19.ReportedModels
open Qatlib.Foundations.BooleanEnergy.HadamardGram
open Qatlib.Foundations.BooleanEnergy.PenaltyExact
open Qatlib.Papers.HadamardAnn19.NativeReduction.Actual
open Qatlib.Papers.HadamardAnn19.MainResults.EnergyChain

/-- The rational polynomial `(M³ + M² − M) / 2` printed as the logical variable count in the
abstract of [SuksmonoMinato2019]. -/
def abstractCount (M : ℕ) : ℚ := ((M:ℚ)^3+(M:ℚ)^2-(M:ℚ))/2

/-- At order four, the printed abstract formula gives 38, whereas the actual variable carrier
has 40 elements. -/
theorem abstract_count_mismatch : abstractCount 4 = 38 ∧ Fintype.card (Variable 4 4) = 40 := by
  constructor
  · norm_num [abstractCount]
  · exact card_variable 4 4

/-- The native carrier has 24 variables for four rows and three columns, and 72 variables for
twelve rows and three columns. -/
theorem rectangular_count : Fintype.card (Variable 4 3) = 24 ∧
    Fintype.card (Variable 12 3) = 72 := ⟨card_variable 4 3,card_variable 12 3⟩

/-- The printed map `s = (1 - q) / 2` sends `q = 1` to zero, which is neither −1 nor 1, exposing
its domain inconsistency in [SuksmonoMinato2019]. -/
theorem printed_spin_map_failure : (1-(1:ℝ))/2 = 0 ∧
    ¬((1-(1:ℝ))/2 = -1 ∨ (1-(1:ℝ))/2 = 1) := by norm_num

/-- The affine map `s = 1 - 2 * q` followed by `q = (1 - s) / 2` returns every real coordinate
`q`. -/
theorem corrected_transform (q : ℝ) : (1-(1-2*q))/2 = q := by ring

/-- The Boolean AND of two true bits does not map to the product of their spins, giving a
concrete failure of the direct spin-product ancillary relation. -/
theorem printed_spin_ancilla_failure : spin (true && true) ≠ spin true*spin true := by
  norm_num [spin,bit]

/-- The scalar expression obtained from `e2S` by lowering the `s0 * s2` coefficient from four to
two, matching the coefficient change in the printed Eq. 22 of [SuksmonoMinato2019]. -/
def reported22 (s0 s1 s2 s3 s4 s5 : ℝ) : ℝ :=
  e2S s0 s1 s2 s3 s4 s5 - 2*s0*s2

/-- The reported scalar expression differs from `e2S` when all six spin coordinates equal one. -/
theorem printed22_mismatch : reported22 1 1 1 1 1 1 ≠ e2S 1 1 1 1 1 1 := by
  norm_num [reported22,e2S]

/-- The two-by-two configuration represented by six bits with precisely indices zero, two, and
five set to true, used for the coefficient-five counterexample. -/
def badFive : Configuration 2 2 := fromSix (fun i => decide (i.val=0 ∨ i.val=2 ∨ i.val=5))

/-- The configuration `badFive` has paper energy −8 at penalty coefficient five. -/
theorem badFive_energy : paperEnergy 5 badFive = -8 := by
  unfold paperEnergy
  rw [pairs_two_univ,Finset.sum_singleton]
  unfold paperPair
  rw [pairs_two_univ,Finset.sum_singleton]
  norm_num [badFive,pairPenalty,Fin.sum_univ_two,pair01,left,right,main,ancilla,
    fromSix,rowLinear,andPenalty,bit]

/-- Every configuration satisfying the AND ancillary constraints has nonnegative paper energy
for any real penalty coefficient. -/
theorem valid_paper_nonneg {M N : ℕ} (δ : ℝ) (x : Configuration M N) (h : Valid x) :
    0 ≤ paperEnergy δ x := by
  rw [paperEnergy_eq_squareEnergy,squareEnergy_valid _ x h]
  exact energy_nonneg _

/-- Although five exceeds the squared row count four, the two-by-two paper energy at coefficient
five has an invalid ground configuration. -/
theorem bare_threshold_counterexample : (4:ℝ)<5 ∧
    ∃ x : Configuration 2 2, IsGround (paperEnergy 5) x ∧ ¬Valid x := by
  refine ⟨by norm_num,?_⟩
  obtain ⟨x,hx⟩ := exists_ground (paperEnergy (M:=2) (N:=2) 5)
  refine ⟨x,hx,?_⟩
  intro hv
  have hn := valid_paper_nonneg 5 x hv
  have hb := hx badFive
  rw [badFive_energy] at hb
  linarith

end Qatlib.Papers.HadamardAnn19.ReportedModels
