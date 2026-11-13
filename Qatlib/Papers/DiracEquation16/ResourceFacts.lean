/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsRefinedDefs
import Mathlib.Tactic

/-!
# Explicit Dirac simulation resource counts

This module records circuit-width, lattice-size, and tabulated gate-count models for the Dirac
simulation. It checks concrete numerical comparisons and bounds the general step model
`stepGateCountModel` above and below by quadratic expressions.

This development follows [FillionGourdeauMacLeanLaflamme2017].

## Main statements

* `circuitWidth_ten`: the width model at ten is forty-two.
* `classical_exceeds_quantum_at_ten`: the lattice point count exceeds ten thousand times the
  tabulated step count.
* `stepGateCountModel_uniformUpperBound`: a uniform quadratic bound for the general step model.

## References

* [Fillion-Gourdeau et al., 2017][FillionGourdeauMacLeanLaflamme2017]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DiracEquation16.ResourceFacts

open Qatlib.Concepts.ResourceBounds.AsymBounds (uniformUpperBound)

/-- The circuit-width model `4 * nx + 2`. -/
def circuitWidth (nx : ℕ) : ℕ := 4 * nx + 2

/-- The circuit-width model at `nx = 10` is forty-two. See [FillionGourdeauMacLeanLaflamme2017]. -/
theorem circuitWidth_ten : circuitWidth 10 = 42 := by
  unfold circuitWidth; norm_num

/-- The circuit-width model at `nx = 100` is four hundred and two. -/
theorem circuitWidth_hundred : circuitWidth 100 = 402 := by
  unfold circuitWidth; norm_num

/-- The per-axis lattice point count `2 ^ nx`. -/
def latticePointsPerAxis (nx : ℕ) : ℕ := 2 ^ nx

/-- The cubic lattice point count `(2 ^ nx) ^ 3`. -/
def totalLatticePoints (nx : ℕ) : ℕ := (2 ^ nx) ^ 3

/-- At `nx = 10`, each axis has 1024 lattice points. -/
theorem latticePointsPerAxis_ten : latticePointsPerAxis 10 = 1024 := by
  unfold latticePointsPerAxis; norm_num

/-- At `nx = 10`, the cubic lattice has 1073741824 points. -/
theorem totalLatticePoints_ten : totalLatticePoints 10 = 1073741824 := by
  unfold totalLatticePoints
  norm_num

/-- At `nx = 100`, the per-axis lattice size lies strictly between `10 ^ 30` and `2 * 10 ^ 30`. -/
theorem perAxis_scale_at_100 :
    10 ^ 30 < latticePointsPerAxis 100 ∧ latticePointsPerAxis 100 < 2 * 10 ^ 30 := by
  unfold latticePointsPerAxis
  exact ⟨by norm_num, by norm_num⟩

/-- At `nx = 100`, the cubic lattice size lies strictly between `10 ^ 90` and `10 ^ 91`. -/
theorem total_scale_at_100 :
    10 ^ 90 < totalLatticePoints 100 ∧ totalLatticePoints 100 < 10 ^ 91 := by
  unfold totalLatticePoints
  have hlo : (10 : ℕ) ^ 30 < 2 ^ 100 := by norm_num
  have hhi : (2 : ℕ) ^ 100 < 2 * 10 ^ 30 := by norm_num
  constructor
  · have h30 : ((10 : ℕ) ^ 30) ^ 3 = 10 ^ 90 := by rw [← pow_mul]
    calc (10 : ℕ) ^ 90 = ((10 ^ 30) ^ 3) := h30.symm
      _ < (2 ^ 100) ^ 3 := Nat.pow_lt_pow_left hlo (by norm_num)
  · have h30 : ((10 : ℕ) ^ 30) ^ 3 = 10 ^ 90 := by rw [← pow_mul]
    have hcube : ((2 : ℕ) ^ 100) ^ 3 < (2 * 10 ^ 30) ^ 3 :=
      Nat.pow_lt_pow_left hhi (by norm_num)
    calc ((2 : ℕ) ^ 100) ^ 3 < (2 * 10 ^ 30) ^ 3 := hcube
      _ = 8 * 10 ^ 90 := by rw [mul_pow, h30]; norm_num
      _ < 10 * 10 ^ 90 := Nat.mul_lt_mul_of_pos_right (by norm_num) (by positivity)
      _ = 10 ^ 91 := by rw [mul_comm, ← pow_succ]

/-- The tabulated mass gate count, equal to 245. -/
def massGateCount : ℕ := 245

/-- The tabulated vector-potential gate count, equal to 3330. -/
def vectorPotentialGateCount : ℕ := 3330

/-- The tabulated one-step gate count at register parameter ten, equal to 12773. -/
def oneStepGateCountAtTen : ℕ := 12773

/-- The sum of the mass and vector-potential gate counts is smaller than the tabulated one-step
count. -/
theorem localGates_lt_stepGates :
    massGateCount + vectorPotentialGateCount < oneStepGateCountAtTen := by
  unfold massGateCount vectorPotentialGateCount oneStepGateCountAtTen
  norm_num

/-- At register parameter ten, the lattice point count exceeds ten thousand times the tabulated
one-step gate count. -/
theorem classical_exceeds_quantum_at_ten :
    10 ^ 4 * oneStepGateCountAtTen < totalLatticePoints 10 := by
  unfold oneStepGateCountAtTen totalLatticePoints
  norm_num

/-- At register parameter ten, the lattice point count lies strictly between one and two
billion. -/
theorem classical_ops_at_ten :
    10 ^ 9 < totalLatticePoints 10 ∧ totalLatticePoints 10 < 2 * 10 ^ 9 := by
  unfold totalLatticePoints
  norm_num

/-- The one-dimensional width model `2 * nz - 1`, using natural-number subtraction. -/
def oneDimensionalWidth (nz : ℕ) : ℕ := 2 * nz - 1

/-- The one-dimensional lattice point count `2 ^ nz`. -/
def oneDimensionalPoints (nz : ℕ) : ℕ := 2 ^ nz

/-- At parameter two, the one-dimensional width is three and the point count is four. -/
theorem tableI_row_two :
    oneDimensionalWidth 2 = 3 ∧ oneDimensionalPoints 2 = 4 := by
  unfold oneDimensionalWidth oneDimensionalPoints; norm_num

/-- At parameter seven, the one-dimensional width is thirteen and the point count is 128. -/
theorem tableI_row_seven :
    oneDimensionalWidth 7 = 13 ∧ oneDimensionalPoints 7 = 128 := by
  unfold oneDimensionalWidth oneDimensionalPoints; norm_num

/-- The tabulated one-dimensional depths for parameters two through seven, with value zero
outside this range. -/
def oneDimensionalDepth (nz : ℕ) : ℕ :=
  match nz with
  | 2 => 60
  | 3 => 182
  | 4 => 376
  | 5 => 642
  | 6 => 980
  | 7 => 1390
  | _ => 0

/-- The tabulated one-dimensional depths strictly increase from parameter two through seven. -/
theorem oneDimensionalDepth_monotone_tabulated :
    oneDimensionalDepth 2 < oneDimensionalDepth 3 ∧
    oneDimensionalDepth 3 < oneDimensionalDepth 4 ∧
    oneDimensionalDepth 4 < oneDimensionalDepth 5 ∧
    oneDimensionalDepth 5 < oneDimensionalDepth 6 ∧
    oneDimensionalDepth 6 < oneDimensionalDepth 7 := by
  unfold oneDimensionalDepth; norm_num

/-- The tabulated Hadamard gate count, equal to seventy-two. -/
def hadamardGates : ℕ := 72
/-- The tabulated Clifford gate count, equal to ninety-two. -/
def cliffordGates : ℕ := 92
/-- The tabulated T gate count, equal to ninety-four. -/
def tGates : ℕ := 94
/-- The tabulated CNOT gate count, equal to fifty. -/
def cnotGates : ℕ := 50

/-- The four tabulated gate counts for the massive one-dimensional case sum to 308. -/
theorem massive_one_dimensional_depth :
    hadamardGates + cliffordGates + tGates + cnotGates = 308 := by
  unfold hadamardGates cliffordGates tGates cnotGates
  norm_num

/-- The step gate-count model `3 * n * n + K`. -/
def stepGateCountModel (K n : ℕ) : ℕ := 3 * n * n + K

/-- The step gate-count model is bounded above by `(K + 3) * (n + 1) ^ 2`. -/
theorem stepGateCountModel_le (K n : ℕ) :
    stepGateCountModel K n ≤ (K + 3) * (n + 1) ^ 2 := by
  unfold stepGateCountModel
  have hA : 3 * n * n ≤ (K + 3) * (n * n) := by
    have h := Nat.mul_le_mul_right (n * n) (by omega : 3 ≤ K + 3)
    simpa [mul_assoc, mul_comm, mul_left_comm] using! h
  have hB : K ≤ K + 3 := by omega
  have h1 : 3 * n * n + K ≤ (K + 3) * (n * n) + (K + 3) :=
    Nat.add_le_add hA hB
  have he : (K + 3) * (n * n) + (K + 3) = (K + 3) * (n * n + 1) := by ring
  have h2 : n * n + 1 ≤ (n + 1) ^ 2 := by
    have e : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
    rw [e]; omega
  calc 3 * n * n + K ≤ (K + 3) * (n * n) + (K + 3) := h1
    _ = (K + 3) * (n * n + 1) := he
    _ ≤ (K + 3) * (n + 1) ^ 2 := Nat.mul_le_mul_left (K + 3) h2

/-- The step gate-count model is bounded below by `3 * n * n`. -/
theorem stepGateCountModel_ge (K n : ℕ) :
    3 * n * n ≤ stepGateCountModel K n := by
  unfold stepGateCountModel
  omega

/-- For fixed `K`, the step gate-count model satisfies a uniform upper bound with coefficient `K
+ 3` and degree two. -/
theorem stepGateCountModel_uniformUpperBound (K : ℕ) :
    uniformUpperBound (fun n => stepGateCountModel K n) (K + 3) 2 := by
  intro n
  simpa [pow_two] using! stepGateCountModel_le K n

end Qatlib.Papers.DiracEquation16.ResourceFacts
