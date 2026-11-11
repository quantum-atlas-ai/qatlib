/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# SupervisedML13.MainResults — shared vocabulary

Lloyd, Mohseni, Rebentrost, "Quantum algorithms for supervised and unsupervised
machine learning", fixed arXiv:1307.0411v2 (4 November 2013).

This module fixes the objects that the paper's main results are stated over:

* the supervised cluster-assignment data (M sample vectors of dimension N, a
  post-processed vector `u`, the sample mean and the squared distance to it);
* the normalization `Z = |u|^2 + (1/M) Σ_j |v_j|^2` of the swap-test
  construction of Section "Supervised cluster assignment" (p. 3);
* the operation-count vocabulary of the assignment (p. 3–4), Lloyd (p. 4),
  adiabatic-clustering (p. 4–5), nonlinear-metric (p. 6) and database-privacy
  (p. 2, p. 6) discussions;
* the weak-measurement perturbation budget of the supplementary material
  (p. 11).

Costs are real-valued *fingerprints* of the paper's own accounting: each is
written as the product of the subroutine counts that the paper multiplies
together (Grover/quantum-counting iterations, state preparations, per-vector
tests), so that the asymptotic identities `O(ε⁻¹ log(MN))`, `O(M log(MN))`,
`O(ε⁻¹ k log kMN)` and `O(ε⁻¹ q log N)` become exact algebraic identities in
`Real.logb` (see the per-claim modules).  No runtime claim is smuggled in:
the only content proved below is the logarithmic algebra, e.g.
`logb 2 (M*N) = logb 2 M + logb 2 N`.

Boundary: this is the paper's *model*, not a compiled circuit semantics; the
qRAM, swap-test and adiabatic primitives are taken as the paper grants them.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SupervisedML13.MainResults

/-! ## §1 Supervised assignment data (paper p. 3) -/

/-- Squared Euclidean norm `Σ_i x_i^2` of a real vector `x : Fin N → ℝ`. -/
def normSq {N : ℕ} (x : Fin N → ℝ) : ℝ := ∑ i, x i ^ 2

/-- The squared norm is nonnegative. -/
theorem normSq_nonneg {N : ℕ} (x : Fin N → ℝ) : 0 ≤ normSq x := by
  unfold normSq
  positivity

/-- Euclidean norm `|x| = sqrt (Σ_i x_i^2)`. -/
def vecNorm {N : ℕ} (x : Fin N → ℝ) : ℝ := Real.sqrt (normSq x)

/-- The mean `(1/M) Σ_j v_j` of `M` sample vectors in `ℝ^N` (paper p. 3). -/
def meanVector {M N : ℕ} (v : Fin M → Fin N → ℝ) : Fin N → ℝ :=
  fun i => (1 / (M : ℝ)) * ∑ j, v j i

/-- The desired distance `|u − (1/M) Σ_j v_j|^2` of the supervised assignment
task (paper p. 3). -/
def distanceToMeanSq {M N : ℕ} (u : Fin N → ℝ) (v : Fin M → Fin N → ℝ) : ℝ :=
  normSq (fun i => u i - meanVector v i)

/-- The normalization `Z = |u|^2 + (1/M) Σ_j |v_j|^2` of the projected ancilla
state `|φ⟩` (paper p. 4, display after eq. (1)). -/
def swapNormalizer {M N : ℕ} (u : Fin N → ℝ) (v : Fin M → Fin N → ℝ) : ℝ :=
  normSq u + (1 / (M : ℝ)) * ∑ j, normSq (v j)

/-! ## §2 Operation-count fingerprints -/

/-- Number of quantum operations of the supervised assignment algorithm:
`O(ε⁻¹ log M)` Grover/quantum-counting iterations plus `O(log N)` qRAM state
preparation (paper p. 3–4), written with the additive constant `2` that the
two logarithmic state preparations contribute. -/
def quantumAssignmentCost (ε : ℝ) (M N : ℕ) : ℝ :=
  ε⁻¹ * (Real.logb 2 (M : ℝ) + Real.logb 2 (N : ℝ) + 2)

/-- Classical cost of one distance evaluation between `N`-dimensional vectors:
`O(N)` per candidate, for each of the `M` vectors, i.e. `O(M N)`. -/
def classicalAssignmentCost (M N : ℕ) : ℝ := (M : ℝ) * (N : ℝ)

/-- Cost of one quantum Lloyd step: every one of the `M` vectors is tested
individually for reassignment (paper p. 4), each test costing
`O(log(M N))`. -/
def lloydStepQuantumCost (M N : ℕ) : ℝ :=
  (M : ℝ) * (Real.logb 2 (M : ℝ) + Real.logb 2 (N : ℝ) + 2)

/-- Cost of one classical Lloyd step: `M` vectors, each compared with `M`
centroids in dimension `N` (paper p. 4). -/
def lloydStepClassicalCost (M N : ℕ) : ℝ := (M : ℝ) ^ 2 * (N : ℝ)

/-- Cost of the adiabatic construction of the clustering state `|χ⟩` to
accuracy `ε` (paper p. 4–5 and p. 11): `k`-fold adiabatic step with overlap
squared `O(1/k)`, i.e. `O(ε⁻¹ k log kMN)`. -/
def adiabaticClusteringCost (ε : ℝ) (k M N : ℕ) : ℝ :=
  ε⁻¹ * (k : ℝ) * (Real.logb 2 (k : ℝ) + Real.logb 2 (M : ℝ) + Real.logb 2 (N : ℝ) + 3)

/-- The same cost when the minimum adiabatic gap is `O(1)` (well-separated
clusters, paper p. 5 and p. 11): the factor `k` is absent, giving
`O(ε⁻¹ log kMN)`. -/
def adiabaticClusteringCostGapOne (ε : ℝ) (k M N : ℕ) : ℝ :=
  ε⁻¹ * (Real.logb 2 (k : ℝ) + Real.logb 2 (M : ℝ) + Real.logb 2 (N : ℝ) + 3)

/-- Cost of estimating a `q`-th order polynomial metric expectation value to
accuracy `ε` with quantum counting (paper p. 6): `O(ε⁻¹ q log N)`. -/
def nonlinearMetricCost (ε : ℝ) (q N : ℕ) : ℝ :=
  ε⁻¹ * (q : ℝ) * (Real.logb 2 (N : ℝ) + 1)

/-- Number of qRAM calls needed for one cluster assignment: the logarithmic
state preparation and distance estimation of the paper (p. 2, p. 6). -/
def assignmentDatabaseQueries (M N : ℕ) : ℝ :=
  Real.logb 2 (M : ℝ) + Real.logb 2 (N : ℝ) + 2

/-- Number of qRAM calls needed to reveal the whole `M`-by-`N` database
(paper p. 2): `O(M N)`. -/
def fullDatabaseQueries (M N : ℕ) : ℝ := (M : ℝ) * (N : ℝ)

/-! ## §3 Weak-measurement budget (supplementary material p. 11) -/

/-- Fidelity perturbation of the `d`-fold clustered state caused by one
distance evaluation, as stated on p. 11: `< d √d δ²`, where `δ` is the
accuracy of the distance evaluation. -/
def weakMeasurementFidelityLoss (d : ℝ) (δ : ℝ) : ℝ := d * Real.sqrt d * δ ^ 2

/-- Fidelity of the `d` copies of the next cluster-assignment state obtained
from the `d` copies of the previous one. -/
def nextLevelFidelity (d : ℝ) (δ : ℝ) : ℝ := 1 - weakMeasurementFidelityLoss d δ

/-- The accuracy threshold `1/d^{2/3}` of p. 11. -/
def paperAccuracyThreshold (d : ℝ) : ℝ := d ^ (-(2 : ℝ) / 3)

end Qatlib.Papers.SupervisedML13.MainResults
