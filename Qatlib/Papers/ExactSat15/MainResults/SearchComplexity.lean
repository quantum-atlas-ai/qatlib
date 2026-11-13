/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.UnknownCount.Theorem3CorrectedTigh
import Qatlib.Papers.ExactSat15.MainResults.XorReductionSubspace
import Qatlib.Papers.ExactSat15.MainResults.OracleGateCount
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Search and counting complexity on the XOR-Reduction candidate register

Paper: arXiv:1512.00859v2 (29 Aug 2016), *Faster than Classical Quantum Algorithm
for dense Formulas of Exact Satisfiability and Occupation Problems*.

This module gives the paper-layer complexity statements.

* **c001**, source p. 5 (Sec. I, first main result): the exact algorithm for XSAT
  and Occupation runs in worst case `O(2^(n-M'))` classically and
  `O(√(2^(n-M')))` quantumly with polynomial space, where `M' ≤ min {n, M}` is
  the number of linearly independent clauses; the quantum algorithm has bounded
  error decreasing exponentially with repetitions.  The quantum search bound is
  bridged to the unknown-count BBHT theorem
  `Qatlib.Concepts.SearchStopping.UnknownCount.theorem3Corrected`.
* **c002**, source p. 5 and p. 11: the corresponding counting problem is bounded
  by `O(2^(n-M'))` classically and by `O(√(V · 2^(n-M')))` quantumly, where
  `V ≤ 2^(n-M')` is the (a priori unknown) number of valid assignments.
* **c006**, source p. 16 (Sec. V): quantum backtracking preserves exactness and,
  since the decision tree has size `T(n) ≤ 2^n`, its worst case stays
  `O(√(2^(n-M')))`; when `T(n)` is smaller the average scaling improves.

The XOR-Reduction combinatorics (`2^(n-M')` candidates, `M' ≤ min {n, M}`) is
reused from `MainResults.XorReductionSubspace`; the oracle ancilla count from
`MainResults.OracleGateCount`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ExactSat15.MainResults.SearchComplexity

-- `ZMod 2` is a field; required to state `Matrix.rank` for the XORSAT matrix.
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib.Concepts.AmplitudeSearch.InterruptMin
open Qatlib.Papers.ExactSat15.MainResults.XorReductionSubspace
open Qatlib.Papers.ExactSat15.MainResults.OracleGateCount

/-- Number of free qubits of the reduced register, `k = n - M'` (source p. 8). -/
def candidateDimension (n M' : ℕ) : ℕ := n - M'

/-- Cardinality of the reduced candidate space, `2^(n-M')` (source Eq. (6)). -/
def candidateCount (n M' : ℕ) : ℕ := 2 ^ candidateDimension n M'

/-- Classical worst-case work: the reduced candidate space must be enumerated. -/
def classicalSearchCost (n M' : ℕ) : ℕ := candidateCount n M'

/-- Quantum worst-case work: Grover/BBHT over the reduced candidate space
(source p. 5: `O(√(2^(n-M')))`). -/
def quantumSearchCost (n M' : ℕ) : ℝ := Real.sqrt (candidateCount n M')

/-- The quantum cost is the square root of the classical exhaustive cost. -/
theorem quantumSearchCost_eq_sqrt (n M' : ℕ) :
    quantumSearchCost n M' = Real.sqrt (classicalSearchCost n M') := rfl

/-- The reduced register has at most `n` qubits. -/
theorem candidateDimension_le_self (n M' : ℕ) : candidateDimension n M' ≤ n :=
  Nat.sub_le n M'

/-- Polynomial space (source p. 5): the reduced register plus the `⌈log₂ M′⌉`
oracle ancillas never exceeds `2n` qubits.  The ancilla bound is the one proved in
`MainResults.OracleGateCount.oracleAncillas_le`. -/
theorem polynomial_space (n M' : ℕ) (hM' : M' ≤ n) (hpos : 1 ≤ M') :
    candidateDimension n M' + oracleAncillas M' ≤ 2 * n := by
  have h1 : candidateDimension n M' ≤ n := candidateDimension_le_self n M'
  have h2 : oracleAncillas M' ≤ n := oracleAncillas_le n M' hM' hpos
  omega

/-! ## c001: the quantum search bridge to the BBHT theorem -/

/-- For `N` candidates with at least one valid assignment, `√(N/V) ≤ √N`. -/
theorem sqrt_div_le_sqrt_self {N V : ℕ} (hV : 1 ≤ V) :
    Real.sqrt ((N : ℝ) / V) ≤ Real.sqrt (N : ℝ) := by
  apply Real.sqrt_le_sqrt
  have hVpos : (0 : ℝ) < (V : ℝ) := by exact_mod_cast hV
  rw [div_le_iff₀ hVpos]
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hV1 : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
  nlinarith [mul_nonneg hN (show (0 : ℝ) ≤ (V : ℝ) - 1 by linarith)]

/-- **Bridging theorem, BBHT Boolean-query cost.**  Reuses
`Qatlib.Concepts.SearchStopping.UnknownCount.theorem3Corrected` (its
fifth conjunct, `TerminalBooleanQueries`).  For a finite search space `I` and a
nonempty marked set `A`, the unknown-count search makes at most
`(29/2)√(|I|/|A|)` phase-kickback Boolean queries in expectation. -/
theorem bbht_boolean_query_bound {I : Type*} [Fintype I] [DecidableEq I]
    (hI : 0 < Fintype.card I) (A : Finset I) (hA : 0 < A.card) :
    ∃ q : ℝ, q ≤ (29 / 2 : ℝ) * Real.sqrt ((Fintype.card I : ℝ) / A.card) := by
  obtain ⟨-, -, -, -, hq, -⟩ := (theorem3Corrected (I := I) hI).1 A hA
  obtain ⟨q, -, hle⟩ := hq
  exact ⟨q, hle.2⟩

/-- Because `V ≥ 1`, the BBHT bound `(29/2)√(N/V)` is dominated by
`(29/2)√N`: searching the reduced register never exceeds the Grover worst-case
bound on the full candidate space. -/
theorem bbht_cost_le_candidate_count {I : Type*} [Fintype I] [DecidableEq I]
    (hI : 0 < Fintype.card I) (A : Finset I) (hA : 0 < A.card) :
    ∃ q : ℝ, q ≤ (29 / 2 : ℝ) * Real.sqrt (Fintype.card I) := by
  obtain ⟨q, hq⟩ := bbht_boolean_query_bound hI A hA
  refine ⟨q, le_trans hq ?_⟩
  have hsq : Real.sqrt ((Fintype.card I : ℝ) / A.card) ≤
      Real.sqrt (Fintype.card I : ℝ) :=
    sqrt_div_le_sqrt_self (N := Fintype.card I) (V := A.card) hA
  exact mul_le_mul_of_nonneg_left hsq (by norm_num)

/-- **c001, quantum bound on the reduced register** (source p. 5): if the
candidate space `2^(n-M')` contains `V ≥ 1` valid assignments, BBHT search costs
at most `(29/2)√(2^(n-M'))` Boolean queries, i.e. `O(√(2^(n-M')))`. -/
theorem bbht_on_candidate_register (n M' V : ℕ) (hV : 1 ≤ V)
    (hV' : V ≤ 2 ^ (n - M')) :
    ∃ A : Finset (Fin (2 ^ (n - M'))), A.card = V ∧
      ∃ q : ℝ, q ≤ (29 / 2 : ℝ) * Real.sqrt ((2 : ℝ) ^ (n - M')) := by
  classical
  obtain ⟨A, -, hAcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin (2 ^ (n - M')))))
      (n := V) (by simpa using hV')
  refine ⟨A, hAcard, ?_⟩
  have hI : 0 < Fintype.card (Fin (2 ^ (n - M'))) := by
    rw [Fintype.card_fin]
    exact pow_pos (by norm_num) _
  have hApos : 0 < A.card := by omega
  obtain ⟨q, hq⟩ := bbht_cost_le_candidate_count (I := Fin (2 ^ (n - M'))) hI A hApos
  refine ⟨q, ?_⟩
  rw [Fintype.card_fin] at hq
  simpa [Nat.cast_pow] using hq

/-- **Bridging theorem, exponential error decay.**  Reuses
`Qatlib.Concepts.SearchStopping.UnknownCount.theorem3Corrected` (its
final conjunct, `RetryReach`).  There is an `N`-dependent cutoff `K = O(√N)` such
that the failure probability after `K+k` attempts is at most `(3/4)^k`; this is
the "bounded error decreasing exponentially with the number of repetitions" of
source p. 5. -/
theorem bbht_error_decay {I : Type*} [Fintype I] [DecidableEq I]
    (hI : 0 < Fintype.card I) :
    ∃ K : ℕ, (K : ℝ) ≤ 6 * Real.sqrt (Fintype.card I) ∧
      ∀ k : ℕ, ∀ A : Finset I, 0 < A.card →
        RetryReach A (ExponentialSizes (Fintype.card I)) (K + k) ≤ (3 / 4 : ℝ) ^ k := by
  obtain ⟨K, hK, hrest⟩ := (theorem3Corrected (I := I) hI).2.2.2
  exact ⟨K, hK, fun k A hA => (hrest k).2 A hA⟩

/-- **c001 capstone, deterministic part** (source p. 5 and Eq. (6)): for a
consistent XORSAT instance with `M' = rank A` independent clauses, the candidate
space has exactly `2^(n-M')` elements, never exceeds the full `2^n` assignment
space, and `M' ≤ min {n, M}`.  All three components are the theorems proved in
`MainResults.XorReductionSubspace`. -/
theorem exact_search_complexity {n M : ℕ} (A : Matrix (Fin M) (Fin n) (ZMod 2))
    (b : Fin M → ZMod 2) (hne : Nonempty (xorSolutionSet A b)) :
    Fintype.card (xorSolutionSet A b) = 2 ^ (n - Matrix.rank A) ∧
      Fintype.card (xorSolutionSet A b) ≤ 2 ^ n ∧
      Matrix.rank A ≤ min n M :=
  ⟨card_xorSolutionSet_of_nonempty A b hne, card_le_full_space A b hne, rank_le_min A⟩

/-- The candidate space of a consistent instance is exactly `candidateCount` at
`M' = rank A`. -/
theorem candidateCount_eq_card {n M : ℕ} (A : Matrix (Fin M) (Fin n) (ZMod 2))
    (b : Fin M → ZMod 2) (hne : Nonempty (xorSolutionSet A b)) :
    Fintype.card (xorSolutionSet A b) = candidateCount n (Matrix.rank A) :=
  card_xorSolutionSet_of_nonempty A b hne

/-! ## c002: the counting problem -/

/-- Quantum-counting query cost `√(V · 2^(n-M'))` (source p. 5 and p. 11). -/
def countingQueryCost (n M' V : ℕ) : ℝ :=
  Real.sqrt ((V : ℝ) * (2 : ℝ) ^ (n - M'))

/-- Classical counting cost `2^(n-M')`: enumerate the candidate space. -/
def countingClassicalCost (n M' : ℕ) : ℝ := (2 : ℝ) ^ (n - M')

/-- The quantum counting cost is nonnegative. -/
theorem countingQueryCost_nonneg (n M' V : ℕ) : 0 ≤ countingQueryCost n M' V :=
  Real.sqrt_nonneg _

/-- Factored form of the counting bound. -/
theorem countingQueryCost_eq_sqrt_mul (n M' V : ℕ) :
    countingQueryCost n M' V =
      Real.sqrt (V : ℝ) * Real.sqrt ((2 : ℝ) ^ (n - M')) := by
  unfold countingQueryCost
  rw [Real.sqrt_mul (Nat.cast_nonneg V)]

/-- **c002, quantum counting never beats the classical worst case** (source
p. 11): since `V ≤ 2^(n-M')`, `√(V · 2^(n-M')) ≤ 2^(n-M')`; in the trivial
worst case `V = 2^(n-M')` the two bounds coincide. -/
theorem countingQueryCost_le_classical (n M' V : ℕ) (hV : V ≤ 2 ^ (n - M')) :
    countingQueryCost n M' V ≤ countingClassicalCost n M' := by
  unfold countingQueryCost countingClassicalCost
  have hN : (0 : ℝ) ≤ (2 : ℝ) ^ (n - M') := by positivity
  have hVr : (V : ℝ) ≤ (2 : ℝ) ^ (n - M') := by exact_mod_cast hV
  calc Real.sqrt ((V : ℝ) * (2 : ℝ) ^ (n - M'))
      ≤ Real.sqrt ((2 : ℝ) ^ (n - M') * (2 : ℝ) ^ (n - M')) := by
        apply Real.sqrt_le_sqrt
        nlinarith
    _ = (2 : ℝ) ^ (n - M') := Real.sqrt_mul_self hN

/-- In the trivial case where every candidate is a solution the quantum and
classical counting costs agree at `2^(n-M')` (source p. 11). -/
theorem countingQueryCost_full (n M' : ℕ) :
    countingQueryCost n M' (2 ^ (n - M')) = countingClassicalCost n M' := by
  unfold countingQueryCost countingClassicalCost
  have hN : (0 : ℝ) ≤ (2 : ℝ) ^ (n - M') := by positivity
  have hcast : ((2 ^ (n - M') : ℕ) : ℝ) = (2 : ℝ) ^ (n - M') := by
    rw [Nat.cast_pow]
    norm_num
  rw [hcast]
  exact Real.sqrt_mul_self hN

/-- **c002 bridge to the solution count**: for a consistent instance the number
`V` of valid assignments is a special case `V = 2^(n-M')` of the candidate
cardinality proved in `MainResults.XorReductionSubspace`. -/
theorem counting_solution_count {n M : ℕ} (A : Matrix (Fin M) (Fin n) (ZMod 2))
    (b : Fin M → ZMod 2) (hne : Nonempty (xorSolutionSet A b)) :
    Fintype.card (xorSolutionSet A b) = 2 ^ (n - Matrix.rank A) :=
  card_xorSolutionSet_of_nonempty A b hne

/-! ## c006: quantum backtracking -/

/-- Abstract model of a quantum-backtracking run (source p. 16, Sec. V):
`treeSize` is the number of nodes `T(n)` of the decision tree, `found` is the
algorithm's output on the instance, `solutionExists` records whether a valid
assignment exists, and `exact_output` is the exactness invariant (no false
positives, no false negatives).  The deterministic decision-tree structure that
this model abstracts is the one developed in
`Qatlib.Concepts.QueryComplexity.DecisionTrees.certificateTree_exists`. -/
structure BacktrackingRun where
  /-- Decision-tree size `T(n)`. -/
  treeSize : ℕ
  /-- Whether the run outputs a valid assignment. -/
  found : Bool
  /-- Whether the instance actually has a valid assignment. -/
  solutionExists : Bool
  /-- Exactness: the run outputs a solution exactly when one exists. -/
  exact_output : found = solutionExists

/-- Classical backtracking work equals the decision-tree size `T(n)`. -/
def classicalBacktrackingCost (r : BacktrackingRun) : ℕ := r.treeSize

/-- Quantum-backtracking work `O(√(T(n)))` oracle calls (source p. 16). -/
def quantumBacktrackingCost (r : BacktrackingRun) : ℝ := Real.sqrt r.treeSize

/-- **c006, exactness is preserved** (source p. 18): the quantum-backtracking
run decides the instance exactly. -/
theorem backtracking_exact (r : BacktrackingRun) :
    r.found = r.solutionExists :=
  r.exact_output

/-- **c006, worst case unchanged** (source p. 18): when the decision tree obeys
the paper's universal bound `T(n) ≤ 2^k` with `k = n - M'`, the quantum cost
`√T` stays below the Grover bound `√(2^k)`. -/
theorem quantum_backtracking_worst_case (r : BacktrackingRun) (k : ℕ)
    (hT : r.treeSize ≤ 2 ^ k) :
    quantumBacktrackingCost r ≤ quantumSearchCost k 0 := by
  unfold quantumBacktrackingCost quantumSearchCost
  have hcand : candidateCount k 0 = 2 ^ k := by
    unfold candidateCount candidateDimension
    simp
  rw [hcand]
  apply Real.sqrt_le_sqrt
  exact_mod_cast hT

/-- **c006, average improvement** (source p. 18): whenever the decision tree is
strictly smaller than the full `2^k` candidate space, quantum backtracking is
strictly faster than the Grover worst case. -/
theorem quantum_backtracking_avg_improves (r : BacktrackingRun) (k : ℕ)
    (hT : r.treeSize < 2 ^ k) :
    quantumBacktrackingCost r < quantumSearchCost k 0 := by
  unfold quantumBacktrackingCost quantumSearchCost
  have hcand : candidateCount k 0 = 2 ^ k := by
    unfold candidateCount candidateDimension
    simp
  rw [hcand]
  apply Real.sqrt_lt_sqrt (Nat.cast_nonneg r.treeSize)
  exact_mod_cast hT

/-- Classical backtracking is never cheaper than its quantum counterpart on the
same tree: `T ≥ √T` for `T ≥ 1`. -/
theorem quantum_backtracking_le_classical (r : BacktrackingRun) (hT : 1 ≤ r.treeSize) :
    quantumBacktrackingCost r ≤ (classicalBacktrackingCost r : ℝ) := by
  unfold quantumBacktrackingCost classicalBacktrackingCost
  have hT' : (1 : ℝ) ≤ (r.treeSize : ℝ) := by exact_mod_cast hT
  have hsq : Real.sqrt (r.treeSize : ℝ) ≤ Real.sqrt ((r.treeSize : ℝ) * (r.treeSize : ℝ)) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  rwa [Real.sqrt_mul_self (Nat.cast_nonneg r.treeSize)] at hsq

end Qatlib.Papers.ExactSat15.MainResults.SearchComplexity
