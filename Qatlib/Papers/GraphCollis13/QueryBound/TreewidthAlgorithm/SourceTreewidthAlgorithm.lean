/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphCollis13.QueryBound.Model.GraphCollisionModel
import Qatlib.Papers.GraphCollis13.TreeDecomp.SourceTreewidthDecomposition
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 1 — treewidth algorithm for graph collision

Fixed arXiv:1305.1021v1, §2, Theorem 1, page 2:

"Graph collision on graph `G` on `n` vertices can be solved with a bounded error
quantum algorithm with `O(√n · t^{1/6})` queries where `t` is the treewidth of
the graph."

Source proof route: preprocess the smooth tree decomposition into the
`⌈(2n−2t−1)/t⌉` vertex subsets of Lemma 1 (each of size at most `2t+1`); run
Grover search over the subsets, using a graph-collision subroutine on each
`(2t+1)`-vertex induced subgraph with `O((2t+1)^{2/3})` queries.  The total is
`O(√(n/t) · t^{2/3}) = O(√n · t^{1/6})`.

The query-count arithmetic is proved below.  The construction of the composed
Grover-plus-subroutine circuit in the fixed-space model is the residual gap.
The final statement is recorded as a `Prop`-valued definition; its proof is not
formalised.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GraphCollis13.QueryBound.TreewidthAlgorithm

open scoped BigOperators
open Qatlib.Papers.GraphCollis13.QueryBound.Model
open Qatlib.Papers.GraphCollis13.TreeDecomp.TreewidthDecomposition

/-- The number of vertex subsets produced by Lemma 1, `⌈(2n−2t−1)/t⌉`. -/
def treewidthBlocks (n t : ℕ) : ℕ :=
  Nat.ceil (((2 * (n : ℝ)) - 2 * (t : ℝ) - 1) / (t : ℝ))

/-- Query cost of the `(2t+1)`-vertex subroutine used by the paper, `(2t+1)^{2/3}`
rounded up.  The paper instantiates the subroutine with Belovs' `O(m^{2/3})`
graph-collision algorithm. -/
def treewidthSubroutineQueries (t : ℕ) : ℕ :=
  Nat.ceil (((2 * (t : ℝ) + 1) : ℝ) ^ ((2 : ℝ) / 3))

/-- The composed query budget: `⌈√m⌉` Grover iterations, each invoking the
`(2t+1)`-vertex subroutine. -/
def treewidthQueryBudget (n t : ℕ) : ℕ :=
  Nat.ceil (Real.sqrt (treewidthBlocks n t)) * treewidthSubroutineQueries t

/-- The Labelled graph underlying an undirected adjacency matrix.  `adj` is the
known graph parameter; the queried input is only the vertex labelling. -/
def adjGraph {n : ℕ} (adj : Fin n → Fin n → Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => adj u v = true

/-- Under the paper's hypotheses (`0 < t < n`) the block count is positive. -/
theorem treewidthBlocks_pos (n t : ℕ) (ht : 0 < t) (htn : t < n) :
    0 < treewidthBlocks n t := by
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hnR : (t : ℝ) < (n : ℝ) := by exact_mod_cast htn
  have hsucc : (t : ℝ) + 1 ≤ (n : ℝ) := by
    have : t + 1 ≤ n := htn
    exact_mod_cast this
  have hx : 0 < ((2 * (n : ℝ)) - 2 * (t : ℝ) - 1) / (t : ℝ) := by
    apply div_pos _ htR
    nlinarith
  have h1 : 1 ≤ treewidthBlocks n t := Nat.one_le_ceil_iff.mpr hx
  omega

/-- `⌈(2n−2t−1)/t⌉ ≤ 3n/t` for `0 < t < n`. -/
theorem treewidthBlocks_le (n t : ℕ) (ht : 0 < t) (htn : t < n) :
    (treewidthBlocks n t : ℝ) ≤ 3 * (n : ℝ) / (t : ℝ) := by
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hnR : (t : ℝ) < (n : ℝ) := by exact_mod_cast htn
  have hsucc : (t : ℝ) + 1 ≤ (n : ℝ) := by
    have : t + 1 ≤ n := htn
    exact_mod_cast this
  have hx : 0 ≤ ((2 * (n : ℝ)) - 2 * (t : ℝ) - 1) / (t : ℝ) := by
    apply div_nonneg _ htR.le
    nlinarith
  have hceil := Nat.ceil_lt_add_one hx
  have h1 : (treewidthBlocks n t : ℝ) ≤
      ((2 * (n : ℝ)) - 2 * (t : ℝ) - 1) / (t : ℝ) + 1 := hceil.le
  have hrewrite : ((2 * (n : ℝ)) - 2 * (t : ℝ) - 1) / (t : ℝ) + 1 =
      ((2 * (n : ℝ)) - (t : ℝ) - 1) / (t : ℝ) := by
    field_simp
    ring
  rw [hrewrite] at h1
  refine h1.trans ?_
  apply div_le_div_of_nonneg_right _ htR.le
  nlinarith

/-- `√⌈(2n−2t−1)/t⌉ ≤ 2√n/√t` for `0 < t < n`. -/
theorem sqrt_treewidthBlocks_le (n t : ℕ) (ht : 0 < t) (htn : t < n) :
    Real.sqrt (treewidthBlocks n t) ≤ 2 * Real.sqrt (n : ℝ) / Real.sqrt (t : ℝ) := by
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le ht (Nat.le_of_lt htn)
  have hb := treewidthBlocks_le n t ht htn
  have hb0 : (0 : ℝ) ≤ (treewidthBlocks n t : ℝ) := Nat.cast_nonneg _
  have hsqrt : Real.sqrt (treewidthBlocks n t) ≤ Real.sqrt (3 * (n : ℝ) / (t : ℝ)) :=
    Real.sqrt_le_sqrt hb
  have hsq3 : Real.sqrt (3 : ℝ) ≤ 2 := by
    have h3 : (0 : ℝ) ≤ 3 := by norm_num
    nlinarith [Real.sq_sqrt h3, Real.sqrt_nonneg (3 : ℝ)]
  have hsplit : Real.sqrt (3 * (n : ℝ) / (t : ℝ)) =
      Real.sqrt 3 * (Real.sqrt (n : ℝ) / Real.sqrt (t : ℝ)) := by
    rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 3 * (n : ℝ)),
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
    ring
  rw [hsplit] at hsqrt
  have hratio : 0 ≤ Real.sqrt (n : ℝ) / Real.sqrt (t : ℝ) := by positivity
  calc Real.sqrt (treewidthBlocks n t)
      ≤ Real.sqrt 3 * (Real.sqrt (n : ℝ) / Real.sqrt (t : ℝ)) := hsqrt
    _ ≤ 2 * (Real.sqrt (n : ℝ) / Real.sqrt (t : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hsq3 hratio
    _ = 2 * Real.sqrt (n : ℝ) / Real.sqrt (t : ℝ) := by ring

/-- `⌈(2t+1)^{2/3}⌉ ≤ 6 t^{2/3}` for `0 < t`. -/
theorem subroutineQueries_le (t : ℕ) (ht : 0 < t) :
    (treewidthSubroutineQueries t : ℝ) ≤ 6 * (t : ℝ) ^ ((2 : ℝ) / 3) := by
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  set a : ℝ := ((2 * (t : ℝ) + 1) : ℝ) ^ ((2 : ℝ) / 3) with ha
  have hbase1 : (1 : ℝ) ≤ 2 * (t : ℝ) + 1 := by nlinarith
  have ha1 : 1 ≤ a := by
    rw [ha]
    exact Real.one_le_rpow hbase1 (by norm_num)
  have ha0 : 0 ≤ a := le_trans zero_le_one ha1
  have hceil := Nat.ceil_lt_add_one ha0
  have h1 : (treewidthSubroutineQueries t : ℝ) ≤ a + 1 := hceil.le
  have h2 : a + 1 ≤ 2 * a := by linarith
  have h3 : a ≤ 3 * (t : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [ha]
    have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    have hb : 2 * (t : ℝ) + 1 ≤ 3 * (t : ℝ) := by nlinarith
    have hmono : (2 * (t : ℝ) + 1) ^ ((2 : ℝ) / 3) ≤
        (3 * (t : ℝ)) ^ ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow (by positivity) hb (by norm_num)
    have hmul : (3 * (t : ℝ)) ^ ((2 : ℝ) / 3) =
        3 ^ ((2 : ℝ) / 3) * (t : ℝ) ^ ((2 : ℝ) / 3) :=
      Real.mul_rpow (by norm_num) htR.le
    have h3le : (3 : ℝ) ^ ((2 : ℝ) / 3) ≤ (3 : ℝ) := by
      simpa using
        (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
          (by norm_num : (2:ℝ)/3 ≤ (1:ℝ)))
    rw [hmul] at hmono
    calc (2 * (t : ℝ) + 1) ^ ((2 : ℝ) / 3)
        ≤ (3 : ℝ) ^ ((2 : ℝ) / 3) * (t : ℝ) ^ ((2 : ℝ) / 3) := hmono
      _ ≤ (3 : ℝ) * (t : ℝ) ^ ((2 : ℝ) / 3) := by
          exact mul_le_mul_of_nonneg_right h3le (Real.rpow_nonneg htR.le _)
  calc (treewidthSubroutineQueries t : ℝ) ≤ a + 1 := h1
    _ ≤ 2 * a := h2
    _ ≤ 2 * (3 * (t : ℝ) ^ ((2 : ℝ) / 3)) := by linarith
    _ = 6 * (t : ℝ) ^ ((2 : ℝ) / 3) := by ring

/-- The paper's total query count `⌈√m⌉·⌈(2t+1)^{2/3}⌉` is at most
`24 √n · t^{1/6}` for `0 < t < n`. -/
theorem treewidthQueryBudget_le (n t : ℕ) (ht : 0 < t) (htn : t < n) :
    (treewidthQueryBudget n t : ℝ) ≤ 24 * Real.sqrt (n : ℝ) * (t : ℝ) ^ ((1 : ℝ) / 6) := by
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le ht (Nat.le_of_lt htn)
  have hmpos := treewidthBlocks_pos n t ht htn
  have hsqrt1 : 1 ≤ Real.sqrt (treewidthBlocks n t) := by
    have : (1 : ℝ) ≤ (treewidthBlocks n t : ℝ) := by exact_mod_cast hmpos
    calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
      _ ≤ Real.sqrt (treewidthBlocks n t) := Real.sqrt_le_sqrt this
  have hsq0 : 0 ≤ Real.sqrt (treewidthBlocks n t) := Real.sqrt_nonneg _
  have hcsqrt : (Nat.ceil (Real.sqrt (treewidthBlocks n t)) : ℝ) ≤
      2 * Real.sqrt (treewidthBlocks n t) := by
    have hceil := Nat.ceil_lt_add_one hsq0
    have hle : (Nat.ceil (Real.sqrt (treewidthBlocks n t)) : ℝ) ≤
        Real.sqrt (treewidthBlocks n t) + 1 := hceil.le
    linarith
  have hcsub := subroutineQueries_le t ht
  have hcsqrt0 : 0 ≤ (Nat.ceil (Real.sqrt (treewidthBlocks n t)) : ℝ) := Nat.cast_nonneg _
  have hbudget_eq : (treewidthQueryBudget n t : ℝ) =
      (Nat.ceil (Real.sqrt (treewidthBlocks n t)) : ℝ) *
        (treewidthSubroutineQueries t : ℝ) := by
    rw [treewidthQueryBudget, Nat.cast_mul]
  have hstep : (treewidthQueryBudget n t : ℝ) ≤
      (2 * Real.sqrt (treewidthBlocks n t)) * (6 * (t : ℝ) ^ ((2 : ℝ) / 3)) := by
    rw [hbudget_eq]
    exact mul_le_mul hcsqrt hcsub (Nat.cast_nonneg _) (by positivity)
  have hsqrtb := sqrt_treewidthBlocks_le n t ht htn
  have hratio0 : 0 ≤ (t : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg htR.le _
  have hstep2 : (2 * Real.sqrt (treewidthBlocks n t)) * (6 * (t : ℝ) ^ ((2 : ℝ) / 3)) ≤
      (2 * (2 * Real.sqrt (n : ℝ) / Real.sqrt (t : ℝ))) *
        (6 * (t : ℝ) ^ ((2 : ℝ) / 3)) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hsqrtb (by norm_num)
  have hpow : ((t : ℝ) ^ ((2 : ℝ) / 3)) / Real.sqrt (t : ℝ) = (t : ℝ) ^ ((1 : ℝ) / 6) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub htR]
    norm_num
  have hfinal : (2 * (2 * Real.sqrt (n : ℝ) / Real.sqrt (t : ℝ))) *
      (6 * (t : ℝ) ^ ((2 : ℝ) / 3)) =
      24 * Real.sqrt (n : ℝ) * (t : ℝ) ^ ((1 : ℝ) / 6) := by
    have hs : Real.sqrt (t : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr htR)
    have hmid : (2 * (2 * Real.sqrt (n : ℝ) / Real.sqrt (t : ℝ))) *
        (6 * (t : ℝ) ^ ((2 : ℝ) / 3)) =
        24 * Real.sqrt (n : ℝ) * (((t : ℝ) ^ ((2 : ℝ) / 3)) / Real.sqrt (t : ℝ)) := by
      field_simp
      ring
    rw [hmid, hpow]
  calc (treewidthQueryBudget n t : ℝ)
      ≤ (2 * Real.sqrt (treewidthBlocks n t)) * (6 * (t : ℝ) ^ ((2 : ℝ) / 3)) := hstep
    _ ≤ (2 * (2 * Real.sqrt (n : ℝ) / Real.sqrt (t : ℝ))) *
          (6 * (t : ℝ) ^ ((2 : ℝ) / 3)) := hstep2
    _ = 24 * Real.sqrt (n : ℝ) * (t : ℝ) ^ ((1 : ℝ) / 6) := hfinal

/-- **Theorem 1 (arXiv:1305.1021v1, page 2).**  For an undirected graph `G` on `n`
vertices with treewidth at most `t` (`0 < t < n`), graph collision admits a
bounded-error quantum algorithm using `O(√n · t^{1/6})` queries; the explicit
budget `treewidthQueryBudget n t` satisfies `≤ 24 √n · t^{1/6}`.

Proof route: Lemma 1 gives `⌈(2n−2t−1)/t⌉` subsets of size `≤ 2t+1` covering all
edges.  Grover search over subsets calls a `(2t+1)`-vertex collision subroutine
`√m` times, each at cost `(2t+1)^{2/3}`.

Formal gap: the composed circuit is not constructed in the fixed-space model.
The needed components exist in the library as separate query upper bounds
(`BitOracleOn` and the Grover/amplitude-amplification templates under
`Concepts.AmplitudeCore`), but no theorem composes a Grover search over an
externally supplied subroutine family with counted queries at this level.
Candidate follow-up: instantiate `Concepts.QueryComplexity.DegreeMethod.QueryAlgorithm`
with the standard Grover iterate and the Belovs subroutine, proving
`QueryCount C ≤ treewidthQueryBudget n t` and the `1/3` success bound by
amplification.  The arithmetic part is fully proved as
`treewidthQueryBudget_le`. -/
def theorem1_treewidth_algorithm (n t : ℕ) (ht : 0 < t) (htn : t < n)
    (adj : Fin n → Fin n → Bool) (hsymm : ∀ u v : Fin n, adj u v = adj v u)
    (htw : HasTreewidthAtMost (adjGraph adj) t) : Prop :=
    ∃ q : ℕ, GraphCollisionQueryUpperBound adj q ∧
      (q : ℝ) ≤ 24 * Real.sqrt (n : ℝ) * (t : ℝ) ^ ((1 : ℝ) / 6)

end Qatlib.Papers.GraphCollis13.QueryBound.TreewidthAlgorithm
