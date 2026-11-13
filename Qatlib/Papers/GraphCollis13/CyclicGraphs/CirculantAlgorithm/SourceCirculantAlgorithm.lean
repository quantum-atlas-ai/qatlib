/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphCollis13.CyclicGraphs.ChunkCollision.SourceChunkCollision
import Qatlib.Papers.GraphCollis13.QueryBound.TreewidthAlgorithm.SourceTreewidthAlgorithm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 5 — linear-query algorithm for `CI(n,a,b)`

Fixed arXiv:1305.1021v1, §4.1, page 7:

`Q(COL(CI(n,a,b))) = O(√n)`.

Source route: split the `n` vertices of the circulant graph into consecutive
chunks of size `D = b − a` (there are `⌈n/D⌉` chunks), solve each chunk with the
subroutine `SUB` at cost `O(√D)` (`SUB` is MIN twice plus a Grover search over
the `3D`-vertex window of Proposition 1), and run Grover search over the chunks.
The total is `O(√(n/D) · √D) = O(√n)`.

Scope note: the query-count arithmetic is proved below; the composed algorithm
(Grover over `SUB`-instances) is outside the scope of this file, as for
Theorem 1.  The final statement is a `Prop`-valued definition whose proof is
not formalised.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GraphCollis13.CyclicGraphs.CirculantAlgorithm

open Qatlib.Papers.GraphCollis13.QueryBound.Model
open Qatlib.Papers.GraphCollis13.QueryBound.TreewidthAlgorithm
open Qatlib.Papers.GraphCollis13.CyclicGraphs.ChunkCollision

/-- Number of chunks, `⌈n/D⌉`, for chunk size `D = b − a`. -/
def chunkCount (n D : ℕ) : ℕ := Nat.ceil ((n : ℝ) / (D : ℝ))

/-- The composed query budget: `⌈√(chunkCount)⌉` Grover iterations, each using the
`O(√D)` subroutine `SUB`. -/
def circulantQueryBudget (n D : ℕ) : ℕ :=
  Nat.ceil (Real.sqrt (chunkCount n D)) * Nat.ceil (Real.sqrt (D : ℝ))

/-- `⌈√m⌉ ≤ 2√m` for `1 ≤ m`. -/
theorem ceil_sqrt_le_two (m : ℕ) (hm : 1 ≤ m) :
    (Nat.ceil (Real.sqrt (m : ℝ)) : ℝ) ≤ 2 * Real.sqrt (m : ℝ) := by
  have h0 : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h2 : (1 : ℝ) ≤ Real.sqrt (m : ℝ) := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt h1
  have hceil := Nat.ceil_lt_add_one h0
  linarith [hceil.le]

/-- The number of chunks is at least one. -/
theorem one_le_chunkCount (n D : ℕ) (hn : 0 < n) (hD : 0 < D) : 1 ≤ chunkCount n D := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  apply Nat.one_le_ceil_iff.mpr
  positivity

/-- `√2 ≤ 2`. -/
theorem sqrt_two_le_two : Real.sqrt 2 ≤ (2 : ℝ) := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]

/-- The paper's total query count `⌈√⌈n/D⌉⌉·⌈√D⌉` is at most `8√n` when
`1 ≤ D ≤ n`. -/
theorem circulantQueryBudget_le (n D : ℕ) (hD1 : 1 ≤ D) (hDn : D ≤ n) :
    (circulantQueryBudget n D : ℝ) ≤ 8 * Real.sqrt (n : ℝ) := by
  have hn0 : 0 < n := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le Nat.zero_lt_one hD1) hDn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hDR : (0 : ℝ) < (D : ℝ) := by
    have : 0 < D := Nat.lt_of_lt_of_le Nat.zero_lt_one hD1
    exact_mod_cast this
  have hm1 : 1 ≤ chunkCount n D := one_le_chunkCount n D hn0 (by omega)
  have hcm := ceil_sqrt_le_two (chunkCount n D) hm1
  have hcD := ceil_sqrt_le_two D hD1
  -- chunkCount * D ≤ 2n
  have hmD : (chunkCount n D : ℝ) * (D : ℝ) ≤ 2 * (n : ℝ) := by
    have hx0 : (0 : ℝ) ≤ (n : ℝ) / (D : ℝ) := by positivity
    have hceil := Nat.ceil_lt_add_one hx0
    have hmle : (chunkCount n D : ℝ) ≤ (n : ℝ) / (D : ℝ) + 1 := hceil.le
    have hmul := mul_le_mul_of_nonneg_right hmle hDR.le
    have hsimp : ((n : ℝ) / (D : ℝ) + 1) * (D : ℝ) = (n : ℝ) + (D : ℝ) := by
      field_simp
    rw [hsimp] at hmul
    have hDle : (D : ℝ) ≤ (n : ℝ) := by exact_mod_cast hDn
    linarith
  have hstep : (circulantQueryBudget n D : ℝ) ≤
      4 * Real.sqrt ((chunkCount n D : ℝ) * (D : ℝ)) := by
    have hprod : (Nat.ceil (Real.sqrt (chunkCount n D)) : ℝ) *
        (Nat.ceil (Real.sqrt (D : ℝ)) : ℝ) ≤
        (2 * Real.sqrt (chunkCount n D)) * (2 * Real.sqrt (D : ℝ)) :=
      mul_le_mul hcm hcD (Nat.cast_nonneg _) (by positivity)
    have hsq : Real.sqrt ((chunkCount n D : ℝ) * (D : ℝ)) =
        Real.sqrt (chunkCount n D) * Real.sqrt (D : ℝ) :=
      Real.sqrt_mul (by positivity) _
    calc (circulantQueryBudget n D : ℝ) =
        (Nat.ceil (Real.sqrt (chunkCount n D)) : ℝ) *
          (Nat.ceil (Real.sqrt (D : ℝ)) : ℝ) := by
          rw [circulantQueryBudget, Nat.cast_mul]
      _ ≤ (2 * Real.sqrt (chunkCount n D)) * (2 * Real.sqrt (D : ℝ)) := hprod
      _ = 4 * Real.sqrt ((chunkCount n D : ℝ) * (D : ℝ)) := by
          rw [hsq]; ring
  have hsqrt_le : Real.sqrt ((chunkCount n D : ℝ) * (D : ℝ)) ≤ 2 * Real.sqrt (n : ℝ) := by
    have h1 : Real.sqrt ((chunkCount n D : ℝ) * (D : ℝ)) ≤ Real.sqrt (2 * (n : ℝ)) :=
      Real.sqrt_le_sqrt hmD
    have h2 : Real.sqrt (2 * (n : ℝ)) = Real.sqrt 2 * Real.sqrt (n : ℝ) :=
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) _
    rw [h2] at h1
    calc Real.sqrt ((chunkCount n D : ℝ) * (D : ℝ))
        ≤ Real.sqrt 2 * Real.sqrt (n : ℝ) := h1
      _ ≤ 2 * Real.sqrt (n : ℝ) :=
          mul_le_mul_of_nonneg_right sqrt_two_le_two (Real.sqrt_nonneg _)
  linarith

/-- **Theorem 5 (arXiv:1305.1021v1, page 7).**  For `0 < a < b ≤ n/2`, graph
collision on `CI(n,a,b)` admits a bounded-error quantum algorithm with
`O(√n)` queries; the explicit budget `circulantQueryBudget n (b − a)` satisfies
`≤ 8√n`.

Proof route: `⌈n/(b−a)⌉` chunks, `SUB` on each at cost `O(√(b−a))` (MIN twice,
then Grover over the window of Proposition 1), Grover over the chunks.

Scope note: the arithmetic bound is proved as `circulantQueryBudget_le`.
The composed algorithm in the fixed-space model is outside the scope of this
file.  Its `SUB` routine combines two MIN calls with Grover search; the
chunk-level search also requires the corrected Proposition 1 reduction of
`ChunkCollision` and a query bound for MIN, followed by Grover composition as
in Theorem 1. -/
def theorem5_circulant_algorithm (n a b : ℕ) (hn : 0 < n) (ha : 0 < a) (hab : a < b)
    (hb : b ≤ n / 2) (adj : Fin n → Fin n → Bool) (hCI : adjGraph adj = CI n a b) : Prop :=
  ∃ q : ℕ, GraphCollisionQueryUpperBound adj q ∧
    (q : ℝ) ≤ 8 * Real.sqrt (n : ℝ)

end Qatlib.Papers.GraphCollis13.CyclicGraphs.CirculantAlgorithm
