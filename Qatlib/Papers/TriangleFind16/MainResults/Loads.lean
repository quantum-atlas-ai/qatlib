/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TriangleFind16.MainResults.CostModel

set_option backward.isDefEq.respectTransparency false

/-!
# Loading a set: Lemmas 3.7 and 3.8

Carette--Laurière--Magniez, fixed arXiv:1609.07786v2, Section 3.3. A *load* of a set `S` is
realised by a path learning graph querying the elements of `S` one after the other.

* `PathLoad`: a path learning graph together with the ordered list of indices it loads.
* `denseLoad_costs`: Lemma 3.7, the path reweighted to `(|S|², 1)`.
* `sparseLoad`: Lemma 3.8, the path with the paper's weights
  `3 (|z_{[k-1]}| + 1) log (|S| + 1)` when `z_k` reveals the positive value and `3 |S| log (|S| + 1)`
  otherwise.
* `sparseLoad_negCost_le`, `sparseLoad_posCost_le`: the two complexity bounds of Lemma 3.8.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.TriangleFind16.MainResults

/-- A path learning graph: `idx` is the ordered list of the indices it queries, one per step. -/
structure PathLoad (N : ℕ) where
  /-- Number of loaded indices, that is `|S|`. -/
  len : ℕ
  /-- The loaded index at every step of the path. -/
  idx : Fin len → Fin N
  /-- Every index is loaded at most once. -/
  injective : Function.Injective idx

namespace PathLoad

variable {N : ℕ} (P : PathLoad N)

/-- The number of 1-bits of `z` on the indices loaded strictly before step `k`. -/
def onesBefore (z : Fin N → Bool) (k : Fin P.len) : ℕ :=
  (Finset.univ.filter fun i : Fin P.len => i.val < k.val ∧ z (P.idx i) = true).card

/-- The number of 1-bits of `z` on the loaded set `S`. -/
def onesAll (z : Fin N → Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin P.len => z (P.idx i) = true).card

/-- The logarithmic factor `log (|S| + 1)` of Lemma 3.8. -/
def loadLog : ℝ := Real.log ((P.len : ℝ) + 1)

/-- The number of previously loaded one-bits is bounded by the total number of loaded one-bits. -/
theorem onesBefore_le_onesAll (P : PathLoad N) {z : Fin N → Bool} {k : Fin P.len} :
    P.onesBefore z k ≤ P.onesAll z := by
  refine Finset.card_le_card fun i hi => ?_
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, hi.2.2⟩

/-- A one-bit at the current step makes the previous count strictly smaller than the total. -/
theorem onesBefore_lt_onesAll (P : PathLoad N) {z : Fin N → Bool} {k : Fin P.len}
    (hk : z (P.idx k) = true) : P.onesBefore z k < P.onesAll z := by
  unfold onesBefore onesAll
  set s := Finset.univ.filter (fun i : Fin P.len => i.val < k.val ∧ z (P.idx i) = true) with hs
  set t := Finset.univ.filter (fun i : Fin P.len => z (P.idx i) = true) with ht
  have hk_not : k ∉ s := by simp [hs]
  have hsub : s ⊆ t := by
    intro i hi
    simp only [hs, ht, Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.2⟩
  calc s.card < s.card + 1 := Nat.lt_succ_self _
    _ = (insert k s).card := (Finset.card_insert_of_notMem hk_not).symm
    _ ≤ t.card := Finset.card_le_card fun i hi => by
        rcases Finset.mem_insert.mp hi with hik | hi
        · rw [hik]
          simp only [ht, Finset.mem_filter]
          exact ⟨Finset.mem_univ k, hk⟩
        · exact hsub hi

/-- The logarithmic load factor is nonnegative. -/
theorem loadLog_nonneg (P : PathLoad N) : 0 ≤ P.loadLog := by
  unfold loadLog
  apply Real.log_nonneg
  have : (0 : ℝ) ≤ (P.len : ℝ) := Nat.cast_nonneg _
  linarith

/-- The step `k` of the sparse path, with respect to the value `b` revealed at that step. -/
def sparseStep (z : Fin N → Bool) (b : Bool) (k : Fin P.len) : ℝ :=
  if z (P.idx k) = b then 3 * (P.onesBefore z k + 1) * P.loadLog else 3 * P.len * P.loadLog

/-- Lemma 3.7 (DenseLoad): the path of length `|S|`, all weights set to `|S|`, has negative
complexity `|S|²` and positive complexity `1`, independently of the input `z`. -/
def denseLoad : FlowData (Fin P.len) where
  w0 _ := P.len
  w1 _ := P.len
  p _ := 1

/-- Lemma 3.7, negative part: `c⁰(DenseLoad_S, z) = |S|²`. -/
theorem denseLoad_negCost (P : PathLoad N) : (P.denseLoad).negCost = (P.len : ℝ) ^ 2 := by
  simp only [denseLoad, FlowData.negCost, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- Lemma 3.7, positive part: `c¹(DenseLoad_S, z) = 1` for `|S| > 0`. -/
theorem denseLoad_posCost (P : PathLoad N) (hlen : 0 < P.len) : (P.denseLoad).posCost = 1 := by
  have hlenR : (P.len : ℝ) ≠ 0 := by exact_mod_cast hlen.ne'
  simp only [denseLoad, FlowData.posCost, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, one_pow]
  field_simp

/-- Lemma 3.8 (SparseLoad): the path with the paper's weights, using the value `b` at every step. -/
def sparseLoad (z : Fin N → Bool) : FlowData (Fin P.len) where
  w0 k := P.sparseStep z false k
  w1 k := P.sparseStep z true k
  p _ := 1

end PathLoad

end Qatlib.Papers.TriangleFind16.MainResults

namespace Qatlib.Papers.TriangleFind16.MainResults.Harmonic

/-- The telescoping identity used in the harmonic bound. -/
theorem log_telescope (m : ℕ) :
    ∑ i ∈ Finset.range m, (Real.log ((i : ℝ) + 2) - Real.log ((i : ℝ) + 1))
      = Real.log ((m : ℝ) + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring_nf

/-- The harmonic sum is at most `1 + log n`. This is the estimate `∑_{i=1}^{|z|} 1/i ≤ log(|z|+1) + 1`
used in the proof of Lemma 3.8. -/
theorem harmonic_le_log (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 : ℝ) / (i + 1)) ≤ 1 + Real.log n := by
  cases n with
  | zero => simp
  | succ m =>
    rw [Finset.sum_range_succ']
    have hstep : ∀ i ∈ Finset.range m,
        (1 : ℝ) / ((i : ℝ) + 2) ≤ Real.log ((i : ℝ) + 2) - Real.log ((i : ℝ) + 1) := by
      intro i _
      have hx : (0 : ℝ) < ((i : ℝ) + 2) / ((i : ℝ) + 1) := by positivity
      have h := Real.one_sub_inv_le_log_of_pos hx
      rw [Real.log_div (by positivity) (by positivity)] at h
      have hleft : 1 - (((i : ℝ) + 2) / ((i : ℝ) + 1))⁻¹ = 1 / ((i : ℝ) + 2) := by
        field_simp
        ring_nf
      rw [hleft] at h
      simpa using h
    have h1 : ∑ i ∈ Finset.range m, (1 : ℝ) / ((i : ℝ) + 2) ≤ Real.log ((m : ℝ) + 1) := by
      calc (∑ i ∈ Finset.range m, (1 : ℝ) / ((i : ℝ) + 2))
          ≤ ∑ i ∈ Finset.range m,
              (Real.log ((i : ℝ) + 2) - Real.log ((i : ℝ) + 1)) := Finset.sum_le_sum hstep
        _ = Real.log ((m : ℝ) + 1) := log_telescope m
    have hsum : ∑ k ∈ Finset.range m, (1 : ℝ) / ((k : ℝ) + 1 + 1)
        = ∑ i ∈ Finset.range m, (1 : ℝ) / ((i : ℝ) + 2) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have : (i : ℝ) + 1 + 1 = (i : ℝ) + 2 := by ring
      rw [this]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [hsum]
    have hconst : (1 : ℝ) / (((0 : ℕ) : ℝ) + 1) = 1 := by norm_num
    rw [hconst]
    linarith

end Qatlib.Papers.TriangleFind16.MainResults.Harmonic

namespace Qatlib.Papers.TriangleFind16.MainResults

namespace PathLoad

variable {N : ℕ}

/-- The set of steps of the sparse path at which the input reveals the positive value. -/
def trueSteps (P : PathLoad N) (z : Fin N → Bool) : Finset (Fin P.len) :=
  Finset.univ.filter fun k => z (P.idx k) = true

/-- The set of true load steps has cardinality equal to the loaded one-bit count. -/
theorem card_trueSteps (P : PathLoad N) (z : Fin N → Bool) :
    (P.trueSteps z).card = P.onesAll z := rfl

/-- At a revealing step the negative weight of the sparse path is the flat weight `3|S|log(|S|+1)`. -/
theorem sparseStep_false_of_true (P : PathLoad N) (z : Fin N → Bool) {k : Fin P.len}
    (hk : z (P.idx k) = true) : P.sparseStep z false k = 3 * (P.len : ℝ) * P.loadLog := by
  unfold PathLoad.sparseStep
  rw [if_neg]
  intro hc
  rw [hk] at hc
  exact Bool.noConfusion hc

/-- At a non-revealing step the negative weight of the sparse path is at most
`3(|z_S| + 1) log(|S| + 1)`. -/
theorem sparseStep_false_le (P : PathLoad N) (z : Fin N → Bool) {k : Fin P.len}
    (hk : z (P.idx k) = false) :
    P.sparseStep z false k ≤ 3 * (P.onesAll z + 1) * P.loadLog := by
  unfold PathLoad.sparseStep
  rw [if_pos hk]
  have hb : ((P.onesBefore z k : ℕ) : ℝ) ≤ (P.onesAll z : ℝ) := by
    exact_mod_cast P.onesBefore_le_onesAll
  have hL := P.loadLog_nonneg
  nlinarith [hb, hL]

/-- Lemma 3.8, negative part: the sparse load of `S` has negative complexity at most
`6 |S| (|z_S| + 1) log(|S| + 1)`. -/
theorem sparseLoad_negCost_le (P : PathLoad N) (z : Fin N → Bool) :
    (P.sparseLoad z).negCost ≤ 6 * (P.len : ℝ) * (P.onesAll z + 1) * P.loadLog := by
  have hL := P.loadLog_nonneg
  have hlen : (0 : ℝ) ≤ (P.len : ℝ) := Nat.cast_nonneg _
  have hw : (0 : ℝ) ≤ (P.onesAll z : ℝ) := Nat.cast_nonneg _
  have hsplit : (P.sparseLoad z).negCost
      = (∑ k ∈ P.trueSteps z, P.sparseStep z false k)
        + (∑ k ∈ Finset.univ.filter (fun k : Fin P.len => ¬ z (P.idx k) = true),
            P.sparseStep z false k) := by
    simp only [sparseLoad, FlowData.negCost]
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun k : Fin P.len => z (P.idx k) = true)]
    rfl
  have hA : ∑ k ∈ P.trueSteps z, P.sparseStep z false k
      = (P.onesAll z : ℝ) * (3 * (P.len : ℝ) * P.loadLog) := by
    have hstep : ∀ k ∈ P.trueSteps z, P.sparseStep z false k = 3 * (P.len : ℝ) * P.loadLog := by
      intro k hk
      exact P.sparseStep_false_of_true z (by simpa [trueSteps] using hk)
    rw [Finset.sum_congr rfl hstep, Finset.sum_const, P.card_trueSteps, nsmul_eq_mul]
  have hB : ∑ k ∈ Finset.univ.filter (fun k : Fin P.len => ¬ z (P.idx k) = true),
        P.sparseStep z false k
      ≤ (P.len : ℝ) * (3 * (P.onesAll z + 1) * P.loadLog) := by
    have hstep : ∀ k ∈ Finset.univ.filter (fun k : Fin P.len => ¬ z (P.idx k) = true),
        P.sparseStep z false k ≤ 3 * (P.onesAll z + 1) * P.loadLog := by
      intro k hk
      have hk' : z (P.idx k) = false := by
        have hk2 : ¬ z (P.idx k) = true := by simpa using hk
        cases hv : z (P.idx k)
        · rfl
        · exact absurd hv hk2
      exact P.sparseStep_false_le z hk'
    calc ∑ k ∈ Finset.univ.filter (fun k : Fin P.len => ¬ z (P.idx k) = true),
          P.sparseStep z false k
        ≤ ∑ _k ∈ Finset.univ.filter (fun k : Fin P.len => ¬ z (P.idx k) = true),
            3 * (P.onesAll z + 1) * P.loadLog := Finset.sum_le_sum hstep
      _ = ((Finset.univ.filter (fun k : Fin P.len => ¬ z (P.idx k) = true)).card : ℝ)
            * (3 * (P.onesAll z + 1) * P.loadLog) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (P.len : ℝ) * (3 * (P.onesAll z + 1) * P.loadLog) := by
          have hc : (Finset.univ.filter (fun k : Fin P.len => ¬ z (P.idx k) = true)).card
              ≤ P.len := by
            have := Finset.card_le_univ (Finset.univ.filter
              (fun k : Fin P.len => ¬ z (P.idx k) = true))
            simpa using this
          have hnonneg : (0 : ℝ) ≤ 3 * (P.onesAll z + 1) * P.loadLog := by positivity
          have : ((Finset.univ.filter (fun k : Fin P.len => ¬ z (P.idx k) = true)).card : ℝ)
              ≤ (P.len : ℝ) := by exact_mod_cast hc
          exact mul_le_mul_of_nonneg_right this hnonneg
  rw [hsplit, hA]
  have hsum : (P.onesAll z : ℝ) * (3 * (P.len : ℝ) * P.loadLog)
      + (P.len : ℝ) * (3 * (P.onesAll z + 1) * P.loadLog)
      = 3 * (P.len : ℝ) * P.loadLog * (2 * (P.onesAll z : ℝ) + 1) := by
    ring
  have hb : (2 * (P.onesAll z : ℝ) + 1) ≤ 2 * ((P.onesAll z : ℝ) + 1) := by linarith
  calc (P.onesAll z : ℝ) * (3 * (P.len : ℝ) * P.loadLog)
        + ∑ k ∈ Finset.univ.filter (fun k : Fin P.len => ¬ z (P.idx k) = true),
            P.sparseStep z false k
      ≤ (P.onesAll z : ℝ) * (3 * (P.len : ℝ) * P.loadLog)
        + (P.len : ℝ) * (3 * (P.onesAll z + 1) * P.loadLog) := by linarith [hB]
    _ = 3 * (P.len : ℝ) * P.loadLog * (2 * (P.onesAll z : ℝ) + 1) := hsum
    _ ≤ 3 * (P.len : ℝ) * P.loadLog * (2 * ((P.onesAll z : ℝ) + 1)) := by
        have h3 : (0 : ℝ) ≤ 3 * (P.len : ℝ) * P.loadLog := by positivity
        exact mul_le_mul_of_nonneg_left hb h3
    _ = 6 * (P.len : ℝ) * (P.onesAll z + 1) * P.loadLog := by ring

end PathLoad

end Qatlib.Papers.TriangleFind16.MainResults
