/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.PairData
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Order

/-!
# A direct cut-and-loop bound for the triangular pair graph

The source's boundary estimate is proved directly, independently of the false
intermediate cyclic-word estimate. The explicit flow sends a pair `(a,b)` to
`(a,b-1)` with weight `N-b+1` and to `(a+1,b)` with weight `a+1`, whenever the
target is a valid pair. Its divergence is two away from adjacent pairs and
`-(N-1)` on adjacent pairs. Summing over a set cancels all internal flow. Every
remaining directed edge carries at most `N`, yielding `two_card_le` uniformly
for every `N` and every selected vertex set, including the empty cases.
-/

public section

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.KhovanovHom25.MainResults.PairFlow


/-- Vertical flow lowers the right coordinate by one. -/
def Down {N : ℕ} (v u : Pair N) : Prop :=
  left v = left u ∧ right u + 1 = right v

/-- Horizontal flow raises the left coordinate by one. -/
def Across {N : ℕ} (v u : Pair N) : Prop :=
  right v = right u ∧ left v + 1 = left u

/-- The explicit nonnegative flow has weights `N-b+1` vertically and `a+1`
horizontally. No target inequality is stored in this definition. -/
noncomputable def flow {N : ℕ} (v u : Pair N) : ℕ := by
  classical
  exact (if Down v u then N - right v + 1 else 0) +
    (if Across v u then left v + 1 else 0)

/-- Summing a constant over a predicate with at most one witness. -/
theorem sum_unique {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] (c : ℕ)
    (unique : ∀ i j, p i → p j → i = j) :
    (∑ i, if p i then c else 0) = if ∃ i, p i then c else 0 := by
  classical
  by_cases hp : ∃ i, p i
  · obtain ⟨i, hi⟩ := hp
    rw [ite_eq_left (show ∃ j, p j from ⟨i, hi⟩)]
    calc
      _ = if p i then c else 0 := by
        apply Finset.sum_eq_single i
        · intro j _hj hji
          have hn : ¬ p j := fun hj => hji (unique j i hj hi)
          simp [hn]
        · simp
      _ = c := ite_eq_left hi
  · rw [ite_eq_right hp]
    apply Finset.sum_eq_zero
    intro i _hi
    simp [show ¬ p i from fun hi => hp ⟨i, hi⟩]

/-- A vertical outgoing edge exists exactly away from the adjacent-pair diagonal. -/
theorem down_exists {N : ℕ} (v : Pair N) :
    (∃ u, Down v u) ↔ left v + 1 < right v := by
  constructor
  · rintro ⟨u, hl, hr⟩
    have := (coords u).1
    omega
  · intro hgap
    let u : Pair N := ⟨(v.val.1, ⟨right v - 1, by have := (coords v).2; omega⟩),
      by change left v < right v - 1; omega⟩
    refine ⟨u, rfl, ?_⟩
    change right v - 1 + 1 = right v
    omega

/-- A horizontal outgoing edge has the same strict-gap criterion. -/
theorem across_exists {N : ℕ} (v : Pair N) :
    (∃ u, Across v u) ↔ left v + 1 < right v := by
  constructor
  · rintro ⟨u, hr, hl⟩
    have := (coords u).1
    omega
  · intro hgap
    let u : Pair N := ⟨(⟨left v + 1, by have := coords v; omega⟩, v.val.2),
      by change left v + 1 < right v; exact hgap⟩
    exact ⟨u, rfl, rfl⟩

/-- A vertical incoming edge exists exactly below the top boundary. -/
theorem up_exists {N : ℕ} (u : Pair N) :
    (∃ v, Down v u) ↔ right u < N := by
  constructor
  · rintro ⟨v, _hl, hr⟩
    have := (coords v).2
    omega
  · intro htop
    let v : Pair N := ⟨(u.val.1, ⟨right u + 1, by omega⟩),
      by change left u < right u + 1; have := (coords u).1; omega⟩
    exact ⟨v, rfl, rfl⟩

/-- A horizontal incoming edge exists exactly to the right of the left boundary. -/
theorem back_exists {N : ℕ} (u : Pair N) :
    (∃ v, Across v u) ↔ 0 < left u := by
  constructor
  · rintro ⟨v, _hr, hl⟩
    omega
  · intro hleft
    let v : Pair N := ⟨(⟨left u - 1, by have := coords u; omega⟩, u.val.2),
      by change left u - 1 < right u; have := (coords u).1; omega⟩
    refine ⟨v, rfl, ?_⟩
    change left u - 1 + 1 = left u
    omega

/-- The total outgoing flow is given by the two explicit outgoing weights. -/
theorem outgoing {N : ℕ} (v : Pair N) :
    (∑ u, flow v u) =
      if left v + 1 < right v then N - right v + 1 + (left v + 1) else 0 := by
  classical
  unfold flow
  rw [Finset.sum_add_distrib]
  rw [sum_unique (Down v), sum_unique (Across v)]
  · simp only [down_exists, across_exists]
    split_ifs <;> omega
  · intro i j hi hj
    apply pair_ext <;> dsimp [Across] at hi hj <;> omega
  · intro i j hi hj
    apply pair_ext <;> dsimp [Down] at hi hj <;> omega

/-- Incoming vertical flow has weight `N-b`, and incoming horizontal flow has
weight `a`, including their boundary cases where these values are zero. -/
theorem incoming {N : ℕ} (u : Pair N) :
    (∑ v, flow v u) = N - right u + left u := by
  classical
  have hv (v : Pair N) :
      (if Down v u then N - right v + 1 else 0) =
        if Down v u then N - right u else 0 := by
    split_ifs with h
    · have := (coords v).2
      dsimp [Down] at h
      omega
    · rfl
  have hh (v : Pair N) :
      (if Across v u then left v + 1 else 0) =
        if Across v u then left u else 0 := by
    split_ifs with h
    · exact h.2
    · rfl
  unfold flow
  simp_rw [hv, hh]
  rw [Finset.sum_add_distrib]
  rw [sum_unique (fun v => Down v u), sum_unique (fun v => Across v u)]
  · simp only [up_exists, back_exists]
    have := (coords u).2
    split_ifs <;> omega
  · intro i j hi hj
    apply pair_ext <;> dsimp [Across] at hi hj <;> omega
  · intro i j hi hj
    apply pair_ext <;> dsimp [Down] at hi hj <;> omega

/-- The flow divergence is two off the diagonal and `-(N-1)` on it, stated
without subtraction in the natural numbers. -/
theorem divergence {N : ℕ} (v : Pair N) :
    (∑ u, flow v u) + (N + 1) * (if IsLoop v then 1 else 0) =
      (∑ u, flow u v) + 2 := by
  classical
  rw [outgoing, incoming]
  have := coords v
  unfold IsLoop
  split_ifs <;> omega

/-- Flow uses only actual nearest-neighbor edges and every edge carries at
most `N` units. -/
theorem flow_capacity {N : ℕ} (v u : Pair N) :
    flow v u ≤ if Adj v u then N else 0 := by
  classical
  have hcoords := coords v
  by_cases hd : Down v u
  · by_cases hh : Across v u
    · dsimp [Down, Across] at hd hh
      omega
    · have hadj : Adj v u := Or.inl ⟨hd.1, Or.inr hd.2⟩
      simp only [flow, hd, hh, hadj, ite_true, ite_false, add_zero]
      omega
  · by_cases hh : Across v u
    · have hadj : Adj v u := Or.inr ⟨hh.1, Or.inl hh.2⟩
      simp only [flow, hd, hh, hadj, ite_true, ite_false, zero_add]
      omega
    · simp [flow, hd, hh]

/-- The total flow leaving a selected vertex is bounded by the actual number
of incident edges to the complement. -/
theorem outside_capacity {N : ℕ} (S : Finset (Pair N)) (v : Pair N) :
    (∑ u ∈ Sᶜ, flow v u) ≤
      N * (Finset.univ.filter (fun u => u ∉ S ∧ Adj v u)).card := by
  classical
  have hf : Sᶜ.filter (Adj v) =
      Finset.univ.filter (fun u => u ∉ S ∧ Adj v u) := by
    ext u
    simp
  calc
    _ ≤ ∑ u ∈ Sᶜ, if Adj v u then N else 0 :=
      Finset.sum_le_sum fun u _hu => flow_capacity v u
    _ = ∑ _u ∈ Sᶜ.filter (Adj v), N := by rw [Finset.sum_filter]
    _ = N * (Finset.univ.filter (fun u => u ∉ S ∧ Adj v u)).card := by
      rw [hf]
      simp [Nat.mul_comm]

/-- Summing the actual divergence cancels every internal flow. The surviving
boundary flow gives a uniform cut-and-loop isoperimetric bound. -/
theorem two_card_le {N : ℕ} (S : Finset (Pair N)) :
    2 * S.card ≤ (N + 1) * loopCount S + N * cutCount S := by
  classical
  let internal := ∑ v ∈ S, ∑ u ∈ S, flow v u
  let boundary := ∑ v ∈ S, ∑ u ∈ Sᶜ, flow v u
  let totalOut := ∑ v ∈ S, ∑ u, flow v u
  let totalIn := ∑ v ∈ S, ∑ u, flow u v
  have hsplit : totalOut = internal + boundary := by
    dsimp [totalOut, internal, boundary]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _hv
    exact (Finset.sum_add_sum_compl S (flow v)).symm
  have hin : internal ≤ totalIn := by
    dsimp [internal, totalIn]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun v _hv =>
      Finset.sum_le_sum_of_subset (Finset.subset_univ S)
  have hbound : boundary ≤ N * cutCount S := by
    dsimp [boundary, cutCount]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun v _hv => outside_capacity S v
  have hd := Finset.sum_congr (s₁ := S) (s₂ := S) rfl
    (fun v (_hv : v ∈ S) => divergence v)
  have hloops : (∑ v ∈ S, if IsLoop v then 1 else 0) = loopCount S := by
    rw [← Finset.card_filter]
    rfl
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hloops,
    Finset.sum_const, nsmul_eq_mul] at hd
  change totalOut + (N + 1) * loopCount S = totalIn + S.card * 2 at hd
  omega

end Qatlib.Papers.KhovanovHom25.MainResults.PairFlow
