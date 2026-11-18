/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ExactSimon97.MainResults.Defs

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped BigOperators Classical

/-!
# Section 4.3 of [BrassardHoyer1997]: the total-query optimization

The source's supplementary optimization (p.7): across all exact subgroup-generation
iterations, each coordinate experiment `Q i` need only run once. A zero output
permanently excludes that coordinate from every later slice, and a nonzero output
supplies that same coordinate as a new shrinking pivot, after which the coordinate
never contributes again. Hence the complete algorithm uses `O(n)` evaluations of `ρ`,
rather than the naive `O(n²)`.

This module formalizes the optimization argument:

* `CoordProbe`/`Permanence`: the coordinate-experiment interface — the outcome of
  `Q i` in the slice with pivot bits `p` is either zero (`none`) or a nonzero output
  carrying new pivot bits — with the §4.3 permanence principle `zero_perm`: a zero
  output stays zero under every later pivot (permanently excluding the coordinate).
* `onePassFrom`/`onePassCalls`: the one-pass schedule from coordinate position `k`,
  probing each remaining coordinate exactly once; `onePassCalls_eq` shows the full
  schedule from position `0` performs exactly `n` coordinate experiments. Each experiment uses a constant number of `ρ` evaluations;
  `onePass_cost` keeps that factor explicit.
* `NaiveRun`: trace semantics of the naive per-round loop, which re-scans all
  coordinates in every round; `Qatlib.Papers.ExactSimon97.MainResults.NaiveRun.depth_le` bounds the continuing rounds by
  the number of coordinates, and `naive_probes_le` combines this with the per-round
  scan bound to give the naive `O(n²)` count.
* `onePass_agrees_naive`: under the permanence interface, the one-pass schedule and
  the naive loop compute the same final pivot bits — the optimization preserves the
  generated data.

Interface boundary: the permanence principle is the interface through which the
group-theoretic analysis of Section 4 (coset-slice structure of the coordinate
experiments, including the fact that a consumed pivot coordinate never contributes
again) enters; the abstract schedule counts experiments. A concrete query circuit must establish
the constant per-experiment oracle charge; this module does not construct it.
-/

namespace Qatlib.Papers.ExactSimon97.MainResults

section TotalQuery

variable {n : ℕ}

/-- Outcome of the coordinate experiment `Q i` in the slice whose pivot bits are `p`:
`none` is the zero output, `some v` a nonzero output carrying the new pivot bits. -/
def CoordProbe (n : ℕ) : Type := (Fin n → Bool) → Fin n → Option (Fin n → Bool)

/-- One reachable pivot update produced by a successful coordinate probe. -/
def ProbeStep (q : CoordProbe n) (p p' : Fin n → Bool) : Prop :=
  ∃ i, q p i = some p'

/-- A finite sequence of actual successful pivot updates. -/
abbrev ProbeReach (q : CoordProbe n) := Relation.ReflTransGen (ProbeStep q)

/-- Conditional permanence along reachable shrinking slices, rather than all
unrelated pivot states. The source group-theoretic model must establish this law. -/
structure Permanence (q : CoordProbe n) : Prop where
  /-- A zero output remains zero along every reachable sequence of updates. -/
  zero_perm : ∀ p p', ProbeReach q p p' → ∀ i, q p i = none → q p' i = none

/-- The one-pass schedule of §4.3 from coordinate position `k`: probe the remaining
coordinates `k, k+1, …` in order, each exactly once; a zero outcome keeps the pivot,
a nonzero outcome replaces the pivot bits. -/
def onePassFrom (q : CoordProbe n) (k : ℕ) (p : Fin n → Bool) : (Fin n → Bool) :=
  if hk : k < n then
    match q p ⟨k, hk⟩ with
    | none => onePassFrom q (k + 1) p
    | some v => onePassFrom q (k + 1) v
  else p
termination_by n - k
decreasing_by
  all_goals omega

/-- The number of coordinate experiments performed by the
one-pass schedule from position `k`: one per remaining coordinate. -/
def onePassCalls (q : CoordProbe n) (k : ℕ) (p : Fin n → Bool) : ℕ :=
  if hk : k < n then
    match q p ⟨k, hk⟩ with
    | none => onePassCalls q (k + 1) p + 1
    | some v => onePassCalls q (k + 1) v + 1
  else 0
termination_by n - k
decreasing_by
  all_goals omega

/-- The one-pass schedule from position `k` performs exactly `n - k` coordinate
experiments — one per remaining coordinate. -/
theorem onePassCalls_eq (q : CoordProbe n) : ∀ (m k : ℕ) (p : Fin n → Bool),
    n - k = m → onePassCalls q k p = n - k := by
  intro m
  induction m with
  | zero =>
      intro k p hm
      unfold onePassCalls
      split
      · next hk => omega
      · omega
  | succ m ih =>
      intro k p hm
      have hklt : k < n := by omega
      unfold onePassCalls
      split
      · next hk =>
          cases hq : q p ⟨k, hk⟩ with
          | none =>
              have hrec := ih (k + 1) p (by omega)
              show onePassCalls q (k + 1) p + 1 = n - k
              rw [hrec]
              omega
          | some v =>
              have hrec := ih (k + 1) v (by omega)
              show onePassCalls q (k + 1) v + 1 = n - k
              rw [hrec]
              omega
      · next hkge => omega

/-- The §4.3 optimization: the full one-pass schedule from position `0` performs
exactly `n` coordinate experiments, against the naive
`O(n²)` count of `naive_probes_le`. -/
theorem onePass_total (q : CoordProbe n) (p : Fin n → Bool) :
    onePassCalls q 0 p = n :=
  onePassCalls_eq q n 0 p rfl

/-- If a concrete coordinate experiment costs `c` oracle calls, the one-pass
schedule has billed cost `c * n`. The per-experiment cost bridge is external. -/
theorem onePass_cost (q : CoordProbe n) (p : Fin n → Bool) (c : ℕ) :
    c * onePassCalls q 0 p = c * n := by
  rw [onePass_total]

/-- If every remaining coordinate probes zero under `p`, the one-pass schedule keeps
the pivot bits `p`. -/
theorem onePassFrom_all_none (q : CoordProbe n) : ∀ (m k : ℕ) (p : Fin n → Bool),
    n - k = m → (∀ j : Fin n, k ≤ (j : ℕ) → q p j = none) → onePassFrom q k p = p := by
  intro m
  induction m with
  | zero =>
      intro k p hm hall
      unfold onePassFrom
      split
      · next hk => omega
      · rfl
  | succ m ih =>
      intro k p hm hall
      have hklt : k < n := by omega
      conv_lhs => unfold onePassFrom
      rw [dite_eq_left hklt]
      rw [hall ⟨k, hklt⟩ (le_refl _)]
      exact ih (k + 1) p (by omega) (fun j hj => hall j (by omega))

/-- Zero outcomes in the positions before `i` leave the pivot untouched, so the
one-pass schedule from `k ≤ i` reaches position `i` with the same pivot bits and
continues from `i + 1` with the new pivot bits carried by the nonzero outcome at
`i`. -/
theorem onePassFrom_skip_zero (q : CoordProbe n) : ∀ (m k : ℕ) (p : Fin n → Bool)
    (i : Fin n) (v : Fin n → Bool), (i : ℕ) - k = m → k ≤ (i : ℕ) →
    (∀ j : Fin n, k ≤ (j : ℕ) → (j : ℕ) < i → q p j = none) → q p i = some v →
    onePassFrom q k p = onePassFrom q ((i : ℕ) + 1) v := by
  intro m
  induction m with
  | zero =>
      intro k p i v hm hki hz hq
      have hkeq : k = (i : ℕ) := by omega
      have hkn : k + 1 = (i : ℕ) + 1 := by omega
      have hislt : (i : ℕ) < n := i.isLt
      have hk : k < n := by omega
      conv_lhs => unfold onePassFrom
      rw [dite_eq_left hk]
      have hfineq : (⟨k, hk⟩ : Fin n) = i := Fin.ext hkeq
      rw [hfineq, hq, hkn]
  | succ m ih =>
      intro k p i v hm hki hz hq
      have hklt : k < (i : ℕ) := by omega
      have hislt : (i : ℕ) < n := i.isLt
      have hkn : k < n := by omega
      conv_lhs => unfold onePassFrom
      rw [dite_eq_left hkn]
      have hkz : q p ⟨k, hkn⟩ = none := hz ⟨k, hkn⟩ (le_refl _) (by omega)
      rw [hkz]
      exact ih (k + 1) p i v (by omega) (by omega)
        (fun j hjk hjj => hz j (by omega) hjj) hq

/-- Trace semantics of the naive per-round loop of §4: in each round the coordinates
are scanned in index order — coordinates decided in earlier rounds re-probe zero —
and the round ends at the first nonzero coordinate `i`, whose output becomes the
next pivot and whose coordinate joins the decided set; the run stops when every
undecided coordinate probes zero. -/
inductive NaiveRun (q : CoordProbe n) :
    (Fin n → Bool) → Finset (Fin n) → Type where
  /-- Terminal round: no undecided coordinate produces a nonzero output. -/
  | stop (p : Fin n → Bool) (D : Finset (Fin n))
      (hall : ∀ i ∉ D, q p i = none) : NaiveRun q p D
  /-- Continuing round: the scan passes over all coordinates before `i` (fresh or
  decided) with zero outputs, and the first nonzero coordinate `i` carries new pivot
  bits `v`; the run continues from `v` with `i` decided. -/
  | step (p : Fin n → Bool) (D : Finset (Fin n)) (i : Fin n) (v : Fin n → Bool)
      (hi : i ∉ D)
      (hbefore : ∀ j : Fin n, (j : ℕ) < i → q p j = none)
      (hq : q p i = some v)
      (hrest : NaiveRun q v (insert i D)) :
    NaiveRun q p D

/-- The number of continuing rounds of a naive run. -/
def NaiveRun.depth {q : CoordProbe n} {p : Fin n → Bool} {D : Finset (Fin n)} :
    NaiveRun q p D → ℕ
  | stop _ _ _ => 0
  | step _ _ _ _ _ _ _ t => t.depth + 1

/-- The final pivot bits reached by a naive run. -/
def NaiveRun.final {q : CoordProbe n} {p : Fin n → Bool} {D : Finset (Fin n)} :
    NaiveRun q p D → (Fin n → Bool)
  | stop p _ _ => p
  | step _ _ _ _v _ _ _ t => t.final

/-- Each continuing round of the naive loop consumes a fresh coordinate, so a run
from decided set `D` performs at most `n - D.card` continuing rounds. -/
theorem NaiveRun.depth_le {q : CoordProbe n} {p : Fin n → Bool} {D : Finset (Fin n)}
    (t : NaiveRun q p D) :
    t.depth + D.card ≤ n := by
  induction t with
  | stop p D hall =>
      have hcard : D.card ≤ Fintype.card (Fin n) :=
        Finset.card_le_card (Finset.subset_univ D)
      simp only [NaiveRun.depth]
      simpa [Fintype.card_fin] using hcard
  | step p D i v hi hbefore hq t ih =>
      simp only [NaiveRun.depth]
      have hcard : (insert i D).card ≤ Fintype.card (Fin n) :=
        Finset.card_le_card (Finset.subset_univ _)
      rw [Fintype.card_fin] at hcard
      have hins : (insert i D).card = D.card + 1 := Finset.card_insert_of_notMem hi
      omega

/-- The naive loop performs at most `n + 1` rounds (each continuing round consumes
one of the `n` coordinates, and one terminal round scans without output), and each
round scans at most the `n` coordinates, so its total probe count is bounded by
`(n + 1) * n` — the naive `O(n²)` of the source, against the `n` coordinate
experiments of the one-pass schedule. -/
theorem naive_probes_le {q : CoordProbe n} {p : Fin n → Bool} {D : Finset (Fin n)}
    (t : NaiveRun q p D) :
    (t.depth + 1) * n ≤ (n + 1) * n := by
  have h1 := t.depth_le
  have hcard : D.card ≤ n := by
    have := Finset.card_le_card (Finset.subset_univ D)
    simpa [Fintype.card_fin] using this
  have h2 : t.depth ≤ n := by omega
  exact Nat.mul_le_mul_right n (by omega)

/-- Under the permanence interface, the one-pass schedule from position `k` computes
exactly the final pivot bits of the naive loop whose decided coordinates all lie
below `k` and whose undecided coordinates below `k` have probed zero before: the two
procedures collect the same nonzero pivot outputs. -/
theorem onePass_agrees_naive {q : CoordProbe n} (h : Permanence q) :
    ∀ {p : Fin n → Bool} {D : Finset (Fin n)} (t : NaiveRun q p D) (k : ℕ) (_hk : k ≤ n)
      (_hDpast : ∀ j ∈ D, (j : ℕ) < k)
      (_hpast : ∀ j : Fin n, (j : ℕ) < k → j ∉ D → ∃ p₀, ProbeReach q p₀ p ∧ q p₀ j = none),
      onePassFrom q k p = t.final := by
  intro p D t k hk hDpast hpast
  revert k hk hDpast hpast
  induction t with
  | stop p D hall =>
      intro k hk hDpast hpast
      exact onePassFrom_all_none q (n - k) k p rfl (fun j hj =>
        hall j (fun hmem => by
          have := hDpast j hmem
          omega))
  | step p D i v hi hbefore hq t ih =>
      intro k hk hDpast hpast
      have hik : k ≤ (i : ℕ) := by
        rcases Nat.lt_or_ge (i : ℕ) k with hilt | hge
        · exfalso
          obtain ⟨p₀, hreach, hp₀⟩ := hpast i hilt hi
          rw [h.zero_perm p₀ p hreach i hp₀] at hq
          simp at hq
        · exact hge
      have hskip := onePassFrom_skip_zero q ((i : ℕ) - k) k p i v rfl hik
        (fun j _ hjj => hbefore j hjj) hq
      rw [hskip]
      refine ih ((i : ℕ) + 1) (by omega) ?_ ?_
      · intro j hjmem
        rcases Finset.mem_insert.mp hjmem with hjeq | hjD
        · rw [hjeq]
          exact Nat.lt_succ_self (i : ℕ)
        · exact (hDpast j hjD).trans (by omega)
      · intro j hjlt hjD
        rcases Nat.lt_or_ge (j : ℕ) k with hjk | hjk
        · obtain ⟨p₀, hreach, hz⟩ :=
            hpast j hjk (fun hmem => hjD (Finset.mem_insert_of_mem hmem))
          exact ⟨p₀, hreach.trans (Relation.ReflTransGen.single ⟨i, hq⟩), hz⟩
        · by_cases hij : j = i
          · exact absurd (Finset.mem_insert_self i D) (by rw [hij] at hjD; exact hjD)
          · exact ⟨p, Relation.ReflTransGen.single ⟨i, hq⟩, hbefore j (by omega)⟩

end TotalQuery

end Qatlib.Papers.ExactSimon97.MainResults
