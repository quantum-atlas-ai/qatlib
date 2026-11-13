/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic.NormNum.RealSqrt
import Qatlib.Concepts.WalkSearch.Primitives.TriangleContracts

/-!
# Diagnostics for triangle-search contracts

`emptyGraph_degreeTest_false` exposes the behavior of the original degree test on an empty
graph. The module also constructs zero-cost, always-rejecting search capabilities and uses them
to refute `fact2DegreeTest`, `theorem1`, and `theorem1Dense` as currently stated.

These counterexamples distinguish the stated interfaces from the effective search guarantees
motivating them [Grover1996].

## Main statements

* `not_fact2DegreeTest`: refute the original degree-test proposition.
* `rejecting_incomplete`: rejecting capabilities fail the completeness contract on graphs with
  triangles.
* `not_theorem1` and `not_theorem1Dense`: refute the unrestricted combined contracts.

## References

* [Grover, 1996][Grover1996]
-/

set_option maxRecDepth 4096

namespace Qatlib.Concepts.WalkSearch.Primitives

open scoped Classical BigOperators

/-- The undirected graph on `Fin n` with no edges. -/
def emptyGraph (n : ℕ) : UGraph n where
  edges := ∅
  symm := by simp
  loopless := by simp

/-- For a positive number of rounds, the original degree test returns `false` on the empty graph
for every tape. -/
theorem emptyGraph_degreeTest_false {n : ℕ} (v : Fin n) (K c : ℕ) (hK : 0 < K)
    (tape : Fin K → Fin c → Fin n) : degreeTestLow (emptyGraph n) v K c tape = false := by
  have hK1 : 1 ≤ K := hK
  simp [degreeTestLow, hitRounds, emptyGraph, hK1]

/-- The original degree-test proposition `fact2DegreeTest` is false. -/
theorem not_fact2DegreeTest : ¬ fact2DegreeTest := by
  intro h
  have hp : (100 : ℝ) ^ (1 / 2 : ℝ) = 10 := by
    rw [← Real.sqrt_eq_rpow]
    norm_num
  let K := 64 * (Nat.log 2 100 + 2)
  let c := Nat.ceil ((100 : ℝ) ^ (1 / 2 : ℝ))
  have hK : 0 < K := by dsimp [K]; omega
  have hc : 0 < c := by dsimp [c]; norm_num [hp]
  have ht : Nat.floor ((100 : ℝ) ^ (1 - (1 / 2 : ℝ)) / 10) = 1 := by norm_num [hp]
  have hb := (h 100 (1 / 2) (by norm_num) (by norm_num) (by norm_num) hc
    (emptyGraph 100) (0 : Fin 100)).2
  have hd : degOf (emptyGraph 100).edges (0 : Fin 100) = 0 := by
    simp [degOf, nbrOf, emptyGraph]
  change ((Finset.univ.filter fun tape : Fin K → Fin c → Fin 100 =>
    degOf (emptyGraph 100).edges (0 : Fin 100) < Nat.floor ((100 : ℝ)^(1 - (1 / 2 : ℝ)) / 10) ∧
      ¬degreeTestLow (emptyGraph 100) 0 K c tape).card : ℕ) * 100^3 ≤
    Fintype.card (Fin K → Fin c → Fin 100) at hb
  simp only [hd, ht, Nat.zero_lt_succ, emptyGraph_degreeTest_false 0 K c hK] at hb
  have hcard : 0 < Fintype.card (Fin K → Fin c → Fin 100) := Fintype.card_pos
  norm_num at hb
  have hpow : 0 < (100 ^ c) ^ K := by positivity
  omega

/-- A `SafeGrover` capability that always returns `none` at zero cost and has failure exponent
zero. -/
noncomputable def rejectingGrover : SafeGrover where
  seed := Unit
  seedFin := inferInstance
  seedNe := inferInstance
  cExp := 0
  κ := 0
  run := fun _ _ _ _ => none
  cost := fun _ _ _ _ => 0
  sound := by intro N marked check floor ρ x h; cases h
  reject := by intros; rfl
  finds := by intros; simp
  charges := by intros; simp

/-- An `EdgeTriSearch` capability that always returns `none` at zero cost and has failure
exponent zero. -/
noncomputable def rejectingEdgeSearch : EdgeTriSearch where
  seed := Unit
  seedFin := inferInstance
  seedNe := inferInstance
  cExp := 0
  κ := 0
  run := fun _ _ _ _ => none
  cost := fun _ _ _ _ => 0
  sound := by intro n G E floor ρ a b c h; cases h
  reject := by intros; rfl
  finds := by intros; simp
  charges := by intros; simp

/-- Every value returned by the transported `SafeGrover` search satisfies the marked predicate. -/
theorem sgsFind_sound (sgs : SafeGrover) {α : Type} [Fintype α] (marked : α → Bool)
    (check floor : ℕ) (ρ : sgs.seed) (x : α) (hx : sgsFind sgs marked check floor ρ = some x) :
    marked x = true := by
  cases hrun : sgs.run (fun i => marked ((Fintype.equivFin α).symm i)) check floor ρ with
  | none => simp [sgsFind, hrun] at hx
  | some i =>
    have hm := sgs.sound _ check floor ρ hrun
    have heq : (Fintype.equivFin α).symm i = x := by simpa [sgsFind, hrun] using hx
    simpa only [heq] using hm

/-- The transported search using `rejectingGrover` always returns `none`. -/
theorem sgsFind_rejecting {α : Type} [Fintype α] (marked : α → Bool)
    (check floor : ℕ) (ρ : rejectingGrover.seed) :
    sgsFind rejectingGrover marked check floor ρ = none := by
  simp [sgsFind, rejectingGrover]

/-- The transported search using `rejectingGrover` has cost zero. -/
private theorem sgsFindCost_rejecting {α : Type} [Fintype α] (marked : α → Bool)
    (check floor : ℕ) (ρ : rejectingGrover.seed) :
    sgsFindCost rejectingGrover marked check floor ρ = 0 := rfl

/-- With `rejectingGrover`, `stepFour` returns no triangle and leaves the accumulated charge
unchanged. -/
theorem stepFour_rejecting {n : ℕ} (hn : 0 < n) (G : UGraph n)
    (stape : ℕ → rejectingGrover.seed) (vs : List (Fin n)) (i q : ℕ) :
    stepFour hn G rejectingGrover stape vs i q = (none, q) := by
  induction vs generalizing i q with
  | nil => rfl
  | cons v vs ih =>
    simp only [stepFour, sgsFind_rejecting, sgsFindCost_rejecting, Nat.add_zero]
    exact ih _ _

/-- Tests whether a classification outcome is a partition rather than a triangle candidate. -/
private def isPartition {n : ℕ} : ClassifyOut n → Bool
  | .part _ _ _ => true
  | .tri _ _ _ _ => false

/-- Classification with `rejectingGrover` always returns a partition outcome. -/
theorem classify_rejecting {n : ℕ} (hn : 0 < n) (G : UGraph n)
    (τ dHi dLo K c : ℕ) (ttape : Fin n → Fin K → Fin c → Fin n)
    (stape : ℕ → rejectingGrover.seed) (S T E : Finset (Fin n × Fin n)) (q fuel : ℕ) :
    isPartition (classify hn G rejectingGrover τ dHi dLo K c ttape stape S T E q fuel) = true := by
  induction fuel generalizing S T E q with
  | zero => rfl
  | succ fuel ih =>
    rw [classify]
    split_ifs with hS
    · rfl
    · cases hd : drainLow S T τ fuel with
      | mk Sd Td =>
        (try dsimp only)
        split_ifs with hempty hgate
        · rfl
        · rw [sgsFind_rejecting]
          exact ih _ _ _ _
        · exact ih _ _ _ _

/-- Tests whether a combinatorial search outcome is rejection. -/
private def isRejection {n : ℕ} : CombOut n → Bool
  | .reject _ => true
  | .tri _ _ _ _ => false

/-- The combinatorial algorithm using both rejecting capabilities always returns a rejection
outcome. -/
theorem combAlg_rejecting {n : ℕ} (hn : 0 < n) (G : UGraph n)
    (k K c dHi dLo τ tThin : ℕ) (vtape : Fin k → Fin n)
    (ttape : Fin n → Fin K → Fin c → Fin n)
    (stape : ℕ → rejectingGrover.seed) (etstape : ℕ → rejectingEdgeSearch.seed) :
    isRejection (combAlg hn G rejectingGrover rejectingEdgeSearch k K c dHi dLo τ tThin
      vtape ttape stape etstape) = true := by
  unfold combAlg
  (try dsimp only)
  rw [stepFour_rejecting]
  (try dsimp only)
  let S := Finset.univ.filter fun p : Fin n × Fin n => ∀ v ∈ Finset.univ.image vtape,
    (p.1, v) ∉ G.edges ∨ (p.2, v) ∉ G.edges
  have hpart := classify_rejecting hn G τ dHi dLo K c ttape (fun i => stape (k + i))
    S ∅ ∅ (k * n) (S.card + 1)
  cases hout : classify hn G rejectingGrover τ dHi dLo K c ttape (fun i => stape (k + i))
      S ∅ ∅ (k * n) (S.card + 1) with
  | tri a b cc q => rw [hout] at hpart; cases hpart
  | part T E q =>
    (try dsimp only)
    rw [sgsFind_rejecting]
    rfl

/-- The graph on 100 vertices containing exactly the edges between distinct vertices among the
first three vertices. -/
private def triangleGraph : UGraph 100 where
  edges := Finset.univ.filter fun p => p.1.val < 3 ∧ p.2.val < 3 ∧ p.1 ≠ p.2
  symm := by
    intro a b h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    exact ⟨h.2.1, h.1, h.2.2.symm⟩
  loopless := by intro a; simp

/-- The graph `triangleGraph` has at least one canonical triangle. -/
private theorem triangleGraph_has_triangle : 1 ≤ triCount triangleGraph.edges := by
  apply Finset.one_le_card.mpr
  refine ⟨(0, 1, 2), ?_⟩
  simp only [trianglesOf, tri3B, triangleGraph, Finset.mem_filter, Finset.mem_univ, true_and]
  decide

/-- On a graph with a triangle and more than two vertices, the rejecting capabilities violate
`combComplete` for every choice of the stated parameters. -/
theorem rejecting_incomplete {n : ℕ} (hn : 0 < n) (hn2 : 2 < n) (G : UGraph n)
    (htri : 1 ≤ triCount G.edges) (k K c dHi dLo τ tThin B : ℕ) :
    ¬ combComplete hn G rejectingGrover rejectingEdgeSearch k K c dHi dLo τ tThin B := by
  intro h
  letI : NeZero n := ⟨hn.ne'⟩
  letI := rejectingGrover.seedFin
  letI := rejectingEdgeSearch.seedFin
  letI := rejectingGrover.seedNe
  letI := rejectingEdgeSearch.seedNe
  have hb := h htri
  have hf : (Finset.univ.filter fun t : combTape n k K c rejectingGrover rejectingEdgeSearch B =>
      combSound.match_1 (fun _ : CombOut n => Bool)
        (combAlg hn G rejectingGrover rejectingEdgeSearch k K c dHi dLo τ tThin
          t.1 t.2.1 (@extendSeed B rejectingGrover.seed rejectingGrover.seedNe t.2.2.1)
            (@extendSeed B rejectingEdgeSearch.seed rejectingEdgeSearch.seedNe t.2.2.2))
        (fun _ _ _ _ => false) (fun _ => true) = true) = Finset.univ := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hr := combAlg_rejecting hn G k K c dHi dLo τ tThin t.1 t.2.1
      (@extendSeed B rejectingGrover.seed rejectingGrover.seedNe t.2.2.1)
      (@extendSeed B rejectingEdgeSearch.seed rejectingEdgeSearch.seedNe t.2.2.2)
    cases hout : combAlg hn G rejectingGrover rejectingEdgeSearch k K c dHi dLo τ tThin
        t.1 t.2.1 (@extendSeed B rejectingGrover.seed rejectingGrover.seedNe t.2.2.1)
          (@extendSeed B rejectingEdgeSearch.seed rejectingEdgeSearch.seedNe t.2.2.2) with
    | tri a b cc q => rw [hout] at hr; cases hr
    | reject q => simp
  rw [Finset.filter_congr_decidable, hf, Finset.card_univ] at hb
  have hcard : 0 < Fintype.card (combTape n k K c rejectingGrover rejectingEdgeSearch B) :=
      Fintype.card_pos
  nlinarith

/-- The unrestricted combinatorial search contract `theorem1` is false. -/
theorem not_theorem1 : ¬ theorem1 := by
  intro h
  have hp : (100 : ℝ) ^ (1 / 2 : ℝ) = 10 := by rw [← Real.sqrt_eq_rpow]; norm_num
  have hk : 0 < Nat.ceil (4 * (100 : ℝ)^(3 / 4 : ℝ) * (Nat.log 2 100 + 1)) := by
    apply Nat.ceil_pos.mpr
    positivity
  have hc : 0 < Nat.ceil ((100 : ℝ) ^ (1 / 2 : ℝ)) := by norm_num [hp]
  have hd : 1 ≤ Nat.floor ((100 : ℝ) ^ (1 - (1 / 2 : ℝ)) / 10) := by norm_num [hp]
  have hresult := h 100 (3 / 4) (1 / 2) (1 / 4) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) triangleGraph rejectingGrover rejectingEdgeSearch hk hc hd
  exact rejecting_incomplete (by norm_num) (by norm_num) triangleGraph triangleGraph_has_triangle
    _ _ _ _ _ _ _ _ hresult.2.1

/-- The unrestricted dense-parameter contract `theorem1Dense` is false. -/
theorem not_theorem1Dense : ¬ theorem1Dense := by
  intro h
  have hp : (100 : ℝ) ^ (1 / 2 : ℝ) = 10 := by rw [← Real.sqrt_eq_rpow]; norm_num
  have hk : 0 < Nat.ceil (4 * (100 : ℝ)^(3 / 7 : ℝ) * (Nat.log 2 100 + 1)) := by
    apply Nat.ceil_pos.mpr
    positivity
  have hc : 0 < Nat.ceil ((100 : ℝ) ^ (1 / 7 : ℝ)) := by
    apply Nat.ceil_pos.mpr
    positivity
  have hexp : (100 : ℝ) ^ (1 / 2 : ℝ) ≤ (100 : ℝ) ^ (6 / 7 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hd : 1 ≤ Nat.floor ((100 : ℝ) ^ (6 / 7 : ℝ) / 10) := by
    apply Nat.le_floor
    rw [hp] at hexp
    linarith
  have hresult := h 100 (by norm_num) triangleGraph rejectingGrover rejectingEdgeSearch hk hc hd
  exact rejecting_incomplete (by norm_num) (by norm_num) triangleGraph triangleGraph_has_triangle
    _ _ _ _ _ _ _ _ hresult.2.1

/-- The displayed dense budget is at least `2 * n ^ (3 / 2)` over the reals. -/
theorem dense_budget_three_halves (n : ℕ) :
    2 * (n : ℝ) ^ (3 / 2 : ℝ) ≤
      4 * (n : ℝ) ^ (10 / 7 : ℝ) + 2 * (n : ℝ) ^ (3 / 2 : ℝ) +
        (n : ℝ) ^ (10 / 7 : ℝ) := by
  nlinarith [Real.rpow_nonneg (Nat.cast_nonneg n) (10 / 7 : ℝ)]

end Qatlib.Concepts.WalkSearch.Primitives
