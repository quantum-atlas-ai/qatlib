/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Papers.WildcardSrch12.MainResults.Model.ReadoutModel

set_option backward.isDefEq.respectTransparency false

/-!
# Query Lower Bound for Quantum Search with Wildcards

This module proves Lemma 6 of Ambainis and Montanaro: any bounded-error quantum
algorithm in the counted-query observed-circuit model that solves search with
wildcards on `n` bits with worst-case success probability at least `2 / 3` from the
all-zero register must make `Ω(√n)` wildcard-oracle queries.

## Main statements

* `card_hammingDist_one`: the Hamming sphere of radius `1` around `x : BitStr n` has
  cardinality `n`.
* `adversaryWt_eq`: total Hamming-distance-one adversary weight `∑ y, wildcardAdversaryWeight x y = n`.
* `lemma6_wildcard_query_lower_bound`: `Ω(√n)` query lower bound for `SolvesWildcardFrom`
  at success threshold `2 / 3`.

## References

* [Ambainis and Montanaro, 2014][AmbainisMontanaro2014], Section 5, Lemma 6, pp. 447--448.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.MbqcFlow.FlowDecision
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery

namespace Qatlib.Papers.WildcardSrch12.MainResults.WildcardLowerBound

open Qatlib.Papers.WildcardSrch12.MainResults

open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws

private def oracleFlip {n r : ℕ} (x : BitStr n) (p : WildcardReg n r) :
    WildcardReg n r :=
  ((p.1.1, p.1.2.1, p.1.2.2 != wildcardReply x p.1.1 p.1.2.1), p.2)

private theorem oracleFlip_involutive {n r : ℕ} (x : BitStr n) :
    Function.Involutive (oracleFlip (r := r) x) := by
  rintro ⟨⟨S, z, b⟩, w⟩
  dsimp [oracleFlip]
  cases b <;> cases wildcardReply x S z <;> rfl

private theorem wildcardOracle_perm {n r : ℕ} (x : BitStr n) :
    wildcardOracle n r x = permMatrix (oracleFlip x) := by
  ext p q
  have he : q = oracleFlip x p ↔ p = oracleFlip x q := by
    constructor <;> intro h
    · rw [h, oracleFlip_involutive x p]
    · rw [h, oracleFlip_involutive x q]
  simp only [wildcardOracle, permMatrix, Matrix.of_apply, oracleFlip] at he ⊢
  simp only [he]

private theorem wildcardOracle_unitary {n r : ℕ} (x : BitStr n) :
    wildcardOracle n r x ∈ Matrix.unitaryGroup (WildcardReg n r) ℂ := by
  rw [wildcardOracle_perm]
  exact permMatrix_unitary (oracleFlip_involutive x)

private theorem wildcardOracle_apply {n r : ℕ} (x : BitStr n)
    (v : QState (WildcardReg n r)) (p : WildcardReg n r) :
    ApplyGate (wildcardOracle n r x) v p = v (oracleFlip x p) := by
  rw [wildcardOracle_perm, applyGate_permMatrix (oracleFlip_involutive x)]

private def pairIP {I : Type} [Fintype I] [DecidableEq I]
    (O₁ O₂ : Matrix I I ℂ) : ObservedCircuit I → QState I → QState I → ℝ
  | .halt _, v₁, v₂ => (Inner v₁ v₂).re
  | .step .query Q, v₁, v₂ => pairIP O₁ O₂ Q (ApplyGate O₁ v₁) (ApplyGate O₂ v₂)
  | .step (.gate U) Q, v₁, v₂ => pairIP O₁ O₂ Q (ApplyGate U v₁) (ApplyGate U v₂)
  | .measure k label next, v₁, v₂ =>
      ∑ o : Fin k, pairIP O₁ O₂ (next o)
        (Collapse v₁ (Finset.univ.filter (fun idx => label idx = o)))
        (Collapse v₂ (Finset.univ.filter (fun idx => label idx = o)))
  | .project A Q₁ Q₂, v₁, v₂ =>
      pairIP O₁ O₂ Q₁ (ApplyGate (1 - A) v₁) (ApplyGate (1 - A) v₂) +
        pairIP O₁ O₂ Q₂ (ApplyGate A v₁) (ApplyGate A v₂)

private def eventMass {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (pred : Bool → I → Prop) [∀ acc idx, Decidable (pred acc idx)] :
    ObservedCircuit I → QState I → ℝ
  | .halt acc, v => MeasureProb v (Finset.univ.filter (fun idx => pred acc idx))
  | .step .query Q, v => eventMass O pred Q (ApplyGate O v)
  | .step (.gate U) Q, v => eventMass O pred Q (ApplyGate U v)
  | .measure k label next, v =>
      ∑ o : Fin k, eventMass O pred (next o)
        (Collapse v (Finset.univ.filter (fun idx => label idx = o)))
  | .project A Q₁ Q₂, v =>
      eventMass O pred Q₁ (ApplyGate (1 - A) v) + eventMass O pred Q₂ (ApplyGate A v)

private theorem foldl_weight {α : Type*} (f : α → ℝ) (xs : List α) (a : ℝ) :
    xs.foldl (fun total x => total + f x) a = a + (xs.map f).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    ring

private theorem eventMass_traces {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (pred : Bool → I → Prop) [∀ acc idx, Decidable (pred acc idx)]
    (P : ObservedCircuit I) (v : QState I) :
    eventMass O pred P v = ((observedTraces O P v).map
      (fun t => MeasureProb t.state (Finset.univ.filter (fun idx => pred t.accepted idx)))).sum := by
  induction P generalizing v with
  | halt acc => simp [eventMass, observedTraces]
  | step s Q ih =>
    cases s <;> simp [eventMass, observedTraces, List.map_map, Function.comp_def, ih]
  | measure k label next ih =>
    simp [eventMass, observedTraces, List.map_flatten, List.sum_flatten,
      List.map_map, Function.comp_def, List.map_ofFn, List.sum_ofFn, ih]
  | project A Q₁ Q₂ ih₁ ih₂ =>
    simp [eventMass, observedTraces, List.map_map, Function.comp_def, ProjectiveBranch, ih₁, ih₂]

private theorem successMass_eventMass {n r : ℕ} (readOut : WildcardReg n r → BitStr n)
    (P : ObservedCircuit (WildcardReg n r)) (v : QState (WildcardReg n r))
    (x : BitStr n) :
    programSuccessMass n r readOut P v x =
      eventMass (wildcardOracle n r x) (fun acc idx => acc = true ∧ readOut idx = x) P v := by
  classical
  rw [eventMass_traces]
  unfold programSuccessMass
  have hf (a : ℝ) (t : BranchTrace (WildcardReg n r)) :
      (if t.accepted then a + outputMass readOut x t.state else a) =
        a + (if t.accepted then outputMass readOut x t.state else 0) := by
    cases t.accepted <;> simp
  simp_rw [hf]
  rw [foldl_weight, zero_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  cases t.accepted <;> simp [outputMass, MeasureProb]

private theorem eventMass_nonneg {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (pred : Bool → I → Prop) [∀ acc idx, Decidable (pred acc idx)]
    (P : ObservedCircuit I) (v : QState I) : 0 ≤ eventMass O pred P v := by
  induction P generalizing v with
  | halt acc => exact measureProb_nonneg _ _
  | step s Q ih => cases s <;> exact ih _
  | measure k label next ih => exact Finset.sum_nonneg (fun o _ => ih o _)
  | project A Q₁ Q₂ ih₁ ih₂ => exact add_nonneg (ih₁ _) (ih₂ _)

private theorem eventMass_partition {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (hO : O ∈ Matrix.unitaryGroup I ℂ)
    (label : Bool → I → Fin 3) (P : ObservedCircuit I)
    (hP : observedWellFormed P) (v : QState I) :
    (∑ t : Fin 3, eventMass O (fun acc i => label acc i = t) P v) = branchMass v := by
  classical
  induction P generalizing v with
  | halt acc =>
    simp only [eventMass, MeasureProb, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp
  | step s Q ih =>
    cases s with
    | gate U =>
      simp only [eventMass]
      rw [ih hP.2]
      exact measureProb_applyGate_univ hP.1 v
    | query =>
      simp only [eventMass]
      rw [ih hP]
      exact measureProb_applyGate_univ hO v
  | measure k labels next ih =>
    simp only [eventMass]
    rw [Finset.sum_comm]
    have hnext (o : Fin k) := ih o (hP o)
    simp_rw [hnext]
    exact sum_measureProb_collapse_partition v labels
  | project A Q₁ Q₂ ih₁ ih₂ =>
    simp only [eventMass, Finset.sum_add_distrib]
    rw [ih₁ hP.2.1, ih₂ hP.2.2]
    exact projectiveBranchMass_add hP.1 v

private theorem sum_sqrt_mul_le {α : Type*} (s : Finset α) (p q : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    (∑ i ∈ s, Real.sqrt (p i * q i)) ≤
      Real.sqrt ((∑ i ∈ s, p i) * (∑ i ∈ s, q i)) := by
  simp_rw [Real.sqrt_mul (hp _)]
  rw [Real.sqrt_mul (Finset.sum_nonneg (fun i _ => hp i))]
  exact Real.sum_sqrt_mul_sqrt_le s hp hq

private theorem two_sqrt_mul_le {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt (a * b) + Real.sqrt (c * d) ≤ Real.sqrt ((a + c) * (b + d)) := by
  simpa using sum_sqrt_mul_le Finset.univ
    (fun i : Bool => if i then a else c) (fun i : Bool => if i then b else d)
    (fun i => by cases i <;> assumption) (fun i => by cases i <;> assumption)

private theorem event_inner_abs_le {I : Type*} (F : Finset I)
    (v₁ v₂ : QState I) :
    |∑ i ∈ F, ((starRingEnd ℂ) (v₁ i) * v₂ i).re| ≤
      Real.sqrt (MeasureProb v₁ F * MeasureProb v₂ F) := by
  calc
    _ ≤ ∑ i ∈ F, |((starRingEnd ℂ) (v₁ i) * v₂ i).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ F, ‖v₁ i‖ * ‖v₂ i‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_mul, Complex.norm_conj] using
        Complex.abs_re_le_norm ((starRingEnd ℂ) (v₁ i) * v₂ i)
    _ ≤ Real.sqrt (∑ i ∈ F, ‖v₁ i‖ ^ 2) *
        Real.sqrt (∑ i ∈ F, ‖v₂ i‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt F (fun i => ‖v₁ i‖) (fun i => ‖v₂ i‖)
    _ = _ := by
      rw [← Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg ‖v₁ i‖))]
      rfl

private theorem pairIP_le_events {I : Type} [Fintype I] [DecidableEq I]
    (O₁ O₂ : Matrix I I ℂ) (label : Bool → I → Fin 3)
    (P : ObservedCircuit I) (v₁ v₂ : QState I) :
    pairIP O₁ O₂ P v₁ v₂ ≤ ∑ t : Fin 3,
      Real.sqrt (eventMass O₁ (fun acc i => label acc i = t) P v₁ *
        eventMass O₂ (fun acc i => label acc i = t) P v₂) := by
  classical
  induction P generalizing v₁ v₂ with
  | halt acc =>
    have hsplit : (Inner v₁ v₂).re =
        ∑ t : Fin 3, ∑ i ∈ Finset.univ.filter (fun i => label acc i = t),
          ((starRingEnd ℂ) (v₁ i) * v₂ i).re := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm, inner_apply, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp
    rw [pairIP, hsplit]
    exact Finset.sum_le_sum (fun t _ => (le_abs_self _).trans (event_inner_abs_le _ v₁ v₂))
  | step s Q ih => cases s <;> exact ih _ _
  | measure k labels next ih =>
    simp only [pairIP, eventMass]
    calc
      _ ≤ ∑ o : Fin k, ∑ t : Fin 3,
          Real.sqrt (eventMass O₁ (fun acc i => label acc i = t) (next o)
            (Collapse v₁ (Finset.univ.filter (fun i => labels i = o))) *
          eventMass O₂ (fun acc i => label acc i = t) (next o)
            (Collapse v₂ (Finset.univ.filter (fun i => labels i = o)))) :=
        Finset.sum_le_sum (fun o _ => ih o _ _)
      _ = _ := Finset.sum_comm
      _ ≤ _ := Finset.sum_le_sum (fun t _ => sum_sqrt_mul_le Finset.univ _ _
        (fun _ => eventMass_nonneg _ _ _ _) (fun _ => eventMass_nonneg _ _ _ _))
  | project A Q₁ Q₂ ih₁ ih₂ =>
    simp only [pairIP, eventMass]
    calc
      _ ≤ _ := add_le_add (ih₁ _ _) (ih₂ _ _)
      _ = _ := (Finset.sum_add_distrib).symm
      _ ≤ _ := Finset.sum_le_sum (fun t _ => two_sqrt_mul_le
        (eventMass_nonneg _ _ _ _) (eventMass_nonneg _ _ _ _)
        (eventMass_nonneg _ _ _ _) (eventMass_nonneg _ _ _ _))

private theorem three_event_gap {a₁ a₂ a₃ b₁ b₂ b₃ : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃)
    (ha : a₁ + a₂ + a₃ = 1) (hb : b₁ + b₂ + b₃ = 1)
    (hax : (2 / 3 : ℝ) ≤ a₁) (hby : (2 / 3 : ℝ) ≤ b₂) :
    Real.sqrt (a₁ * b₁) + Real.sqrt (a₂ * b₂) + Real.sqrt (a₃ * b₃) ≤ 19 / 20 := by
  rw [Real.sqrt_mul ha₁, Real.sqrt_mul ha₂, Real.sqrt_mul ha₃]
  have sa₁ := Real.sq_sqrt ha₁
  have sa₂ := Real.sq_sqrt ha₂
  have sa₃ := Real.sq_sqrt ha₃
  have sb₁ := Real.sq_sqrt hb₁
  have sb₂ := Real.sq_sqrt hb₂
  have sb₃ := Real.sq_sqrt hb₃
  have la₁ : (81 / 100 : ℝ) ≤ Real.sqrt a₁ := by
    nlinarith only [sa₁, hax, Real.sqrt_nonneg a₁]
  have lb₂ : (81 / 100 : ℝ) ≤ Real.sqrt b₂ := by
    nlinarith only [sb₂, hby, Real.sqrt_nonneg b₂]
  have ub : b₁ ≤ (1 / 3 : ℝ) := by linarith only [hb, hb₃, hby]
  have ua : a₂ ≤ (1 / 3 : ℝ) := by linarith only [ha, ha₃, hax]
  have ub₁ : Real.sqrt b₁ ≤ (58 / 100 : ℝ) := by
    nlinarith only [sb₁, ub, Real.sqrt_nonneg b₁]
  have ua₂ : Real.sqrt a₂ ≤ (58 / 100 : ℝ) := by
    nlinarith only [sa₂, ua, Real.sqrt_nonneg a₂]
  have g₁ : (529 / 10000 : ℝ) ≤ (Real.sqrt a₁ - Real.sqrt b₁) ^ 2 := by
    nlinarith only [la₁, ub₁, sq_nonneg (Real.sqrt a₁ - Real.sqrt b₁ - 23 / 100)]
  have g₂ : (529 / 10000 : ℝ) ≤ (Real.sqrt b₂ - Real.sqrt a₂) ^ 2 := by
    nlinarith only [lb₂, ua₂, sq_nonneg (Real.sqrt b₂ - Real.sqrt a₂ - 23 / 100)]
  nlinarith only [sa₁, sa₂, sa₃, sb₁, sb₂, sb₃, ha, hb, g₁, g₂,
    sq_nonneg (Real.sqrt a₃ - Real.sqrt b₃)]

/-- Flip the `i`-th bit of `x`. -/
def flipAt {n : ℕ} (x : BitStr n) (i : Fin n) : BitStr n :=
  fun j => if j = i then !(x j) else x j

/-- Flipping one bit changes the Hamming distance by exactly one: the difference
support of `x` and `flipAt x i` is the singleton `{i}`. -/
theorem hammingDist_flipAt {n : ℕ} (x : BitStr n) (i : Fin n) :
    hammingDist x (flipAt x i) = 1 := by
  classical
  unfold hammingDist
  have hset : Finset.univ.filter (fun j => x j ≠ flipAt x i j) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases hj : j = i
    · subst hj
      simp only [flipAt]
      cases x j <;> simp
    · simp [flipAt, hj]
  rw [hset]
  simp

/-- The bit-flip family is injective. -/
theorem flipAt_injective {n : ℕ} (x : BitStr n) : Function.Injective (flipAt x) := by
  intro i j h
  have hc := congrFun h i
  simp only [flipAt] at hc
  by_cases hji : i = j
  · exact hji
  · simp only [hji, ↓reduceIte] at hc
    cases hx : x i <;> simp [hx] at hc

/-- Every string at Hamming distance one from `x` is a single bit flip of `x`. -/
theorem exists_flipAt_of_hammingDist_one {n : ℕ} (x y : BitStr n)
    (h : hammingDist x y = 1) : ∃ i : Fin n, y = flipAt x i := by
  classical
  unfold hammingDist at h
  have hpos : 0 < (Finset.univ.filter (fun j => x j ≠ y j)).card := by
    rw [h]; norm_num
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  have hsingle : Finset.univ.filter (fun j => x j ≠ y j) = {i} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hi, ?_⟩
    intro k hk
    exact Finset.card_le_one.mp (le_of_eq h) k hk i hi
  refine ⟨i, ?_⟩
  have hxi : x i ≠ y i := (Finset.mem_filter.mp hi).2
  have hyi : y i = !(x i) := by
    cases hx : x i <;> cases hy : y i <;> simp_all
  funext j
  by_cases hj : j = i
  · rw [hj]
    simp [flipAt, hyi]
  · have hnotmem : j ∉ Finset.univ.filter (fun k => x k ≠ y k) := by
      rw [hsingle]
      simp [hj]
    have hxy : x j = y j := by
      by_contra hne
      exact hnotmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
    simp only [flipAt, hj, ↓reduceIte]
    exact hxy.symm

/-- **The radius-one Hamming sphere has `n` points**: the bit-flip map
`i ↦ flipAt x i` is a bijection from `Fin n` onto the strings at distance one
from `x`. -/
theorem card_hammingDist_one {n : ℕ} (x : BitStr n) :
    (Finset.univ.filter (fun y => hammingDist x y = 1)).card = n := by
  classical
  have hcard : (Finset.univ : Finset (BitStr n)).filter (fun y => hammingDist x y = 1) =
      Finset.univ.image (flipAt x) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro hy
      obtain ⟨i, hi⟩ := exists_flipAt_of_hammingDist_one x y hy
      exact ⟨i, hi.symm⟩
    · rintro ⟨i, hi⟩
      rw [← hi]
      exact hammingDist_flipAt x i
  rw [hcard, Finset.card_image_of_injective _ (flipAt_injective x), Finset.card_univ,
    Fintype.card_fin]

/-- The adversary weight of Lemma 6: `w(x,y) = 1` when `d(x,y) = 1`. -/
noncomputable def wildcardAdversaryWeight {n : ℕ} (x y : BitStr n) : ℝ :=
  if hammingDist x y = 1 then 1 else 0

/-- `wt(x) = Σ_y w(x,y) = n`. -/
theorem adversaryWt_eq {n : ℕ} (x : BitStr n) :
    (∑ y : BitStr n, wildcardAdversaryWeight x y) = (n : ℝ) := by
  classical
  have hsum : (∑ y : BitStr n, wildcardAdversaryWeight x y)
      = ((Finset.univ.filter (fun y => hammingDist x y = 1)).card : ℝ) := by
    unfold wildcardAdversaryWeight
    rw [← Finset.sum_filter]
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hsum, card_hammingDist_one]

private theorem flipAt_flipAt {n : ℕ} (x : BitStr n) (j : Fin n) :
    flipAt (flipAt x j) j = x := by
  funext i
  by_cases h : i = j <;> simp [flipAt, h]

private theorem wildcardReply_flipAt_notMem {n : ℕ} (x : BitStr n)
    (S : Finset (Fin n)) (z : BitStr n) (j : Fin n) (hj : j ∉ S) :
    wildcardReply (flipAt x j) S z = wildcardReply x S z := by
  unfold wildcardReply
  congr 1
  apply propext
  constructor <;> intro h i hi
  · have hij : i ≠ j := fun he => hj (he ▸ hi)
    simpa [flipAt, hij] using h i hi
  · have hij : i ≠ j := fun he => hj (he ▸ hi)
    simpa [flipAt, hij] using h i hi

private theorem wildcardReply_flipAt_false_iff {n : ℕ} (x : BitStr n)
    (S : Finset (Fin n)) (z : BitStr n) (j : Fin n)
    (hx : wildcardReply x S z = true) :
    wildcardReply (flipAt x j) S z = false ↔ j ∈ S := by
  constructor
  · intro hf
    by_contra hj
    rw [wildcardReply_flipAt_notMem x S z j hj, hx] at hf
    contradiction
  · intro hj
    have hx' : ∀ k ∈ S, z k = x k := by
      simpa only [wildcardReply, decide_eq_true_eq] using hx
    cases hy : wildcardReply (flipAt x j) S z with
    | false => rfl
    | true =>
      have hy' : ∀ k ∈ S, z k = flipAt x j k := by
        simpa only [wildcardReply, decide_eq_true_eq] using hy
      have h₁ := hx' j hj
      have h₂ := hy' j hj
      simp only [flipAt, ↓reduceIte] at h₂
      rw [← h₁] at h₂
      revert h₂; cases z j <;> decide

private theorem wildcard_star_inj {n : ℕ} (S : Finset (Fin n)) (z : BitStr n) :
    Set.InjOn (fun p : BitStr n × Fin n => flipAt p.1 p.2)
      (↑((Finset.univ.filter (fun x => wildcardReply x S z = true)) ×ˢ S)) := by
  classical
  rintro ⟨x, i⟩ hp ⟨y, j⟩ hq heq
  obtain ⟨hx, hi⟩ := Finset.mem_product.mp hp
  obtain ⟨hy, _⟩ := Finset.mem_product.mp hq
  have hx' : ∀ k ∈ S, z k = x k := by
    simpa only [wildcardReply, decide_eq_true_eq] using (Finset.mem_filter.mp hx).2
  have hy' : ∀ k ∈ S, z k = y k := by
    simpa only [wildcardReply, decide_eq_true_eq] using (Finset.mem_filter.mp hy).2
  have hij : i = j := by
    by_contra hne
    have h := congrFun heq i
    simp only [flipAt, ↓reduceIte, hne] at h
    rw [← hx' i hi, ← hy' i hi] at h
    cases z i <;> simp_all
  subst j
  have hxy : x = y := by
    have h := congrArg (fun w => flipAt w i) heq
    simpa only [flipAt_flipAt] using h
  exact Prod.ext hxy rfl

private theorem star_four_sum_le {α β : Type*} [Fintype α]
    [DecidableEq α] [DecidableEq β] (A : Finset α) (S : Finset β)
    (τ : α → β → α) (N : α → ℝ) (hN : ∀ x, 0 ≤ N x)
    (hinj : Set.InjOn (fun p : α × β => τ p.1 p.2) (↑(A ×ˢ S)))
    (hout : ∀ x ∈ A, ∀ j ∈ S, τ x j ∉ A) :
    4 * (∑ p ∈ A ×ˢ S, Real.sqrt (N p.1) * Real.sqrt (N (τ p.1 p.2))) ≤
      2 * Real.sqrt (S.card : ℝ) * ∑ x, N x := by
  classical
  let E := A ×ˢ S
  let T := E.image (fun p => τ p.1 p.2)
  have hdis : Disjoint A T := by
    apply Finset.disjoint_left.mpr
    intro y hy hyT
    obtain ⟨⟨x, j⟩, hp, rfl⟩ := Finset.mem_image.mp hyT
    obtain ⟨hx, hj⟩ := Finset.mem_product.mp hp
    exact hout x hx j hj hy
  have hA : 0 ≤ ∑ x ∈ A, N x := Finset.sum_nonneg (fun x _ => hN x)
  have hT : 0 ≤ ∑ x ∈ T, N x := Finset.sum_nonneg (fun x _ => hN x)
  have htotal : (∑ x ∈ A, N x) + (∑ x ∈ T, N x) ≤ ∑ x, N x := by
    rw [← Finset.sum_union hdis]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun x _ _ => hN x)
  have hsrc : (∑ p ∈ E, N p.1) = (S.card : ℝ) * ∑ x ∈ A, N x := by
    simp only [E, Finset.sum_product, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
  have htar : (∑ p ∈ E, N (τ p.1 p.2)) = ∑ x ∈ T, N x := by
    exact (Finset.sum_image hinj).symm
  have hcs := Real.sum_sqrt_mul_sqrt_le (f := fun p : α × β => N p.1)
    (g := fun p : α × β => N (τ p.1 p.2)) E
    (fun p => hN p.1) (fun p => hN (τ p.1 p.2))
  rw [hsrc, htar, Real.sqrt_mul (Nat.cast_nonneg S.card)] at hcs
  have ham : 2 * Real.sqrt (∑ x ∈ A, N x) * Real.sqrt (∑ x ∈ T, N x) ≤
      (∑ x ∈ A, N x) + (∑ x ∈ T, N x) := by
    nlinarith only [sq_nonneg (Real.sqrt (∑ x ∈ A, N x) - Real.sqrt (∑ x ∈ T, N x)),
      Real.sq_sqrt hA, Real.sq_sqrt hT]
  calc
    4 * (∑ p ∈ A ×ˢ S, Real.sqrt (N p.1) * Real.sqrt (N (τ p.1 p.2)))
      ≤ 4 * (Real.sqrt (S.card : ℝ) * Real.sqrt (∑ x ∈ A, N x) *
          Real.sqrt (∑ x ∈ T, N x)) := mul_le_mul_of_nonneg_left hcs (by norm_num)
    _ ≤ 2 * Real.sqrt (S.card : ℝ) *
          ((∑ x ∈ A, N x) + (∑ x ∈ T, N x)) := by
      nlinarith only [mul_le_mul_of_nonneg_left ham (Real.sqrt_nonneg (S.card : ℝ))]
    _ ≤ 2 * Real.sqrt (S.card : ℝ) * ∑ x, N x :=
      mul_le_mul_of_nonneg_left htotal (by positivity)

private theorem wildcard_disagreement_sum_le {n : ℕ} (S : Finset (Fin n))
    (z : BitStr n) (N : BitStr n → ℝ) (hN : ∀ x, 0 ≤ N x) :
    (∑ x : BitStr n, ∑ j : Fin n,
      if wildcardReply x S z ≠ wildcardReply (flipAt x j) S z then
        2 * Real.sqrt (N x) * Real.sqrt (N (flipAt x j)) else 0) ≤
      2 * Real.sqrt (n : ℝ) * ∑ x, N x := by
  classical
  let A := Finset.univ.filter (fun x : BitStr n => wildcardReply x S z = true)
  let E := A ×ˢ S
  let e : (BitStr n × Fin n) ≃ (BitStr n × Fin n) :=
    { toFun := fun p => (flipAt p.1 p.2, p.2)
      invFun := fun p => (flipAt p.1 p.2, p.2)
      left_inv := by rintro ⟨x, j⟩; simp [flipAt_flipAt]
      right_inv := by rintro ⟨x, j⟩; simp [flipAt_flipAt] }
  let G : BitStr n × Fin n → ℝ := fun p =>
    if p ∈ E then Real.sqrt (N p.1) * Real.sqrt (N (flipAt p.1 p.2)) else 0
  have hmem (p : BitStr n × Fin n) : p ∈ E ↔
      wildcardReply p.1 S z = true ∧ wildcardReply (flipAt p.1 p.2) S z = false := by
    simp only [E, A, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hj⟩
      exact ⟨hx, (wildcardReply_flipAt_false_iff p.1 S z p.2 hx).2 hj⟩
    · rintro ⟨hx, hy⟩
      exact ⟨hx, (wildcardReply_flipAt_false_iff p.1 S z p.2 hx).1 hy⟩
  have hpoint (p : BitStr n × Fin n) :
      (if wildcardReply p.1 S z ≠ wildcardReply (flipAt p.1 p.2) S z then
        2 * Real.sqrt (N p.1) * Real.sqrt (N (flipAt p.1 p.2)) else 0) =
        2 * G p + 2 * G (e p) := by
    have he : e p = (flipAt p.1 p.2, p.2) := rfl
    rw [he]
    dsimp only [G]
    simp only [hmem, flipAt_flipAt]
    cases wildcardReply p.1 S z <;>
      cases wildcardReply (flipAt p.1 p.2) S z <;> simp <;> ring
  have hG : (∑ p, G p) =
      ∑ p ∈ E, Real.sqrt (N p.1) * Real.sqrt (N (flipAt p.1 p.2)) := by
    simp only [G]
    rw [← Finset.sum_filter]
    simp
  have horient :
      (∑ x : BitStr n, ∑ j : Fin n,
        if wildcardReply x S z ≠ wildcardReply (flipAt x j) S z then
          2 * Real.sqrt (N x) * Real.sqrt (N (flipAt x j)) else 0) =
      4 * (∑ p ∈ E, Real.sqrt (N p.1) * Real.sqrt (N (flipAt p.1 p.2))) := by
    rw [(Fintype.sum_prod_type' _).symm]
    calc
      _ = ∑ p, (2 * G p + 2 * G (e p)) :=
        Finset.sum_congr rfl (fun p _ => hpoint p)
      _ = 4 * ∑ p, G p := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, e.sum_comp G]
        ring
      _ = _ := by rw [hG]
  have hout : ∀ x ∈ A, ∀ j ∈ S, flipAt x j ∉ A := by
    intro x hx j hj hy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    have hf := (wildcardReply_flipAt_false_iff x S z j hx').2 hj
    simp_all
  have hstar := star_four_sum_le A S (fun x j => flipAt x j) N hN
    (wildcard_star_inj S z) hout
  have hcard : (S.card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show S.card ≤ n by simpa using Finset.card_le_univ S)
  have hmass : 0 ≤ ∑ x, N x := Finset.sum_nonneg (fun x _ => hN x)
  calc
    _ = 4 * (∑ p ∈ E, Real.sqrt (N p.1) * Real.sqrt (N (flipAt p.1 p.2))) := horient
    _ ≤ 2 * Real.sqrt (S.card : ℝ) * ∑ x, N x := hstar
    _ ≤ 2 * Real.sqrt (n : ℝ) * ∑ x, N x := by
      nlinarith only [mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hcard) hmass]

private theorem reply_inner_change_le (f g : Bool → ℂ) (a b : Bool) :
    |(∑ t : Bool, ((starRingEnd ℂ) (f (t != a)) * g (t != b)).re) -
      ∑ t : Bool, ((starRingEnd ℂ) (f t) * g t).re| ≤
      if a ≠ b then
        2 * Real.sqrt (∑ t : Bool, ‖f t‖ ^ 2) * Real.sqrt (∑ t : Bool, ‖g t‖ ^ 2)
      else 0 := by
  have hmass (v : Bool → ℂ) (c : Bool) :
      MeasureProb (fun t => v (t != c)) Finset.univ = ∑ t : Bool, ‖v t‖ ^ 2 := by
    cases c <;> simp [MeasureProb, BornProb, add_comm]
  by_cases h : a = b
  · subst b
    cases a <;> simp [add_comm]
  · simp only [ne_eq, h, not_false_eq_true, ↓reduceIte]
    have h₁ := event_inner_abs_le Finset.univ (fun t => f (t != a)) (fun t => g (t != b))
    have h₂ := event_inner_abs_le Finset.univ f g
    rw [hmass f a, hmass g b] at h₁
    dsimp only [MeasureProb, BornProb] at h₂
    rw [Real.sqrt_mul (Finset.sum_nonneg (fun t _ => sq_nonneg ‖f t‖))] at h₁ h₂
    calc
      _ ≤ |∑ t : Bool, ((starRingEnd ℂ) (f (t != a)) * g (t != b)).re| +
          |∑ t : Bool, ((starRingEnd ℂ) (f t) * g t).re| := abs_sub _ _
      _ ≤ _ := by linarith only [h₁, h₂]

private theorem sum_register {n r : ℕ} (f : WildcardReg n r → ℝ) :
    (∑ p, f p) = ∑ S, ∑ z, ∑ w, ∑ b : Bool, f ((S, z, b), w) := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro z _
  exact Finset.sum_comm

private theorem sum_pair_comm {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  rw [(Fintype.sum_prod_type' (fun a b => ∑ c, f a b c)).symm, Finset.sum_comm]
  simp only [Fintype.sum_prod_type]

private theorem wildcard_query_change_le {n r : ℕ}
    (u : BitStr n → QState (WildcardReg n r)) :
    |(∑ x : BitStr n, ∑ j : Fin n,
        (Inner (ApplyGate (wildcardOracle n r x) (u x))
          (ApplyGate (wildcardOracle n r (flipAt x j)) (u (flipAt x j)))).re) -
      (∑ x : BitStr n, ∑ j : Fin n, (Inner (u x) (u (flipAt x j))).re)| ≤
      2 * Real.sqrt (n : ℝ) * ∑ x, branchMass (u x) := by
  classical
  let D := fun S z w (x : BitStr n) (j : Fin n) =>
    (∑ b : Bool, ((starRingEnd ℂ)
      (u x ((S, z, b != wildcardReply x S z), w)) *
      u (flipAt x j) ((S, z, b != wildcardReply (flipAt x j) S z), w)).re) -
    ∑ b : Bool, ((starRingEnd ℂ) (u x ((S, z, b), w)) *
      u (flipAt x j) ((S, z, b), w)).re
  let N := fun S z w (x : BitStr n) => ∑ b : Bool, ‖u x ((S, z, b), w)‖ ^ 2
  have hsplit :
      (∑ x : BitStr n, ∑ j : Fin n,
        (Inner (ApplyGate (wildcardOracle n r x) (u x))
          (ApplyGate (wildcardOracle n r (flipAt x j)) (u (flipAt x j)))).re) -
      (∑ x : BitStr n, ∑ j : Fin n, (Inner (u x) (u (flipAt x j))).re) =
        ∑ S, ∑ z, ∑ w, ∑ x, ∑ j, D S z w x j := by
    calc
      _ = ∑ x, ∑ j, ∑ S, ∑ z, ∑ w, D S z w x j := by
        simp only [inner_apply, Complex.re_sum, sum_register, wildcardOracle_apply,
          oracleFlip, D, Finset.sum_sub_distrib]
      _ = _ := by
        rw [sum_pair_comm]
        apply Finset.sum_congr rfl; intro S _
        rw [sum_pair_comm]
        apply Finset.sum_congr rfl; intro z _
        exact sum_pair_comm _
  rw [hsplit]
  calc
    _ ≤ ∑ S, ∑ z, ∑ w, ∑ x, ∑ j, |D S z w x j| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum; intro S _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum; intro z _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum; intro w _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum; intro x _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S, ∑ z, ∑ w, 2 * Real.sqrt (n : ℝ) * ∑ x, N S z w x := by
      apply Finset.sum_le_sum; intro S _
      apply Finset.sum_le_sum; intro z _
      apply Finset.sum_le_sum; intro w _
      exact (Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun j _ =>
        reply_inner_change_le (fun b => u x ((S, z, b), w))
          (fun b => u (flipAt x j) ((S, z, b), w))
          (wildcardReply x S z) (wildcardReply (flipAt x j) S z)))).trans
        (wildcard_disagreement_sum_le S z (N S z w)
          (fun x => Finset.sum_nonneg (fun b _ => sq_nonneg _)))
    _ = _ := by
      simp only [← Finset.mul_sum]
      congr 1
      have hcomm (S : Finset (Fin n)) (z : BitStr n) :
          (∑ w, ∑ x, N S z w x) = ∑ x, ∑ w, N S z w x := Finset.sum_comm
      simp_rw [hcomm]
      rw [sum_pair_comm]
      apply Finset.sum_congr rfl; intro x _
      exact (sum_register (fun p => ‖u x p‖ ^ 2)).symm

private theorem inner_collapse_partition {I : Type} [Fintype I] [DecidableEq I]
    (v w : QState I) {k : ℕ} (label : I → Fin k) :
    (∑ o : Fin k, (Inner
      (Collapse v (Finset.univ.filter (fun i => label i = o)))
      (Collapse w (Finset.univ.filter (fun i => label i = o))))).re = (Inner v w).re := by
  have hfiber (o : Fin k) : Inner
      (Collapse v (Finset.univ.filter (fun i => label i = o)))
      (Collapse w (Finset.univ.filter (fun i => label i = o))) =
      ∑ i, if label i = o then (starRingEnd ℂ) (v i) * w i else 0 := by
    rw [inner_apply]
    apply Finset.sum_congr rfl; intro i _
    by_cases h : label i = o <;> simp [collapse_apply, h]
  simp_rw [hfiber]
  rw [Finset.sum_comm, inner_apply]
  congr 1
  apply Finset.sum_congr rfl; intro i _
  simp

private theorem inner_projector_pair {I : Type} [Fintype I] {A : Matrix I I ℂ}
    (hA : IsOrthogonalProjector A) (v w : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (ApplyGate A v) (ApplyGate A w) =
      Qatlib.Foundations.PureStateMath.Inner v (ApplyGate A w) := by
  have hAA : A.conjTranspose * A = A := by
    rw [← Matrix.star_eq_conjTranspose, hA.2]
    exact hA.1
  simp only [Qatlib.Foundations.PureStateMath.Inner, ApplyGate]
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hAA,
    Matrix.dotProduct_mulVec]

private theorem inner_projective_pair {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℂ} (hA : IsOrthogonalProjector A) (v w : QState I) :
    (Qatlib.Foundations.PureStateMath.Inner (ApplyGate (1 - A) v) (ApplyGate (1 - A) w)).re +
      (Qatlib.Foundations.PureStateMath.Inner (ApplyGate A v) (ApplyGate A w)).re =
      (Qatlib.Foundations.PureStateMath.Inner v w).re := by
  rw [← Complex.add_re, inner_projector_pair (isOrthogonalProjector_compl hA),
    inner_projector_pair hA]
  have hadd (a b : QState I) :
      Qatlib.Foundations.PureStateMath.Inner v a + Qatlib.Foundations.PureStateMath.Inner v b =
        Qatlib.Foundations.PureStateMath.Inner v (a + b) := by
    simp only [inner_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [hadd]
  have hsum : ApplyGate (1 - A) w + ApplyGate A w = w := by
    simp [ApplyGate, Matrix.sub_mulVec]
  rw [hsum]

private def inputProgress {n : ℕ} {I : Type} [Fintype I]
    (u : BitStr n → QState I) : ℝ :=
  ∑ x, ∑ j, (Qatlib.Foundations.PureStateMath.Inner (u x) (u (flipAt x j))).re

private def wildcardProgress {n r : ℕ} (P : ObservedCircuit (WildcardReg n r))
    (u : BitStr n → QState (WildcardReg n r)) : ℝ :=
  ∑ x, ∑ j, pairIP (wildcardOracle n r x) (wildcardOracle n r (flipAt x j))
    P (u x) (u (flipAt x j))

private theorem coeff_nonneg {n r : ℕ} (u : BitStr n → QState (WildcardReg n r)) :
    0 ≤ 2 * Real.sqrt (n : ℝ) * ∑ x, branchMass (u x) :=
  mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    (Finset.sum_nonneg (fun _ _ => measureProb_nonneg _ _))

private theorem wildcard_tree_change_le {n r : ℕ}
    (P : ObservedCircuit (WildcardReg n r)) (hP : observedWellFormed P)
    (u : BitStr n → QState (WildcardReg n r)) :
    |wildcardProgress P u - inputProgress u| ≤
      2 * Real.sqrt (n : ℝ) * (∑ x, branchMass (u x)) * (observedQueryDepth P : ℝ) := by
  classical
  induction P generalizing u with
  | halt acc => simp [wildcardProgress, inputProgress, pairIP, observedQueryDepth]
  | step s Q ih =>
    cases s with
    | gate U =>
      have hmass : (∑ x, branchMass (ApplyGate U (u x))) = ∑ x, branchMass (u x) :=
        Finset.sum_congr rfl (fun x _ => measureProb_applyGate_univ hP.1 (u x))
      simpa only [wildcardProgress, inputProgress, pairIP, inner_applyGate hP.1,
        observedQueryDepth, hmass] using ih hP.2 (fun x => ApplyGate U (u x))
    | query =>
      let v := fun x => ApplyGate (wildcardOracle n r x) (u x)
      have hmass : (∑ x, branchMass (v x)) = ∑ x, branchMass (u x) :=
        Finset.sum_congr rfl (fun x _ =>
          measureProb_applyGate_univ (wildcardOracle_unitary x) (u x))
      change |wildcardProgress Q v - inputProgress u| ≤ _
      calc
        _ ≤ |wildcardProgress Q v - inputProgress v| + |inputProgress v - inputProgress u| :=
          abs_sub_le _ _ _
        _ ≤ 2 * Real.sqrt (n : ℝ) * (∑ x, branchMass (v x)) *
            (observedQueryDepth Q : ℝ) +
            2 * Real.sqrt (n : ℝ) * ∑ x, branchMass (u x) :=
          add_le_add (ih hP v) (wildcard_query_change_le u)
        _ = _ := by rw [hmass]; simp only [observedQueryDepth, Nat.cast_add, Nat.cast_one]; ring
  | measure k label next ih =>
    let v := fun o x => Collapse (u x) (Finset.univ.filter (fun i => label i = o))
    have hi : (∑ o, inputProgress (v o)) = inputProgress u := by
      unfold inputProgress
      rw [← sum_pair_comm]
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro j _
      exact (Complex.re_sum _ _).symm.trans (inner_collapse_partition _ _ label)
    have hw : wildcardProgress (.measure k label next) u =
        ∑ o, wildcardProgress (next o) (v o) := by
      unfold wildcardProgress
      simp only [pairIP]
      exact sum_pair_comm _
    have hm : (∑ o, ∑ x, branchMass (v o x)) = ∑ x, branchMass (u x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro x _
      exact sum_measureProb_collapse_partition (u x) label
    have hd (o : Fin k) : observedQueryDepth (next o) ≤
        observedQueryDepth (.measure k label next) := by
      simp only [observedQueryDepth_eq_budget, observedQueryBudget]
      exact Finset.le_sup (f := fun o' => observedQueryBudget (next o')) (Finset.mem_univ o)
    rw [hw, ← hi, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ o, |wildcardProgress (next o) (v o) - inputProgress (v o)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ o, 2 * Real.sqrt (n : ℝ) * (∑ x, branchMass (v o x)) *
          (observedQueryDepth (.measure k label next) : ℝ) := by
        apply Finset.sum_le_sum; intro o _
        exact (ih o (hP o) (v o)).trans (mul_le_mul_of_nonneg_left
          (Nat.cast_le.mpr (hd o)) (coeff_nonneg (v o)))
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum, hm]
  | project A Q₁ Q₂ ih₁ ih₂ =>
    let v := fun x => ApplyGate (1 - A) (u x)
    let w := fun x => ApplyGate A (u x)
    have hi : inputProgress v + inputProgress w = inputProgress u := by
      simp only [inputProgress, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro j _
      exact inner_projective_pair hP.1 _ _
    have hw : wildcardProgress (.project A Q₁ Q₂) u =
        wildcardProgress Q₁ v + wildcardProgress Q₂ w := by
      simp only [wildcardProgress, pairIP, Finset.sum_add_distrib, v, w]
    have hm : (∑ x, branchMass (v x)) + (∑ x, branchMass (w x)) =
        ∑ x, branchMass (u x) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun x _ => projectiveBranchMass_add hP.1 (u x))
    have h₁ := (ih₁ hP.2.1 v).trans (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (le_max_left (observedQueryDepth Q₁) (observedQueryDepth Q₂)))
      (coeff_nonneg v))
    have h₂ := (ih₂ hP.2.2 w).trans (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (le_max_right (observedQueryDepth Q₁) (observedQueryDepth Q₂)))
      (coeff_nonneg w))
    rw [hw, ← hi]
    calc
      |(wildcardProgress Q₁ v + wildcardProgress Q₂ w) - (inputProgress v + inputProgress w)|
        = |(wildcardProgress Q₁ v - inputProgress v) +
            (wildcardProgress Q₂ w - inputProgress w)| := by congr 1; ring
      _ ≤ 2 * Real.sqrt (n : ℝ) * (∑ x, branchMass (v x)) *
            ((max (observedQueryDepth Q₁) (observedQueryDepth Q₂) : ℕ) : ℝ) +
          2 * Real.sqrt (n : ℝ) * (∑ x, branchMass (w x)) *
            ((max (observedQueryDepth Q₁) (observedQueryDepth Q₂) : ℕ) : ℝ) :=
        (abs_add_le _ _).trans (add_le_add h₁ h₂)
      _ = 2 * Real.sqrt (n : ℝ) * (∑ x, branchMass (u x)) *
            (observedQueryDepth (.project A Q₁ Q₂) : ℝ) := by
        simp only [observedQueryDepth]
        rw [← hm]
        ring

/-- **Lemma 6**: any program that solves search with wildcards on `n` bits with
worst-case success probability `2/3`, starting from the all-zero register, makes
`Ω(√n)` wildcard queries. -/
theorem lemma6_wildcard_query_lower_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n r : ℕ) (readOut : WildcardReg n (r + 1) → BitStr n)
        (P : ObservedCircuit (WildcardReg n (r + 1))),
        2 ≤ n → SolvesWildcardFrom n (r + 1) readOut P (Ket (zeroReg n r)) (2 / 3 : ℝ) →
        c * Real.sqrt (n : ℝ) ≤ (programQueries P : ℝ) := by
  classical
  refine ⟨1 / 40, by norm_num, ?_⟩
  intro n r readOut P hn ⟨hP, hsucc⟩
  let ψ₀ : QState (WildcardReg n (r + 1)) := Qatlib.Foundations.PureStateMath.Ket (zeroReg n r)
  let u : BitStr n → QState (WildcardReg n (r + 1)) := fun _ => ψ₀
  have hbm : branchMass ψ₀ = 1 := by
    simp only [branchMass, MeasureProb, BornProb, ψ₀, Qatlib.Foundations.PureStateMath.Ket]
    rw [Finset.sum_eq_single (zeroReg n r)]
    · simp
    · intro p _ hp; simp [hp]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  have hin : (Qatlib.Foundations.PureStateMath.Inner ψ₀ ψ₀).re = 1 := by
    rw [inner_apply]
    simp only [ψ₀, Qatlib.Foundations.PureStateMath.Ket]
    rw [Finset.sum_eq_single (zeroReg n r)]
    · simp
    · intro p _ hp; simp [hp]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  have hpair (x : BitStr n) (j : Fin n) :
      pairIP (wildcardOracle n (r + 1) x) (wildcardOracle n (r + 1) (flipAt x j))
        P ψ₀ ψ₀ ≤ 19 / 20 := by
    have hne : flipAt x j ≠ x := by
      intro heq
      have hd := hammingDist_flipAt x j
      rw [heq] at hd
      simp [hammingDist] at hd
    let lbl : Bool → WildcardReg n (r + 1) → Fin 3 := fun acc idx =>
      if acc = true ∧ readOut idx = x then 0
      else if acc = true ∧ readOut idx = flipAt x j then 1
      else 2
    let a : Fin 3 → ℝ := fun t =>
      eventMass (wildcardOracle n (r + 1) x) (fun acc idx => lbl acc idx = t) P ψ₀
    let b : Fin 3 → ℝ := fun t =>
      eventMass (wildcardOracle n (r + 1) (flipAt x j)) (fun acc idx => lbl acc idx = t) P ψ₀
    have ha_sum : a 0 + a 1 + a 2 = 1 := by
      have hp := eventMass_partition (wildcardOracle n (r + 1) x)
        (wildcardOracle_unitary x) lbl P hP ψ₀
      rw [Fin.sum_univ_three, hbm] at hp
      exact hp
    have hb_sum : b 0 + b 1 + b 2 = 1 := by
      have hp := eventMass_partition (wildcardOracle n (r + 1) (flipAt x j))
        (wildcardOracle_unitary (flipAt x j)) lbl P hP ψ₀
      rw [Fin.sum_univ_three, hbm] at hp
      exact hp
    have hl0 (acc : Bool) (idx : WildcardReg n (r + 1)) :
        (lbl acc idx = 0) ↔ (acc = true ∧ readOut idx = x) := by
      dsimp [lbl]
      by_cases h1 : acc = true ∧ readOut idx = x
      · simp [h1]
      · by_cases h2 : acc = true ∧ readOut idx = flipAt x j <;> simp [h1, h2]
    have hl1 (acc : Bool) (idx : WildcardReg n (r + 1)) :
        (lbl acc idx = 1) ↔ (acc = true ∧ readOut idx = flipAt x j) := by
      dsimp [lbl]
      by_cases h1 : acc = true ∧ readOut idx = x
      · simp [h1, Ne.symm hne]
      · by_cases h2 : acc = true ∧ readOut idx = flipAt x j
        · simp [h2]; exact hne
        · simp [h1, h2]
    have ha0 : (2 / 3 : ℝ) ≤ a 0 := by
      have heq : a 0 = programSuccessMass n (r + 1) readOut P ψ₀ x := by
        rw [successMass_eventMass]
        dsimp [a]
        simp only [hl0]
      rw [heq]
      exact hsucc x
    have hb1 : (2 / 3 : ℝ) ≤ b 1 := by
      have heq : b 1 = programSuccessMass n (r + 1) readOut P ψ₀ (flipAt x j) := by
        rw [successMass_eventMass]
        dsimp [b]
        simp only [hl1]
      rw [heq]
      exact hsucc (flipAt x j)
    have hle := pairIP_le_events (wildcardOracle n (r + 1) x)
      (wildcardOracle n (r + 1) (flipAt x j)) lbl P ψ₀ ψ₀
    rw [Fin.sum_univ_three] at hle
    exact hle.trans (three_event_gap
      (eventMass_nonneg _ _ P ψ₀) (eventMass_nonneg _ _ P ψ₀) (eventMass_nonneg _ _ P ψ₀)
      (eventMass_nonneg _ _ P ψ₀) (eventMass_nonneg _ _ P ψ₀) (eventMass_nonneg _ _ P ψ₀)
      ha_sum hb_sum ha0 hb1)
  let M : ℝ := (Fintype.card (BitStr n) : ℝ)
  have hMpos : 0 < M := Nat.cast_pos.mpr Fintype.card_pos
  have hin_u : inputProgress u = M * (n : ℝ) := by
    simp [inputProgress, u, hin, M, Finset.sum_const, nsmul_eq_mul]
  have hbm_u : (∑ x : BitStr n, branchMass (u x)) = M := by
    simp [u, hbm, M, Finset.sum_const, nsmul_eq_mul]
  have hwp : wildcardProgress P u ≤ M * ((n : ℝ) * (19 / 20)) := by
    unfold wildcardProgress
    calc
      (∑ x : BitStr n, ∑ j : Fin n,
          pairIP (wildcardOracle n (r + 1) x) (wildcardOracle n (r + 1) (flipAt x j))
            P (u x) (u (flipAt x j)))
        ≤ ∑ _x : BitStr n, ∑ _j : Fin n, (19 / 20 : ℝ) :=
          Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun j _ => hpair x j))
      _ = M * ((n : ℝ) * (19 / 20)) := by
        simp [M, Finset.sum_const, nsmul_eq_mul]
  have htree := wildcard_tree_change_le P hP u
  rw [hin_u, hbm_u] at htree
  have hgap : M * (n : ℝ) - wildcardProgress P u ≤
      2 * Real.sqrt (n : ℝ) * M * (programQueries P : ℝ) := by
    have habs : M * (n : ℝ) - wildcardProgress P u ≤
        |wildcardProgress P u - M * (n : ℝ)| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    exact habs.trans htree
  have hstep1 : (1 / 20 : ℝ) * (n : ℝ) * M ≤
      2 * Real.sqrt (n : ℝ) * (programQueries P : ℝ) * M := by
    linarith only [hwp, hgap]
  have hstep2 : (1 / 20 : ℝ) * (n : ℝ) ≤
      2 * Real.sqrt (n : ℝ) * (programQueries P : ℝ) :=
    le_of_mul_le_mul_right hstep1 hMpos
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn0
  nlinarith only [hstep2, hsqrt_pos, hsq]

end Qatlib.Papers.WildcardSrch12.MainResults.WildcardLowerBound
