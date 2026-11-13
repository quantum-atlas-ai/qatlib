/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.FreshValidationCheckerQuan
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkRealBudget
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.Theorem4Stat
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkContracts
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkContractsClassical
import Qatlib.Concepts.WalkSearch.CollisionSearch.Theorem3Quan

/-!
# Corrected triangle-search guarantees

This module proves soundness, a finite-seed failure bound, and an explicit cost bound for
`th4Alg`, culminating in `theorem4_answer` for the corrected contract `Theorem4`. The proof
combines least-power parameter choices with the checker using fresh validation seeds and a real
cost bound proportional to n^(13/10) with logarithmic factors.

It also constructs zero-cost search contracts and proves `theorem4_rounding_obstruction`, which
refutes the original `theorem4` parameter window. The triangle-search setting follows
[Ambainis2005].

## Main statements

* `th4Alg_sound`: any returned triple has distinct vertices and the required edges.
* `th4Alg_complete`: the number of failing seed pairs satisfies the stated bound.
* `theorem4_answer`: the corrected triangle-search contract holds.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.WalkSearch.CollisionSearch

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms
open scoped Classical

/-- A noisy-search interface with a single seed, zero charge, and zero failure exponent that
always returns `none`. -/
def nullNoisySearch : NoisySearch where
  seed := Unit
  seedFin := inferInstance
  seedNe := inferInstance
  cExp := 0
  κ := 0
  run := fun {_N} _marked _test _tcost _floor _ρ => none
  cost := fun {_N} _marked _test _tcost _floor _ρ => 0
  sound := by intro N marked test tcost floor ρ v h; cases h
  reject := by intros; rfl
  finds := by intros; simp
  charges := by intros; simp

/-- A safe Grover-search interface with a single seed, zero charge, and zero failure exponent
that always returns `none`. -/
def nullSafeGrover : SafeGrover where
  seed := Unit
  seedFin := inferInstance
  seedNe := inferInstance
  cExp := 0
  κ := 0
  run := fun {_N} _marked _check _floor _ρ => none
  cost := fun {_N} _marked _check _floor _ρ => 0
  sound := by intro N marked check floor ρ x h; cases h
  reject := by intros; rfl
  finds := by intros; simp
  charges := by intros; simp

/-- No positive natural number has its fifth power between 8 and 24 inclusive. -/
theorem theorem4_no_subset_size_at_two :
    ¬ ∃ r : ℕ, 1 ≤ r ∧ 8 ≤ r * r * r * r * r ∧ r * r * r * r * r ≤ 24 := by
  rintro ⟨r, _, hlo, hhi⟩
  by_cases hr : r ≤ 1
  · have hp : r ^ 5 ≤ 1 ^ 5 := Nat.pow_le_pow_left hr 5
    nlinarith
  · have hr2 : 2 ≤ r := by omega
    have hp : 2 ^ 5 ≤ r ^ 5 := Nat.pow_le_pow_left hr2 5
    nlinarith

/-- The original `theorem4` contract is false because its subset-size window has no solution at
`n = 2`. -/
theorem theorem4_rounding_obstruction : ¬ theorem4 := by
  intro h
  obtain ⟨r, r', hr, hlo, hhi, _⟩ := h 2 (by norm_num) (fun _ _ => false)
    (nullKCollisionSolver 0) nullNoisySearch nullSafeGrover
  exact theorem4_no_subset_size_at_two ⟨r, hr, by norm_num at hlo; exact hlo,
    by norm_num at hhi; exact hhi⟩

/-- The zero-cost collision and noisy-search interfaces satisfy `triCheckSpec` for every
adjacency predicate, subset, and choice of checker parameters. -/
theorem triCheckSpec_null {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
    (r' c₀ : ℕ) : triCheckSpec adj U (nullKCollisionSolver 0) nullNoisySearch r' c₀ := by
  simp [triCheckSpec, triCheck, cCOf, nullKCollisionSolver, nullNoisySearch]

/-- The Boolean predicate selecting vertices distinct from both entries of `t` and adjacent from
each of them. -/
def walkThird {n : ℕ} (adj : Fin n → Fin n → Bool) (t : Fin 2 → Fin n) : Fin n → Bool :=
  fun w => decide (w ≠ t 0 ∧ w ≠ t 1 ∧ adj (t 0) w ∧ adj (t 1) w)

/-- Expands `th4Alg` into collision search followed by safe Grover search with predicate
`walkThird`, including its validation branches and accumulated costs. -/
theorem th4Alg_eq {n : ℕ} (adj : Fin n → Fin n → Bool)
    (kcs : KCollisionSolver) (ncs : NoisySearch) (sgs : SafeGrover) (r r' c₀ : ℕ)
    (stape : ℕ → kcs.seed) (gtape : ℕ → sgs.seed) :
    th4Alg adj kcs ncs sgs r r' c₀ stape gtape =
    match kcs.run (n := n) (k := 2) r (triRel adj) (r*r) r (cCOf kcs ncs n r r' c₀) (stape 0) with
    | some t =>
      match sgs.run (N := n) (walkThird adj t) 3 n (gtape 0) with
      | some w =>
        if adj (t 0) (t 1) && adj (t 0) w && adj (t 1) w then
          (some (t 0,t 1,w),kcs.cost (n := n) (k := 2) r (triRel adj) (r*r) r (cCOf kcs ncs n r r' c₀) (stape 0)+
            sgs.cost (N := n) (walkThird adj t) 3 n (gtape 0)+3)
        else (none,kcs.cost (n := n) (k := 2) r (triRel adj) (r*r) r (cCOf kcs ncs n r r' c₀) (stape 0)+
            sgs.cost (N := n) (walkThird adj t) 3 n (gtape 0)+3)
      | none => (none,kcs.cost (n := n) (k := 2) r (triRel adj) (r*r) r (cCOf kcs ncs n r r' c₀) (stape 0)+
          sgs.cost (N := n) (walkThird adj t) 3 n (gtape 0))
    | none => (none,kcs.cost (n := n) (k := 2) r (triRel adj) (r*r) r (cCOf kcs ncs n r r' c₀) (stape 0)) := rfl

/-- For a loopless adjacency predicate, a pair satisfying `triRel` has a third vertex satisfying
`walkThird`. -/
theorem walkThird_exists {n : ℕ} (adj : Fin n → Fin n → Bool)
    (hl : ∀ a, adj a a = false) (t : Fin 2 → Fin n) (ht : triRel adj t = true) :
    ∃ w, walkThird adj t w = true := by
  simp only [triRel,decide_eq_true_eq] at ht
  obtain ⟨_,_,w,h0,h1⟩ := ht
  refine ⟨w,?_⟩
  simp only [walkThird,decide_eq_true_eq]
  refine ⟨?_,?_,h0,h1⟩
  · intro h; subst w; simp [hl] at h0
  · intro h; subst w; simp [hl] at h1

/-- A pair satisfying `triRel` and a vertex satisfying `walkThird` pass the three-edge Boolean
validation. -/
theorem walkThird_validation {n : ℕ} (adj : Fin n → Fin n → Bool)
    (t : Fin 2 → Fin n) (w : Fin n) (ht : triRel adj t = true)
    (hw : walkThird adj t w = true) :
    (adj (t 0) (t 1) && adj (t 0) w && adj (t 1) w) = true := by
  simp only [triRel,decide_eq_true_eq] at ht
  simp only [walkThird,decide_eq_true_eq] at hw
  simp [ht.2.1,hw.2.2.1,hw.2.2.2]

/-- Every triple returned by `th4Alg` consists of three distinct vertices with all three
specified adjacency values equal to `true`. -/
theorem th4Alg_sound {n : ℕ} (adj : Fin n → Fin n → Bool)
    (kcs : KCollisionSolver) (ncs : NoisySearch) (sgs : SafeGrover) (r r' c₀ : ℕ)
    (stape : ℕ → kcs.seed) (gtape : ℕ → sgs.seed) :
    (match th4Alg adj kcs ncs sgs r r' c₀ stape gtape with
    | (some (a,b,c),_) => a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      adj a b = true ∧ adj a c = true ∧ adj b c = true
    | (none,_) => True) := by
  cases hk : kcs.run r (triRel adj) (r*r) r (cCOf kcs ncs n r r' c₀) (stape 0) with
  | none => simp only [th4Alg_eq,hk]
  | some t =>
    have ht := kcs.sound r (triRel adj) (r*r) r (cCOf kcs ncs n r r' c₀) (stape 0) hk
    cases hg : sgs.run (walkThird adj t) 3 n (gtape 0) with
    | none => simp only [th4Alg_eq,hk,hg]
    | some w =>
      have hw := sgs.sound (walkThird adj t) 3 n (gtape 0) hg
      have hv := walkThird_validation adj t w ht hw
      simp only [triRel,decide_eq_true_eq] at ht
      simp only [walkThird,decide_eq_true_eq] at hw
      simpa only [th4Alg_eq,hk,hg,hv,if_true] using
        (show t 0 ≠ t 1 ∧ t 1 ≠ w ∧ t 0 ≠ w ∧
          adj (t 0) (t 1) = true ∧ adj (t 0) w = true ∧ adj (t 1) w = true from
          ⟨ht.1,hw.2.1.symm,hw.1.symm,ht.2.1,hw.2.2.1,hw.2.2.2⟩)

/-- Bounds the recorded cost of `th4Alg` by the collision-search charge, the safe Grover-search
charge, and three final validation queries. -/
theorem th4Alg_cost_le {n : ℕ} (adj : Fin n → Fin n → Bool)
    (kcs : KCollisionSolver) (ncs : NoisySearch) (sgs : SafeGrover) (r r' c₀ : ℕ)
    (stape : ℕ → kcs.seed) (gtape : ℕ → sgs.seed) :
    (th4Alg adj kcs ncs sgs r r' c₀ stape gtape).2 ≤
      kcs.κ*(Nat.log 2 (n+1)+2)*(r*r+(n/r)*(cCOf kcs ncs n r r' c₀+Nat.sqrt r*r))+
      sgs.κ*(Nat.log 2 (n+1)+2)*4*(Nat.sqrt (n+1)+1)+3 := by
  have hc := kcs.charges r (triRel adj) (r*r) r (cCOf kcs ncs n r r' c₀) (stape 0)
  norm_num only [show 2/2=1 by decide,Nat.pow_one] at hc
  cases hk : kcs.run r (triRel adj) (r*r) r (cCOf kcs ncs n r r' c₀) (stape 0) with
  | none => simp only [th4Alg_eq,hk]; omega
  | some t =>
    have hg := sgs.charges (walkThird adj t) 3 n (gtape 0)
    simp only [max_self,show 3+1=4 by decide] at hg
    cases hs : sgs.run (walkThird adj t) 3 n (gtape 0) with
    | none => simp only [th4Alg_eq,hk,hs]; omega
    | some w =>
      simp only [th4Alg_eq,hk,hs]
      split <;> (try dsimp only) <;> omega

/-- If the loopless adjacency predicate has a pair satisfying `triRel`, the number of seed pairs
for which `th4Alg` fails, multiplied by `(n + 1)` to the smaller failure exponent, is at
most twice the total number of seed pairs. -/
theorem th4Alg_complete {n : ℕ} (adj : Fin n → Fin n → Bool)
    (hl : ∀ a, adj a a = false)
    (kcs : KCollisionSolver) (ncs : NoisySearch) (sgs : SafeGrover) (r r' c₀ : ℕ)
    (hex : ∃ t, triRel adj t = true) :
    haveI := kcs.seedFin
    haveI := sgs.seedFin
    (Finset.univ.filter fun ρ : kcs.seed × sgs.seed =>
      (th4Alg adj kcs ncs sgs r r' c₀ (fun _ => ρ.1) (fun _ => ρ.2)).1 = none).card *
        (n+1)^(min kcs.cExp sgs.cExp) ≤ 2*Fintype.card (kcs.seed × sgs.seed) := by
  letI := kcs.seedFin
  letI := sgs.seedFin
  let run := kcs.run r (triRel adj) (r*r) r (cCOf kcs ncs n r r' c₀)
  let B := (n+1)^(min kcs.cExp sgs.cExp)
  let C := Fintype.card sgs.seed
  have hB : B ≤ (n+1)^kcs.cExp := Nat.pow_le_pow_right (by omega) (Nat.min_le_left _ _)
  have hB' : B ≤ (n+1)^sgs.cExp := Nat.pow_le_pow_right (by omega) (Nat.min_le_right _ _)
  have houter : (Finset.univ.filter fun ρ : kcs.seed => run ρ = none).card * B ≤ Fintype.card kcs.seed :=
    (Nat.mul_le_mul_left _ hB).trans (kcs.finds r (triRel adj) (r*r) r _ hex)
  have hfiber (ρk : kcs.seed) :
      (Finset.univ.filter fun ρg : sgs.seed =>
        (th4Alg adj kcs ncs sgs r r' c₀ (fun _ => ρk) (fun _ => ρg)).1 = none).card * B ≤
      (if run ρk = none then C*B else 0) + C := by
    cases hk : run ρk with
    | none =>
      have hc : (Finset.univ.filter fun ρg : sgs.seed =>
        (th4Alg adj kcs ncs sgs r r' c₀ (fun _ => ρk) (fun _ => ρg)).1 = none).card ≤ C :=
        Finset.card_le_univ _
      exact (Nat.mul_le_mul_right _ hc).trans (Nat.le_add_right _ _)
    | some t =>
      have ht := kcs.sound r (triRel adj) (r*r) r (cCOf kcs ncs n r r' c₀) ρk hk
      have he := walkThird_exists adj hl t ht
      have hc := sgs.finds (walkThird adj t) 3 n he
      simp only [max_self] at hc
      have heq : (Finset.univ.filter fun ρg : sgs.seed =>
        (th4Alg adj kcs ncs sgs r r' c₀ (fun _ => ρk) (fun _ => ρg)).1 = none) =
        Finset.univ.filter fun ρg : sgs.seed => sgs.run (walkThird adj t) 3 n ρg = none := by
        ext ρg
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        cases hg : sgs.run (walkThird adj t) 3 n ρg with
        | none => simp only [th4Alg_eq,show kcs.run r (triRel adj) (r*r) r (cCOf kcs ncs n r r' c₀) ρk = some t from hk,hg]
        | some w =>
          have hw := sgs.sound (walkThird adj t) 3 n ρg hg
          have hv := walkThird_validation adj t w ht hw
          simp only [th4Alg_eq,show kcs.run r (triRel adj) (r*r) r (cCOf kcs ncs n r r' c₀) ρk = some t from hk,hg,hv,if_true,Option.some_ne_none]
      rw [heq]
      simp only [Option.some_ne_none,if_false,zero_add]
      exact (Nat.mul_le_mul_left _ hB').trans hc
  have hsum := Finset.sum_le_sum (fun ρk (_ : ρk ∈ (Finset.univ : Finset kcs.seed)) => hfiber ρk)
  have hindicator : (∑ ρk : kcs.seed, if run ρk = none then C*B else 0) =
      (Finset.univ.filter fun ρk : kcs.seed => run ρk = none).card * (C*B) := by
    rw [← Finset.sum_filter]
    simp [Finset.sum_const]
  rw [Finset.sum_add_distrib,hindicator,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  have hfirst := Nat.mul_le_mul_right C houter
  rw [filter_product_card_sum_fst,Finset.sum_mul]
  simp only [Fintype.card_prod]
  change _ ≤ 2*(Fintype.card kcs.seed*C)
  dsimp only [B] at hsum hfirst
  simp only [Nat.cast_id] at hsum
  nlinarith only [hsum,hfirst]

/-- Establishes the corrected triangle-search contract `Theorem4`, including fresh validation,
soundness, a failure-count bound, and the n^(13/10) cost bound with explicit constants and
logarithmic factors; see [Ambainis2005]. -/
theorem theorem4_answer : Theorem4 := by
  intro n hn adj _hs hl kcs ncs sgs hk _hnc _hsg
  obtain ⟨r,hr,hlo,hhi⟩ := correctedSubsetWindow (n^3) 5 (pow_pos hn _) (by decide)
  obtain ⟨r',hr',hlo',hhi'⟩ := correctedSubsetWindow (r^2) 3 (pow_pos hr _) (by decide)
  refine ⟨r,r',hr,by simpa [pow_succ] using hlo,by simpa [pow_succ] using hhi,
    hr',by simpa [pow_two] using hlo',by simpa [pow_two] using hhi',
    freshValidationChecker_answer n adj Finset.univ kcs ncs r' 4,
    th4Alg_sound adj kcs ncs sgs r r' 4,?_,?_⟩
  · exact th4Alg_complete adj hl kcs ncs sgs r r' 4
  · intro stape gtape
    exact (show ((th4Alg adj kcs ncs sgs r r' 4 stape gtape).2 : ℝ) ≤ _ by
      exact_mod_cast th4Alg_cost_le adj kcs ncs sgs r r' 4 stape gtape).trans
        (walk_real_budget n r r' hn hr hr' hlo hhi hlo' hhi' kcs ncs sgs hk)

end Qatlib.Concepts.WalkSearch.WalkAlgorithms
