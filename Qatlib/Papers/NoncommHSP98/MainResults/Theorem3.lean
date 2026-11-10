/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoncommHSP98.MainResults.MaxIdentify
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
set_option warningAsError false

namespace Qatlib.Papers.NoncommHSP98.MainResults

def mapDist {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (p : FinDist X) (f : X → Y) : FinDist Y := by
  classical
  exact
    { prob := fun y => evMass p (fun x => f x = y)
      nonneg := by
        intro y
        unfold evMass eventMass
        exact Finset.sum_nonneg fun x _ => p.nonneg x
      sum_one := by
        unfold evMass eventMass
        have h := Finset.sum_fiberwise (s := (Finset.univ : Finset X)) (g := f) (f := p.prob)
        rw [p.sum_one] at h
        rw [← h]
        refine Finset.sum_congr rfl ?_
        intro y _
        exact Finset.sum_congr
          (Finset.filter_congr_decidable (Finset.univ : Finset X) (fun x => f x = y) _)
          (fun x _ => rfl) }

def pointDist {Y : Type*} [Fintype Y] [DecidableEq Y] (y : Y) : FinDist Y where
  prob y' := if y' = y then 1 else 0
  nonneg y' := by by_cases h : y' = y <;> simp [h]
  sum_one := by
    classical
    simp [Finset.sum_ite_eq', Finset.mem_univ]

theorem eventMass_inst_eq {X : Type*} [Fintype X] (p : FinDist X) (E : X → Prop)
    (i1 i2 : DecidablePred E) :
    @eventMass X _ p E i1 = @eventMass X _ p E i2 := by
  have hi : i1 = i2 := funext fun x => Subsingleton.elim _ _
  exact congrArg (fun i => @eventMass X _ p E i) hi

noncomputable def probSingleC {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (E : X → Prop) : ℝ :=
  @probSingle X _ _ p E (Classical.decPred E)

theorem probSingle_inst_eq {X : Type*} [Fintype X] [DecidableEq X] (p : FinDist X)
    (E : X → Prop) (i1 i2 : DecidablePred E) :
    @probSingle X _ _ p E i1 = @probSingle X _ _ p E i2 := by
  have hi : i1 = i2 := funext fun x => Subsingleton.elim _ _
  exact congrArg (fun i => @probSingle X _ _ p E i) hi

theorem probSingle_eq_C {X : Type*} [Fintype X] [DecidableEq X] (p : FinDist X)
    (E : X → Prop) [DecidablePred E] : probSingle p E = probSingleC p E := by
  classical
  unfold probSingleC
  exact probSingle_inst_eq p E _ (Classical.decPred E)

theorem probSingle_eq_eventMass {X : Type*} [Fintype X] [DecidableEq X] (p : FinDist X)
    (E : X → Prop) (i : DecidablePred E) :
    @probSingle X _ _ p E i = @eventMass X _ p E i := rfl

theorem eventMass_mapDist {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (p : FinDist X) (f : X → Y) (y : Y)
    (i : DecidablePred (fun o => o = y)) :
    @eventMass Y _ (mapDist p f) (fun o => o = y) i = evMass p (fun x => f x = y) := by
  unfold eventMass mapDist
  rw [Finset.sum_eq_single y]
  · intro b hb hby
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact absurd hb hby
  · intro hy
    exact absurd (by simp) hy

theorem probSingleC_mapDist {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (p : FinDist X) (f : X → Y) (y : Y) :
    probSingleC (mapDist p f) (fun o => o = y) = evMass p (fun x => f x = y) := by
  classical
  unfold probSingleC
  rw [probSingle_eq_eventMass _ _ (Classical.decPred _)]
  exact eventMass_mapDist p f y (Classical.decPred _)

def bestK (N : ℕ) [NeZero N] (m : ℕ) (ω : Fin m → ZMod N) : ZMod N := by
  classical
  exact if h : (Candidates N).Nonempty then
    Classical.choose (Finset.exists_max_image (Candidates N)
      (fun k => ∑ i, cosPhase N k (ω i)) h)
  else 0

theorem bestK_mem {N : ℕ} [NeZero N] {m : ℕ} (ω : Fin m → ZMod N)
    (h : (Candidates N).Nonempty) : bestK N m ω ∈ Candidates N := by
  unfold bestK
  rw [dif_pos h]
  exact (Classical.choose_spec (Finset.exists_max_image (Candidates N)
    (fun k => ∑ i, cosPhase N k (ω i)) h)).1

theorem bestK_max {N : ℕ} [NeZero N] {m : ℕ} (ω : Fin m → ZMod N)
    (h : (Candidates N).Nonempty) :
    ∀ k ∈ Candidates N, ∑ i, cosPhase N k (ω i)
      ≤ ∑ i, cosPhase N (bestK N m ω) (ω i) := by
  unfold bestK
  rw [dif_pos h]
  exact (Classical.choose_spec (Finset.exists_max_image (Candidates N)
    (fun k => ∑ i, cosPhase N k (ω i)) h)).2

theorem bestK_eq_kRep {N : ℕ} [NeZero N] {m : ℕ} {k0 : ZMod N} (hk0 : k0 ≠ 0)
    {ω : Fin m → ZMod N}
    (hω : ∀ k ∈ Candidates N, k ≠ kRep N k0 →
      ∑ i, cosPhase N k (ω i) < ∑ i, cosPhase N (kRep N k0) (ω i))
    (hC : (Candidates N).Nonempty) : bestK N m ω = kRep N k0 := by
  classical
  have hb := bestK_mem (N := N) (m := m) ω hC
  have hmax := bestK_max (N := N) (m := m) ω hC
  by_contra hne
  have hlt := hω _ hb hne
  have hle := hmax _ (kRep_mem_Candidates hk0)
  linarith

def postproc (N : ℕ) [NeZero N] {R : Type*} (γ : DihPt N → R)
    (k : ZMod N) : Option (ZMod N) := by
  classical
  exact if γ (0, 0) = γ (k, 1) then some k
    else if γ (0, 0) = γ (-k, 1) then some (-k)
    else none

theorem postproc_eq_some_of_H2 {N : ℕ} [NeZero N] {R : Type*} {k0 k : ZMod N}
    {γ : DihPt N → R} (hγ : FulfillsDihedralPromise N (H2 N k0) γ)
    (hk : k = k0 ∨ k = -k0) : postproc N γ k = some k0 := by
  unfold postproc
  rcases hk with hk | hk
  · rw [if_pos ((promise_H2_test_iff hγ).mpr hk), hk]
  · rw [hk]
    by_cases h2 : -k0 = k0
    · rw [if_pos ((promise_H2_test_iff hγ).mpr h2)]
      rw [show (-k0) = k0 from h2]
    · rw [if_neg (fun hne => h2 ((promise_H2_test_iff hγ).mp hne))]
      have htest : γ (0, 0) = γ (-(-k0), 1) :=
        (promise_H2_test_iff hγ).mpr (by simp)
      rw [if_pos htest, neg_neg]

theorem postproc_eq_none_of_HTriv {N : ℕ} [NeZero N] {R : Type*} {γ : DihPt N → R}
    (hγ : FulfillsDihedralPromise N (HTriv N) γ) {k : ZMod N} (_hk : k ≠ 0) :
    postproc N γ k = none := by
  have hne : γ (0, 0) ≠ γ (k, 1) := by
    intro heq
    obtain ⟨h, hh, hmul⟩ := FulfillsDihedralPromise.coset_of_eq hγ heq
    rw [mem_HTriv] at hh
    subst hh
    simp [dihMul] at hmul
  have hne2 : γ (0, 0) ≠ γ (-k, 1) := by
    intro heq
    obtain ⟨h, hh, hmul⟩ := FulfillsDihedralPromise.coset_of_eq hγ heq
    rw [mem_HTriv] at hh
    subst hh
    simp [dihMul] at hmul
  unfold postproc
  rw [if_neg hne, if_neg hne2]

def hiddenK (N : ℕ) [NeZero N] (R : Type*) (γ : DihPt N → R) : Option (ZMod N) := by
  classical
  exact if h : ∃ k0 : ZMod N, k0 ≠ 0 ∧ FulfillsDihedralPromise N (H2 N k0) γ
    then some (Classical.choose h) else none

theorem hiddenK_eq_some {N : ℕ} [NeZero N] {R : Type*} {k0 : ZMod N} {γ : DihPt N → R}
    (hk0 : k0 ≠ 0) (hγ : FulfillsDihedralPromise N (H2 N k0) γ) :
    hiddenK N R γ = some k0 := by
  unfold hiddenK
  have h0 : ∃ k0 : ZMod N, k0 ≠ 0 ∧ FulfillsDihedralPromise N (H2 N k0) γ :=
    ⟨k0, hk0, hγ⟩
  rw [dif_pos h0]
  congr 1
  obtain ⟨hk0', hγ'⟩ := Classical.choose_spec h0
  exact (promise_H2_test_iff hγ).mp ((promise_H2_test_iff hγ').mpr rfl)

theorem hiddenK_eq_none {N : ℕ} [NeZero N] {R : Type*} {γ : DihPt N → R}
    (hγ : FulfillsDihedralPromise N (HTriv N) γ) : hiddenK N R γ = none := by
  classical
  unfold hiddenK
  rw [dif_neg (by
    rintro ⟨k0, hk0, hγ2⟩
    have htest : γ (0, 0) = γ (k0, 1) := (promise_H2_test_iff hγ2).mpr rfl
    obtain ⟨h, hh, hmul⟩ := FulfillsDihedralPromise.coset_of_eq hγ htest
    rw [mem_HTriv] at hh
    subst hh
    simp [dihMul] at hmul)]

def sampleCount (N : ℕ) : ℕ := 2 * Nat.ceil (64 * Real.log N)

def algDist (N : ℕ) [NeZero N] (R : Type*) (γ : DihPt N → R) :
    FinDist (Option (ZMod N)) :=
  match hiddenK N R γ with
  | some k0 => mapDist (independent (fun _ : Fin (sampleCount N) => zLaw N k0))
      (fun ω : Fin (sampleCount N) → ZMod N =>
        postproc N γ (bestK N (sampleCount N) ω))
  | none => pointDist none

def alg (N : ℕ) [NeZero N] (R : Type*) : DihAlgorithm N R where
  queries _ := sampleCount N + 5
  dist γ := algDist N R γ

theorem probSingleC_point_none {N : ℕ} [NeZero N] :
    probSingleC (pointDist (none : Option (ZMod N))) (fun o => o = none) = 1 := by
  classical
  unfold probSingleC probSingle pointDist
  simp

theorem probSingleC_algDist_HTriv {N : ℕ} [NeZero N] {R : Type*} {γ : DihPt N → R}
    (hγ : FulfillsDihedralPromise N (HTriv N) γ) :
    probSingleC (algDist N R γ) (fun o => o = none) = 1 := by
  unfold probSingleC
  unfold algDist
  rw [hiddenK_eq_none hγ]
  (try dsimp only)
  exact probSingleC_point_none

theorem le_sampleCount {N : ℕ} (h2N : 2 ≤ N) :
    64 * Real.log N ≤ (sampleCount N : ℝ) := by
  have hpos : 0 ≤ 64 * Real.log N := by
    have : 0 < Real.log N := Real.log_pos (by exact_mod_cast h2N)
    positivity
  have hle := Nat.le_ceil (64 * Real.log N)
  unfold sampleCount
  push_cast
  nlinarith [hle, Nat.zero_le (Nat.ceil (64 * Real.log N))]

theorem theorem5_evMass {N : ℕ} [NeZero N] (h2N : 2 ≤ N) {k0 : ZMod N}
    (hk0 : k0 ≠ 0) {m : ℕ} (hm : 64 * Real.log N ≤ (m : ℝ)) :
    1 - 1 / (2 * (N : ℝ)) ≤ evMass (independent (fun _ : Fin m => zLaw N k0))
      (fun ω : Fin m → ZMod N => ∀ k ∈ Candidates N, k ≠ kRep N k0 →
        ∑ i, cosPhase N k (ω i) < ∑ i, cosPhase N (kRep N k0) (ω i)) := by
  have h := theorem5_holds N h2N k0 hk0 m hm
  rw [probEvent_inst_eq (zLaw N k0) _ _ (Classical.decPred _),
    @probEvent_eq_eventMass_independent (ZMod N) _ _ (zLaw N k0) m _ (Classical.decPred _)]
    at h
  simpa [evMass] using! h

theorem probSingleC_algDist_H2 {N : ℕ} [NeZero N] {R : Type*} {k0 : ZMod N}
    (hk0 : k0 ≠ 0) (h2N : 2 ≤ N) {γ : DihPt N → R}
    (hγ : FulfillsDihedralPromise N (H2 N k0) γ) :
    1 - 1 / (2 * (N : ℝ)) ≤ probSingleC (algDist N R γ) (fun o => o = some k0) := by
  unfold probSingleC
  unfold algDist
  rw [hiddenK_eq_some hk0 hγ]
  (try dsimp only)
  rw [probSingle_eq_eventMass _ _ (Classical.decPred _)]
  rw [eventMass_mapDist _ _ _ (Classical.decPred _)]
  have hT5 := theorem5_evMass (N := N) h2N hk0 (m := sampleCount N) (le_sampleCount h2N)
  refine le_trans hT5 (evMass_mono _ (fun ω hω => ?_))
  have hC : (Candidates N).Nonempty := ⟨kRep N k0, kRep_mem_Candidates hk0⟩
  have hbk : bestK N (sampleCount N) ω = kRep N k0 := bestK_eq_kRep hk0 hω hC
  rw [hbk]
  exact postproc_eq_some_of_H2 hγ (kRep_eq_or N k0)

theorem queries_le {N : ℕ} [NeZero N] (h2N : 2 ≤ N) :
    (sampleCount N + 5 : ℝ) ≤ 89 * Real.log N / Real.log 2 + 7 := by
  have hlnN : 0 ≤ Real.log N := (Real.log_pos (by exact_mod_cast h2N)).le
  have hln2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hceil : (Nat.ceil (64 * Real.log N) : ℝ) < 64 * Real.log N + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hlog2 : 128 * Real.log 2 ≤ 89 := by
    nlinarith [Real.log_two_lt_d9]
  have hkey : 128 * Real.log N ≤ 89 * Real.log N / Real.log 2 := by
    rw [le_div_iff₀ hln2]
    nlinarith [hlog2, hlnN]
  unfold sampleCount
  push_cast
  linarith

theorem theorem3_holds : Theorem3Statement := by
  intro N hN R h2N
  refine ⟨alg N R, ?_, ?_, ?_⟩
  · intro γ
    simpa [alg] using! queries_le h2N
  · intro γ hγ
    rw [probSingle_eq_C]
    exact probSingleC_algDist_HTriv hγ
  · intro k0 hk0 γ hγ
    rw [probSingle_eq_C]
    exact probSingleC_algDist_H2 hk0 h2N hγ

end Qatlib.Papers.NoncommHSP98.MainResults
