/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PolyMethod01.MainResults.QueryComparisonSourceContinuationDefs
import Mathlib.Tactic.Linarith
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs.Coin

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.PolyMethod01.MainResults

open Matrix
open Qatlib
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open scoped Classical BigOperators ENNReal

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

theorem run_eq_of_not_queried {I : Type} [DecidableEq I] {Output : Type}
    (t : BoolQueryTree I Output) (g g' : I → Bool) (i : I)
    (hi : i ∉ queriedSet t g) (hagree : ∀ j, j ≠ i → g j = g' j) :
    (BoolQueryTree.Run g t).1 = (BoolQueryTree.Run g' t).1 := by
  induction t with
  | halt o => rfl
  | ask j onFalse onTrue ihFalse ihTrue =>
      have hj : j ≠ i := by
        intro hji
        subst hji
        exact hi (Finset.mem_insert_self j _)
      have hg : g j = g' j := hagree j hj
      simp only [BoolQueryTree.Run]
      by_cases hgj : g j = true
      · have hgj' : g' j = true := by rw [← hg]; exact hgj
        rw [if_pos hgj, if_pos hgj']
        simp only [queriedSet] at hi
        rw [if_pos hgj] at hi
        refine ihTrue ?_
        intro hmem
        exact hi (Finset.mem_insert_of_mem hmem)
      · have hgj' : ¬ g' j = true := by intro h; exact hgj (hg ▸ h)
        rw [if_neg hgj, if_neg hgj']
        simp only [queriedSet] at hi
        rw [if_neg hgj] at hi
        refine ihFalse ?_
        intro hmem
        exact hi (Finset.mem_insert_of_mem hmem)

theorem card_queriedSet_le_run {I : Type} [DecidableEq I] {Output : Type}
    (t : BoolQueryTree I Output) (g : I → Bool) :
    Finset.card (queriedSet t g) ≤ (BoolQueryTree.Run g t).2 := by
  induction t with
  | halt o => simp [queriedSet, BoolQueryTree.Run]
  | ask j onFalse onTrue ihFalse ihTrue =>
      simp only [queriedSet, BoolQueryTree.Run]
      by_cases hgj : g j = true
      · rw [if_pos hgj, if_pos hgj]
        have hle : (insert j (queriedSet onTrue g)).card
            ≤ (queriedSet onTrue g).card + 1 :=
          Finset.card_insert_le (a := j) (s := queriedSet onTrue g)
        have hih : (queriedSet onTrue g).card
            ≤ (BoolQueryTree.Run g onTrue).2 := ihTrue
        show (insert j (queriedSet onTrue g)).card
          ≤ (BoolQueryTree.Run g onTrue).2 + 1
        omega
      · rw [if_neg hgj, if_neg hgj]
        have hle : (insert j (queriedSet onFalse g)).card
            ≤ (queriedSet onFalse g).card + 1 :=
          Finset.card_insert_le (a := j) (s := queriedSet onFalse g)
        have hih : (queriedSet onFalse g).card
            ≤ (BoolQueryTree.Run g onFalse).2 := ihFalse
        show (insert j (queriedSet onFalse g)).card
          ≤ (BoolQueryTree.Run g onFalse).2 + 1
        omega

theorem mem_zeroErrorSearch_depthSet {I : Type} [Fintype I] [DecidableEq I]
    {M : ZeroErrorSearchClass I} {n : ℕ} :
    n ∈ M.depthSet ↔
      ∃ t ∈ M.trees, (∀ g : I → Bool, SearchTreeCorrect t g) ∧
        BoolQueryTree.MaxQueries t = n := by
  unfold ZeroErrorSearchClass.depthSet
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨t, ht, hn⟩
    obtain ⟨htm, hdec⟩ := List.mem_filter.mp ht
    exact ⟨t, htm, of_decide_eq_true hdec, hn⟩
  · rintro ⟨t, htm, hcorrect, hn⟩
    refine ⟨t, List.mem_filter.mpr ⟨htm, ?_⟩, hn⟩
    rw [decide_eq_true_eq]
    exact hcorrect

theorem searchTree_queries_every_coordinate {I : Type} [Fintype I] [DecidableEq I]
    (t : SearchTree I) (hcorrect : ∀ g : I → Bool, SearchTreeCorrect t g) :
    ∀ i : I, i ∈ queriedSet t (fun _ => false) := by
  intro i
  by_contra hnot
  have hout := run_eq_of_not_queried t (fun _ => false) (fun j => j = i) i hnot (by
    intro j hj
    simp [hj])
  have hg0 := hcorrect (fun _ => false)
  have hgi := hcorrect (fun j => j = i)
  have hout0 : (BoolQueryTree.Run (fun _ => false) t).1 = none :=
    (hg0.1).mpr (by intro j; simp)
  have houti : (BoolQueryTree.Run (fun j => j = i) t).1 ≠ none := by
    obtain ⟨j, hj, hgj⟩ := hgi.2 i (by simp)
    rw [hj]
    simp
  rw [hout0] at hout
  exact absurd hout.symm houti

theorem searchTree_depth_ge {I : Type} [Fintype I] [DecidableEq I] (t : SearchTree I)
    (hcorrect : ∀ g : I → Bool, SearchTreeCorrect t g) :
    Fintype.card I ≤ BoolQueryTree.MaxQueries t := by
  have hq := searchTree_queries_every_coordinate t hcorrect
  have hsub : (Finset.univ : Finset I) ⊆ queriedSet t (fun _ => false) := by
    intro i hi
    exact hq i
  have hcard : Fintype.card I ≤ Finset.card (queriedSet t (fun _ => false)) :=
    Finset.card_le_card hsub
  calc
    Fintype.card I ≤ Finset.card (queriedSet t (fun _ => false)) := hcard
    _ ≤ (BoolQueryTree.Run (fun _ => false) t).2 := card_queriedSet_le_run t _
    _ ≤ BoolQueryTree.MaxQueries t := BoolQueryTree.run_queries_le _ t

theorem searchScanTree_none {I : Type} [DecidableEq I] (l : List I) (g : I → Bool) :
    (BoolQueryTree.Run g (searchScanTree l)).1 = none ↔ ∀ i ∈ l, g i = false := by
  induction l with
  | nil => simp [searchScanTree, BoolQueryTree.Run]
  | cons i l ih =>
      by_cases hgi : g i = true
      · rw [searchScanTree, BoolQueryTree.Run]
        simp [BoolQueryTree.Run, hgi]
      · have hgi' : g i = false := by simpa using! hgi
        rw [searchScanTree, BoolQueryTree.Run]
        simp [hgi', ih]

theorem searchScanTree_some {I : Type} [DecidableEq I] (l : List I) (g : I → Bool)
    (j : I) (hj : (BoolQueryTree.Run g (searchScanTree l)).1 = some j) :
    g j = true := by
  induction l with
  | nil =>
      have hn : (BoolQueryTree.Run g (searchScanTree ([] : List I))).1 = none := by
        simp [searchScanTree, BoolQueryTree.Run]
      rw [hn] at hj
      simp at hj
  | cons i l ih =>
      by_cases hgi : g i = true
      · have hmain : (BoolQueryTree.Run g (searchScanTree (i :: l))).1 = some i := by
          rw [searchScanTree, BoolQueryTree.Run]
          simp [BoolQueryTree.Run, hgi]
        rw [hmain] at hj
        simp at hj
        subst hj
        exact hgi
      · have hsel : (if g i = true then BoolQueryTree.Run g (BoolQueryTree.halt (some i))
              else BoolQueryTree.Run g (searchScanTree l)).1
            = (BoolQueryTree.Run g (searchScanTree l)).1 := by
          simp [hgi]
        have hmain : (BoolQueryTree.Run g (searchScanTree (i :: l))).1
              = (BoolQueryTree.Run g (searchScanTree l)).1 := by
          rw [searchScanTree, BoolQueryTree.Run, hsel]
        rw [hmain] at hj
        exact ih hj

theorem searchScanTree_correctOn {I : Type} [DecidableEq I] (l : List I) (g : I → Bool) :
    SearchTreeCorrectOn l (searchScanTree l) g := by
  refine ⟨searchScanTree_none l g, ?_⟩
  intro i hi hgi
  by_cases hn : (BoolQueryTree.Run g (searchScanTree l)).1 = none
  · have hnone : ∀ k ∈ l, g k = false := (searchScanTree_none l g).mp hn
    exact absurd (hnone i hi) (by simpa using! hgi)
  · cases hh : (BoolQueryTree.Run g (searchScanTree l)).1 with
    | none => exact absurd hh hn
    | some k => exact ⟨k, rfl, searchScanTree_some l g k hh⟩

theorem searchScanTree_correct_all {I : Type} [Fintype I] [DecidableEq I] :
    ∀ g : I → Bool, SearchTreeCorrect (searchScanTree (allElements I)) g := by
  intro g
  obtain ⟨hnone, hsome⟩ := searchScanTree_correctOn (allElements I) g
  refine ⟨?_, ?_⟩
  · constructor
    · intro hn
      exact fun i => (hnone.mp hn) i (allElements_mem I i)
    · intro hall
      exact hnone.mpr (fun i _ => hall i)
  · intro i hi
    obtain ⟨j, hj, hgj⟩ := hsome i (allElements_mem I i) hi
    exact ⟨j, hj, hgj⟩

theorem searchScanTree_maxQueries {I : Type} (l : List I) :
    BoolQueryTree.MaxQueries (searchScanTree l) = l.length := by
  induction l with
  | nil => simp [searchScanTree, BoolQueryTree.MaxQueries]
  | cons i l ih =>
      have hih := ih
      simp [searchScanTree, BoolQueryTree.MaxQueries, hih, Nat.add_comm]

theorem zeroErrorSearchMin_depth {I : Type} [Fintype I] [DecidableEq I]
    (M : ZeroErrorSearchClass I) (h : ∃ n, n ∈ M.depthSet) :
    Fintype.card I ≤ M.minDepth h := by
  have hmem : M.minDepth h ∈ M.depthSet := finsetMinNat_mem (s := M.depthSet) (h := h)
  obtain ⟨t, ht, hcorrect, hcnt⟩ :=
    (mem_zeroErrorSearch_depthSet (M := M) (n := M.minDepth h)).mp hmem
  have hdeg := searchTree_depth_ge t hcorrect
  rw [← hcnt]
  exact hdeg

theorem zeroErrorSearchMin_depth_scan {I : Type} [Fintype I] [DecidableEq I] :
    ZeroErrorSearchClass.minDepth (scanSearchClass (allElements I))
      (by
        refine ⟨BoolQueryTree.MaxQueries (searchScanTree (allElements I)), ?_⟩
        apply (mem_zeroErrorSearch_depthSet (M := scanSearchClass (allElements I))
          (n := BoolQueryTree.MaxQueries (searchScanTree (allElements I)))).mpr
        exact ⟨searchScanTree (allElements I), by simp [scanSearchClass],
          ⟨searchScanTree_correct_all, rfl⟩⟩) =
      Fintype.card I := by
  have hne : ∃ n, n ∈ (scanSearchClass (allElements I)).depthSet := by
    refine ⟨BoolQueryTree.MaxQueries (searchScanTree (allElements I)), ?_⟩
    apply (mem_zeroErrorSearch_depthSet (M := scanSearchClass (allElements I))
      (n := BoolQueryTree.MaxQueries (searchScanTree (allElements I)))).mpr
    exact ⟨searchScanTree (allElements I), by simp [scanSearchClass],
      ⟨searchScanTree_correct_all, rfl⟩⟩
  have hlower := zeroErrorSearchMin_depth (scanSearchClass (allElements I)) hne
  have hmem : Fintype.card I ∈ (scanSearchClass (allElements I)).depthSet := by
    apply (mem_zeroErrorSearch_depthSet (M := scanSearchClass (allElements I))
      (n := Fintype.card I)).mpr
    refine ⟨searchScanTree (allElements I), ?_, ?_⟩
    · simp [scanSearchClass]
    · rw [searchScanTree_maxQueries, allElements_length]
      exact ⟨searchScanTree_correct_all, rfl⟩
  have hle : (scanSearchClass (allElements I)).minDepth hne ≤ Fintype.card I :=
    finsetMinNat_le (s := (scanSearchClass (allElements I)).depthSet) (h := hne) hmem
  exact le_antisymm hle hlower

theorem clause64_complete :
    ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ),
      (∀ k : ℕ, k ≤ n → Qatlib.Concepts.QueryComplexity.DegreeMethod.permLayerAverage n p k
            = Qatlib.Concepts.QueryComplexity.DegreeMethod.layerAverage p k) ∧
        ∃ q : Polynomial ℝ,
          Polynomial.natDegree q ≤ MvPolynomial.totalDegree p ∧
            ∀ k : ℕ, k ≤ n → Qatlib.Concepts.QueryComplexity.DegreeMethod.layerAverage p k = Polynomial.eval (k : ℝ) q :=
  Qatlib.Concepts.QueryComplexity.DegreeMethod.clause64_complete

theorem clause64_empty_layer (n : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.permLayerAverage n p n
      = Qatlib.Concepts.QueryComplexity.DegreeMethod.layerAverage p n :=
  (Qatlib.Concepts.QueryComplexity.DegreeMethod.clause64_complete n p).1 n (Nat.le_refl n)

theorem clause64_zero_variables (p : MvPolynomial (Fin 0) ℝ) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.permLayerAverage 0 p 0
      = Qatlib.Concepts.QueryComplexity.DegreeMethod.layerAverage p 0 :=
  (Qatlib.Concepts.QueryComplexity.DegreeMethod.clause64_complete 0 p).1 0 (Nat.le_refl 0)

theorem clause67_complete (M : MachineClass I W) (f : (I → Bool) → Bool)
    (hE : ∃ n, n ∈ ConventionCountSet M .exact f)
    (hB : ∃ n, n ∈ ConventionCountSet M .bounded f)
    (hS : ∃ n, n ∈ ConventionCountSet M .success f)
    (hZ : ∃ n, n ∈ ConventionCountSet M (.zeroErrorInconclusive (1 / 3)) f) :
    (∀ Q ∈ M.programs, ConventionHolds .exact Q f →
        ConventionMinQueries M .exact f hE ≤ QueryCount Q.circuit) ∧
      (∀ Q ∈ M.programs, ConventionHolds .bounded Q f →
        ConventionMinQueries M .bounded f hB ≤ QueryCount Q.circuit) ∧
      (∀ Q ∈ M.programs, ConventionHolds .success Q f →
        ConventionMinQueries M .success f hS ≤ QueryCount Q.circuit) ∧
      (∀ Q ∈ M.programs, ConventionHolds (.zeroErrorInconclusive (1 / 3)) Q f →
        ConventionMinQueries M (.zeroErrorInconclusive (1 / 3)) f hZ ≤ QueryCount Q.circuit) ∧
      (∃ Q ∈ M.programs, ConventionHolds .exact Q f ∧
        QueryCount Q.circuit = ConventionMinQueries M .exact f hE) ∧
      ConventionMinQueries M .success f hS ≤ ConventionMinQueries M .bounded f hB ∧
        ConventionMinQueries M .bounded f hB ≤ ConventionMinQueries M .exact f hE ∧
      Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree (I := I) f
        ≤ 2 * ConventionMinQueries M .exact f hE := by
  have hE' : ∃ n, n ∈ M.exactCountSet f := by
    rw [← conventionCountSet_exact_eq M f]
    exact hE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q hQ hQf
    exact conventionMin_le_of_program hQ (by simpa [ConventionHolds] using! hQf)
  · intro Q hQ hQf
    exact conventionMin_le_of_program hQ (by simpa [ConventionHolds] using! hQf)
  · intro Q hQ hQf
    exact conventionMin_le_of_program hQ (by simpa [ConventionHolds] using! hQf)
  · intro Q hQ hQf
    exact conventionMin_le_of_program hQ (by simpa [ConventionHolds] using! hQf)
  · obtain ⟨Q, hQ, hQf, hcnt⟩ := conventionMin_attained (M := M) (c := .exact) (f := f) (h := hE)
    exact ⟨Q, hQ, by simpa [ConventionHolds] using! hQf, hcnt⟩
  · exact conventionMin_antitone (c := .bounded) (c' := .success)
      conventionStronger_bounded_success (f := f) (h := hB) (h' := hS)
  · exact conventionMin_antitone (c := .exact) (c' := .bounded)
      conventionStronger_exact_bounded (f := f) (h := hE) (h' := hB)
  · have hdeg := Qatlib.Concepts.QueryComplexity.DegreeMethod.minExactQueries_degree_bound
      (M := M) (f := f) (h := hE')
    rw [← conventionMin_exact_eq M f hE] at hdeg
    exact hdeg

theorem orScanTree_correct_all {I : Type} [Fintype I] [DecidableEq I] (g : I → Bool) :
    (BoolQueryTree.Run g (orScanTree (allElements I))).1 = orFunction g := by
  have h1 := orScanTree_run (allElements I) g
  by_cases h : orFunction g = true
  · obtain ⟨i, hgi⟩ : ∃ i, g i = true := by simpa [orFunction] using! h
    have hout : (BoolQueryTree.Run g (orScanTree (allElements I))).1 = true :=
      h1.mpr ⟨i, allElements_mem I i, hgi⟩
    rw [h, hout]
  · have hne : ¬ (∃ i, g i = true) := by simpa [orFunction] using! h
    have hnot : ¬ (∃ i ∈ allElements I, g i = true) := by
      rintro ⟨i, hi, hgi⟩
      exact hne ⟨i, hgi⟩
    have hout : (BoolQueryTree.Run g (orScanTree (allElements I))).1 = false := by
      cases hh : (BoolQueryTree.Run g (orScanTree (allElements I))).1 with
      | true => exact absurd (h1.mp hh) hnot
      | false => rfl
    have hor : orFunction g = false := by
      cases hb : orFunction g with
      | true => exact absurd hb h
      | false => rfl
    rw [hor, hout]

theorem zeroErrorDepth_or_lower {I : Type} [Fintype I] [DecidableEq I]
    (hcard : 0 < Fintype.card I) (t : BoolQueryTree I Bool)
    (h : ∀ g, (BoolQueryTree.Run g t).1 = orFunction g) :
    Fintype.card I ≤ BoolQueryTree.MaxQueries t := by
  have hdeg := tree_depth_ge_exactDegree t orFunction h
  rw [clause70_complete hcard] at hdeg
  exact hdeg

theorem zeroErrorDepth_or_upper {I : Type} [Fintype I] [DecidableEq I] :
    BoolQueryTree.MaxQueries (orScanTree (allElements I)) = Fintype.card I := by
  rw [orScanTree_maxQueries, allElements_length]

theorem zeroErrorDepth_or_min {I : Type} [Fintype I] [DecidableEq I]
    (hcard : 0 < Fintype.card I) (M : ClassicalMachineClass I)
    (hscan : orScanTree (allElements I) ∈ M.trees)
    (h : ∃ n, n ∈ M.depthSet orFunction) :
    M.minDepth orFunction h = Fintype.card I := by
  have hmem : M.minDepth orFunction h ∈ M.depthSet orFunction :=
    finsetMinNat_mem (s := M.depthSet orFunction) (h := h)
  unfold ClassicalMachineClass.depthSet at hmem
  rw [List.mem_toFinset, List.mem_map] at hmem
  obtain ⟨t, ht, hcnt⟩ := hmem
  obtain ⟨htm, hdec⟩ := List.mem_filter.mp ht
  have hcomp : ∀ g, (BoolQueryTree.Run g t).1 = orFunction g := of_decide_eq_true hdec
  have hlower : Fintype.card I ≤ M.minDepth orFunction h := by
    have hdeg := zeroErrorDepth_or_lower hcard t hcomp
    rw [hcnt] at hdeg
    exact hdeg
  have hupper : Fintype.card I ∈ M.depthSet orFunction := by
    unfold ClassicalMachineClass.depthSet
    rw [List.mem_toFinset, List.mem_map]
    refine ⟨orScanTree (allElements I), List.mem_filter.mpr ⟨hscan, ?_⟩, ?_⟩
    · rw [decide_eq_true_eq]
      exact orScanTree_correct_all
    · rw [zeroErrorDepth_or_upper]
  have hle : M.minDepth orFunction h ≤ Fintype.card I :=
    finsetMinNat_le (s := M.depthSet orFunction) (h := h) hupper
  exact le_antisymm hle hlower

theorem zeroErrorDepth_and_lower {I : Type} [Fintype I] [DecidableEq I]
    (t : BoolQueryTree I Bool) (h : ∀ g, (BoolQueryTree.Run g t).1 = andFunction g) :
    Fintype.card I ≤ BoolQueryTree.MaxQueries t := by
  have hq : ∀ i : I, i ∈ queriedSet t (fun _ => false) := by
    intro i
    by_contra hnot
    have hout := run_eq_of_not_queried t (fun _ => false) (fun j => j = i) i hnot (by
      intro j hj
      simp [hj])
    have hg0 : (BoolQueryTree.Run (fun _ => false) t).1 = true := by
      have hh := h (fun _ => false)
      simpa [andFunction] using! hh
    have hgi : (BoolQueryTree.Run (fun j => j = i) t).1 = false := by
      have hh := h (fun j => j = i)
      have hval : andFunction (fun j => j = i) = false := by
        simp [andFunction]
      rw [hval] at hh
      exact hh
    rw [hg0] at hout
    exact absurd (hout ▸ hgi) (by simp)
  have hsub : (Finset.univ : Finset I) ⊆ queriedSet t (fun _ => false) := by
    intro i hi
    exact hq i
  have hcard : Fintype.card I ≤ Finset.card (queriedSet t (fun _ => false)) :=
    Finset.card_le_card hsub
  calc
    Fintype.card I ≤ Finset.card (queriedSet t (fun _ => false)) := hcard
    _ ≤ (BoolQueryTree.Run (fun _ => false) t).2 := card_queriedSet_le_run t _
    _ ≤ BoolQueryTree.MaxQueries t := BoolQueryTree.run_queries_le _ t

theorem clause71_complete {I : Type} [Fintype I] [DecidableEq I]
    (M : ZeroErrorSearchClass I) (h : ∃ n, n ∈ M.depthSet) :
    Fintype.card I ≤ M.minDepth h :=
  zeroErrorSearchMin_depth M h

theorem clause71_scan_upper {I : Type} [Fintype I] [DecidableEq I] :
    ZeroErrorSearchClass.minDepth (scanSearchClass (allElements I))
      (by
        refine ⟨BoolQueryTree.MaxQueries (searchScanTree (allElements I)), ?_⟩
        apply (mem_zeroErrorSearch_depthSet (M := scanSearchClass (allElements I))
          (n := BoolQueryTree.MaxQueries (searchScanTree (allElements I)))).mpr
        exact ⟨searchScanTree (allElements I), by simp [scanSearchClass],
          ⟨searchScanTree_correct_all, rfl⟩⟩) =
      Fintype.card I :=
  zeroErrorSearchMin_depth_scan

theorem clause71_or_transport {I : Type} [Fintype I] [DecidableEq I]
    (M : ZeroErrorSearchClass I) (h : ∃ n, n ∈ M.depthSet)
    (hcard : 0 < Fintype.card I) :
    Fintype.card I ≤ M.minDepth h ∧
      (∀ t : BoolQueryTree I Bool, (∀ g, (BoolQueryTree.Run g t).1 = orFunction g) →
        Fintype.card I ≤ BoolQueryTree.MaxQueries t) :=
  ⟨zeroErrorSearchMin_depth M h, fun t ht => zeroErrorDepth_or_lower hcard t ht⟩

end Qatlib.Papers.PolyMethod01.MainResults
