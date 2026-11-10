/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.ClassificationScan
import Qatlib.Concepts.WalkSearch.MainResults.AdaptiveTapeUnionBound
import Qatlib.Concepts.WalkSearch.MainResults.DegreeFailureEvent
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.WalkSearch.Primitives
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults
open scoped Classical BigOperators
variable {n : ℕ}

def scanTapeNext (G : UGraph n) (sgs : SGSExecution) (τ K c : ℕ) (stape : Fin n→sgs.seed)
    (v : Fin n) (state : Option (SymmetricPairSet n)) (row : Fin K→Fin c→Fin n) : Option (SymmetricPairSet n) :=
  match state with
  | none=>none
  | some S=>
    let Sd:=drainedPairSet S τ
    if pairsAt Sd.edges v=∅ then some Sd
    else if degreeTestLowCorrected (presentGraph G Sd.edges Sd.symm) v K c row then some (lowRemaining Sd v)
    else match operationalSgsFind sgs (neighborhoodMarked G v) 2 (n*n) (stape v) with
      | some _=>none
      | none=>some (highRemaining G Sd v)

def scanTapeCorrect (G : UGraph n) (τ dHi dLo K c : ℕ)
    (v : Fin n) (state : Option (SymmetricPairSet n)) (row : Fin K→Fin c→Fin n) : Prop :=
  match state with
  | none=>True
  | some S=>
    let Sd:=drainedPairSet S τ
    if pairsAt Sd.edges v=∅ then True
    else testCorrectCorrected (presentGraph G Sd.edges Sd.symm) v dHi dLo K c row

theorem scanTapeGood_halted (G : UGraph n) (sgs : SGSExecution) (τ dHi dLo K c : ℕ)
    (stape : Fin n→sgs.seed) (vs : List (Fin n)) (t : Fin n→Fin K→Fin c→Fin n) :
    adaptiveTapeGood (scanTapeNext G sgs τ K c stape) (scanTapeCorrect G τ dHi dLo K c) vs none t := by
  induction vs with
  | nil => trivial
  | cons v vs ih => exact ⟨trivial,ih⟩

theorem scanTapeGood_iff (G : UGraph n) (sgs : SGSExecution) (τ dHi dLo K c : ℕ)
    (stape : Fin n→sgs.seed) (vs : List (Fin n)) (S : SymmetricPairSet n)
    (t : Fin n→Fin K→Fin c→Fin n) :
    adaptiveTapeGood (scanTapeNext G sgs τ K c stape) (scanTapeCorrect G τ dHi dLo K c) vs (some S) t↔
      classifyScanTestsCorrect G sgs τ dHi dLo K c t stape vs S := by
  induction vs generalizing S with
  | nil => rfl
  | cons v vs ih =>
    simp only [adaptiveTapeGood,scanTapeNext,scanTapeCorrect,classifyScanTestsCorrect]
    split_ifs with he hl
    · simpa only [true_and] using ih (drainedPairSet S τ)
    · exact and_congr_right (fun _=>ih (lowRemaining (drainedPairSet S τ) v))
    · cases hrun : operationalSgsFind sgs (neighborhoodMarked G v) 2 (n*n) (stape v) with
      | some p =>
        (try dsimp only)
        exact and_congr_right
            (fun _=>iff_true_intro (scanTapeGood_halted G sgs τ dHi dLo K c stape vs t))
      | none =>
        (try dsimp only)
        exact and_congr_right (fun _=>ih (highRemaining G (drainedPairSet S τ) v))

theorem classifyScan_bad_tests_card_positive (n : ℕ) (δ : ℝ) (hn : 0<n) (hδ : 0<δ) (hδ1 : δ<1) :
    let K : ℕ :=64*(Nat.log 2 n+2)
    let c : ℕ :=Nat.ceil ((n:ℝ)^δ)
    let dHi : ℕ :=10*Nat.ceil ((n:ℝ)^(1-δ))
    let dLo : ℕ :=Nat.floor ((n:ℝ)^(1-δ)/10)
    0<c→∀ (G : UGraph n) (sgs : SGSExecution) (τ : ℕ) (stape : Fin n→sgs.seed) (S : SymmetricPairSet n),
      (Finset.univ.filter (fun t : Fin n→Fin K→Fin c→Fin n=>
        ¬classifyScanTestsCorrect G sgs τ dHi dLo K c t stape Finset.univ.toList S)).card*n^3≤
          2*n*Fintype.card (Fin n→Fin K→Fin c→Fin n) := by
  intro K c dHi dLo hc G sgs τ stape S
  letI : NeZero n := ⟨by omega⟩
  have herr : ∀ v state,(Finset.univ.filter (fun row : Fin K→Fin c→Fin n=>¬scanTapeCorrect G τ dHi dLo K c v state row)).card*n^3≤
      2*Fintype.card (Fin K→Fin c→Fin n) := by
    intro v state
    cases state with
    | none => simp [scanTapeCorrect]
    | some S=>
      dsimp only [scanTapeCorrect]
      by_cases he : pairsAt (drainedPairSet S τ).edges v=∅
      · simp only [if_pos he,not_true_eq_false,Finset.filter_false,Finset.card_empty,zero_mul,Nat.zero_le]
      · simpa only [if_neg he] using degreeTest_failure_card_positive n δ hn hδ hδ1 hc
          (presentGraph G (drainedPairSet S τ).edges (drainedPairSet S τ).symm) v
  have hh:=adaptiveTape_bad_card_bound (scanTapeNext G sgs τ K c stape) (scanTapeCorrect G τ dHi dLo K c)
    (n^3) 2 herr Finset.univ.toList Finset.univ.nodup_toList (some S)
  simpa only [scanTapeGood_iff,Finset.length_toList,Finset.card_univ,Fintype.card_fin,Nat.mul_comm] using hh

theorem classifyScan_bad_tests_card (n : ℕ) (δ : ℝ) (hn : 64≤n) (hδ : 0<δ) (hδ1 : δ<1) :
    let K : ℕ :=64*(Nat.log 2 n+2)
    let c : ℕ :=Nat.ceil ((n:ℝ)^δ)
    let dHi : ℕ :=10*Nat.ceil ((n:ℝ)^(1-δ))
    let dLo : ℕ :=Nat.floor ((n:ℝ)^(1-δ)/10)
    0<c→∀ (G : UGraph n) (sgs : SGSExecution) (τ : ℕ) (stape : Fin n→sgs.seed) (S : SymmetricPairSet n),
      (Finset.univ.filter (fun t : Fin n→Fin K→Fin c→Fin n=>
        ¬classifyScanTestsCorrect G sgs τ dHi dLo K c t stape Finset.univ.toList S)).card*n^3≤
          2*n*Fintype.card (Fin n→Fin K→Fin c→Fin n) := by
  exact classifyScan_bad_tests_card_positive n δ (by omega) hδ hδ1
end Qatlib.Concepts.WalkSearch.MainResults
