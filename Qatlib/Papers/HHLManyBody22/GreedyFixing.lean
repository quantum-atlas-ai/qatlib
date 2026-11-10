/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HHLManyBody22.HomOverlap.BornReadout
import Mathlib.Data.Finset.Max
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Papers.HHLManyBody22.GreedyFixing

abbrev ClockBits (n : ℕ) := Fin n→Bool

def clockMass {n : ℕ} (w : ClockBits n→ℝ) (S : Finset (ClockBits n)) : ℝ := ∑x∈S,w x

def fixChild {n : ℕ} (S : Finset (ClockBits n)) (c : Fin n×Bool) : Finset (ClockBits n) :=
  S.filter (fun x => x c.1=c.2)

def fixCandidates {n : ℕ} (R : Finset (Fin n)) : Finset (Fin n×Bool) := R×ˢFinset.univ

theorem fixCandidates_nonempty {n : ℕ} (R : Finset (Fin n)) (hR : R.Nonempty) :
    (fixCandidates R).Nonempty := by
  obtain ⟨i,hi⟩ := hR
  exact ⟨(i,false),by simp [fixCandidates,hi]⟩

def bestFixPair {n : ℕ} (w : ClockBits n→ℝ) (S : Finset (ClockBits n))
    (R : Finset (Fin n)) (hR : R.Nonempty) : Fin n×Bool :=
  Classical.choose (Finset.exists_max_image (fixCandidates R)
    (fun c => clockMass w (fixChild S c)) (fixCandidates_nonempty R hR))

theorem bestFixPair_spec {n : ℕ} (w : ClockBits n→ℝ) (S : Finset (ClockBits n))
    (R : Finset (Fin n)) (hR : R.Nonempty) :
    bestFixPair w S R hR∈fixCandidates R ∧
    ∀c∈fixCandidates R,clockMass w (fixChild S c)≤
      clockMass w (fixChild S (bestFixPair w S R hR)) :=
  Classical.choose_spec (Finset.exists_max_image (fixCandidates R)
    (fun c => clockMass w (fixChild S c)) (fixCandidates_nonempty R hR))

structure GreedyFixResult (n : ℕ) where
  event : Finset (ClockBits n)
  choices : List (Fin n×Bool)

def greedyFix {n : ℕ} (w : ClockBits n→ℝ) (threshold : ℝ) :
    ℕ→Finset (Fin n)→Finset (ClockBits n)→GreedyFixResult n
  | 0,_,S => ⟨S,[]⟩
  | fuel+1,R,S =>
    if hR : R.Nonempty then
      let c := bestFixPair w S R hR
      if 0<clockMass w S ∧ threshold*clockMass w S≤clockMass w (fixChild S c) then
        let tail := greedyFix w threshold fuel (R.erase c.1) (fixChild S c)
        ⟨tail.event,c::tail.choices⟩
      else ⟨S,[]⟩
    else ⟨S,[]⟩

theorem greedyFix_mass {n : ℕ} (w : ClockBits n→ℝ) (threshold : ℝ)
    (ht : 0≤threshold) (fuel : ℕ) (R : Finset (Fin n)) (S : Finset (ClockBits n)) :
    threshold^(greedyFix w threshold fuel R S).choices.length*clockMass w S≤
      clockMass w (greedyFix w threshold fuel R S).event := by
  induction fuel generalizing R S with
  | zero => simp [greedyFix]
  | succ fuel ih =>
    simp only [greedyFix]
    split_ifs with hR ha
    · (try dsimp only)
      have hrec := ih (R.erase (bestFixPair w S R hR).1) (fixChild S (bestFixPair w S R hR))
      simp only [List.length_cons]
      rw [pow_succ]
      simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left ha.2 (pow_nonneg ht _)).trans hrec
    · simp
    · simp

theorem greedyFix_length {n : ℕ} (w : ClockBits n→ℝ) (threshold : ℝ)
    (fuel : ℕ) (R : Finset (Fin n)) (S : Finset (ClockBits n)) :
    (greedyFix w threshold fuel R S).choices.length≤fuel := by
  induction fuel generalizing R S with
  | zero => simp [greedyFix]
  | succ fuel ih =>
    simp only [greedyFix]
    split_ifs with hR ha
    · exact Nat.succ_le_succ (ih _ _)
    · simp
    · simp

theorem greedyFix_normalized_event {n : ℕ} (w : ClockBits n→ℝ) (threshold : ℝ)
    (ht : 0≤threshold) (hNorm : ∑x,w x=1) :
    threshold^(greedyFix w threshold n Finset.univ Finset.univ).choices.length≤
      clockMass w (greedyFix w threshold n Finset.univ Finset.univ).event := by
  have h := greedyFix_mass w threshold ht n Finset.univ Finset.univ
  simpa only [clockMass,hNorm,mul_one] using h

theorem greedyFix_zero_mass {n : ℕ} (w : ClockBits n→ℝ) (threshold : ℝ)
    (fuel : ℕ) (R : Finset (Fin n)) (S : Finset (ClockBits n))
    (hz : clockMass w S=0) : greedyFix w threshold fuel R S=⟨S,[]⟩ := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [greedyFix,hz]

theorem greedyFix_event {n : ℕ} (w : ClockBits n→ℝ) (threshold : ℝ)
    (fuel : ℕ) (R : Finset (Fin n)) (S : Finset (ClockBits n)) (x : ClockBits n) :
    x∈(greedyFix w threshold fuel R S).event ↔ x∈S ∧
      ∀c∈(greedyFix w threshold fuel R S).choices,x c.1=c.2 := by
  induction fuel generalizing R S with
  | zero => simp [greedyFix]
  | succ fuel ih =>
    simp only [greedyFix]
    split_ifs with hR ha
    · (try dsimp only)
      rw [ih]
      simp only [fixChild,Finset.mem_filter,List.mem_cons,forall_eq_or_imp]
      tauto
    · simp
    · simp

theorem greedyFix_choice_remaining {n : ℕ} (w : ClockBits n→ℝ) (threshold : ℝ)
    (fuel : ℕ) (R : Finset (Fin n)) (S : Finset (ClockBits n)) :
    ∀c∈(greedyFix w threshold fuel R S).choices,c.1∈R := by
  induction fuel generalizing R S with
  | zero => simp [greedyFix]
  | succ fuel ih =>
    simp only [greedyFix]
    split_ifs with hR ha
    · intro c hc
      rcases List.mem_cons.mp hc with rfl|hc
      · have hm := (bestFixPair_spec w S R hR).1
        exact (Finset.mem_product.mp hm).1
      · exact Finset.mem_of_mem_erase (ih _ _ c hc)
    · simp
    · simp

end Qatlib.Papers.HHLManyBody22.GreedyFixing
