/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HHLManyBody22.HomOverlap.BornReadout
import Mathlib.Data.Finset.Max

/-!
# Greedy conditional fixing of clock bits

The greedy procedure `greedyFix` repeatedly chooses a remaining bit and Boolean value with
maximal retained clock mass. It continues only when the current mass is positive and the chosen
child reaches the specified fraction of that mass.

The module bounds the number of choices by the supplied fuel and the final event mass by the
threshold raised to the number of choices. `greedyFix_event` characterizes the event as the
initial set restricted by all recorded choices. See [BaskaranEtAl2023].

## Main statements

* `greedyFix_mass`: For a nonnegative threshold, the final event mass is at least the initial
  mass times the threshold raised to the number of recorded choices.
* `greedyFix_event`: A clock assignment belongs to the final event exactly when it belongs to
  the initial event and satisfies every recorded choice.
* `greedyFix_choice_remaining`: Every clock index appearing in the recorded choices belongs to
  the initial set of remaining indices.

## References

* [Baskaran et al., 2023][BaskaranEtAl2023]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Papers.HHLManyBody22.GreedyFixing

/-- Boolean assignments to the `n` clock positions. -/
abbrev ClockBits (n : ℕ) := Fin n→Bool

/-- The total weight of the clock assignments in `S`. -/
def clockMass {n : ℕ} (w : ClockBits n→ℝ) (S : Finset (ClockBits n)) : ℝ := ∑x∈S,w x

/-- The subset of `S` satisfying the specified bit and Boolean value. -/
def fixChild {n : ℕ} (S : Finset (ClockBits n)) (c : Fin n×Bool) : Finset (ClockBits n) :=
  S.filter (fun x => x c.1=c.2)

/-- The pairs of a remaining clock index with either Boolean value. -/
def fixCandidates {n : ℕ} (R : Finset (Fin n)) : Finset (Fin n×Bool) := R×ˢFinset.univ

/-- A nonempty set of remaining indices gives a nonempty set of fixing candidates. -/
theorem fixCandidates_nonempty {n : ℕ} (R : Finset (Fin n)) (hR : R.Nonempty) :
    (fixCandidates R).Nonempty := by
  obtain ⟨i,hi⟩ := hR
  exact ⟨(i,false),by simp [fixCandidates,hi]⟩

/-- A candidate bit and value maximizing the weight retained from `S`. -/
def bestFixPair {n : ℕ} (w : ClockBits n→ℝ) (S : Finset (ClockBits n))
    (R : Finset (Fin n)) (hR : R.Nonempty) : Fin n×Bool :=
  Classical.choose (Finset.exists_max_image (fixCandidates R)
    (fun c => clockMass w (fixChild S c)) (fixCandidates_nonempty R hR))

/-- The chosen pair is a candidate and its child mass is maximal among all candidates. -/
theorem bestFixPair_spec {n : ℕ} (w : ClockBits n→ℝ) (S : Finset (ClockBits n))
    (R : Finset (Fin n)) (hR : R.Nonempty) :
    bestFixPair w S R hR∈fixCandidates R ∧
    ∀c∈fixCandidates R,clockMass w (fixChild S c)≤
      clockMass w (fixChild S (bestFixPair w S R hR)) :=
  Classical.choose_spec (Finset.exists_max_image (fixCandidates R)
    (fun c => clockMass w (fixChild S c)) (fixCandidates_nonempty R hR))

/-- The final clock event together with the ordered list of fixed bit values. -/
structure GreedyFixResult (n : ℕ) where
  event : Finset (ClockBits n)
  choices : List (Fin n×Bool)

/-- The fuel bounded procedure that greedily fixes a remaining bit when its maximal child has at
least the threshold fraction of a positive current mass. -/
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

/-- For a nonnegative threshold, the final event mass is at least the initial mass times the
threshold raised to the number of recorded choices. -/
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

/-- The number of choices recorded by greedy fixing is at most its fuel. -/
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

/-- If the total clock weight is one and the threshold is nonnegative, the final event mass is
at least the threshold raised to the number of choices. See [BaskaranEtAl2023]. -/
theorem greedyFix_normalized_event {n : ℕ} (w : ClockBits n→ℝ) (threshold : ℝ)
    (ht : 0≤threshold) (hNorm : ∑x,w x=1) :
    threshold^(greedyFix w threshold n Finset.univ Finset.univ).choices.length≤
      clockMass w (greedyFix w threshold n Finset.univ Finset.univ).event := by
  have h := greedyFix_mass w threshold ht n Finset.univ Finset.univ
  simpa only [clockMass,hNorm,mul_one] using h

/-- Greedy fixing leaves an event of zero mass unchanged and records no choices. -/
theorem greedyFix_zero_mass {n : ℕ} (w : ClockBits n→ℝ) (threshold : ℝ)
    (fuel : ℕ) (R : Finset (Fin n)) (S : Finset (ClockBits n))
    (hz : clockMass w S=0) : greedyFix w threshold fuel R S=⟨S,[]⟩ := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [greedyFix,hz]

/-- A clock assignment belongs to the final event exactly when it belongs to the initial event
and satisfies every recorded choice. See [BaskaranEtAl2023]. -/
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

/-- Every clock index appearing in the recorded choices belongs to the initial set of remaining
indices. -/
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
