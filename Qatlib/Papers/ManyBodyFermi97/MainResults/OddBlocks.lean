/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.ParallelBlocks

/-!
# Odd hopping blocks on an open chain

`oddSite` indexes the interior pairs of an even open chain, leaving its endpoints isolated. The
module identifies the corresponding odd hopping entries, packages their block evolution as
`oddWord`, and bounds the first-quantized Hubbard step cost.

The mathematical setting is that of [AbramsLloyd1997].

## Main statements

* `oddBlocks_interior`: The odd hopping matrix has entry `t` between the two sites of each
  interior pair.
* `oddWord_correct`: The odd block circuit is unitary, uses no queries, and consists of one gate
  in the supplied block basis.
* `block_step_cost_le`: For `q ≥ 1`, the first-quantized Hubbard step cost is at most `14 * q ^
  2`.

## References

* [Abrams and Lloyd, 1997][AbramsLloyd1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ManyBodyFermi97.MainResults.OddBlocks
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators

open ParallelBlocks

/-- Maps a parity bit and an interior block index to site `2 * x.2.val + 1 + (if x.1 then 1 else
0)` of the open chain. -/
def oddSite (k : ℕ) (x : Bool × Fin (k-1)) : Fin (2*k) :=
  ⟨2*x.2.val + 1 + (if x.1 then 1 else 0), by
    have h := x.2.isLt
    split <;> omega⟩

/-- Distinct parity and block indices map to distinct interior sites. [AbramsLloyd1997] -/
theorem oddSite_injective (k : ℕ) : Function.Injective (oddSite k) := by
  intro x y h
  have hv := congrArg Fin.val h
  rcases x with ⟨b,a⟩
  rcases y with ⟨d,c⟩
  cases b <;> cases d <;>
    simp only [oddSite, Bool.false_eq_true, if_false, if_true] at hv
  all_goals first
    | omega
    | (have hac : a = c := Fin.ext (by omega); subst c; rfl)

/-- Every site between `1` and `2 * k - 2` lies in the image of `oddSite k` when `1 ≤ k`.
[AbramsLloyd1997] -/
theorem oddSite_surjective_on (k : ℕ) (hk : 1 ≤ k) (i : Fin (2*k))
    (hlo : 1 ≤ i.val) (hhi : i.val ≤ 2*k - 2) :
    ∃ x : Bool × Fin (k-1), oddSite k x = i := by
  refine ⟨(decide (i.val % 2 = 0), ⟨(i.val - 1) / 2, by omega⟩), Fin.ext ?_⟩
  simp only [oddSite]
  by_cases h : i.val % 2 = 0
  · simp [h]; omega
  · simp [h]; omega

/-- The interior block indexing never reaches the first site when `1 ≤ k`. -/
theorem oddSite_ne_zero (k : ℕ) (hk : 1 ≤ k) (x : Bool × Fin (k-1)) :
    oddSite k x ≠ (⟨0, by omega⟩ : Fin (2*k)) := by
  intro h
  have hv := congrArg Fin.val h
  rcases x with ⟨b,a⟩
  cases b <;> simp only [oddSite, Bool.false_eq_true, if_false, if_true] at hv
  all_goals omega

/-- The interior block indexing never reaches the last site. -/
theorem oddSite_ne_last (k : ℕ) (x : Bool × Fin (k-1)) :
    oddSite k x ≠ ⟨2*k - 1, by have := x.2.isLt; omega⟩ := by
  intro h
  have hv := congrArg Fin.val h
  rcases x with ⟨b,a⟩
  cases b <;> simp only [oddSite, Bool.false_eq_true, if_false, if_true] at hv
  all_goals omega

/-- The odd hopping matrix has entry `t` between the two sites of each interior pair.
[AbramsLloyd1997] -/
theorem oddBlocks_interior (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (a : Fin (k-1)) :
    oddBlocks (2*k) t ⟨2*a.val+1, by have := a.isLt; omega⟩
      ⟨2*a.val+2, by have := a.isLt; omega⟩ = (t : ℂ) := by
  unfold oddBlocks chainHopping
  have hne : (2*a.val+1)/2 ≠ (2*a.val+2)/2 := by omega
  rw [if_pos hne]
  rw [if_pos (by
    left
    simp only [Fin.val_mk]
    push_cast
    omega)]

/-- Every diagonal entry of the odd hopping matrix is zero. -/
theorem oddBlocks_diagonal_zero (m : ℕ) (t : ℝ) (i : Fin m) :
    oddBlocks m t i i = 0 := by
  simp [oddBlocks, chainHopping]

/-- A chain hopping matrix entry vanishes when its two sites are not adjacent. -/
theorem chainHopping_eq_zero_of_not_adj (m : ℕ) (t : ℂ) {i j : Fin m}
    (h : ¬ ((i.val : ℤ) + 1 = (j.val : ℤ) ∨ (j.val : ℤ) + 1 = (i.val : ℤ))) :
    chainHopping m t i j = 0 := by
  unfold chainHopping
  rw [if_neg h]

/-- The first row of the odd hopping matrix vanishes on an even open chain with `1 ≤ k`.
[AbramsLloyd1997] -/
theorem oddBlocks_zero_site (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (j : Fin (2*k)) :
    oddBlocks (2*k) t (⟨0, by omega⟩ : Fin (2*k)) j = 0 := by
  by_cases h : ((⟨0, by omega⟩ : Fin (2*k)).val / 2 = j.val / 2)
  · unfold oddBlocks
    rw [if_neg (by omega)]
  · unfold oddBlocks
    rw [if_pos (by omega)]
    refine chainHopping_eq_zero_of_not_adj _ _ (by
      have h0 : (((⟨0, by omega⟩ : Fin (2*k))).val : ℤ) = 0 := by simp
      rw [h0]
      omega)

/-- The last row of the odd hopping matrix vanishes on an even open chain with `1 ≤ k`.
[AbramsLloyd1997] -/
theorem oddBlocks_zero_last (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (j : Fin (2*k)) :
    oddBlocks (2*k) t ⟨2*k - 1, by omega⟩ j = 0 := by
  by_cases h : ((⟨2*k - 1, by omega⟩ : Fin (2*k)).val / 2 = j.val / 2)
  · unfold oddBlocks
    rw [if_neg (by omega)]
  · unfold oddBlocks
    rw [if_pos (by omega)]
    refine chainHopping_eq_zero_of_not_adj _ _ (by
      have hlast : (((⟨2*k - 1, by omega⟩ : Fin (2*k))).val : ℤ) = (k : ℤ) * 2 - 1 := by
        simp; omega
      rw [hlast]
      omega)

/-- The block evolution circuit on the parity bit and the `k - 1` interior block labels. -/
def oddWord (k : ℕ) (t time : ℝ) : Circuit (Bool × Fin (k-1)) :=
  word (k-1) t time

/-- The odd block circuit is unitary, uses no queries, and consists of one gate in the supplied
block basis. [AbramsLloyd1997] -/
theorem oddWord_correct (k : ℕ) (t time : ℝ) :
    IsUnitaryCircuit (oddWord k t time) ∧
      QueryCount (oddWord k t time) = 0 ∧
      GateCount (oddWord k t time) = 1 := by
  unfold oddWord
  exact (word_correct (k-1) t time (fun _ => 0)).2

/-- For `q ≥ 1`, the first-quantized Hubbard step cost is at most `14 * q ^ 2`.
[AbramsLloyd1997] -/
theorem block_step_cost_le {q : ℕ} (hq : 1 ≤ q) :
    firstQuantHubbardStepCost q ≤ 14 * q ^ 2 :=
  firstQuantHubbardStepCost_bound hq

end Qatlib.Papers.ManyBodyFermi97.MainResults.OddBlocks
