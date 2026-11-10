/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Ext
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Concepts.SketchArith.TransposeAccess

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace FinDist

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

private theorem fiber_mass (f : X → Y) (c : ℝ) (x : X) :
    (∑ y, if f x = y then c else 0) = c := by
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ (f x))]

private theorem fiber_sum (f : X → Y) (φ : Y → ℝ) (x : X) :
    (∑ y, if f x = y then φ y else 0) = φ (f x) := by
  have hsingle : (∑ y ∈ (Finset.univ : Finset Y), if f x = y then φ y else 0)
      = if f x = f x then φ (f x) else 0 := by
    refine Finset.sum_eq_single (f x) (fun b _ hb => ?_) ?_
    · rw [if_neg (fun h => hb h.symm)]
    · intro hcontra
      exact absurd (Finset.mem_univ (f x)) hcontra
  exact hsingle.trans (if_pos rfl)

private theorem fiber_mass_mul (f : X → Y) (c : ℝ) (g : Y → ℝ) (x : X) :
    (∑ y, (if f x = y then c else 0) * g y) = c * g (f x) := by
  have hshift : ∀ y, (if f x = y then c else 0) * g y
      = if f x = y then c * g y else 0 := by
    intro y
    by_cases h : f x = y
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, zero_mul]
  rw [Finset.sum_congr rfl fun y _ => hshift y]
  exact fiber_sum f (fun y => c * g y) x

theorem exists_pushforward (p : FinDist X) (f : X → Y) :
    ∃ q : FinDist Y, ∀ y, q.prob y = ∑ x, if f x = y then p.prob x else 0 := by
  refine ⟨⟨fun y => ∑ x, if f x = y then p.prob x else 0, fun y => ?_, ?_⟩, fun y => rfl⟩
  · refine Finset.sum_nonneg fun x _ => ?_
    by_cases h : f x = y
    · rw [if_pos h]
      exact p.nonneg x
    · rw [if_neg h]
  · calc (∑ y, ∑ x, if f x = y then p.prob x else 0)
      = ∑ x, ∑ y, if f x = y then p.prob x else 0 := Finset.sum_comm
    _ = ∑ x, p.prob x := Finset.sum_congr rfl fun x _ => fiber_mass f (p.prob x) x
    _ = 1 := p.sum_one

theorem expect_eq_of_pushforward (p : FinDist X) (q : FinDist Y) (f : X → Y) (h : Y → ℝ)
    (hq : ∀ y, q.prob y = ∑ x, if f x = y then p.prob x else 0) :
    q.expect h = p.expect (fun x => h (f x)) := by
  calc q.expect h
      = ∑ y, q.prob y * h y := rfl
    _ = ∑ y, ∑ x, (if f x = y then p.prob x else 0) * h y := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hq y]
        exact Finset.sum_mul (Finset.univ : Finset X)
          (fun x => if f x = y then p.prob x else 0) (h y)
    _ = ∑ x, ∑ y, (if f x = y then p.prob x else 0) * h y := Finset.sum_comm
    _ = ∑ x, p.prob x * h (f x) :=
        Finset.sum_congr rfl fun x _ => fiber_mass_mul f (p.prob x) h x
    _ = p.expect (fun x => h (f x)) := rfl

theorem variance_eq_of_pushforward (p : FinDist X) (q : FinDist Y) (f : X → Y) (h : Y → ℝ)
    (hq : ∀ y, q.prob y = ∑ x, if f x = y then p.prob x else 0) :
    q.variance h = p.variance (fun x => h (f x)) := by
  have hmean : q.expect h = p.expect (fun x => h (f x)) :=
    expect_eq_of_pushforward p q f h hq
  have hcenter : ∀ y : Y, (h y - q.expect h) ^ 2
      = (h y - p.expect (fun x => h (f x))) ^ 2 := by
    intro y
    rw [hmean]
  unfold variance
  rw [expect_eq_of_pushforward p q f (fun y => (h y - q.expect h) ^ 2) hq]
  refine Finset.sum_congr rfl fun x _ => ?_
  show p.prob x * (h (f x) - q.expect h) ^ 2
      = p.prob x * (h (f x) - p.expect (fun x => h (f x))) ^ 2
  rw [hcenter (f x)]

omit [DecidableEq X] in

theorem exists_pmf (p : FinDist X) :
    ∃ μ : PMF X, ∀ x, μ x = ENNReal.ofReal (p.prob x) := by
  have hsum : (∑ x, ENNReal.ofReal (p.prob x)) = 1 := by
    have hof := ENNReal.ofReal_sum_of_nonneg (s := (Finset.univ : Finset X))
      (f := fun x => p.prob x) fun i _ => p.nonneg i
    rw [p.sum_one, ENNReal.ofReal_one] at hof
    exact hof.symm
  exact ⟨PMF.ofFintype (fun x => ENNReal.ofReal (p.prob x)) hsum, fun x => rfl⟩

theorem exists_pushforward_pmf (p : FinDist X) (f : X → Y) :
    ∃ q : FinDist Y, ∃ μ : PMF X, ∃ ν : PMF Y,
      (∀ y, q.prob y = ∑ x, if f x = y then p.prob x else 0) ∧
      (∀ x, μ x = ENNReal.ofReal (p.prob x)) ∧
      (∀ y, ν y = ENNReal.ofReal (q.prob y)) ∧ μ.map f = ν ∧
      (∀ h : Y → ℝ, q.expect h = p.expect (fun x => h (f x))) := by
  obtain ⟨q, hq⟩ := exists_pushforward p f
  obtain ⟨μ, hμ⟩ := exists_pmf p
  obtain ⟨ν, hν⟩ := exists_pmf q
  refine ⟨q, μ, ν, hq, hμ, hν, ?_, fun h => ?_⟩
  · refine PMF.ext fun y => ?_
    rw [PMF.map_apply, tsum_eq_sum fun _ hx => (hx (Finset.mem_univ _)).elim]

    have hinst : (∑ x, @ite ENNReal (y = f x) (Classical.propDecidable (y = f x)) (μ x) 0)
        = ∑ x, if y = f x then μ x else 0 :=
      Finset.sum_congr rfl fun x _ => by
        by_cases hc : y = f x <;> simp [hc]
    rw [hinst]
    have h1 : (∑ x, if y = f x then μ x else 0)
        = ∑ x, if y = f x then ENNReal.ofReal (p.prob x) else 0 :=
      Finset.sum_congr rfl fun x _ => by
        by_cases hc : y = f x <;> simp [hc, hμ x]
    rw [h1]
    have h2 : (∑ x, if y = f x then ENNReal.ofReal (p.prob x) else 0)
        = ENNReal.ofReal (∑ x, if y = f x then p.prob x else 0) := by
      have hpush : (∑ x, if y = f x then ENNReal.ofReal (p.prob x) else 0)
          = ∑ x, ENNReal.ofReal (if y = f x then p.prob x else 0) :=
        Finset.sum_congr rfl fun x _ => by
          by_cases hc : y = f x <;> simp [hc, ENNReal.ofReal_zero]
      rw [hpush]
      have hof := ENNReal.ofReal_sum_of_nonneg (s := (Finset.univ : Finset X))
        (f := fun x => if y = f x then p.prob x else 0) (fun i _ => ?_)
      · rw [← hof]
      · by_cases hc : y = f i <;> simp [hc, p.nonneg i]
    rw [h2]
    have h3 : (∑ x, if y = f x then p.prob x else 0)
        = ∑ x, if f x = y then p.prob x else 0 :=
      Finset.sum_congr rfl fun x _ => by
        by_cases hc : y = f x
        · rw [if_pos hc, if_pos hc.symm]
        · rw [if_neg hc, if_neg (fun h => hc h.symm)]
    rw [h3, ← hq y, hν y]
  · exact expect_eq_of_pushforward p q f h hq

end FinDist

end Qatlib.Concepts.SketchArith.TransposeAccess
