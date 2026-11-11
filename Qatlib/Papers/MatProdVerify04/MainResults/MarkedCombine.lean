/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MatProdVerify04.MainResults.MarkedIndependent
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Combining marked-window probability bounds

Event-mass monotonicity transfers bounds from a subset of incorrect matrix entries to the full
set. `lemma3_bound` combines the independent-entry and row-occupancy alternatives to obtain an
explicit lower bound for a uniformly sampled square window to meet the marked set.

The mathematical setting is that of [BuhrmanSpalek2006].

## Main statements

* `eventMass_hit_mono`: Enlarging the marked-cell set can only increase the probability that a
  uniform window meets it.
* `lemma3_bound`: Under either the independent-subset condition or the stated nonzero-row and
  maximal-row-occupancy conditions, a uniform `k` by `k` window meets `W` with probability at
  least `q * k ^ 2 / (4 * card Row * card Col)`.

## References

* [Buhrman and Špalek, 2006][BuhrmanSpalek2006]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MatProdVerify04.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration

/-- If event `E` implies event `F` pointwise, its mass under a finite distribution is at most
the mass of `F`. [BuhrmanSpalek2006] -/
theorem eventMass_mono {X : Type*} [Fintype X] (p : FinDist X)
    {E F : X → Prop} [DecidablePred E] [DecidablePred F]
    (h : ∀ x, E x → F x) : eventMass p E ≤ eventMass p F := by
  classical
  unfold eventMass
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => p.nonneg x)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact h x hx

/-- Enlarging the marked-cell set can only increase the probability that a uniform window meets
it. [BuhrmanSpalek2006] -/
theorem eventMass_hit_mono {Row Col : Type*} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col] {W₁ W₂ : Finset (Row × Col)}
    (hsub : W₁ ⊆ W₂) (r s : ℕ) (hr : r ≤ Fintype.card Row)
    (hs : s ≤ Fintype.card Col) :
    eventMass (uniformWindow r s hr hs) (fun RS => ¬ Disjoint W₁ (windowCells RS))
      ≤ eventMass (uniformWindow r s hr hs)
          (fun RS => ¬ Disjoint W₂ (windowCells RS)) := by
  classical
  refine eventMass_mono _ (fun RS h => ?_)
  rw [Finset.not_disjoint_iff] at h ⊢
  obtain ⟨p, hp1, hpc⟩ := h
  exact ⟨p, hsub hp1, hpc⟩

/-- Under either the independent-subset condition or the stated nonzero-row and
maximal-row-occupancy conditions, a uniform `k` by `k` window meets `W` with probability at
least `q * k ^ 2 / (4 * card Row * card Col)`. [BuhrmanSpalek2006] -/
theorem lemma3_bound {Row Col : Type*} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col] (W W' : Finset (Row × Col))
    (hsub : W' ⊆ W) (hind : IsIndependent W') (q k : ℕ)
    (hRow : 0 < Fintype.card Row) (hCol : 0 < Fintype.card Col)
    (hkRow : k ≤ Fintype.card Row) (hkCol : k ≤ Fintype.card Col)
    (hq : (q ≤ W'.card ∧ (k : ℝ) * (k : ℝ) ≤ (Fintype.card Col : ℝ))
          ∨ (q ≤ W.card ∧ k ≤ Fintype.card Row / (nzRows W).card
              ∧ k ≤ Fintype.card Col / maxRowW W)) :
    (1 / 4) * (q : ℝ) * (k : ℝ) * (k : ℝ)
        / ((Fintype.card Row : ℝ) * (Fintype.card Col : ℝ))
      ≤ eventMass (uniformWindow k k hkRow hkCol)
          (fun RS => ¬ Disjoint W (windowCells RS)) := by
  classical
  have hnR : (0 : ℝ) < (Fintype.card Row : ℝ) := by exact_mod_cast hRow
  have hnC : (0 : ℝ) < (Fintype.card Col : ℝ) := by exact_mod_cast hCol
  have hkcast : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hksq : (0 : ℝ) ≤ (k : ℝ) * (k : ℝ) := mul_nonneg hkcast hkcast
  rcases hq with ⟨hqW', hk2⟩ | ⟨hqW, hrw, hsw⟩
  · have h10 := lemma10_bound W' k k hRow hCol hkRow hkCol hind hk2
    have hmono := eventMass_hit_mono hsub k k hkRow hkCol
    have hqR : (q : ℝ) ≤ (W'.card : ℝ) := by exact_mod_cast hqW'
    have hcoef' : (1 / 4) * (q : ℝ) * (k : ℝ) * (k : ℝ)
        ≤ (1 / 2) * (W'.card : ℝ) * (k : ℝ) * (k : ℝ) := by
      nlinarith [hqR, hkcast, hksq]
    have hcoef := div_le_div_of_nonneg_right hcoef'
      (by positivity : (0 : ℝ) ≤ (Fintype.card Row : ℝ) * (Fintype.card Col : ℝ))
    exact le_trans hcoef (le_trans h10 hmono)
  · have h9 := lemma9_bound W k k hRow hCol hkRow hkCol hrw hsw
    have hqR : (q : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hqW
    have hcoef' : (1 / 4) * (q : ℝ) * (k : ℝ) * (k : ℝ)
        ≤ (1 / 4) * (W.card : ℝ) * (k : ℝ) * (k : ℝ) := by
      nlinarith [hqR, hksq]
    have hcoef := div_le_div_of_nonneg_right hcoef'
      (by positivity : (0 : ℝ) ≤ (Fintype.card Row : ℝ) * (Fintype.card Col : ℝ))
    exact le_trans hcoef h9

end Qatlib.Papers.MatProdVerify04.MainResults
