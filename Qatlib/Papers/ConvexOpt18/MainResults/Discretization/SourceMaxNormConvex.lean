/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ConvexOpt18.MainResults.Model.SourceAnalyticModel

set_option backward.isDefEq.respectTransparency false

/-!
# Convexity of the Max-Norm Lower-Bound Objective

This module formalizes Lemma C.1 of [Chakrabarti et al., 2020][ChakrabartiChildsLiWu2020], proving
that the projected max-norm objective `maxNormObjective c` is convex on `ℝⁿ` for every Boolean
center `c ∈ {0, 1}ⁿ`.

## Main statements

* `piProj_eq`, `projectionPenalty_eq_max`, `projectionPenalty_identity`: piecewise characterization
  of `[0, 1]`-projection and its coordinate penalty.
* `maxNormObjective_eq_sup`: restriction of `maxNormObjective c` to `[0, 1]ⁿ`.
* `source_lemma_C_1`: convexity `ConvexOn ℝ Set.univ (fun x => maxNormObjective c x)` for
  `c ∈ {0, 1}ⁿ`.

## References

* [Chakrabarti et al., 2020][ChakrabartiChildsLiWu2020]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ConvexOpt18.MainResults

/-- The projection `π` of (C.2), in piecewise form. -/
lemma piProj_eq (x : ℝ) : piProj x = if x < 0 then 0 else if x ≤ 1 then x else 1 := by
  unfold piProj
  split_ifs with h1 h2
  · rw [min_eq_left (by linarith), max_eq_left (le_of_lt h1)]
  · rw [min_eq_left h2, max_eq_right (not_lt.mp h1)]
  · rw [min_eq_right (le_of_lt (not_le.mp h2)), max_eq_right zero_le_one]

/-- Equation (C.3): the penalty `g_i(x) = |π(x_i) - x_i|` vanishes on `[0,1]` and equals
`max{-x_i, 0, x_i-1}`. -/
lemma projectionPenalty_eq_max {n : ℕ} (x : Pt n) (i : Fin n) :
    projectionPenalty x i = max (max (-(x i)) 0) (x i - 1) := by
  unfold projectionPenalty
  rw [piProj_eq]
  split_ifs with h1 h2
  · rw [abs_of_pos (by linarith : 0 < 0 - x i),
      max_eq_left (by linarith : -(x i) ≥ 0),
      max_eq_left (by linarith : -(x i) ≥ x i - 1)]
    ring
  · rw [sub_self, abs_zero,
      max_eq_right (by linarith : -(x i) ≤ 0),
      max_eq_left (by linarith : (0 : ℝ) ≥ x i - 1)]
  · rw [abs_of_neg (by linarith : 1 - x i < 0),
      max_eq_right (by linarith : -(x i) ≤ 0),
      max_eq_right (by linarith : (0 : ℝ) ≤ x i - 1)]
    ring

/-- Projection identity used in (C.4): `|π(x)| + |π(x) - x| = |x|`. -/
lemma abs_piProj_add (x : ℝ) : |piProj x| + |piProj x - x| = |x| := by
  rw [piProj_eq]
  split_ifs with h1 h2
  · rw [abs_zero, zero_add, abs_of_pos (by linarith : 0 < 0 - x), abs_of_neg h1]
    ring
  · rw [sub_self, abs_zero, add_zero]
  · rw [abs_one, abs_of_neg (by linarith : 1 - x < 0),
      abs_of_pos (by linarith : 0 < x)]
    ring

/-- Projection identity used in (C.5)--(C.6): `|π(x) - 1| + |π(x) - x| = |x - 1|`. -/
lemma abs_piProj_sub_one (x : ℝ) : |piProj x - 1| + |piProj x - x| = |x - 1| := by
  rw [piProj_eq]
  split_ifs with h1 h2
  · rw [zero_sub, abs_neg, abs_one, abs_of_pos (by linarith : 0 < 0 - x)]
    have hR : |x - 1| = 1 - x := by
      rw [abs_of_neg (by linarith : x - 1 < 0)]; ring
    rw [hR]; ring
  · rw [sub_self, abs_zero, add_zero]
  · rw [sub_self, abs_zero, zero_add, abs_sub_comm]

/-- Equations (C.4)--(C.6): for `c_i ∈ {0,1}`,
`h_{c,i}(x) = |π(x_i) - c_i| + |π(x_i) - x_i| = |x_i - c_i|`. -/
lemma projectionPenalty_identity {n : ℕ} (x : Pt n) (c : Pt n) (i : Fin n)
    (hc : c i = 0 ∨ c i = 1) :
    |piProj (x i) - c i| + projectionPenalty x i = |x i - c i| := by
  unfold projectionPenalty
  rcases hc with hc | hc
  · rw [hc, sub_zero, sub_zero]
    exact abs_piProj_add (x i)
  · rw [hc]
    exact abs_piProj_sub_one (x i)

/-- Equation (3.14) restricted to `[0,1]ⁿ`: `f_c(x) = max_i |x_i - c_i|` for `x ∈ [0,1]ⁿ`. -/
lemma maxNormObjective_eq_sup {n : ℕ} (c x : Pt n) (hc : ∀ i, c i = 0 ∨ c i = 1)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1) :
    maxNormObjective c x = ⨆ i, |x i - c i| := by
  have hpi : ∀ i : Fin n, piProj (x i) = x i := by
    intro i
    rcases hc i with _ | _ <;>
      · rw [piProj_eq]
        split_ifs <;> linarith [hx0 i, hx1 i]
  unfold maxNormObjective
  have hsum : (∑ i, projectionPenalty x i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    unfold projectionPenalty
    rw [hpi i, sub_self, abs_zero]
  rw [hsum, add_zero]
  congr 1
  funext i
  rw [hpi i]

private lemma coordinate_affine_convex {n : ℕ} (i : Fin n) (a b : ℝ) :
    ConvexOn ℝ Set.univ (fun x : Pt n => a * x i + b) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ u v _ _ huv
  change a * (u * x i + v * y i) + b ≤ u * (a * x i + b) + v * (a * y i + b)
  nlinarith [congrArg (fun t : ℝ => t * b) huv]

private lemma projectionPenalty_convex {n : ℕ} (i : Fin n) :
    ConvexOn ℝ Set.univ (fun x : Pt n => projectionPenalty x i) := by
  have hneg : ConvexOn ℝ Set.univ (fun x : Pt n => -(x i)) := by
    simpa using coordinate_affine_convex i (-1) 0
  have hsub : ConvexOn ℝ Set.univ (fun x : Pt n => x i - 1) := by
    simpa [sub_eq_add_neg] using coordinate_affine_convex i 1 (-1)
  have heq : (fun x : Pt n => projectionPenalty x i) =
      ((fun x : Pt n => -(x i)) ⊔ (fun _ => (0 : ℝ))) ⊔ (fun x => x i - 1) := by
    funext x
    exact projectionPenalty_eq_max x i
  rw [heq]
  exact (hneg.sup (convexOn_const 0 convex_univ)).sup hsub

private lemma projectionPenalty_sum_convex {n : ℕ} (s : Finset (Fin n)) :
    ConvexOn ℝ Set.univ (fun x : Pt n => ∑ i ∈ s, projectionPenalty x i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set (Pt n))))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (show ConvexOn ℝ Set.univ (fun x : Pt n =>
        projectionPenalty x i + ∑ j ∈ s, projectionPenalty x j) from
        (projectionPenalty_convex i).add ih)

private lemma finite_max_convex {n : ℕ} (s : Finset (Fin n)) (hs : s.Nonempty)
    (F : Fin n → Pt n → ℝ) (hF : ∀ i ∈ s, ConvexOn ℝ Set.univ (F i)) :
    ConvexOn ℝ Set.univ (fun x => s.sup' hs (fun i => F i x)) := by
  have h : ConvexOn ℝ Set.univ (s.sup' hs F) :=
    Finset.sup'_induction hs F (fun _ hf _ hg => hf.sup hg) hF
  simpa only [← Finset.sup'_apply] using h

/-- Lemma C.1 (p. 38): the max-norm objective `f_c` of (C.1) is convex on `ℝⁿ` for
`c ∈ {0,1}ⁿ`.  The paper's proof writes `f_c` as the pointwise maximum of the `n` convex
functions `h_{c,i}(x) + Σ_{j≠i} g_j(x)` (equation (C.9)), using
`h_{c,i}(x) = |x_i - c_i|` (proved above). -/
theorem source_lemma_C_1 {n : ℕ} (c : Pt n) (hc : ∀ i, c i = 0 ∨ c i = 1) :
    ConvexOn ℝ Set.univ (fun x => maxNormObjective c x) := by
  cases n with
  | zero =>
    simpa [maxNormObjective, iSup, Real.sSup_empty] using
      (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set (Pt 0))))
  | succ n =>
    let F (i : Fin (n + 1)) (x : Pt (n + 1)) : ℝ :=
      |x i - c i| + ∑ j ∈ Finset.univ.erase i, projectionPenalty x j
    have hF : ∀ i, ConvexOn ℝ Set.univ (F i) := by
      intro i
      have hpos : ConvexOn ℝ Set.univ (fun x : Pt (n + 1) => x i - c i) := by
        simpa [sub_eq_add_neg] using coordinate_affine_convex i 1 (-c i)
      have hneg : ConvexOn ℝ Set.univ (fun x : Pt (n + 1) => -(x i - c i)) := by
        simpa [sub_eq_add_neg, add_comm] using coordinate_affine_convex i (-1) (c i)
      have habs : ConvexOn ℝ Set.univ (fun x : Pt (n + 1) => |x i - c i|) := by
        have heq : (fun x : Pt (n + 1) => |x i - c i|) =
            (fun x => x i - c i) ⊔ (fun x => -(x i - c i)) := by
          funext x
          exact abs_eq_max_neg
        rw [heq]
        exact hpos.sup hneg
      exact habs.add (projectionPenalty_sum_convex (Finset.univ.erase i))
    have hne : (Finset.univ : Finset (Fin (n + 1))).Nonempty := ⟨0, Finset.mem_univ 0⟩
    have heq : (fun x => maxNormObjective c x) =
        (fun x => Finset.univ.sup' hne (fun i => F i x)) := by
      funext x
      have hcoordinate (i : Fin (n + 1)) :
          |piProj (x i) - c i| + ∑ j, projectionPenalty x j = F i x := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← add_assoc,
          projectionPenalty_identity x c i (hc i)]
      have hsup : (⨆ i, |piProj (x i) - c i|) =
          Finset.univ.sup' hne (fun i => |piProj (x i) - c i|) := by
        apply le_antisymm
        · exact ciSup_le (fun i =>
            Finset.le_sup' (fun i : Fin (n + 1) => |piProj (x i) - c i|) (Finset.mem_univ i))
        · exact Finset.sup'_le hne _ (fun i _ =>
            le_ciSup (Finite.bddAbove_range (fun i : Fin (n + 1) => |piProj (x i) - c i|)) i)
      unfold maxNormObjective
      rw [hsup, Finset.apply_sup'_eq_sup'_comp hne
        (fun t : ℝ => t + ∑ j, projectionPenalty x j) (fun _ _ => (max_add_add_right _ _ _).symm)]
      exact Finset.sup'_congr hne rfl (fun i _ => hcoordinate i)
    rw [heq]
    exact finite_max_convex Finset.univ hne F (fun i _ => hF i)

end Qatlib.Papers.ConvexOpt18.MainResults
