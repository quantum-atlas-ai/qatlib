/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QActiveLearn14.TailedBounds
import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Adaptive remixing with one unflagged state

The repeat program in [PaparoEtAl2014], Theorem 4, starts its next mixing block at the
last sampled state. With a sole unflagged state, the first-hit law is exactly geometric
after the first failed check. A positive reversible three-state kernel shows that this
law can differ from the flagged conditional law of the first check, the identification
made in Equation (21). The kernel here represents the whole mixing block.
-/

namespace Qatlib.Papers.QActiveLearn14.ClassicalAgent

open Qatlib.Papers.QActiveLearn14.TailedBounds

variable {X : Type*}

/-- Probability of first hitting the flagged output `x` on check `n+1`, where the sole
unflagged state is `u` and `y` is the initial state. The kernel is indexed destination first. -/
def soleUnflaggedHit (K : X → X → ℝ) (u : X) (x : {x : X // x ≠ u}) : X → ℕ → ℝ
  | y, 0 => K x y
  | y, n + 1 => K u y * soleUnflaggedHit K u x u n

/-- If the retry state has positive escape probability, summing the successive disjoint
first-hit events gives the actual eventual probability of a flagged output. -/
theorem sole_unflagged_hit_hasSum (K : X → X → ℝ)
    (u y : X) (x : {x : X // x ≠ u}) (h₀ : 0 ≤ K u u) (h₁ : K u u < 1) :
    HasSum (soleUnflaggedHit K u x y) (K x y + K u y * K x u / (1 - K u u)) := by
  have hterm (n : ℕ) :
      soleUnflaggedHit K u x y (n + 1) = K u y * (K u u) ^ n * K x u := by
    induction n generalizing y with
    | zero => simp [soleUnflaggedHit]
    | succ n ih => rw [soleUnflaggedHit, ih u, pow_succ]; ring
  have htail : HasSum (fun n => soleUnflaggedHit K u x y (n + 1))
      (K u y * K x u / (1 - K u u)) := by
    simp_rw [hterm]
    convert ((hasSum_geometric_of_lt_one h₀ h₁).mul_left (K u y)).mul_right (K x u) using 1
    ring
  rw [← hasSum_nat_add_iff' 1]
  simpa [soleUnflaggedHit] using htail

/-- A three-state mixing kernel with self-loop probability `1/2` and cross-state probability
`1/4`. It has positive transitions and is reversible for the uniform law. -/
noncomputable def threeStateKernel (x y : Fin 3) : ℝ := if x = y then 1 / 2 else 1 / 4

/-- Every entry of the example kernel is positive, its columns sum to one, and it satisfies
detailed balance for the strictly positive uniform stationary law. -/
theorem three_state_kernel_properties :
    (∀ x y, 0 < threeStateKernel x y) ∧
    (∀ y, ∑ x, threeStateKernel x y = 1) ∧
    (∀ x y, (1 / 3 : ℝ) * threeStateKernel x y = (1 / 3 : ℝ) * threeStateKernel y x) := by
  refine ⟨fun x y => ?_, ?_, fun x y => ?_⟩
  · unfold threeStateKernel
    split <;> norm_num
  · intro y
    fin_cases y <;> norm_num [Fin.sum_univ_three, threeStateKernel]
  · by_cases h : x = y
    · subst y; rfl
    · simp [threeStateKernel, h, Ne.symm h]

/-- From state `0` with flags `{0, 1}`, the actual eventual probability of output `0`
is `5/8`, whereas conditioning the first check gives `2/3`. Thus the reset-law premise
in [PaparoEtAl2014], Equation (21), can fail even for a positive reversible kernel. -/
theorem adaptive_hit_ne_first_tail :
    (∑' n, soleUnflaggedHit threeStateKernel 2 ⟨0, by decide⟩ 0 n) = 5 / 8 ∧
    tailed (fun x => threeStateKernel x 0) ({0, 1} : Finset (Fin 3)) 0 = 2 / 3 ∧
    (∑' n, soleUnflaggedHit threeStateKernel 2 ⟨0, by decide⟩ 0 n) ≠
      tailed (fun x => threeStateKernel x 0) ({0, 1} : Finset (Fin 3)) 0 := by
  have h₁ := (sole_unflagged_hit_hasSum threeStateKernel 2 0 ⟨0, by decide⟩
    (by norm_num [threeStateKernel]) (by norm_num [threeStateKernel])).tsum_eq
  norm_num [threeStateKernel] at h₁
  have h₂ : tailed (fun x => threeStateKernel x 0) ({0, 1} : Finset (Fin 3)) 0 = 2 / 3 := by
    norm_num [tailed, flaggedMass, threeStateKernel, Finset.sum_insert, Finset.sum_singleton]
  exact ⟨h₁, h₂, by rw [h₁, h₂]; norm_num⟩

end Qatlib.Papers.QActiveLearn14.ClassicalAgent
