/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Tactic.Ring
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma2RestrictedQuan
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma3RestrictedQuan
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma4RestrictedStat

/-!
# Sign action of the rank-one amplification iterate

This module computes the action of `RankOneReflection.iterate` with both phases equal to -1 on
the good and bad parts of a prepared state. It also proves invariance of the span of the good
and bad components of an arbitrary vector and the prepared state under general unit-modulus
phases. For background, see [BrassardHoyerTapp1998Counting].

## Main statements

* `zoo_counting_two_dimensional_sign_action`: For a unitary preparation, the sign-phase iterate
  acts on the good and bad components by the stated two-dimensional formulas, and their squared
  masses sum to one. See [Brassard et al., Lemma 4][BrassardHoyerTapp1998Counting].

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

open Qatlib.Concepts.AEMeanReadout.RankOneSubspace.RankOneReflection

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace

open scoped BigOperators

/-- The rank-one iterate with unit-modulus phases preserves the span of the good and bad parts
of `v` and of the prepared state `A|0⟩`, when `A * A.conjTranspose = 1`. -/
lemma zoo_counting_two_dimensional_sign_action_span_invariant
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
    (φ ϕ : ℂ) (hφ : ‖φ‖ = 1) (hϕ : ‖ϕ‖ = 1)
    (hA : A * A.conjTranspose = 1) (v : Fin (n + 1) → ℂ) :
    ∀ w ∈ Submodule.span ℂ {RankOneReflection.goodPart g v,
        RankOneReflection.badPart g v,
        RankOneReflection.goodPart g (fun i => A i 0),
        RankOneReflection.badPart g (fun i => A i 0)},
      (RankOneReflection.iterate A g φ ϕ).mulVec w ∈
        Submodule.span ℂ {RankOneReflection.goodPart g v,
          RankOneReflection.badPart g v,
          RankOneReflection.goodPart g (fun i => A i 0),
          RankOneReflection.badPart g (fun i => A i 0)} := by
  intro w hw
  have hψ : (fun i => A i 0) =
      RankOneReflection.goodPart g (fun i => A i 0) +
        RankOneReflection.badPart g (fun i => A i 0) := by
    funext i
    by_cases h : g i <;> simp [RankOneReflection.goodPart, RankOneReflection.badPart, h]
  obtain ⟨hg, hb⟩ := zoo_counting_good_bad_phase_action n A g φ ϕ v hA
  obtain ⟨hga, hba⟩ :=
    zoo_counting_two_dimensional_phase_action n A g φ ϕ hA hφ hϕ
  rw [hψ] at hg hb
  induction hw using Submodule.span_induction with
  | mem x hx =>
      have hx' : x = RankOneReflection.goodPart g v ∨
          x = RankOneReflection.badPart g v ∨
          x = RankOneReflection.goodPart g (fun i => A i 0) ∨
          x = RankOneReflection.badPart g (fun i => A i 0) := by
        simpa using hx
      rcases hx' with rfl | rfl | rfl | rfl
      · rw [hg]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _
            (Submodule.add_mem _
              (Submodule.subset_span (by simp))
              (Submodule.subset_span (by simp))))
      · rw [hb]
        exact Submodule.add_mem _
          (Submodule.neg_mem _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _
            (Submodule.add_mem _
              (Submodule.subset_span (by simp))
              (Submodule.subset_span (by simp))))
      · rw [hga]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      · rw [hba]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  | zero =>
      rw [Matrix.mulVec_zero]
      exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
      rw [Matrix.mulVec_add]
      exact Submodule.add_mem _ ihx ihy
  | smul r x _ ih =>
      rw [Matrix.mulVec_smul]
      exact Submodule.smul_mem _ r ih

/-- For a unitary preparation, the sign-phase iterate acts on the good and bad components by the
stated two-dimensional formulas, and their squared masses sum to one. See [Brassard et al.,
Lemma 4][BrassardHoyerTapp1998Counting]. -/
theorem zoo_counting_two_dimensional_sign_action :
    ∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (g : Fin (n + 1) → Bool),
    A * A.conjTranspose = 1 →
    let ψ : Fin (n + 1) → ℂ := fun i => A i 0;
    let ψa := RankOneReflection.goodPart g ψ;
    let ψb := RankOneReflection.badPart g ψ;
    let a : ℝ := ∑ i, Complex.normSq (ψa i);
    let b : ℝ := ∑ i, Complex.normSq (ψb i);
    (RankOneReflection.iterate A g (-1) (-1)).mulVec ψa =
      (1 - 2 * (a : ℂ)) • ψa - (2 * (a : ℂ)) • ψb ∧
    (RankOneReflection.iterate A g (-1) (-1)).mulVec ψb =
      (1 - 2 * (a : ℂ)) • ψb + (2 * (b : ℂ)) • ψa ∧
    b = 1 - a := by
  intro n A g hA
  have hn : ‖(-1 : ℂ)‖ = 1 := by simp
  obtain ⟨h1, h2⟩ :=
    zoo_counting_two_dimensional_phase_action n A g (-1 : ℂ) (-1 : ℂ) hA hn hn
  have hb := zoo_counting_two_dimensional_phase_action_bad_normSq A g hA
  refine ⟨?_, ?_, hb⟩
  · funext i
    have hi := congrFun h1 i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    rw [hi]
    ring
  · funext i
    have hi := congrFun h2 i
    have hbC : ((∑ j, Complex.normSq
        (RankOneReflection.badPart g (fun k => A k 0) j) : ℝ) : ℂ) =
        1 - ((∑ j, Complex.normSq
          (RankOneReflection.goodPart g (fun k => A k 0) j) : ℝ) : ℂ) := by
      rw [hb, Complex.ofReal_sub, Complex.ofReal_one]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    rw [hi, hbC]
    ring

/-- The sign-action theorem satisfies the proposition `Lemma4RestrictedSpec.expected`. -/
theorem zoo_counting_two_dimensional_sign_action_contract :
    Lemma4RestrictedSpec.expected :=
  zoo_counting_two_dimensional_sign_action

end Qatlib.Concepts.AEMeanReadout.RankOneSubspace
