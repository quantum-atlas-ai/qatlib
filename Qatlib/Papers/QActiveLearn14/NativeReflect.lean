/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.FlagProjection.Coherence
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QActiveLearn14.NativeReflect
open Qatlib.Foundations.MatrixGeometry.FlagProjection
variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in

theorem actual_input (pi : X → ℝ) (P : X → X → ℝ)
    (hn : ∀ x, 0 ≤ pi x) (hs : ∑ x, pi x = 1)
    (hP : ∀ j i, 0 ≤ P j i) (hsP : ∀ i, ∑ j, P j i = 1) :
    inner ℂ (pairCoherent pi P) (pairCoherent pi P) = 1 ∧
    ∀ i, (∑ j, ‖(pairCoherent pi P).ofLp (i,j)‖^2) = pi i :=
  ⟨pair_unit pi P hn hs hP hsP, pair_marginal pi P hn hP hsP⟩

theorem source_lemma6_figure (pi : X → ℝ) (P : X → X → ℝ)
    (hn : ∀ x, 0 ≤ pi x) (hP : ∀ j i, 0 ≤ P j i) (hsP : ∀ i, ∑ j, P j i = 1)
    (S : Finset X) (hflag : 0 < ∑ i ∈ S, pi i) (a b : ℂ) :
    hyper (tail (pairFlags S) (pairCoherent pi P))
      (a • pairCoherent pi P + b • tail (pairFlags S) (pairCoherent pi P)) =
    -checkFig (pairFlags S)
      (a • pairCoherent pi P + b • tail (pairFlags S) (pairCoherent pi P)) := by
  have hp : 0 < mass (pairFlags S) (pairCoherent pi P) := by
    rw [pair_mass pi P hn hP hsP]; exact hflag
  exact figure_lemma6 _ _ hp a b

theorem literal_lemma6_fails (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v) :
    hyper (tail S v) (tail S v) ≠ -check8 S (tail S v) := by
  have hh : hyper (tail S v) (tail S v) = -tail S v := by
    rw [hyper, tail_unit S v hp]
    module
  have hc : check8 S (tail S v) = -tail S v := by
    rw [check8, project_tail]
    module
  rw [hh, hc, neg_neg]
  intro he
  have hi := congrArg (fun q => inner ℂ (tail S v) q) he
  try dsimp only at hi
  rw [inner_neg_right, tail_unit S v hp] at hi
  norm_num at hi

theorem ideal_output_tail (pi : X → ℝ) (P : X → X → ℝ)
    (hn : ∀ x, 0 ≤ pi x) (hs : ∑ x, pi x = 1)
    (hP : ∀ j i, 0 ≤ P j i) (hsP : ∀ i, ∑ j, P j i = 1)
    (S : Finset X) (hflag : 0 < ∑ i ∈ S, pi i) (n : ℕ)
    (houtput : 0 < mass (pairFlags S) (runFig (pairFlags S) (pairCoherent pi P) n)) (i : X) :
    (∑ j, conditionalBorn (pairFlags S) (runFig (pairFlags S) (pairCoherent pi P) n) (i,j)) =
      if i ∈ S then pi i / (∑ x ∈ S, pi x) else 0 := by
  have hp : 0 < mass (pairFlags S) (pairCoherent pi P) := by
    rw [pair_mass pi P hn hP hsP]; exact hflag
  have hout := houtput
  rw [figure_mass] at hout
  have hl := figure_conditional (pairFlags S) (pairCoherent pi P) hp
    (pair_unit pi P hn hs hP hsP) n hout
  simp_rw [hl]
  exact pair_conditional pi P hn hP hsP S i

theorem ideal_word_normalized (pi : X → ℝ) (P : X → X → ℝ)
    (hn : ∀ x, 0 ≤ pi x) (hs : ∑ x, pi x = 1)
    (hP : ∀ j i, 0 ≤ P j i) (hsP : ∀ i, ∑ j, P j i = 1)
    (S : Finset X) (n : ℕ) :
    ‖runFig (pairFlags S) (pairCoherent pi P) n‖^2 = 1 := by
  have hu := pair_unit pi P hn hs hP hsP
  have hv : ‖pairCoherent pi P‖^2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hu]
    norm_num
  rw [runFig_phase, norm_smul, mul_pow, run_norm_sq _ _ hu n, hv]
  norm_num
end Qatlib.Papers.QActiveLearn14.NativeReflect
