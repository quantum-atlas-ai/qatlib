/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkSpectra04.WalkDefinition.SzegedyDefTwoDiscriminantStat

/-!
# Bipartite discriminant identities

This module proves the discriminant formulation of Definition 2 in [Szegedy2004]. Normalized
nonnegative kernels yield isometric frames, whose cross Gram matrix has entries given by square
roots of products of kernel entries. `szegedyDefTwoDiscriminant` combines these facts with the
tilde Gram identity and the block discriminant of a transition matrix.

## Main statements

* `szegedyDefTwoDiscriminant`: the frame, Gram, and transition-matrix discriminant identities.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.WalkSearch.TwoLevelLower

namespace Qatlib.Papers.QWalkSpectra04.WalkDefinition

/-- The frame `paperFrameA c` is isometric when `c` has nonnegative entries and every row sums
to one. -/
private theorem frameA_isometry {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (c : I → J → ℝ)
    (hn : ∀ i j, 0 ≤ c i j) (hs : ∀ i, ∑ j, c i j = 1) :
    IsIsometry (paperFrameA c) := by
  ext x x'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
    paperFrameA, Matrix.of_apply, Matrix.one_apply]
  by_cases hxx' : x = x'
  · subst hxx'
    have hkey : ∀ p : I × J,
        (starRingEnd ℂ) (if p.1 = x then ((Real.sqrt (c x p.2) : ℂ)) else 0)
            * (if p.1 = x then ((Real.sqrt (c x p.2) : ℂ)) else 0)
          = if p.1 = x then ((c x p.2 : ℂ)) else 0 := by
      intro p
      by_cases hp : p.1 = x
      · rw [if_pos hp, if_pos hp, Complex.conj_ofReal, ← Complex.ofReal_mul, ← sq,
          Real.sq_sqrt (hn x p.2)]
      · rw [if_neg hp, if_neg hp, map_zero, zero_mul]
    rw [Finset.sum_congr rfl (fun p _ => hkey p), Fintype.sum_prod_type,
      Finset.sum_eq_single x]
    · simp only [if_true]
      exact_mod_cast hs x
    · intro a _ ha
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [if_neg (fun e : (a, y).1 = x => ha e)]
    · intro hcon
      exact absurd (Finset.mem_univ x) hcon
  · have hzero : ∀ p : I × J,
        (starRingEnd ℂ) (if p.1 = x then ((Real.sqrt (c x p.2) : ℂ)) else 0)
            * (if p.1 = x' then ((Real.sqrt (c x' p.2) : ℂ)) else 0) = 0 := by
      intro p
      by_cases hp : p.1 = x
      · simp only [if_pos hp,
          if_neg (show ¬(p.1 = x') from fun e => hxx' (hp.symm.trans e)), mul_zero]
      · simp only [if_neg hp, map_zero, zero_mul]
    rw [Finset.sum_eq_zero (fun p _ => hzero p), if_neg hxx']

/-- The frame `paperFrameB r` is isometric when `r` has nonnegative entries and every row sums
to one. -/
private theorem frameB_isometry {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (r : J → I → ℝ)
    (hn : ∀ j i, 0 ≤ r j i) (hs : ∀ j, ∑ i, r j i = 1) :
    IsIsometry (paperFrameB r) := by
  have ha := frameA_isometry r hn hs
  ext j k
  change (∑ p : I×J, star (paperFrameB r p j) * paperFrameB r p k) = (1 : Matrix J J ℂ) j k
  have hh := congrFun (congrFun ha j) k
  change (∑ p : J×I, star (paperFrameA r p j) * paperFrameA r p k) = _ at hh
  simp only [paperFrameA, paperFrameB, Matrix.of_apply, Fintype.sum_prod_type] at hh ⊢
  rw [Finset.sum_comm]
  exact hh

/-- Establishes `SzegedyDefTwoDiscriminant`, including frame isometry, cross Gram entries, the
tilde Gram identity, and the transition-matrix block discriminant. See [Szegedy, Definition
2][Szegedy2004]. -/
theorem szegedyDefTwoDiscriminant : SzegedyDefTwoDiscriminant := by
  intro I J _ _ _ _ c r h
  have ha := frameA_isometry c h.1 h.2.1
  have hb := frameB_isometry r h.2.2.1 h.2.2.2
  refine ⟨ha, hb, ?_, (bipartite_discriminant_tilde_bridge (I×J) I J _ _ ha hb).2.1, ?_⟩
  · intro i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, paperFrameA, paperFrameB,
      Matrix.of_apply, RCLike.star_def]
    rw [Finset.sum_eq_single (i,j)]
    · simp only [if_true, Complex.conj_ofReal, ← Complex.ofReal_mul,
        ← Real.sqrt_mul (h.1 i j)]
    · intro p _ hp
      by_cases hi : p.1 = i
      · have hj : p.2 ≠ j := fun hj => hp (Prod.ext hi hj)
        simp [hi, hj]
      · simp [hi]
    · simp
  · intro K _ _ P hP
    have hB : paperFrameB P = SzegedyIsometryB P := by
      ext ⟨a,b⟩ j
      exact (szegedyIsometryB_apply P a b j).symm
    refine ⟨rfl, hB, ?_⟩
    have hgram := szegedy_gram_eq_discriminant P hP
    have hrev : (SzegedyIsometryB P)ᴴ * SzegedyIsometry P =
        (SzegedyDiscriminant P).map Complex.ofReal := by
      calc
        _ = ((SzegedyIsometry P)ᴴ * SzegedyIsometryB P)ᴴ := by simp
        _ = (SzegedyIsometry P)ᴴ * SzegedyIsometryB P := szegedy_gram_hermitian P hP
        _ = _ := hgram
    simp only [bipartiteDiscriminant, hgram, hrev]

end Qatlib.Papers.QWalkSpectra04.WalkDefinition
