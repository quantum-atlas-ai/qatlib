/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.WeightEnum07.MainResults.Theorem13
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# Euclidean weight geometry

Geraci--Van Bussel's weight enumerator counts nonzero coordinates.  This file records the
corresponding finite-dimensional geometry without replacing the Euclidean norm by a coordinate
maximum.  A word is embedded as its support indicator in `EuclideanSpace`, so its squared norm is
exactly its Hamming weight.  Filtering the words of the finite code model by that norm squared
therefore gives the weight counts used by the enumerator.  This identity concerns exact weights.

The same support defines a diagonal projector.  Its `L2Operator` norm is at most one, with
equality when the word has nonempty support.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Papers.WeightEnum07.MainResults

namespace Qatlib.Papers.WeightEnum07.MainResults

/-- The Euclidean support indicator of an integer word. -/
def supportVector {n : ℕ} (w : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => if w i = 0 then 0 else 1)

/-- The diagonal support projector of an integer word. -/
def supportProjector {n : ℕ} (w : Fin n → ℤ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => if w i = 0 then 0 else 1)

/-- The support indicator has squared Euclidean norm equal to the Hamming weight. -/
theorem supportVector_norm_sq {n : ℕ} (w : Fin n → ℤ) :
    ‖supportVector w‖ ^ 2 = (hammingWeightOf w : ℝ) := by
  change ‖supportVector w‖ ^ 2 =
    (Nat.card {i : Fin n // w i ≠ 0} : ℝ)
  have hcard : Nat.card {i : Fin n // w i ≠ 0} =
      (Finset.univ.filter (fun i : Fin n => w i ≠ 0)).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype _
  have hsum : (∑ i : Fin n, (if w i = 0 then (0 : ℝ) else 1)) =
      ((Finset.univ.filter (fun i : Fin n => w i ≠ 0)).card : ℝ) := by
    simpa using (Finset.natCast_card_filter (R := ℝ)
      (fun i : Fin n => w i ≠ 0) (Finset.univ : Finset (Fin n))).symm
  calc
    ‖supportVector w‖ ^ 2 =
        ∑ i : Fin n, (if w i = 0 then (0 : ℝ) else 1) := by
      rw [supportVector, EuclideanSpace.norm_sq_eq]
      simp [Real.norm_eq_abs]
    _ = ((Finset.univ.filter (fun i : Fin n => w i ≠ 0)).card : ℝ) := hsum
    _ = (Nat.card {i : Fin n // w i ≠ 0} : ℝ) := by rw [hcard]

open Classical in
/-- The exact weight counts are the cardinalities of the squared Euclidean norm level sets. -/
theorem weightCounts_eq_card_filter_supportVector_norm_sq (code : ICQCode) (i : ℕ) :
    code.weightCounts i =
      (code.words.filter (fun w => ‖supportVector w‖ ^ 2 = (i : ℝ))).card := by
  rw [code.weightCounts_spec]
  congr 1
  ext w
  simp only [Finset.mem_filter, supportVector_norm_sq, Nat.cast_inj]

/-- Every support projector is a contraction in the Euclidean operator norm. -/
theorem supportProjector_opNorm_le_one {n : ℕ} (w : Fin n → ℤ) :
    ‖supportProjector w‖ ≤ 1 := by
  rw [supportProjector, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).2
  intro i
  by_cases h : w i = 0 <;> simp [h]

/-- A nonempty support gives the sharp L2 operator norm of the support projector. -/
theorem supportProjector_opNorm_eq_one {n : ℕ} (w : Fin n → ℤ)
    (hsupport : ∃ i, w i ≠ 0) :
    ‖supportProjector w‖ = 1 := by
  apply le_antisymm (supportProjector_opNorm_le_one w)
  rw [supportProjector, Matrix.l2_opNorm_diagonal]
  obtain ⟨i, hi⟩ := hsupport
  simpa [hi] using
    (norm_le_pi_norm (fun j : Fin n => if w j = 0 then (0 : ℂ) else 1) i)

/-- One is a uniform upper bound for the support projector norms at any positive word length. -/
theorem supportProjector_uniform_bound {n : ℕ} (_hn : 0 < n) :
    ∀ w : Fin n → ℤ, ‖supportProjector w‖ ≤ 1 := by
  intro w
  exact supportProjector_opNorm_le_one w

end Qatlib.Papers.WeightEnum07.MainResults
