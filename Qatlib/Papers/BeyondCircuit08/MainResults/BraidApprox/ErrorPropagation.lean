/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BeyondCircuit08.MainResults.Model.WordAlgebra

@[expose] public section

/-!
# Error propagation for composed braid words (Proposition 1)

Paper: Stephen P. Jordan, *Quantum Computation Beyond the Circuit Model*,
arXiv:0809.2307v1 (2008), §3.11, proof of Proposition 1, pp. 81–88.

The recursive construction of Proposition 1 builds a long braid word from
shorter words and needs the approximation error to stay under control when
two approximate unitaries are multiplied: this is the "error propagation"
step of pp. 81–88.  This file formalises that step with the true Euclidean
(L2) operator norm on complex matrices, induced by `Matrix.toEuclideanCLM`
on `EuclideanSpace`.

## Main statements

* `norm_le_one_of_mem_unitaryGroup`: a unitary matrix is a contraction.
* `evalWord_mem_unitaryGroup`: a signed word in unitary generators evaluates
  to a unitary matrix.
* `norm_mul_sub_mul_le`: if `‖B‖ ≤ 1` and `‖U‖ ≤ 1`, then
  `‖A * B - U * V‖ ≤ ‖A - U‖ + ‖B - V‖`.
* `evalWord_append_error_le`: errors add when braid words are concatenated.
* `evalWord_append_error_le_pair`: the simultaneous two-block form used by
  the recursion of Proposition 1, with additive crossing counts.
-/

set_option autoImplicit false
noncomputable section

open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.BeyondCircuit08.MainResults.BraidApprox

open Qatlib.Papers.BeyondCircuit08.MainResults.Model

/-- A unitary complex matrix has L2 operator norm at most `1`, by the
C*-identity `‖Uᴴ * U‖ = ‖U‖ * ‖U‖` and `star U * U = 1`. -/
theorem norm_le_one_of_mem_unitaryGroup {ι : Type} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    ‖U‖ ≤ 1 := by
  have hstar : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hsq : ‖U‖ * ‖U‖ ≤ 1 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self U
    rw [← Matrix.star_eq_conjTranspose, hstar, Matrix.cstar_norm_def (1 : Matrix ι ι ℂ),
      map_one] at h
    exact h.symm.le.trans ContinuousLinearMap.norm_id_le
  nlinarith [sq_nonneg (‖U‖ - 1)]

/-- The matrix inverse of a unitary matrix again lies in the unitary group:
for unitary `U` one has `U⁻¹ = star U`, and `star (star U) * star U = 1`. -/
theorem inv_mem_unitaryGroup_of_mem {ι : Type} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    U⁻¹ ∈ Matrix.unitaryGroup ι ℂ := by
  have h1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hinv : U⁻¹ = star U := Matrix.inv_eq_right_inv h1
  rw [Matrix.mem_unitaryGroup_iff', hinv, star_star]
  exact h1

/-- Evaluating a signed braid word in unitary generators gives a unitary
matrix: the empty word gives `1`, and each signed generator factor is
unitary, the inverse factors by `inv_mem_unitaryGroup_of_mem`. -/
theorem evalWord_mem_unitaryGroup {ι : Type} [Fintype ι] [DecidableEq ι]
    {k : ℕ} {gen : Fin (k - 1) → Matrix ι ι ℂ}
    (hgen : ∀ i, gen i ∈ Matrix.unitaryGroup ι ℂ) (w : BraidWord k) :
    evalWord gen w ∈ Matrix.unitaryGroup ι ℂ := by
  induction w with
  | nil =>
      rw [evalWord_nil]
      exact one_mem _
  | cons g w ih =>
      have hfactor : (if g.2 then gen g.1 else (gen g.1)⁻¹) ∈
          Matrix.unitaryGroup ι ℂ := by
        by_cases hb : g.2
        · rw [ite_eq_left hb]
          exact hgen _
        · rw [ite_eq_right hb]
          exact inv_mem_unitaryGroup_of_mem (hgen _)
      have hcons : evalWord gen (g :: w) =
          (if g.2 then gen g.1 else (gen g.1)⁻¹) * evalWord gen w := by
        simp [evalWord]
      rw [hcons]
      exact mul_mem hfactor ih

/-- Operator-norm error of a product: if `‖B‖ ≤ 1` and `‖U‖ ≤ 1`, then the
error of the product `A * B` against `U * V` is at most the sum of the
factor errors, via `A * B - U * V = (A - U) * B + U * (B - V)` and
submultiplicativity of the L2 operator norm. -/
theorem norm_mul_sub_mul_le {ι : Type} [Fintype ι] [DecidableEq ι]
    {A B U V : Matrix ι ι ℂ} (hB : ‖B‖ ≤ 1) (hU : ‖U‖ ≤ 1) :
    ‖A * B - U * V‖ ≤ ‖A - U‖ + ‖B - V‖ := by
  have hdecomp : A * B - U * V = (A - U) * B + U * (B - V) := by
    noncomm_ring
  rw [hdecomp]
  calc ‖(A - U) * B + U * (B - V)‖
      ≤ ‖(A - U) * B‖ + ‖U * (B - V)‖ := norm_add_le _ _
    _ ≤ ‖A - U‖ * ‖B‖ + ‖U‖ * ‖B - V‖ :=
        add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
    _ ≤ ‖A - U‖ + ‖B - V‖ :=
        add_le_add (mul_le_of_le_one_right (norm_nonneg _) hB)
          (mul_le_of_le_one_left (norm_nonneg _) hU)

/-- Concatenating braid words on `extraStrands + 2` strands adds the
approximation errors: if `w₁` and `w₂` approximate targets `U₁` and `U₂`
with errors `ε₁` and `ε₂` in the L2 operator norm and `U₁` is unitary,
then the concatenation approximates `U₁ * U₂` with
error at most `ε₁ + ε₂`.  This is the error-propagation step of the
recursive proof of Proposition 1 of [Jordan2008]. -/
theorem evalWord_append_error_le {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {extraStrands : ℕ} {gen : Fin (extraStrands + 2 - 1) → Matrix ι ι ℂ}
    (hgen : ∀ i, gen i ∈ Matrix.unitaryGroup ι ℂ) (w₁ w₂ : BraidWord (extraStrands + 2))
    {U₁ U₂ : Matrix ι ι ℂ} (hU₁ : U₁ ∈ Matrix.unitaryGroup ι ℂ) {ε₁ ε₂ : ℝ}
    (h₁ : ‖evalWord gen w₁ - U₁‖ ≤ ε₁) (h₂ : ‖evalWord gen w₂ - U₂‖ ≤ ε₂) :
    ‖evalWord gen (List.append w₁ w₂) - U₁ * U₂‖ ≤ ε₁ + ε₂ := by
  rw [evalWord_append]
  refine le_trans (norm_mul_sub_mul_le ?_ ?_) (add_le_add h₁ h₂)
  · exact norm_le_one_of_mem_unitaryGroup (evalWord_mem_unitaryGroup hgen w₂)
  · exact norm_le_one_of_mem_unitaryGroup hU₁

/-- Simultaneous two-block error propagation, in the shape consumed by the
recursion of Proposition 1: the *same* concatenated word `w₁ ++ w₂` is
evaluated in two unitary representations, the errors on both blocks add,
and the crossing count of the concatenation is the sum of the crossing
counts. -/
theorem evalWord_append_error_le_pair {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] [Fintype ι'] [DecidableEq ι'] [Nonempty ι'] {extraStrands : ℕ}
    {gen : Fin (extraStrands + 2 - 1) → Matrix ι ι ℂ}
    {gen' : Fin (extraStrands + 2 - 1) → Matrix ι' ι' ℂ}
    (hgen : ∀ i, gen i ∈ Matrix.unitaryGroup ι ℂ)
    (hgen' : ∀ i, gen' i ∈ Matrix.unitaryGroup ι' ℂ) (w₁ w₂ : BraidWord (extraStrands + 2))
    {U₁ U₂ : Matrix ι ι ℂ} (hU₁ : U₁ ∈ Matrix.unitaryGroup ι ℂ)
    {V₁ V₂ : Matrix ι' ι' ℂ} (hV₁ : V₁ ∈ Matrix.unitaryGroup ι' ℂ)
    {ε₁ ε₂ δ₁ δ₂ : ℝ}
    (h₁ : ‖evalWord gen w₁ - U₁‖ ≤ ε₁) (h₂ : ‖evalWord gen w₂ - U₂‖ ≤ ε₂)
    (h₁' : ‖evalWord gen' w₁ - V₁‖ ≤ δ₁) (h₂' : ‖evalWord gen' w₂ - V₂‖ ≤ δ₂) :
    ‖evalWord gen (List.append w₁ w₂) - U₁ * U₂‖ ≤ ε₁ + ε₂ ∧
      ‖evalWord gen' (List.append w₁ w₂) - V₁ * V₂‖ ≤ δ₁ + δ₂ ∧
      crossingCount (List.append w₁ w₂) = crossingCount w₁ + crossingCount w₂ := by
  refine ⟨?_, ?_, ?_⟩
  · exact evalWord_append_error_le hgen w₁ w₂ hU₁ h₁ h₂
  · exact evalWord_append_error_le hgen' w₁ w₂ hV₁ h₁' h₂'
  · exact crossingCount_append w₁ w₂

end Qatlib.Papers.BeyondCircuit08.MainResults.BraidApprox
