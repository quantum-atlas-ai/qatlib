/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Qatlib.Papers.NestedQWalk12.CoherentTrunc.Native

@[expose] public section

/-!
# Operator-norm truncation error for coherent conversion

Source: [JefferyKothariMagniez2013], Lemma 3.3. For the lemma's identity-replacement
construction, converting the coherent input `|s⟩ = ∑ᵢ αᵢ |i⟩ |sᵢ⟩` at a fixed query cutoff
moves the ideal output by at most `2 * √(tail mass)` in the
Hilbert-space (Euclidean) norm, and the truncation-error matrix itself has true L2 operator
norm at most `2`.

`truncated_controlled_error_sq_le` computes the squared Euclidean norm of the output
difference branch by branch, `truncated_controlled_error_norm` takes square roots, and
`truncated_controlled_error_constant` packages the uniform constant `2` outside the
universal quantifiers. `truncated_controlled_l2OperatorNorm_le` bounds the error matrix in
the genuine `Matrix.Norms.L2Operator` operator norm. The discarded mass is
`tailMass α queries cutoff`, the squared control weight of branches whose query count
exceeds the cutoff.

These are finite-norm companion estimates to the overlap bounds of
`Qatlib.Papers.NestedQWalk12.CoherentTrunc.Native`; they do not construct a query-word
cutoff fee producer or an end-to-end bounded-error decision procedure.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Foundations.MatrixGeometry.LcuFrame
open Qatlib.Foundations.MatrixGeometry.BranchUnitary
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.NestedQWalk12.CoherentTrunc

variable {Label Sys : Type*} [Fintype Label] [DecidableEq Label]
  [Fintype Sys] [DecidableEq Sys]

/-- A unitary matrix preserves the Euclidean norm of every coordinate state. -/
theorem norm_toHilbert_mulVec_unitary (M : Matrix Sys Sys ℂ)
    (hM : M ∈ Matrix.unitaryGroup Sys ℂ) (w : State Sys) :
    ‖toHilbert (M *ᵥ w)‖ = ‖toHilbert w‖ := by
  have h1 := inner_self_eq_norm_sq (𝕜 := ℂ) (toHilbert (M *ᵥ w))
  have h2 := inner_self_eq_norm_sq (𝕜 := ℂ) (toHilbert w)
  rw [inner_toHilbert, unitary_inner M hM w w, ← inner_toHilbert] at h1
  rw [h2] at h1
  have h3 := congrArg Real.sqrt h1
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h3
  exact h3.symm

omit [DecidableEq Label] in
/-- The discarded-branch mass is nonnegative. -/
theorem tailMass_nonneg (α : Label → ℂ) (queries : Label → ℕ) (cutoff : ℕ) :
    0 ≤ tailMass α queries cutoff := by
  unfold tailMass
  exact Finset.sum_nonneg fun c _ => by split_ifs <;> positivity

omit [DecidableEq Sys] in
/-- The difference of two controlled matrices acts through the branchwise matrix difference on
each control slice. -/
theorem controlled_sub_apply (U V : Label → Matrix Sys Sys ℂ) (ψ : State (Sys × Label))
    (s : Sys) (i : Label) :
    ((controlled U - controlled V) *ᵥ ψ) (s, i) = ((U i - V i) *ᵥ fun t => ψ (t, i)) s := by
  have hf : (controlled U - controlled V) *ᵥ ψ =
      controlled U *ᵥ ψ - controlled V *ᵥ ψ := Matrix.sub_mulVec _ _ _
  have hg : (U i - V i) *ᵥ (fun t => ψ (t, i)) =
      (U i *ᵥ fun t => ψ (t, i)) - (V i *ᵥ fun t => ψ (t, i)) := Matrix.sub_mulVec _ _ _
  rw [hf, hg, Pi.sub_apply, Pi.sub_apply, controlled_apply, controlled_apply]

/-- Pointwise form of the truncation error on a coherent state: kept branches contribute zero;
discarded branches contribute the control amplitude times the branchwise difference of the
identity and the branch unitary. -/
theorem truncated_error_apply (U : Label → Matrix Sys Sys ℂ) (α : Label → ℂ)
    (conditional : Label → State Sys) (queries : Label → ℕ) (cutoff : ℕ)
    (s : Sys) (i : Label) :
    ((controlled (truncated U queries cutoff) - controlled U) *ᵥ coherent α conditional) (s, i) =
      if cutoff < queries i then α i * (conditional i - U i *ᵥ conditional i) s else 0 := by
  rw [controlled_sub_apply]
  change ((truncated U queries cutoff i - U i) *ᵥ (α i • conditional i)) s =
    (if cutoff < queries i then α i * (conditional i - U i *ᵥ conditional i) s else 0)
  by_cases h : queries i ≤ cutoff
  · have hn : ¬ cutoff < queries i := Nat.not_lt.mpr h
    simp [truncated, h, hn, sub_self, Matrix.zero_mulVec]
  · have ht : cutoff < queries i := Nat.lt_of_not_ge h
    simp [truncated, h, ht, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub]

/-- The squared Euclidean norm of the truncation error on a coherent state is at most four times
the discarded-branch mass. -/
theorem truncated_controlled_error_sq_le (U : Label → Matrix Sys Sys ℂ)
    (hU : ∀ i, U i ∈ Matrix.unitaryGroup Sys ℂ) (α : Label → ℂ)
    (conditional : Label → State Sys) (hs : ∀ i, Normalized (conditional i))
    (queries : Label → ℕ) (cutoff : ℕ) :
    ∑ x : Sys × Label,
        ‖((controlled (truncated U queries cutoff) - controlled U) *ᵥ
          coherent α conditional) x‖ ^ 2 ≤
      4 * tailMass α queries cutoff := by
  have hnorm : ∀ i : Label, ‖toHilbert (conditional i)‖ = 1 :=
    fun i => (normalized_iff_hilbert _).1 (hs i)
  have hun : ∀ i : Label, ‖toHilbert (U i *ᵥ conditional i)‖ = 1 := by
    intro i
    rw [norm_toHilbert_mulVec_unitary (U i) (hU i)]
    exact hnorm i
  have hbranch : ∀ i : Label,
      (∑ s : Sys, ‖((controlled (truncated U queries cutoff) - controlled U) *ᵥ
        coherent α conditional) (s, i)‖ ^ 2) ≤
        4 * (if cutoff < queries i then ‖α i‖ ^ 2 else 0) := by
    intro i
    by_cases h : queries i ≤ cutoff
    · have hn : ¬ cutoff < queries i := Nat.not_lt.mpr h
      simp [truncated_error_apply, hn, norm_zero]
    · have ht : cutoff < queries i := Nat.lt_of_not_ge h
      have hrewrite : (∑ s : Sys, ‖((controlled (truncated U queries cutoff) - controlled U) *ᵥ
            coherent α conditional) (s, i)‖ ^ 2) =
          ∑ s : Sys, ‖α i * (conditional i - U i *ᵥ conditional i) s‖ ^ 2 := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [truncated_error_apply]
        simp [ht]
      rw [hrewrite]
      have hnormsq : (∑ s : Sys, ‖α i * (conditional i - U i *ᵥ conditional i) s‖ ^ 2) =
          ‖α i‖ ^ 2 * ‖toHilbert (conditional i - U i *ᵥ conditional i)‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        change ‖α i * (conditional i - U i *ᵥ conditional i) s‖ ^ 2 =
          ‖α i‖ ^ 2 * ‖(conditional i - U i *ᵥ conditional i) s‖ ^ 2
        rw [norm_mul, mul_pow]
      rw [hnormsq]
      have hbound : ‖toHilbert (conditional i - U i *ᵥ conditional i)‖ ≤ 2 := by
        have e1 : toHilbert (conditional i - U i *ᵥ conditional i) =
            toHilbert (conditional i) - toHilbert (U i *ᵥ conditional i) := by
          ext s
          rfl
        rw [e1]
        calc ‖toHilbert (conditional i) - toHilbert (U i *ᵥ conditional i)‖
            ≤ ‖toHilbert (conditional i)‖ + ‖toHilbert (U i *ᵥ conditional i)‖ :=
              norm_sub_le _ _
          _ = 2 := by rw [hnorm, hun]; norm_num
      have hsq : ‖toHilbert (conditional i - U i *ᵥ conditional i)‖ ^ 2 ≤ 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
        exact (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr hbound
      calc ‖α i‖ ^ 2 * ‖toHilbert (conditional i - U i *ᵥ conditional i)‖ ^ 2
          ≤ ‖α i‖ ^ 2 * 4 := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
        _ = 4 * (if cutoff < queries i then ‖α i‖ ^ 2 else 0) := by
            simp [ht, mul_comm]
  calc ∑ x : Sys × Label,
        ‖((controlled (truncated U queries cutoff) - controlled U) *ᵥ
          coherent α conditional) x‖ ^ 2
      = ∑ i : Label, ∑ s : Sys, ‖((controlled (truncated U queries cutoff) - controlled U) *ᵥ
          coherent α conditional) (s, i)‖ ^ 2 := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ ≤ ∑ i : Label, 4 * (if cutoff < queries i then ‖α i‖ ^ 2 else 0) :=
        Finset.sum_le_sum fun i _ => hbranch i
    _ = 4 * tailMass α queries cutoff := by
        have hmul : ∑ i : Label, 4 * (if cutoff < queries i then ‖α i‖ ^ 2 else 0) =
            4 * ∑ i : Label, (if cutoff < queries i then ‖α i‖ ^ 2 else 0) :=
          (Finset.mul_sum Finset.univ (fun i => if cutoff < queries i then ‖α i‖ ^ 2 else 0) 4).symm
        exact hmul.trans rfl

/-- The Euclidean (Hilbert-space) distance between the ideal controlled output and its
identity-replacement truncation is at most `2 * √(tailMass α queries cutoff)`. This is the
norm estimate for the identity-replacement construction of [JefferyKothariMagniez2013],
Lemma 3.3. -/
theorem truncated_controlled_error_norm [Nonempty Label] [Nonempty Sys]
    (U : Label → Matrix Sys Sys ℂ)
    (hU : ∀ i, U i ∈ Matrix.unitaryGroup Sys ℂ) (α : Label → ℂ)
    (conditional : Label → State Sys) (hs : ∀ i, Normalized (conditional i))
    (queries : Label → ℕ) (cutoff : ℕ) :
    ‖toHilbert ((controlled (truncated U queries cutoff) - controlled U) *ᵥ
      coherent α conditional)‖ ≤ 2 * Real.sqrt (tailMass α queries cutoff) := by
  have hsq := truncated_controlled_error_sq_le U hU α conditional hs queries cutoff
  rw [EuclideanSpace.norm_eq]
  have hsqrt := Real.sqrt_le_sqrt hsq
  refine hsqrt.trans ?_
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
    show Real.sqrt (4 : ℝ) = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]

/-- Uniform form of the truncation error bound: a single positive constant `C = 2` works for
every nonempty finite label and system type, every unitary branch family, and every coherent
input with normalized conditional states. -/
theorem truncated_controlled_error_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ {Label Sys : Type*} [Fintype Label] [DecidableEq Label]
      [Nonempty Label] [Fintype Sys] [DecidableEq Sys] [Nonempty Sys]
      (U : Label → Matrix Sys Sys ℂ) (_hU : ∀ i, U i ∈ Matrix.unitaryGroup Sys ℂ)
      (α : Label → ℂ) (conditional : Label → State Sys)
      (_hs : ∀ i, Normalized (conditional i))
      (queries : Label → ℕ) (cutoff : ℕ),
      ‖toHilbert ((controlled (truncated U queries cutoff) - controlled U) *ᵥ
        coherent α conditional)‖ ≤ C * Real.sqrt (tailMass α queries cutoff) := by
  refine ⟨2, by norm_num, ?_⟩
  intro Label Sys _ _ _ _ _ _ U hU α conditional hs queries cutoff
  exact truncated_controlled_error_norm U hU α conditional hs queries cutoff

/-- Pointwise form of the truncation error on an arbitrary system-control state: kept branches
contribute zero; discarded branches contribute the branchwise difference of the identity and
the branch unitary. -/
theorem truncated_error_apply_generic (U : Label → Matrix Sys Sys ℂ)
    (w : State (Sys × Label))
    (queries : Label → ℕ) (cutoff : ℕ) (s : Sys) (i : Label) :
    ((controlled (truncated U queries cutoff) - controlled U) *ᵥ w) (s, i) =
      if cutoff < queries i then (w (s, i) - (U i *ᵥ fun t => w (t, i)) s) else 0 := by
  rw [controlled_sub_apply]
  by_cases h : queries i ≤ cutoff
  · have hn : ¬ cutoff < queries i := Nat.not_lt.mpr h
    simp [truncated, h, hn, sub_self, Matrix.zero_mulVec]
  · have ht : cutoff < queries i := Nat.lt_of_not_ge h
    simp [truncated, h, ht, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]

/-- The squared coordinate norm of the truncation error on an arbitrary system-control state is
at most four times the squared coordinate norm of the input restricted to the discarded
branches. -/
theorem truncated_controlled_error_sq_le_generic (U : Label → Matrix Sys Sys ℂ)
    (hU : ∀ i, U i ∈ Matrix.unitaryGroup Sys ℂ) (w : State (Sys × Label))
    (queries : Label → ℕ) (cutoff : ℕ) :
    ∑ p : Sys × Label, ‖((controlled (truncated U queries cutoff) - controlled U) *ᵥ w) p‖ ^ 2 ≤
      4 * ∑ i : Label, (if cutoff < queries i then ∑ s : Sys, ‖w (s, i)‖ ^ 2 else 0) := by
  have hbranch : ∀ i : Label,
      (∑ s : Sys, ‖((controlled (truncated U queries cutoff) - controlled U) *ᵥ w) (s, i)‖ ^ 2) ≤
        4 * (if cutoff < queries i then ∑ s : Sys, ‖w (s, i)‖ ^ 2 else 0) := by
    intro i
    by_cases h : queries i ≤ cutoff
    · have hn : ¬ cutoff < queries i := Nat.not_lt.mpr h
      simp [truncated_error_apply_generic, hn, norm_zero]
    · have ht : cutoff < queries i := Nat.lt_of_not_ge h
      have hrewrite : (∑ s : Sys, ‖((controlled (truncated U queries cutoff) - controlled U) *ᵥ
            w) (s, i)‖ ^ 2) =
          ∑ s : Sys, ‖w (s, i) - (U i *ᵥ fun t => w (t, i)) s‖ ^ 2 := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [truncated_error_apply_generic]
        simp [ht]
      rw [hrewrite]
      have hun : ‖toHilbert (U i *ᵥ (fun t => w (t, i)))‖ = ‖toHilbert (fun t => w (t, i))‖ :=
        norm_toHilbert_mulVec_unitary (U i) (hU i) _
      have hbound : ‖toHilbert (fun s => w (s, i) - (U i *ᵥ fun t => w (t, i)) s)‖ ≤
          2 * ‖toHilbert (fun t => w (t, i))‖ := by
        have e1 : (fun s => w (s, i) - (U i *ᵥ fun t => w (t, i)) s) =
            (fun t => w (t, i)) - U i *ᵥ (fun t => w (t, i)) := by
          ext s
          rfl
        rw [e1]
        have e2 : toHilbert ((fun t => w (t, i)) - U i *ᵥ (fun t => w (t, i))) =
            toHilbert (fun t => w (t, i)) - toHilbert (U i *ᵥ (fun t => w (t, i))) := by
          ext s
          rfl
        rw [e2]
        calc ‖toHilbert (fun t => w (t, i)) - toHilbert (U i *ᵥ (fun t => w (t, i)))‖
            ≤ ‖toHilbert (fun t => w (t, i))‖ +
                ‖toHilbert (U i *ᵥ (fun t => w (t, i)))‖ := norm_sub_le _ _
          _ = 2 * ‖toHilbert (fun t => w (t, i))‖ := by rw [hun]; ring
      have hsq : ‖toHilbert (fun s => w (s, i) - (U i *ᵥ fun t => w (t, i)) s)‖ ^ 2 ≤
          4 * ‖toHilbert (fun t => w (t, i))‖ ^ 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← mul_pow]
        exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg zero_le_two (norm_nonneg _))).mpr hbound
      have e3 : ‖toHilbert (fun s => w (s, i) - (U i *ᵥ fun t => w (t, i)) s)‖ ^ 2 =
          ∑ s : Sys, ‖w (s, i) - (U i *ᵥ fun t => w (t, i)) s‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        exact Finset.sum_congr rfl fun s _ => rfl
      have e4 : ‖toHilbert (fun t => w (t, i))‖ ^ 2 = ∑ s : Sys, ‖w (s, i)‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        exact Finset.sum_congr rfl fun s _ => rfl
      rw [e3, e4] at hsq
      simp only [ht]
      exact hsq
  calc ∑ p : Sys × Label, ‖((controlled (truncated U queries cutoff) - controlled U) *ᵥ w) p‖ ^ 2
      = ∑ i : Label, ∑ s : Sys, ‖((controlled (truncated U queries cutoff) - controlled U) *ᵥ
          w) (s, i)‖ ^ 2 := by rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ ≤ ∑ i : Label, 4 * (if cutoff < queries i then ∑ s : Sys, ‖w (s, i)‖ ^ 2 else 0) :=
        Finset.sum_le_sum fun i _ => hbranch i
    _ = 4 * ∑ i : Label, (if cutoff < queries i then ∑ s : Sys, ‖w (s, i)‖ ^ 2 else 0) := by
        rw [← Finset.mul_sum]

/-- The truncation-error matrix `controlled (truncated U queries cutoff) - controlled U` has
true L2 operator norm at most `2`, uniformly in the cutoff. This bound controls the error on
arbitrary vectors for the identity-replacement construction of [JefferyKothariMagniez2013],
Lemma 3.3. -/
theorem truncated_controlled_l2OperatorNorm_le [Nonempty Label] [Nonempty Sys]
    (U : Label → Matrix Sys Sys ℂ)
    (hU : ∀ i, U i ∈ Matrix.unitaryGroup Sys ℂ)
    (queries : Label → ℕ) (cutoff : ℕ) :
    ‖controlled (truncated U queries cutoff) - controlled U‖ ≤ 2 := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x => ?_
  have hsq := truncated_controlled_error_sq_le_generic U hU x.ofLp queries cutoff
  have hclm : ‖(((Matrix.toEuclideanLin (𝕜 := ℂ) (m := Sys × Label) (n := Sys × Label)).trans
        LinearMap.toContinuousLinearMap (controlled (truncated U queries cutoff) -
          controlled U)) x)‖ ^ 2 =
      ∑ p : Sys × Label,
        ‖((controlled (truncated U queries cutoff) - controlled U) *ᵥ x.ofLp) p‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  have h2 : ‖(((Matrix.toEuclideanLin (𝕜 := ℂ) (m := Sys × Label) (n := Sys × Label)).trans
        LinearMap.toContinuousLinearMap (controlled (truncated U queries cutoff) -
          controlled U)) x)‖ ^ 2 ≤ (2 * ‖x‖) ^ 2 := by
    have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h4] at hsq
    rw [hclm, mul_pow]
    refine le_trans hsq ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2 ^ 2)
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
    exact Finset.sum_le_sum fun i _ => by
      split_ifs
      · exact le_refl _
      · exact Finset.sum_nonneg fun s _ => sq_nonneg _
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg zero_le_two (norm_nonneg _))).mp h2

end Qatlib.Papers.NestedQWalk12.CoherentTrunc
