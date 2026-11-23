/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Order.Floor.Defs
public import Qatlib.Papers.NestedQWalk12.CoherentTrunc.OperatorNorm

@[expose] public section

/-!
# Two-level nested truncation budget

Source context: [JefferyKothariMagniez2013], Theorem 3.2 and Corollary 4.1. Applying
the identity-replacement construction of Lemma 3.3 at two levels, composing an outer coherent
truncation (budget `Q` against outer query counts `q`) with per-branch inner truncations
(cutoff `R` against inner query counts `r i`) keeps the real output overlap above
`1 - 2 * outerTail - 2 * √(innerTailTotal)`, with every constant explicit and the number of
levels visible in the budget.

`nested_truncation_overlap` proves the explicit-constant overlap bound on the nested coherent
state `coherent α (fun i => coherent (β i) (η i))`, and `nested_truncation_constant`
packages the uniform constant `2` outside the universal quantifiers.
`tailMass_le_ceil_mean_div` formalizes the cutoff selection from Lemma 3.3: for a target
`ε > 0`, the positive cutoff `max 1 ⌈meanQueries / ε⌉₊` keeps the discarded mass at most `ε`.

This is a finite two-level linear-algebra budget; it does not construct the actual nested
walk oracles, the quantum-data update instructions, or the full bounded-error decision
procedure of the source.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open Qatlib.Foundations.MatrixGeometry.LcuFrame
open Qatlib.Foundations.MatrixGeometry.BranchUnitary
open Qatlib.Papers.NestedQWalk12.CoherentTrunc
open scoped BigOperators

namespace Qatlib.Papers.NestedQWalk12.ErrorBudget

variable {Outer ι Sys : Type*} [Fintype Outer] [DecidableEq Outer]
  [Fintype ι] [DecidableEq ι]
  [Fintype Sys] [DecidableEq Sys]

/-- Pointwise comparison of the outer-only truncated walk and the fully truncated walk on the
two-level coherent state: discarded outer branches agree exactly, kept branches differ by the
inner truncation error scaled by the outer control amplitude. -/
theorem nested_error_apply (U : Outer → ι → Matrix Sys Sys ℂ) (α : Outer → ℂ)
    (β : Outer → ι → ℂ) (η : Outer → ι → State Sys)
    (q : Outer → ℕ) (Q : ℕ) (r : Outer → ι → ℕ) (R : ℕ)
    (x : Sys × ι) (i : Outer) :
    ((controlled (truncated (fun i => controlled (truncated (U i) (r i) R)) q Q) -
        controlled (truncated (fun i => controlled (U i)) q Q)) *ᵥ
        coherent α (fun i => coherent (β i) (η i))) (x, i) =
      (if q i ≤ Q then α i * ((controlled (truncated (U i) (r i) R) - controlled (U i)) *ᵥ
        coherent (β i) (η i)) x else 0) := by
  rw [controlled_sub_apply]
  change ((truncated (fun i => controlled (truncated (U i) (r i) R)) q Q i -
      truncated (fun i => controlled (U i)) q Q i) *ᵥ
      (α i • coherent (β i) (η i))) x =
    (if q i ≤ Q then α i * ((controlled (truncated (U i) (r i) R) - controlled (U i)) *ᵥ
      coherent (β i) (η i)) x else 0)
  by_cases h : q i ≤ Q
  · simp only [truncated, h, ite_true, Matrix.sub_mulVec, Matrix.mulVec_smul, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, mul_sub]
  · simp only [truncated, h, ite_false, sub_self, Matrix.zero_mulVec, Pi.zero_apply]

/-- Squared distance between the outer-only truncated output and the fully truncated output on
the nested coherent state: it is at most four times the outer-amplitude weighted sum of the
inner discarded masses. -/
theorem nested_error_norm_sq_le (U : Outer → ι → Matrix Sys Sys ℂ)
    (hU : ∀ i j, U i j ∈ Matrix.unitaryGroup Sys ℂ) (α : Outer → ℂ)
    (β : Outer → ι → ℂ) (η : Outer → ι → State Sys)
    (hη : ∀ i j, Normalized (η i j))
    (q : Outer → ℕ) (Q : ℕ) (r : Outer → ι → ℕ) (R : ℕ) :
    ∑ y : (Sys × ι) × Outer,
        ‖((controlled (truncated (fun i => controlled (truncated (U i) (r i) R)) q Q) -
            controlled (truncated (fun i => controlled (U i)) q Q)) *ᵥ
          coherent α (fun i => coherent (β i) (η i))) y‖ ^ 2 ≤
      4 * ∑ i : Outer, ‖α i‖ ^ 2 * tailMass (β i) (r i) R := by
  have hbranch : ∀ i : Outer,
      (∑ x : Sys × ι, ‖((controlled (truncated (fun i => controlled (truncated (U i) (r i) R)) q Q) -
          controlled (truncated (fun i => controlled (U i)) q Q)) *ᵥ
        coherent α (fun i => coherent (β i) (η i))) (x, i)‖ ^ 2) ≤
        4 * (‖α i‖ ^ 2 * (if q i ≤ Q then tailMass (β i) (r i) R else 0)) := by
    intro i
    by_cases h : q i ≤ Q
    · have hrewrite : (∑ x : Sys × ι, ‖((controlled (truncated (fun i => controlled (truncated (U i) (r i) R)) q Q) -
            controlled (truncated (fun i => controlled (U i)) q Q)) *ᵥ
          coherent α (fun i => coherent (β i) (η i))) (x, i)‖ ^ 2) =
          ∑ x : Sys × ι, ‖α i * ((controlled (truncated (U i) (r i) R) -
            controlled (U i)) *ᵥ coherent (β i) (η i)) x‖ ^ 2 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [nested_error_apply]
        simp [h]
      rw [hrewrite]
      calc (∑ x : Sys × ι, ‖α i * ((controlled (truncated (U i) (r i) R) -
              controlled (U i)) *ᵥ coherent (β i) (η i)) x‖ ^ 2)
          = ‖α i‖ ^ 2 * (∑ x : Sys × ι, ‖((controlled (truncated (U i) (r i) R) -
              controlled (U i)) *ᵥ coherent (β i) (η i)) x‖ ^ 2) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [norm_mul, mul_pow]
          _ ≤ ‖α i‖ ^ 2 * (4 * tailMass (β i) (r i) R) :=
              mul_le_mul_of_nonneg_left (truncated_controlled_error_sq_le (U i) (hU i)
                (β i) (η i) (hη i) (r i) R) (sq_nonneg _)
          _ = 4 * (‖α i‖ ^ 2 * (if q i ≤ Q then tailMass (β i) (r i) R else 0)) := by
              simp [h, mul_left_comm]
    · have hrewrite : (∑ x : Sys × ι, ‖((controlled (truncated (fun i => controlled (truncated (U i) (r i) R)) q Q) -
            controlled (truncated (fun i => controlled (U i)) q Q)) *ᵥ
          coherent α (fun i => coherent (β i) (η i))) (x, i)‖ ^ 2) = 0 := by
        apply Finset.sum_eq_zero fun x _ => ?_
        rw [nested_error_apply]
        simp [h]
      rw [hrewrite]
      have hnn : 0 ≤ ‖α i‖ ^ 2 * (if q i ≤ Q then tailMass (β i) (r i) R else 0) := by
        apply mul_nonneg (sq_nonneg _)
        by_cases h2 : q i ≤ Q
        · simp only [h2, ite_true]
          exact tailMass_nonneg _ _ _
        · simp only [h2, ite_false]
          norm_num
      linarith
  calc ∑ y : (Sys × ι) × Outer,
        ‖((controlled (truncated (fun i => controlled (truncated (U i) (r i) R)) q Q) -
            controlled (truncated (fun i => controlled (U i)) q Q)) *ᵥ
          coherent α (fun i => coherent (β i) (η i))) y‖ ^ 2
      = ∑ i : Outer, ∑ x : Sys × ι, ‖((controlled (truncated (fun i => controlled (truncated (U i) (r i) R)) q Q) -
          controlled (truncated (fun i => controlled (U i)) q Q)) *ᵥ
        coherent α (fun i => coherent (β i) (η i))) (x, i)‖ ^ 2 := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ ≤ ∑ i : Outer, 4 * (‖α i‖ ^ 2 * (if q i ≤ Q then tailMass (β i) (r i) R else 0)) :=
        Finset.sum_le_sum fun i _ => hbranch i
    _ = 4 * ∑ i : Outer, ‖α i‖ ^ 2 * (if q i ≤ Q then tailMass (β i) (r i) R else 0) := by
        rw [← Finset.mul_sum]
    _ ≤ 4 * ∑ i : Outer, ‖α i‖ ^ 2 * tailMass (β i) (r i) R := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases h : q i ≤ Q
        · simp [h]
        · simp only [h, ite_false, mul_zero]
          exact mul_nonneg (sq_nonneg _) (tailMass_nonneg _ _ _)

/-- Two-level nested truncation overlap: the real overlap between the ideal nested output and
the doubly truncated output is at least `1 - 2 * outerTail - 2 * √(innerTailTotal)`, where
`outerTail` is the discarded outer control mass and `innerTailTotal` is the outer-amplitude
weighted sum of the inner discarded masses. This is the explicit two-level form of the nested
error budget of [JefferyKothariMagniez2013]. -/
theorem nested_truncation_overlap (U : Outer → ι → Matrix Sys Sys ℂ)
    (hU : ∀ i j, U i j ∈ Matrix.unitaryGroup Sys ℂ)
    (α : Outer → ℂ) (hα : ∑ i, ‖α i‖ ^ 2 = 1)
    (β : Outer → ι → ℂ) (hβ : ∀ i, ∑ j, ‖β i j‖ ^ 2 = 1)
    (η : Outer → ι → State Sys) (hη : ∀ i j, Normalized (η i j))
    (q : Outer → ℕ) (Q : ℕ) (r : Outer → ι → ℕ) (R : ℕ) :
    1 - 2 * tailMass α q Q -
        2 * Real.sqrt (∑ i, ‖α i‖ ^ 2 * tailMass (β i) (r i) R) ≤
      (Inner (controlled (fun i => controlled (U i)) *ᵥ
          coherent α (fun i => coherent (β i) (η i)))
        (controlled (truncated (fun i => controlled (truncated (U i) (r i) R)) q Q) *ᵥ
          coherent α (fun i => coherent (β i) (η i)))).re := by
  have hψ : Normalized (coherent α (fun i => coherent (β i) (η i))) :=
    coherent_normalized α _ hα fun i => coherent_normalized (β i) (η i) (hβ i) (hη i)
  have hW : controlled (fun i => controlled (U i)) ∈
      Matrix.unitaryGroup ((Sys × ι) × Outer) ℂ :=
    controlled_unitary _ fun i => controlled_unitary _ (hU i)
  have hstep1 := truncation_real_overlap (fun i => controlled (U i))
    (fun i => controlled_unitary _ (hU i)) α (fun i => coherent (β i) (η i)) hα
    (fun i => coherent_normalized (β i) (η i) (hβ i) (hη i)) q Q
  have hsq := nested_error_norm_sq_le U hU α β η hη q Q r R
  have hsub : controlled (truncated (fun i => controlled (truncated (U i) (r i) R)) q Q) *ᵥ
      coherent α (fun i => coherent (β i) (η i)) -
    controlled (truncated (fun i => controlled (U i)) q Q) *ᵥ
      coherent α (fun i => coherent (β i) (η i)) =
    (controlled (truncated (fun i => controlled (truncated (U i) (r i) R)) q Q) -
        controlled (truncated (fun i => controlled (U i)) q Q)) *ᵥ
      coherent α (fun i => coherent (β i) (η i)) :=
    (Matrix.sub_mulVec _ _ _).symm
  have hsum : ‖toHilbert ((controlled (truncated (fun i => controlled (truncated (U i) (r i) R)) q Q) -
        controlled (truncated (fun i => controlled (U i)) q Q)) *ᵥ
      coherent α (fun i => coherent (β i) (η i)))‖ ^ 2 ≤
      4 * ∑ i, ‖α i‖ ^ 2 * tailMass (β i) (r i) R := by
    rw [EuclideanSpace.norm_sq_eq]
    exact hsq
  have hstep2 : ‖toHilbert (controlled (truncated (fun i => controlled (truncated (U i) (r i) R)) q Q) *ᵥ
        coherent α (fun i => coherent (β i) (η i))) -
      toHilbert (controlled (truncated (fun i => controlled (U i)) q Q) *ᵥ
        coherent α (fun i => coherent (β i) (η i)))‖ ≤
      2 * Real.sqrt (∑ i, ‖α i‖ ^ 2 * tailMass (β i) (r i) R) := by
    have e1 : toHilbert (controlled (truncated (fun i => controlled (truncated (U i) (r i) R)) q Q) *ᵥ
        coherent α (fun i => coherent (β i) (η i)) -
      controlled (truncated (fun i => controlled (U i)) q Q) *ᵥ
        coherent α (fun i => coherent (β i) (η i))) =
      toHilbert (controlled (truncated (fun i => controlled (truncated (U i) (r i) R)) q Q) *ᵥ
          coherent α (fun i => coherent (β i) (η i))) -
      toHilbert (controlled (truncated (fun i => controlled (U i)) q Q) *ᵥ
        coherent α (fun i => coherent (β i) (η i))) := by
      ext s
      rfl
    rw [← e1, hsub]
    have hsqrt := Real.sqrt_le_sqrt hsum
    rw [Real.sqrt_sq (norm_nonneg _)] at hsqrt
    calc ‖toHilbert ((controlled (truncated (fun i => controlled (truncated (U i) (r i) R)) q Q) -
            controlled (truncated (fun i => controlled (U i)) q Q)) *ᵥ
          coherent α (fun i => coherent (β i) (η i)))‖
        ≤ Real.sqrt (4 * ∑ i, ‖α i‖ ^ 2 * tailMass (β i) (r i) R) := hsqrt
      _ = 2 * Real.sqrt (∑ i, ‖α i‖ ^ 2 * tailMass (β i) (r i) R) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
            show Real.sqrt (4 : ℝ) = 2 by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have hX : ‖toHilbert (controlled (fun i => controlled (U i)) *ᵥ
      coherent α (fun i => coherent (β i) (η i)))‖ = 1 :=
    (normalized_iff_hilbert _).1 (unitary_normalized _ hW _ hψ)
  have hdecomp : inner ℂ (toHilbert (controlled (fun i => controlled (U i)) *ᵥ
        coherent α (fun i => coherent (β i) (η i))))
      (toHilbert (controlled (truncated (fun i => controlled (truncated (U i) (r i) R)) q Q) *ᵥ
        coherent α (fun i => coherent (β i) (η i)))) =
    inner ℂ (toHilbert (controlled (fun i => controlled (U i)) *ᵥ
        coherent α (fun i => coherent (β i) (η i))))
      (toHilbert (controlled (truncated (fun i => controlled (U i)) q Q) *ᵥ
        coherent α (fun i => coherent (β i) (η i)))) +
    inner ℂ (toHilbert (controlled (fun i => controlled (U i)) *ᵥ
        coherent α (fun i => coherent (β i) (η i))))
      (toHilbert (controlled (truncated (fun i => controlled (truncated (U i) (r i) R)) q Q) *ᵥ
          coherent α (fun i => coherent (β i) (η i))) -
       toHilbert (controlled (truncated (fun i => controlled (U i)) q Q) *ᵥ
        coherent α (fun i => coherent (β i) (η i)))) := by
    rw [inner_sub_right]
    ring
  rw [← inner_toHilbert] at hstep1
  have h1 := hstep1
  have h2 : -(2 * Real.sqrt (∑ i, ‖α i‖ ^ 2 * tailMass (β i) (r i) R)) ≤
      (inner ℂ (toHilbert (controlled (fun i => controlled (U i)) *ᵥ
          coherent α (fun i => coherent (β i) (η i))))
        (toHilbert (controlled (truncated (fun i => controlled (truncated (U i) (r i) R)) q Q) *ᵥ
            coherent α (fun i => coherent (β i) (η i))) -
         toHilbert (controlled (truncated (fun i => controlled (U i)) q Q) *ᵥ
          coherent α (fun i => coherent (β i) (η i))))).re := by
    have hre := (abs_le.mp (Complex.abs_re_le_norm
      (inner ℂ (toHilbert (controlled (fun i => controlled (U i)) *ᵥ
          coherent α (fun i => coherent (β i) (η i))))
        (toHilbert (controlled (truncated (fun i => controlled (truncated (U i) (r i) R)) q Q) *ᵥ
            coherent α (fun i => coherent (β i) (η i))) -
         toHilbert (controlled (truncated (fun i => controlled (U i)) q Q) *ᵥ
          coherent α (fun i => coherent (β i) (η i))))))).1
    have hni := norm_inner_le_norm (𝕜 := ℂ) (toHilbert (controlled (fun i => controlled (U i)) *ᵥ
        coherent α (fun i => coherent (β i) (η i))))
      (toHilbert (controlled (truncated (fun i => controlled (truncated (U i) (r i) R)) q Q) *ᵥ
          coherent α (fun i => coherent (β i) (η i))) -
       toHilbert (controlled (truncated (fun i => controlled (U i)) q Q) *ᵥ
        coherent α (fun i => coherent (β i) (η i))))
    rw [hX, one_mul] at hni
    linarith
  rw [← inner_toHilbert, hdecomp, Complex.add_re]
  linarith

/-- Uniform form of the two-level nested truncation bound: a single positive constant `C = 2`
works for every nondegenerate finite register geometry and every normalized nested coherent
input, with the two-level error budget explicit. -/
theorem nested_truncation_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ {Outer ι Sys : Type*} [Fintype Outer] [DecidableEq Outer]
      [Nonempty Outer] [Fintype ι] [DecidableEq ι] [Nonempty ι]
      [Fintype Sys] [DecidableEq Sys] [Nonempty Sys]
      (U : Outer → ι → Matrix Sys Sys ℂ)
      (_hU : ∀ i j, U i j ∈ Matrix.unitaryGroup Sys ℂ)
      (α : Outer → ℂ) (_hα : ∑ i, ‖α i‖ ^ 2 = 1)
      (β : Outer → ι → ℂ) (_hβ : ∀ i, ∑ j, ‖β i j‖ ^ 2 = 1)
      (η : Outer → ι → State Sys) (_hη : ∀ i j, Normalized (η i j))
      (q : Outer → ℕ) (Q : ℕ) (r : Outer → ι → ℕ) (R : ℕ),
      1 - C * (tailMass α q Q + Real.sqrt (∑ i, ‖α i‖ ^ 2 * tailMass (β i) (r i) R)) ≤
        (Inner (controlled (fun i => controlled (U i)) *ᵥ
            coherent α (fun i => coherent (β i) (η i)))
          (controlled (truncated (fun i => controlled (truncated (U i) (r i) R)) q Q) *ᵥ
            coherent α (fun i => coherent (β i) (η i)))).re := by
  refine ⟨2, by norm_num, ?_⟩
  intro Outer ι Sys _ _ _ _ _ _ _ _ _ U hU α hα β hβ η hη q Q r R
  have h := nested_truncation_overlap U hU α hα β hβ η hη q Q r R
  linarith

omit [DecidableEq Outer] in
/-- The cutoff selected by the Markov argument of [JefferyKothariMagniez2013], Lemma 3.3,
keeps the actual discarded mass at most `ε`. The lower limit of one keeps the cutoff positive
when the weighted mean query count vanishes. -/
theorem tailMass_le_ceil_mean_div [Nonempty Outer]
    (α : Outer → ℂ) (q : Outer → ℕ) (ε : ℝ) (hε : 0 < ε) :
    tailMass α q (max 1 (Nat.ceil (meanQueries α q / ε))) ≤ ε := by
  let cutoff := max 1 (Nat.ceil (meanQueries α q / ε))
  have hcut : 0 < cutoff := Nat.zero_lt_one.trans_le (le_max_left _ _)
  have hceil : (Nat.ceil (meanQueries α q / ε) : ℝ) ≤ (cutoff : ℝ) := by
    exact_mod_cast (le_max_right 1 (Nat.ceil (meanQueries α q / ε)))
  refine (tailMass_le_mean α q cutoff hcut).trans ?_
  rw [div_le_iff₀ (Nat.cast_pos.mpr hcut), mul_comm ε]
  exact (div_le_iff₀ hε).mp ((Nat.le_ceil _).trans hceil)

end Qatlib.Papers.NestedQWalk12.ErrorBudget
