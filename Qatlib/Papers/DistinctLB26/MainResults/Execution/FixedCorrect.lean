/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Anti-concentration with fixed correctness projectors

Fixed source: arXiv:2604.05133v1, Definitions 3.8--3.9 and Proposition 3.11.
The correctness subsets of the hidden register are fixed by the problem.
Strong anti-concentration means membership in `H tensor A`, where `H` is an
anti-concentrated subspace of the hidden register. It does not quantify over
arbitrary correctness subsets (which would include the identity projector).

The measurement is an actual input-independent unitary on the work register
followed by a coordinate measurement and a response map. Its success
probability is derived from the resulting joint amplitudes.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.DistinctLB26.MainResults.FixedCorrect

/-- Finite complex Hilbert space in the coordinate representation. -/
abbrev Vec (I : Type*) := EuclideanSpace ℂ I

variable {Y A R : Type*} [Fintype Y] [Fintype A]

/-- Evaluation of a finite Hilbert-space coordinate as a linear map. -/
def coordinate {I : Type*} (i : I) : Vec I →ₗ[ℂ] ℂ where
  toFun v := v i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A fixed correctness projector on the hidden register. -/
def project (M : R → Y → Prop) [∀ r, DecidablePred (M r)] (r : R) (v : Vec Y) : Vec Y :=
  WithLp.toLp 2 (fun y => if M r y then v y else 0)

/-- Anti-concentration is a bound on the problem's fixed correctness projectors. -/
def AntiConc (M : R → Y → Prop) [∀ r, DecidablePred (M r)]
    (γ : ℝ) (H : Submodule ℂ (Vec Y)) : Prop :=
  ∀ (r : R) (v : Vec Y), v ∈ H → ‖project M r v‖ ^ 2 ≤ γ ^ 2 * ‖v‖ ^ 2

/-- A hidden-register slice at a work-register coordinate. -/
def column (ψ : Vec (Y × A)) (a : A) : Vec Y :=
  WithLp.toLp 2 (fun y => ψ (y, a))

/-- Membership in `H tensor A` in finite coordinates. -/
def Strong (H : Submodule ℂ (Vec Y)) (ψ : Vec (Y × A)) : Prop :=
  ∀ a : A, column ψ a ∈ H

/-- The work-register slice at a hidden-register label. -/
def row (ψ : Vec (Y × A)) (y : Y) : Vec A :=
  WithLp.toLp 2 (fun a => ψ (y, a))

/-- The same work-register unitary on every hidden-register input. -/
def rotate (U : Vec A ≃ₗᵢ[ℂ] Vec A) (ψ : Vec (Y × A)) : Vec (Y × A) :=
  WithLp.toLp 2 (fun z => U (row ψ z.1) z.2)

/-- Rotation preserves the full joint norm. -/
theorem rotate_norm (U : Vec A ≃ₗᵢ[ℂ] Vec A) (ψ : Vec (Y × A)) :
    ‖rotate U ψ‖ = ‖ψ‖ := by
  have hs (y : Y) : (∑ a, ‖U (row ψ y) a‖ ^ 2) = ∑ a, ‖ψ (y, a)‖ ^ 2 := by
    rw [← EuclideanSpace.norm_sq_eq, U.norm_map, EuclideanSpace.norm_sq_eq]
    rfl
  have hsq : ‖rotate U ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun y _ => hs y
  nlinarith [norm_nonneg (rotate U ψ), norm_nonneg ψ]

omit [Fintype Y] in
/-- A rotated hidden-register column is a genuine linear combination of the original columns. -/
theorem rotate_column (U : Vec A ≃ₗᵢ[ℂ] Vec A) (ψ : Vec (Y × A)) (a : A) :
    column (rotate U ψ) a =
      ∑ b : A, (U (EuclideanSpace.basisFun A ℂ b) a) • column ψ b := by
  ext y
  have hv := (EuclideanSpace.basisFun A ℂ).sum_repr (row ψ y)
  have hu := congrArg ((coordinate a).comp U.toLinearEquiv.toLinearMap) hv
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr] at hu
  change ((coordinate a).comp U.toLinearEquiv.toLinearMap) (row ψ y) = (coordinate y) _
  rw [← hu, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  change (ψ (y, b)) * (U (EuclideanSpace.basisFun A ℂ b) a) =
    (U (EuclideanSpace.basisFun A ℂ b) a) * ψ (y, b)
  exact mul_comm _ _

omit [Fintype Y] in
/-- Arbitrary local unitary gates preserve strong anti-concentration's subspace membership. -/
theorem strong_rotate {H : Submodule ℂ (Vec Y)} {ψ : Vec (Y × A)}
    (hψ : Strong H ψ) (U : Vec A ≃ₗᵢ[ℂ] Vec A) : Strong H (rotate U ψ) := by
  intro a
  rw [rotate_column]
  exact H.sum_mem fun b _ => H.smul_mem _ (hψ b)

/-- The sum of squared column norms is the actual joint squared norm. -/
theorem column_squares (ψ : Vec (Y × A)) :
    (∑ a : A, ‖column ψ a‖ ^ 2) = ‖ψ‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, column]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- The successful part of the final state after a work-register measurement. -/
def successful (M : R → Y → Prop) [∀ r, DecidablePred (M r)] (answer : A → R)
    (ψ : Vec (Y × A)) : Vec (Y × A) :=
  WithLp.toLp 2 (fun z => if M (answer z.2) z.1 then ψ z else 0)

/-- The Born success probability of a specified unitary measurement and response map. -/
def successProb (M : R → Y → Prop) [∀ r, DecidablePred (M r)]
    (answer : A → R) (U : Vec A ≃ₗᵢ[ℂ] Vec A) (ψ : Vec (Y × A)) : ℝ :=
  ‖successful M answer (rotate U ψ)‖ ^ 2

/-- Success splits over the mutually exclusive coordinate measurement outcomes. -/
theorem success_slices (M : R → Y → Prop) [∀ r, DecidablePred (M r)]
    (answer : A → R) (U : Vec A ≃ₗᵢ[ℂ] Vec A) (ψ : Vec (Y × A)) :
    successProb M answer U ψ =
      ∑ a : A, ‖project M (answer a) (column (rotate U ψ) a)‖ ^ 2 := by
  simp only [successProb, EuclideanSpace.norm_sq_eq, successful, project, column,
    PiLp.toLp_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- Proposition 3.11: every actual local unitary measurement obeys the fixed-projector bound. -/
theorem success_bound (M : R → Y → Prop) [∀ r, DecidablePred (M r)]
    (γ : ℝ) (H : Submodule ℂ (Vec Y)) (hanti : AntiConc M γ H)
    (ψ : Vec (Y × A)) (hψ : Strong H ψ) (answer : A → R)
    (U : Vec A ≃ₗᵢ[ℂ] Vec A) :
    successProb M answer U ψ ≤ γ ^ 2 * ‖ψ‖ ^ 2 := by
  have hstrong := strong_rotate hψ U
  rw [success_slices]
  calc
    (∑ a : A, ‖project M (answer a) (column (rotate U ψ) a)‖ ^ 2) ≤
        ∑ a : A, γ ^ 2 * ‖column (rotate U ψ) a‖ ^ 2 :=
      Finset.sum_le_sum fun a _ => hanti (answer a) _ (hstrong a)
    _ = γ ^ 2 * ‖rotate U ψ‖ ^ 2 := by rw [← Finset.mul_sum, column_squares]
    _ = γ ^ 2 * ‖ψ‖ ^ 2 := by rw [rotate_norm]

/-- An arbitrary coordinate-success projector is a contraction on joint states. -/
theorem successful_le (M : R → Y → Prop) [∀ r, DecidablePred (M r)]
    (answer : A → R) (ψ : Vec (Y × A)) : ‖successful M answer ψ‖ ≤ ‖ψ‖ := by
  have hs : ‖successful M answer ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro z _
    by_cases hz : M (answer z.2) z.1 <;> simp [successful, hz]
  nlinarith [norm_nonneg (successful M answer ψ), norm_nonneg ψ]

omit [Fintype Y] [Fintype A] in
/-- The measurement projection is additive. -/
theorem successful_add (M : R → Y → Prop) [∀ r, DecidablePred (M r)]
    (answer : A → R) (u v : Vec (Y × A)) :
    successful M answer (u + v) = successful M answer u + successful M answer v := by
  ext z
  by_cases hz : M (answer z.2) z.1 <;> simp [successful, hz]

omit [Fintype Y] in
/-- Local unitary execution is additive. -/
theorem rotate_add (U : Vec A ≃ₗᵢ[ℂ] Vec A) (u v : Vec (Y × A)) :
    rotate U (u + v) = rotate U u + rotate U v := by
  have hr (y : Y) : row (u + v) y = row u y + row v y := rfl
  ext z
  simp only [rotate, PiLp.toLp_apply, hr, map_add, PiLp.add_apply]

/-- Lemma 3.12 with the actual measurement and a genuine strong subspace component. -/
theorem decomposed_bound (M : R → Y → Prop) [∀ r, DecidablePred (M r)]
    (γ δ : ℝ) (hγ : 0 ≤ γ) (H : Submodule ℂ (Vec Y))
    (hanti : AntiConc M γ H) (u v : Vec (Y × A)) (hv : Strong H v)
    (hu : ‖u‖ ≤ δ) (hvnorm : ‖v‖ ≤ 1) (answer : A → R)
    (U : Vec A ≃ₗᵢ[ℂ] Vec A) : successProb M answer U (u + v) ≤ (γ + δ) ^ 2 := by
  have hvb := success_bound M γ H hanti v hv answer U
  have hvbound : ‖successful M answer (rotate U v)‖ ≤ γ := by
    have hv2 : ‖v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v]
    have hmul := mul_le_mul_of_nonneg_left hv2 (sq_nonneg γ)
    unfold successProb at hvb
    nlinarith [norm_nonneg (successful M answer (rotate U v))]
  have hub : ‖successful M answer (rotate U u)‖ ≤ δ :=
    ((successful_le M answer _).trans (le_of_eq (rotate_norm U u))).trans hu
  have hsum : ‖successful M answer (rotate U (u + v))‖ ≤ γ + δ := by
    rw [rotate_add, successful_add]
    exact (norm_add_le _ _).trans (by linarith)
  exact pow_le_pow_left₀ (norm_nonneg _) hsum 2

end Qatlib.Papers.DistinctLB26.MainResults.FixedCorrect
