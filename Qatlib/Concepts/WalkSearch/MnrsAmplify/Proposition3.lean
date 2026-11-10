/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Proposition3
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open scoped BigOperators

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Proposition3Spec

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify

open Qatlib

namespace search_via_quantum_walk_proposition3

lemma stationary_pos {X : Type*} [Fintype X] [DecidableEq X]
    {P : Matrix X X ℝ} {π : X → ℝ} (hP : P.IsIrreducible)
    (hπ : ∀ x, 0 ≤ π x) (hsum : ∑ x, π x = 1)
    (hstat : ∀ y, ∑ x, π x * P x y = π y) : ∀ x, 0 < π x := by
  have hex : ∃ x, 0 < π x := by
    by_contra! h
    have hz : ∀ x, π x = 0 := fun x => le_antisymm (h x) (hπ x)
    simp [hz] at hsum
  obtain ⟨a, ha⟩ := hex
  have step : ∀ x y, 0 < π x → 0 < P x y → 0 < π y := by
    intro x y hx hxy
    rw [← hstat y]
    exact lt_of_lt_of_le (mul_pos hx hxy)
      (Finset.single_le_sum (fun z _ => mul_nonneg (hπ z) (hP.nonneg z y))
        (Finset.mem_univ x))
  letI : Quiver X := P.toQuiver
  intro x
  obtain ⟨p, hp⟩ := hP.connected a x
  clear hp
  induction p with
  | nil => exact ha
  | cons p e ih => exact step _ _ ih e.down

noncomputable def stationaryVector {X : Type*} (π : X → ℝ) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun x => (Real.sqrt (π x) : ℂ))

noncomputable def leftLift {X : Type*} (P : Matrix X X ℝ)
    (u : EuclideanSpace ℂ X) : EuclideanSpace ℂ (X × X) :=
  WithLp.toLp 2 (fun p => u p.1 * (Real.sqrt (P p.1 p.2) : ℂ))

noncomputable def rightLift {X : Type*} (P : Matrix X X ℝ) (π : X → ℝ)
    (w : EuclideanSpace ℂ X) : EuclideanSpace ℂ (X × X) :=
  WithLp.toLp 2 (fun p => w p.2 * (Real.sqrt (π p.1) : ℂ) *
    (Real.sqrt (P p.1 p.2) : ℂ) / (Real.sqrt (π p.2) : ℂ))

lemma norm_sqrt_sq {a : ℝ} (ha : 0 ≤ a) : ‖(Real.sqrt a : ℂ)‖ ^ 2 = a := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg a),
    Real.sq_sqrt ha]

lemma sqrt_ne_zero {a : ℝ} (ha : 0 < a) : (Real.sqrt a : ℂ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 ha))

lemma stationaryVector_norm {X : Type*} [Fintype X] {π : X → ℝ}
    (hπ : ∀ x, 0 ≤ π x) (hsum : ∑ x, π x = 1) :
    ‖stationaryVector π‖ = 1 := by
  have h : ‖stationaryVector π‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa only [stationaryVector, WithLp.ofLp_toLp, norm_sqrt_sq (hπ _)] using hsum
  nlinarith [norm_nonneg (stationaryVector π)]

lemma leftLift_norm {X : Type*} [Fintype X] {P : Matrix X X ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (u : EuclideanSpace ℂ X) : ‖leftLift P u‖ = ‖u‖ := by
  have h : ‖leftLift P u‖ ^ 2 = ‖u‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, leftLift,
      norm_mul, mul_pow, norm_sqrt_sq (hP _ _), Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hrow, mul_one]
  nlinarith [norm_nonneg (leftLift P u), norm_nonneg u]

lemma rightLift_norm {X : Type*} [Fintype X] {P : Matrix X X ℝ} {π : X → ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hπ : ∀ x, 0 < π x)
    (hstat : ∀ y, ∑ x, π x * P x y = π y)
    (w : EuclideanSpace ℂ X) : ‖rightLift P π w‖ = ‖w‖ := by
  have h : ‖rightLift P π w‖ ^ 2 = ‖w‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, rightLift,
      norm_div, norm_mul, div_pow, mul_pow, norm_sqrt_sq (hP _ _),
      norm_sqrt_sq (le_of_lt (hπ _)), Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    simp_rw [mul_assoc, ← Finset.sum_div, ← Finset.mul_sum, hstat]
    exact mul_div_cancel_right₀ _ (ne_of_gt (hπ y))
  nlinarith [norm_nonneg (rightLift P π w), norm_nonneg w]

lemma lift_inner {X : Type*} [Fintype X] [DecidableEq X]
    {P : Matrix X X ℝ} {π : X → ℝ} (hP : ∀ x y, 0 ≤ P x y)
    (u w : EuclideanSpace ℂ X) :
    inner ℂ (leftLift P u) (rightLift P π w) =
      inner ℂ u (Matrix.toEuclideanLin (mnrsDiscriminant P π) w) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply', leftLift, rightLift,
    Fintype.sum_prod_type, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, mnrsDiscriminant, map_mul,
    Complex.conj_ofReal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have hs : (Real.sqrt (P x y) : ℂ) ^ 2 = (P x y : ℂ) := by
    exact_mod_cast Real.sq_sqrt (hP x y)
  push_cast
  calc
    _ = starRingEnd ℂ (u x) * (w y * (Real.sqrt (π x) : ℂ) *
      (Real.sqrt (P x y) : ℂ) ^ 2 / (Real.sqrt (π y) : ℂ)) := by ring
    _ = _ := by rw [hs]; ring

lemma discriminant_stationaryVector {X : Type*} [Fintype X] [DecidableEq X]
    {P : Matrix X X ℝ} {π : X → ℝ}
    (hrow : ∀ x, ∑ y, P x y = 1) (hπ : ∀ x, 0 < π x) :
    Matrix.toEuclideanLin (mnrsDiscriminant P π) (stationaryVector π) =
      stationaryVector π := by
  ext x
  change (∑ y, mnrsDiscriminant P π x y * (Real.sqrt (π y) : ℂ)) =
    (Real.sqrt (π x) : ℂ)
  simp only [mnrsDiscriminant, Complex.ofReal_div, Complex.ofReal_mul,
    div_mul_cancel₀ _ (sqrt_ne_zero (hπ _)), ← Finset.mul_sum,
    ← Complex.ofReal_sum, hrow, Complex.ofReal_one, mul_one]

lemma adjoint_stationaryVector {X : Type*} [Fintype X] [DecidableEq X]
    {P : Matrix X X ℝ} {π : X → ℝ} (hπ : ∀ x, 0 < π x)
    (hstat : ∀ y, ∑ x, π x * P x y = π y) :
    (Matrix.toEuclideanLin (mnrsDiscriminant P π)).adjoint (stationaryVector π) =
      stationaryVector π := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  ext y
  change (∑ x, star (mnrsDiscriminant P π x y) * (Real.sqrt (π x) : ℂ)) =
    (Real.sqrt (π y) : ℂ)
  have he : ∀ x, star (mnrsDiscriminant P π x y) * (Real.sqrt (π x) : ℂ) =
      ((π x * P x y / Real.sqrt (π y) : ℝ) : ℂ) := by
    intro x
    simp only [mnrsDiscriminant, Complex.star_def, Complex.conj_ofReal,
      ← Complex.ofReal_mul]
    congr 1
    rw [div_mul_eq_mul_div]
    rw [show Real.sqrt (π x) * P x y * Real.sqrt (π x) = π x * P x y by
      calc
        _ = (Real.sqrt (π x)) ^ 2 * P x y := by ring
        _ = _ := by rw [Real.sq_sqrt (le_of_lt (hπ x))]]
  simp_rw [he]
  rw [← Complex.ofReal_sum, ← Finset.sum_div, hstat]
  congr 1
  apply (div_eq_iff (ne_of_gt (Real.sqrt_pos.2 (hπ y)))).2
  nlinarith [Real.sq_sqrt (le_of_lt (hπ y))]

lemma lift_eq_edge {X : Type*} {P : Matrix X X ℝ} {π : X → ℝ}
    (hπ : ∀ x, 0 < π x) {u w : EuclideanSpace ℂ X}
    (h : leftLift P u = rightLift P π w) {x y : X} (hxy : 0 < P x y) :
    u x / (Real.sqrt (π x) : ℂ) = w y / (Real.sqrt (π y) : ℂ) := by
  have he := congrArg (fun z : EuclideanSpace ℂ (X × X) => z (x, y)) h
  change u x * (Real.sqrt (P x y) : ℂ) =
    w y * (Real.sqrt (π x) : ℂ) * (Real.sqrt (P x y) : ℂ) /
      (Real.sqrt (π y) : ℂ) at he
  have hx := sqrt_ne_zero (hπ x)
  have hy := sqrt_ne_zero (hπ y)
  have hp := sqrt_ne_zero hxy
  apply (div_eq_div_iff hx hy).2
  apply (mul_right_cancel₀ hp)
  have he' := (eq_div_iff hy).1 he
  calc
    _ = (u x * (Real.sqrt (P x y) : ℂ)) * (Real.sqrt (π y) : ℂ) := by ring
    _ = _ := he'

lemma unit_pair_eq {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {P : Matrix X X ℝ} {π : X → ℝ} (hP : P.IsIrreducible)
    (hrow : ∀ x, ∑ y, P x y = 1) (hdiag : ∀ x, 0 < P x x)
    (hπ : ∀ x, 0 < π x) (hstat : ∀ y, ∑ x, π x * P x y = π y)
    {u w : EuclideanSpace ℂ X} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hinner : inner ℂ u (Matrix.toEuclideanLin (mnrsDiscriminant P π) w) = 1) :
    ∃ c : ℂ, u = c • stationaryVector π ∧ w = c • stationaryVector π := by
  have hl : leftLift P u = rightLift P π w :=
    (inner_eq_one_iff_of_norm_eq_one
      ((leftLift_norm hP.nonneg hrow u).trans hu)
      ((rightLift_norm hP.nonneg hπ hstat w).trans hw)).1
      ((lift_inner hP.nonneg u w).trans hinner)
  have huw : u = w := by
    ext x
    exact (div_left_inj' (sqrt_ne_zero (hπ x))).1 (lift_eq_edge hπ hl (hdiag x))
  have hedge : ∀ x y, 0 < P x y →
      w x / (Real.sqrt (π x) : ℂ) = w y / (Real.sqrt (π y) : ℂ) := by
    intro x y hxy
    simpa only [huw] using lift_eq_edge hπ hl hxy
  let a : X := Classical.choice inferInstance
  have hratio : ∀ y, w a / (Real.sqrt (π a) : ℂ) =
      w y / (Real.sqrt (π y) : ℂ) := by
    letI : Quiver X := P.toQuiver
    intro y
    obtain ⟨p, hp⟩ := hP.connected a y
    clear hp
    induction p with
    | nil => rfl
    | cons p e ih => exact ih.trans (hedge _ _ e.down)
  refine ⟨w a / (Real.sqrt (π a) : ℂ), ?_, ?_⟩
  · rw [huw]
    ext y
    exact (eq_div_iff (sqrt_ne_zero (hπ y))).1 (hratio y) |>.symm
  · ext y
    exact (eq_div_iff (sqrt_ne_zero (hπ y))).1 (hratio y) |>.symm

lemma norm_preserving_mem_span {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {P : Matrix X X ℝ} {π : X → ℝ} (hP : P.IsIrreducible)
    (hrow : ∀ x, ∑ y, P x y = 1) (hdiag : ∀ x, 0 < P x x)
    (hπ : ∀ x, 0 < π x) (hstat : ∀ y, ∑ x, π x * P x y = π y)
    (w : EuclideanSpace ℂ X)
    (hw : ‖Matrix.toEuclideanLin (mnrsDiscriminant P π) w‖ = ‖w‖) :
    w ∈ Submodule.span ℂ {stationaryVector π} := by
  by_cases hz : w = 0
  · simp [hz]
  let T := Matrix.toEuclideanLin (mnrsDiscriminant P π)
  let z : EuclideanSpace ℂ X := ((‖w‖ : ℂ)⁻¹) • w
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hz
  have hc : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  have hzn : ‖z‖ = 1 := by
    simp [z, norm_smul, Complex.norm_real, hn]
  have htzn : ‖T z‖ = 1 := by
    change ‖T (((‖w‖ : ℂ)⁻¹) • w)‖ = 1
    rw [map_smul, norm_smul]
    change ‖(‖w‖ : ℂ)⁻¹‖ * ‖Matrix.toEuclideanLin (mnrsDiscriminant P π) w‖ = 1
    rw [hw]
    simpa only [z, norm_smul] using hzn
  have hi : inner ℂ (T z) (T z) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, htzn]
    norm_num
  obtain ⟨c, _, hzc⟩ := unit_pair_eq hP hrow hdiag hπ hstat htzn hzn hi
  have hzmem : z ∈ Submodule.span ℂ {stationaryVector π} := by
    rw [hzc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  have hrecover : (‖w‖ : ℂ) • z = w := by
    simp [z, smul_smul, hc]
  rw [← hrecover]
  exact Submodule.smul_mem _ _ hzmem

lemma eigenspace_eq_span {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {P : Matrix X X ℝ} {π : X → ℝ} (hP : P.IsIrreducible)
    (hrow : ∀ x, ∑ y, P x y = 1) (hdiag : ∀ x, 0 < P x x)
    (hπ : ∀ x, 0 < π x) (hstat : ∀ y, ∑ x, π x * P x y = π y) :
    Module.End.eigenspace
      ((Matrix.toEuclideanLin (mnrsDiscriminant P π)).adjoint.comp
        (Matrix.toEuclideanLin (mnrsDiscriminant P π))) (1 : ℂ) =
      Submodule.span ℂ {stationaryVector π} := by
  let T := Matrix.toEuclideanLin (mnrsDiscriminant P π)
  apply le_antisymm
  · intro w hw
    have he : T.adjoint (T w) = w := by
      simpa only [Module.End.mem_eigenspace_iff, LinearMap.comp_apply, one_smul] using hw
    have hi := T.adjoint_inner_right w (T w)
    rw [he, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hi
    have hn : ‖T w‖ ^ 2 = ‖w‖ ^ 2 := by exact_mod_cast hi.symm
    apply norm_preserving_mem_span hP hrow hdiag hπ hstat w
    change ‖T w‖ = ‖w‖
    nlinarith [norm_nonneg (T w), norm_nonneg w]
  · apply Submodule.span_le.2
    intro w hw
    obtain rfl := Set.mem_singleton_iff.1 hw
    apply Module.End.mem_eigenspace_iff.2
    rw [LinearMap.comp_apply,
      discriminant_stationaryVector hrow hπ, adjoint_stationaryVector hπ hstat, one_smul]

lemma unique_singularValue_of_finrank_eigenspace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : E →ₗ[ℂ] E)
    (h : Module.finrank ℂ (Module.End.eigenspace (T.adjoint.comp T) (1 : ℂ)) = 1) :
    ∃! k : ℕ, T.singularValues k = 1 := by
  classical
  have hcard := T.isSymmetric_adjoint_comp_self.card_filter_eigenvalues_eq rfl (1 : ℂ)
  rw [h] at hcard
  obtain ⟨i, hi⟩ := Finset.card_eq_one.1 hcard
  have hi' : ({j | (T.isSymmetric_adjoint_comp_self.eigenvalues rfl j : ℂ) = 1} : Finset _) = {i} := by
    convert! hi using 1
  have his : T.singularValues i = 1 := by
    have he : (T.isSymmetric_adjoint_comp_self.eigenvalues rfl i : ℂ) = 1 := by
      have hm : i ∈ ({j | (T.isSymmetric_adjoint_comp_self.eigenvalues rfl j : ℂ) = 1} : Finset _) := by
        rw [hi']
        exact Finset.mem_singleton_self i
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hm
    rw [T.singularValues_fin rfl i, Real.sqrt_eq_one]
    exact_mod_cast he
  refine ⟨i, his, ?_⟩
  intro k hk
  have hlt : k < Module.finrank ℂ E := by
    by_contra! hge
    rw [T.singularValues_of_finrank_le hge] at hk
    norm_num at hk
  have he : (T.isSymmetric_adjoint_comp_self.eigenvalues rfl ⟨k, hlt⟩ : ℂ) = 1 := by
    rw [T.singularValues_of_lt rfl hlt, Real.sqrt_eq_one] at hk
    exact_mod_cast hk
  have hm : (⟨k, hlt⟩ : Fin (Module.finrank ℂ E)) ∈
      ({j | (T.isSymmetric_adjoint_comp_self.eigenvalues rfl j : ℂ) = 1} : Finset _) := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using he
  rw [hi', Finset.mem_singleton] at hm
  exact congrArg Fin.val hm

end search_via_quantum_walk_proposition3

theorem search_via_quantum_walk_proposition3 :
    ∀ (X : Type) [Fintype X] [DecidableEq X] [Nonempty X]
      (P : Matrix X X ℝ) (π : X → ℝ),
      P.IsIrreducible →
      (∀ x, ∑ y, P x y = 1) →
      (∀ x, 0 < P x x) →
      (∀ x, 0 ≤ π x) →
      (∑ x, π x) = 1 →
      (∀ y, ∑ x, π x * P x y = π y) →
      ∃! k : ℕ,
        (Matrix.toEuclideanLin (mnrsDiscriminant P π)).singularValues k = 1 := by
  intro X _ _ _ P π hP hrow hdiag hπ hsum hstat
  have hpos := search_via_quantum_walk_proposition3.stationary_pos hP hπ hsum hstat
  apply search_via_quantum_walk_proposition3.unique_singularValue_of_finrank_eigenspace
  rw [search_via_quantum_walk_proposition3.eigenspace_eq_span hP hrow hdiag hpos hstat]
  apply finrank_span_singleton
  intro hz
  have hn := search_via_quantum_walk_proposition3.stationaryVector_norm hπ hsum
  rw [hz, norm_zero] at hn
  norm_num at hn

end Qatlib.Concepts.WalkSearch.MnrsAmplify
