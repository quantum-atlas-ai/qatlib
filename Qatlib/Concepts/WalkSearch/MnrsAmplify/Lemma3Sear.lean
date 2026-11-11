/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MnrsAmplify.Lemma3Stat
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# Singular-value bounds for Markov discriminants

Proves that the discriminant obtained by conjugating a transition matrix with square roots of a
positive stationary distribution is a contraction. Consequently, its singular values lie in `[0,
1]`, as required in the MNRS walk analysis [MagniezNayakRolandSantha2011].

## Main statements

* `mnrs_discriminant_singular_values_mem_unit_interval`: The discriminant singular values of the
  stated finite irreducible chain with a positive stationary distribution lie in `[0, 1]`
  [Magniez et al., Lemma 3][MagniezNayakRolandSantha2011].
* `mnrs_discriminant_singular_values_mem_unit_interval_spec`: Establishes the discriminant
  singular-value contract `Lemma3WalkSpec.expected` [Magniez et al., Lemma
  3][MagniezNayakRolandSantha2011].

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open scoped BigOperators ComplexConjugate

set_option linter.unusedVariables false

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify

section Discriminant

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Expands an entry of the stationary-distribution similarity transform as `sqrt (π x) * P x y
/ sqrt (π y)`, with all factors interpreted in `ℂ`. -/
theorem mnrs_discriminant_singular_values_mem_unit_interval_entry
    (P : Matrix X X ℝ) (π : X → ℝ) (x y : X) :
    (Matrix.diagonal (fun x => (Real.sqrt (π x) : ℂ)) * Matrix.of (fun x y => (P x y : ℂ)) *
        Matrix.diagonal (fun x => (Real.sqrt (π x) : ℂ)⁻¹)) x y
      = (Real.sqrt (π x) : ℂ) * (P x y : ℂ) * (Real.sqrt (π y) : ℂ)⁻¹ := by
  simp

/-- Expands the inner product of `u` with the matrix image of `v` as the corresponding double
sum of complex entries. -/
theorem mnrs_discriminant_singular_values_mem_unit_interval_inner
    (M : Matrix X X ℂ) (u v : EuclideanSpace ℂ X) :
    inner ℂ u (Matrix.toEuclideanLin M v) = ∑ x, ∑ y, conj (u x) * (M x y * v y) :=
  Qatlib.Foundations.PureStateMath.BornBridge.inner_toEuclideanLin M u v

/-- For a nonnegative stochastic matrix with a positive stationary distribution, the
discriminant pairing has norm at most `‖u‖ * ‖v‖`. -/
theorem mnrs_discriminant_singular_values_mem_unit_interval_abs_inner_le
    {P : Matrix X X ℝ} {π : X → ℝ} {D : Matrix X X ℂ}
    (hD : ∀ x y, D x y = (Real.sqrt (π x) : ℂ) * (P x y : ℂ) * (Real.sqrt (π y) : ℂ)⁻¹)
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hπ : ∀ x, 0 < π x) (hstat : ∀ y, ∑ x, π x * P x y = π y)
    (u v : EuclideanSpace ℂ X) :
    ‖inner ℂ u (Matrix.toEuclideanLin D v)‖ ≤ ‖u‖ * ‖v‖ := by
  have hs : ∀ x y : X, (Real.sqrt (P x y) : ℂ) * (Real.sqrt (P x y) : ℂ) = (P x y : ℂ) := by
    intro x y
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hP x y)]
  have hc : ∀ x y : X, ((Real.sqrt (π x) / Real.sqrt (π y) : ℝ) : ℂ)
      = (Real.sqrt (π x) : ℂ) * (Real.sqrt (π y) : ℂ)⁻¹ := by
    intro x y
    rw [Complex.ofReal_div, div_eq_mul_inv]

  set a : EuclideanSpace ℂ (X × X) :=
    WithLp.toLp 2 (fun p : X × X => u p.1 * (Real.sqrt (P p.1 p.2) : ℂ)) with ha
  set b : EuclideanSpace ℂ (X × X) :=
    WithLp.toLp 2 (fun p : X × X => v p.2 *
      (((Real.sqrt (π p.1) / Real.sqrt (π p.2) : ℝ) : ℂ) * (Real.sqrt (P p.1 p.2) : ℂ))) with hb
  have hterma : ∀ p : X × X,
      ‖u p.1 * (Real.sqrt (P p.1 p.2) : ℂ)‖ ^ 2 = ‖u p.1‖ ^ 2 * P p.1 p.2 := by
    intro p
    rw [norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg (P p.1 p.2)), mul_pow,
      Real.sq_sqrt (hP p.1 p.2)]
  have htermb : ∀ p : X × X,
      ‖v p.2 * (((Real.sqrt (π p.1) / Real.sqrt (π p.2) : ℝ) : ℂ) *
          (Real.sqrt (P p.1 p.2) : ℂ))‖ ^ 2
        = (‖v p.2‖ ^ 2 * (π p.1 * P p.1 p.2)) / π p.2 := by
    intro p
    rw [norm_mul, norm_mul,
      Complex.norm_of_nonneg (div_nonneg (Real.sqrt_nonneg (π p.1)) (Real.sqrt_nonneg (π p.2))),
      Complex.norm_of_nonneg (Real.sqrt_nonneg (P p.1 p.2)), mul_pow, mul_pow, div_pow,
      Real.sq_sqrt (le_of_lt (hπ p.1)), Real.sq_sqrt (le_of_lt (hπ p.2)),
      Real.sq_sqrt (hP p.1 p.2)]
    ring
  have hinner : inner ℂ u (Matrix.toEuclideanLin D v) = inner ℂ a b := by
    rw [mnrs_discriminant_singular_values_mem_unit_interval_inner D u v]
    rw [show inner ℂ a b = ∑ p : X × X, conj (a p) * b p from by
      rw [PiLp.inner_apply]
      exact Finset.sum_congr rfl fun p _ => by rw [RCLike.inner_apply]; ring]
    rw [← Finset.sum_product', ← Finset.univ_product_univ]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [ha, hb, PiLp.toLp_apply]
    rw [hD p.1 p.2, ← hs p.1 p.2, hc p.1 p.2, map_mul conj, Complex.conj_ofReal]
    ring
  have hna : ‖a‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [ha, PiLp.toLp_apply]
    calc ∑ p : X × X, ‖u p.1 * (Real.sqrt (P p.1 p.2) : ℂ)‖ ^ 2
        = ∑ p : X × X, ‖u p.1‖ ^ 2 * P p.1 p.2 := Finset.sum_congr rfl fun p _ => hterma p
      _ = ∑ x, ∑ y, ‖u x‖ ^ 2 * P x y :=
          Fintype.sum_prod_type' (fun x y => ‖u x‖ ^ 2 * P x y)
      _ = ∑ x, ‖u x‖ ^ 2 * ∑ y, P x y := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ x, ‖u x‖ ^ 2 := by simp [hrow]
      _ = ‖u‖ ^ 2 := (EuclideanSpace.norm_sq_eq u).symm
  have hnb : ‖b‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [hb, PiLp.toLp_apply]
    calc ∑ p : X × X, ‖v p.2 * (((Real.sqrt (π p.1) / Real.sqrt (π p.2) : ℝ) : ℂ) *
            (Real.sqrt (P p.1 p.2) : ℂ))‖ ^ 2
        = ∑ p : X × X, (‖v p.2‖ ^ 2 * (π p.1 * P p.1 p.2)) / π p.2 :=
          Finset.sum_congr rfl fun p _ => htermb p
      _ = ∑ y, ∑ x, (‖v y‖ ^ 2 * (π x * P x y)) / π y :=
          Fintype.sum_prod_type_right (fun p => (‖v p.2‖ ^ 2 * (π p.1 * P p.1 p.2)) / π p.2)
      _ = ∑ y, ‖v y‖ ^ 2 * (∑ x, π x * P x y) / π y := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← Finset.sum_div, ← Finset.mul_sum]
      _ = ∑ y, ‖v y‖ ^ 2 := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hstat y, mul_div_cancel_right₀ _ (ne_of_gt (hπ y))]
      _ = ‖v‖ ^ 2 := (EuclideanSpace.norm_sq_eq v).symm
  have hsq : ∀ r s : ℝ, 0 ≤ r → 0 ≤ s → r ^ 2 = s ^ 2 → r = s := by
    intro r s hr hs h
    calc r = √(r ^ 2) := (Real.sqrt_sq hr).symm
      _ = √(s ^ 2) := by rw [h]
      _ = s := Real.sqrt_sq hs
  calc ‖inner ℂ u (Matrix.toEuclideanLin D v)‖ = ‖inner ℂ a b‖ := by rw [hinner]
    _ ≤ ‖a‖ * ‖b‖ := norm_inner_le_norm a b
    _ = ‖u‖ * ‖v‖ := by rw [hsq _ _ (norm_nonneg a) (norm_nonneg u) hna,
      hsq _ _ (norm_nonneg b) (norm_nonneg v) hnb]

/-- The discriminant associated with a nonnegative stochastic matrix and a positive stationary
distribution does not increase vector norms. -/
theorem mnrs_discriminant_singular_values_mem_unit_interval_norm_map_le
    {P : Matrix X X ℝ} {π : X → ℝ} {D : Matrix X X ℂ}
    (hD : ∀ x y, D x y = (Real.sqrt (π x) : ℂ) * (P x y : ℂ) * (Real.sqrt (π y) : ℂ)⁻¹)
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hπ : ∀ x, 0 < π x) (hstat : ∀ y, ∑ x, π x * P x y = π y)
    (v : EuclideanSpace ℂ X) :
    ‖Matrix.toEuclideanLin D v‖ ≤ ‖v‖ := by
  have hpair : ∀ u w : EuclideanSpace ℂ X,
      ‖inner ℂ u (Matrix.toEuclideanLin D w)‖ ≤ ‖u‖ * ‖w‖ :=
    mnrs_discriminant_singular_values_mem_unit_interval_abs_inner_le hD hP hrow hπ hstat
  have h2 : ‖Matrix.toEuclideanLin D v‖ ^ 2 ≤ ‖Matrix.toEuclideanLin D v‖ * ‖v‖ := by
    have h := hpair (Matrix.toEuclideanLin D v) v
    rw [inner_self_eq_norm_sq_to_K, Complex.norm_pow, RCLike.norm_ofReal, abs_norm] at h
    exact h
  by_cases hz : ‖Matrix.toEuclideanLin D v‖ = 0
  · rw [hz]
    exact norm_nonneg v
  · have hpos : 0 < ‖Matrix.toEuclideanLin D v‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

end Discriminant

/-- Every singular value of a finite-dimensional linear contraction is at most one. -/
theorem mnrs_discriminant_singular_values_mem_unit_interval_singularValues_le_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {T : E →ₗ[ℂ] E} (hT : ∀ v, ‖T v‖ ≤ ‖v‖) (n : ℕ) :
    T.singularValues n ≤ 1 := by
  rcases Nat.lt_or_ge n (Module.finrank ℂ E) with hn | hn
  · rw [T.singularValues_of_lt rfl hn, Real.sqrt_le_one]
    have happ : (LinearMap.adjoint T ∘ₗ T)
        (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl ⟨n, hn⟩)
        = ((T.isSymmetric_adjoint_comp_self.eigenvalues rfl ⟨n, hn⟩ : ℝ) : ℂ) •
          T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl ⟨n, hn⟩ :=
      T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl ⟨n, hn⟩
    have hL : inner ℂ (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl ⟨n, hn⟩)
        ((LinearMap.adjoint T ∘ₗ T) (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl ⟨n, hn⟩))
      = inner ℂ (T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl ⟨n, hn⟩))
          (T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl ⟨n, hn⟩)) := by
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
    rw [happ, inner_smul_right,
      (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).inner_eq_one ⟨n, hn⟩, mul_one,
      inner_self_eq_norm_sq_to_K] at hL
    have hμ : T.isSymmetric_adjoint_comp_self.eigenvalues rfl ⟨n, hn⟩
        = ‖T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl ⟨n, hn⟩)‖ ^ 2 := by
      have h1 : ((T.isSymmetric_adjoint_comp_self.eigenvalues rfl ⟨n, hn⟩ : ℝ) : ℂ)
          = ((‖T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl ⟨n, hn⟩)‖ : ℝ) : ℂ) ^ 2 :=
        hL
      exact_mod_cast h1
    have h1 : ‖T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl ⟨n, hn⟩)‖ ≤ 1 := by
      have h := hT (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl ⟨n, hn⟩)
      rwa [(T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).norm_eq_one ⟨n, hn⟩] at h
    rw [hμ]
    nlinarith [h1, norm_nonneg (T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl ⟨n, hn⟩))]
  · rw [T.singularValues_of_finrank_le hn]
    exact zero_le_one

section Core

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- For the stated irreducible stochastic chain and normalized positive stationary distribution,
every dimension-indexed discriminant singular value lies in `[0, 1]`. -/
theorem mnrs_discriminant_singular_values_mem_unit_interval_core
    (P : Matrix X X ℝ) (π : X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hirr : ∀ x y, Relation.ReflTransGen (fun a b : X => 0 < P a b) x y)
    (hπ : ∀ x, 0 < π x) (hmass : (∑ x, π x) = 1)
    (hstat : ∀ y, ∑ x, π x * P x y = π y) :
    ∀ i : Fin (Fintype.card X),
      (Matrix.toEuclideanLin (Matrix.diagonal (fun x => (Real.sqrt (π x) : ℂ)) *
          Matrix.of (fun x y => (P x y : ℂ)) *
          Matrix.diagonal (fun x => (Real.sqrt (π x) : ℂ)⁻¹))).singularValues i.val
        ∈ Set.Icc (0 : ℝ) 1 := by
  intro i
  have hentry : ∀ x y : X,
      (Matrix.diagonal (fun x => (Real.sqrt (π x) : ℂ)) *
          Matrix.of (fun x y => (P x y : ℂ)) *
          Matrix.diagonal (fun x => (Real.sqrt (π x) : ℂ)⁻¹)) x y
        = (Real.sqrt (π x) : ℂ) * (P x y : ℂ) * (Real.sqrt (π y) : ℂ)⁻¹ :=
    mnrs_discriminant_singular_values_mem_unit_interval_entry P π
  have hnorm : ∀ v : EuclideanSpace ℂ X,
      ‖(Matrix.toEuclideanLin (Matrix.diagonal (fun x => (Real.sqrt (π x) : ℂ)) *
          Matrix.of (fun x y => (P x y : ℂ)) *
          Matrix.diagonal (fun x => (Real.sqrt (π x) : ℂ)⁻¹))) v‖ ≤ ‖v‖ :=
    mnrs_discriminant_singular_values_mem_unit_interval_norm_map_le hentry hP hrow hπ hstat
  exact Set.mem_Icc.mpr
    ⟨LinearMap.singularValues_nonneg _ _,
     mnrs_discriminant_singular_values_mem_unit_interval_singularValues_le_one hnorm _⟩

end Core

/-- The discriminant singular values of the stated finite irreducible chain with a positive
stationary distribution lie in `[0, 1]` [Magniez et al., Lemma
3][MagniezNayakRolandSantha2011]. -/
theorem mnrs_discriminant_singular_values_mem_unit_interval :
    ∀ (X : Type*) [Fintype X] [DecidableEq X]
      (P : Matrix X X ℝ) (π : X → ℝ),
    (∀ x y, 0 ≤ P x y) →
    (∀ x, (∑ y : X, P x y) = 1) →
    (∀ x y, Relation.ReflTransGen (fun a b : X => 0 < P a b) x y) →
    (∀ x, 0 < π x) →
    (∑ x : X, π x) = 1 →
    (∀ y, (∑ x : X, π x * P x y) = π y) →
    let PC : Matrix X X ℂ := fun x y => (P x y : ℂ);
    let D : Matrix X X ℂ :=
      Matrix.diagonal (fun x => (Real.sqrt (π x) : ℂ)) * PC *
        Matrix.diagonal (fun x => (Real.sqrt (π x) : ℂ)⁻¹);
    ∀ i : Fin (Fintype.card X),
      (Matrix.toEuclideanLin D).singularValues i.val ∈ Set.Icc (0 : ℝ) 1 :=
  fun X _ _ P π hP hrow hirr hπ hmass hstat =>
    mnrs_discriminant_singular_values_mem_unit_interval_core P π hP hrow hirr hπ hmass hstat

/-- Establishes the discriminant singular-value contract `Lemma3WalkSpec.expected` [Magniez et
al., Lemma 3][MagniezNayakRolandSantha2011]. -/
theorem mnrs_discriminant_singular_values_mem_unit_interval_spec :
    Lemma3WalkSpec.expected :=
  mnrs_discriminant_singular_values_mem_unit_interval

end Qatlib.Concepts.WalkSearch.MnrsAmplify
