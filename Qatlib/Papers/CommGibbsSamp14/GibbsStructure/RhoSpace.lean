/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

/-!
# Commuting Gibbs samplers — the `ρ`-weighted `L²` space of observables

See [KastoryanoBrandao2014], Eq. (2) and Definition 8
([arXiv v3](https://arxiv.org/abs/1409.3435v3)).

For a Hamiltonian diagonal in a product basis, restrict the observables to the real
diagonal algebra in that basis. The restriction of the paper's Eq. (2) to this algebra
has inner product `⟨f,g⟩_ρ = tr[ρ f g] = ∑ x, ρ(x) f(x) g(x)`. This file builds that
space explicitly:

* `rhoInner` is the `ρ`-weighted inner product and `rhoNorm` is the induced `L²(ρ)` norm,
  realised as a genuine `EuclideanSpace` norm of the square-root gauge vector
  `f ↦ √ρ · f`;
* `IsOrthProj` captures the linearity, weighted self-adjointness and idempotence of an
  orthogonal projection. Positivity and unitality are separate properties of conditional
  expectations in Definition 8.

The results give the Hilbert-space properties of weighted orthogonal projections,
including contraction and orthogonal decomposition of the residual for a composition.
For commuting projections this gives variance subadditivity relative to the joint
projection. Theorem 23 of the paper uses a separate quasi-factorization estimate
with a clustering-dependent factor.
-/

set_option autoImplicit false

namespace Qatlib.Papers.CommGibbsSamp14.GibbsStructure

open scoped InnerProductSpace
open Finset

variable {X : Type*}

/-- A Gibbs weight on a finite configuration space: a strictly positive probability
distribution. For a diagonal Hamiltonian this can be obtained by normalizing its
Boltzmann weights. -/
structure GibbsWeight (X : Type*) [Fintype X] where
  /-- the diagonal entries `ρ(x)` -/
  weight : X → ℝ
  /-- the Gibbs state is faithful: every configuration has positive weight -/
  pos : ∀ x, 0 < weight x
  /-- the weight is normalised -/
  sum_eq_one : ∑ x, weight x = 1

namespace GibbsWeight

variable [Fintype X] (ρ : GibbsWeight X)

/-- Each Gibbs weight is non-negative. -/
theorem nonneg (x : X) : 0 ≤ ρ.weight x := (ρ.pos x).le

/-- The square-root gauge vector `√ρ · f`, an element of the ordinary Euclidean space that
carries the `L²(ρ)` norm of `f`. -/
noncomputable def gauge (f : X → ℝ) : EuclideanSpace ℝ X :=
  (EuclideanSpace.equiv X ℝ).symm (fun x => Real.sqrt (ρ.weight x) * f x)

/-- Evaluation of the square-root gauge vector. -/
@[simp] theorem gauge_apply (f : X → ℝ) (x : X) :
    (ρ.gauge f : X → ℝ) x = Real.sqrt (ρ.weight x) * f x := rfl

end GibbsWeight

variable [Fintype X]

/-- The `ρ`-weighted `L²` inner product `⟨f,g⟩_ρ = ∑ x, ρ(x) f(x) g(x)`.
On real diagonal observables, the paper's Eq. (2), `tr[√ρ f √ρ g]`, reduces to this sum. -/
noncomputable def rhoInner (ρ : GibbsWeight X) (f g : X → ℝ) : ℝ :=
  ∑ x, ρ.weight x * f x * g x

/-- The squared `ρ`-weighted `L²` norm `‖f‖²_{2,ρ}` of the paper. -/
noncomputable def rhoNormSq (ρ : GibbsWeight X) (f : X → ℝ) : ℝ := rhoInner ρ f f

/-- The `ρ`-weighted `L²` norm `‖f‖_{2,ρ}`, computed as a genuine `EuclideanSpace` norm of
the square-root gauge vector. -/
noncomputable def rhoNorm (ρ : GibbsWeight X) (f : X → ℝ) : ℝ := ‖ρ.gauge f‖

/-- The definitional identity `‖f‖²_{2,ρ} = ⟨f,f⟩_ρ`. -/
theorem rhoNormSq_def (ρ : GibbsWeight X) (f : X → ℝ) :
    rhoNormSq ρ f = rhoInner ρ f f := rfl

/-- The squared `EuclideanSpace` norm of the square-root gauge is the `ρ`-weighted square
norm. -/
theorem rhoNorm_sq (ρ : GibbsWeight X) (f : X → ℝ) :
    rhoNorm ρ f ^ 2 = rhoNormSq ρ f := by
  unfold rhoNorm rhoNormSq rhoInner
  rw [EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [GibbsWeight.gauge_apply, mul_pow, Real.sq_sqrt (ρ.nonneg x)]
  ring

/-- The `ρ`-weighted norm is non-negative. -/
theorem rhoNorm_nonneg (ρ : GibbsWeight X) (f : X → ℝ) : 0 ≤ rhoNorm ρ f :=
  norm_nonneg _

/-! ## Algebraic properties of the weighted inner product -/

/-- The `ρ`-weighted inner product is symmetric. -/
theorem rhoInner_symm (ρ : GibbsWeight X) (f g : X → ℝ) :
    rhoInner ρ f g = rhoInner ρ g f := by
  unfold rhoInner
  refine Finset.sum_congr rfl (fun x _ => ?_)
  ring

/-- Negation in the left argument. -/
theorem rhoInner_neg_left (ρ : GibbsWeight X) (f g : X → ℝ) :
    rhoInner ρ (-f) g = -rhoInner ρ f g := by
  unfold rhoInner
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [Pi.neg_apply]
  ring

/-- Additivity in the left argument. -/
theorem rhoInner_add_left (ρ : GibbsWeight X) (f₁ f₂ g : X → ℝ) :
    rhoInner ρ (f₁ + f₂) g = rhoInner ρ f₁ g + rhoInner ρ f₂ g := by
  unfold rhoInner
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [Pi.add_apply]
  ring

/-- Subtraction in the left argument. -/
theorem rhoInner_sub_left (ρ : GibbsWeight X) (f₁ f₂ g : X → ℝ) :
    rhoInner ρ (f₁ - f₂) g = rhoInner ρ f₁ g - rhoInner ρ f₂ g := by
  rw [sub_eq_add_neg, rhoInner_add_left, rhoInner_neg_left, sub_eq_add_neg]

/-- Additivity in the right argument. -/
theorem rhoInner_add_right (ρ : GibbsWeight X) (f g₁ g₂ : X → ℝ) :
    rhoInner ρ f (g₁ + g₂) = rhoInner ρ f g₁ + rhoInner ρ f g₂ := by
  rw [rhoInner_symm, rhoInner_add_left, rhoInner_symm ρ g₁ f, rhoInner_symm ρ g₂ f]

/-- Subtraction in the right argument. -/
theorem rhoInner_sub_right (ρ : GibbsWeight X) (f g₁ g₂ : X → ℝ) :
    rhoInner ρ f (g₁ - g₂) = rhoInner ρ f g₁ - rhoInner ρ f g₂ := by
  rw [rhoInner_symm, rhoInner_sub_left, rhoInner_symm ρ g₁ f, rhoInner_symm ρ g₂ f]

/-- Negation in the right argument. -/
theorem rhoInner_neg_right (ρ : GibbsWeight X) (f g : X → ℝ) :
    rhoInner ρ f (-g) = -rhoInner ρ f g := by
  rw [rhoInner_symm, rhoInner_neg_left, rhoInner_symm ρ f g]

/-- Homogeneity in the left argument. -/
theorem rhoInner_smul_left (ρ : GibbsWeight X) (c : ℝ) (f g : X → ℝ) :
    rhoInner ρ (c • f) g = c * rhoInner ρ f g := by
  unfold rhoInner
  simp only [Pi.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  ring

/-- Homogeneity in the right argument. -/
theorem rhoInner_smul_right (ρ : GibbsWeight X) (c : ℝ) (f g : X → ℝ) :
    rhoInner ρ f (c • g) = c * rhoInner ρ f g := by
  rw [rhoInner_symm, rhoInner_smul_left, rhoInner_symm]

/-- The zero observable has zero pairing. -/
theorem rhoInner_zero_left (ρ : GibbsWeight X) (g : X → ℝ) : rhoInner ρ 0 g = 0 := by
  unfold rhoInner
  simp

/-- The pairing of a finite sum is the sum of the pairings. -/
theorem rhoInner_sum_left {ι : Type*} (ρ : GibbsWeight X) (s : Finset ι)
    (f : ι → X → ℝ) (g : X → ℝ) :
    rhoInner ρ (∑ i ∈ s, f i) g = ∑ i ∈ s, rhoInner ρ (f i) g := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [rhoInner_zero_left]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, rhoInner_add_left, ih]

/-- The pairing against a finite sum is the sum of the pairings. -/
theorem rhoInner_sum_right {ι : Type*} (ρ : GibbsWeight X) (s : Finset ι)
    (f : ι → X → ℝ) (g : X → ℝ) :
    rhoInner ρ g (∑ i ∈ s, f i) = ∑ i ∈ s, rhoInner ρ g (f i) := by
  rw [rhoInner_symm, rhoInner_sum_left]
  exact Finset.sum_congr rfl (fun i _ => rhoInner_symm ρ _ _)

/-- The `ρ`-weighted square norm is non-negative. -/
theorem rhoInner_self_nonneg (ρ : GibbsWeight X) (f : X → ℝ) : 0 ≤ rhoInner ρ f f := by
  unfold rhoInner
  refine Finset.sum_nonneg (fun x _ => ?_)
  have h := ρ.nonneg x
  have : ρ.weight x * f x * f x = ρ.weight x * (f x) ^ 2 := by ring
  rw [this]
  exact mul_nonneg h (sq_nonneg _)

/-- Positive definiteness: the `ρ`-weighted square norm vanishes only on the zero
observable. -/
theorem rhoInner_self_eq_zero (ρ : GibbsWeight X) {f : X → ℝ}
    (h : rhoInner ρ f f = 0) : f = 0 := by
  funext x
  have hnonneg : ∀ y ∈ (Finset.univ : Finset X), 0 ≤ ρ.weight y * f y * f y := by
    intro y _
    have hy := ρ.nonneg y
    have : ρ.weight y * f y * f y = ρ.weight y * (f y) ^ 2 := by ring
    rw [this]
    exact mul_nonneg hy (sq_nonneg _)
  have hx := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h x (Finset.mem_univ x)
  rcases mul_eq_zero.mp hx with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (ne_of_gt (ρ.pos x))
    · exact h2
  · exact h1

/-- A non-zero observable has strictly positive `ρ`-weighted square norm. -/
theorem rhoInner_self_pos (ρ : GibbsWeight X) {f : X → ℝ} (hf : f ≠ 0) :
    0 < rhoInner ρ f f := by
  rcases lt_or_eq_of_le (rhoInner_self_nonneg ρ f) with h | h
  · exact h
  · exact absurd (rhoInner_self_eq_zero ρ h.symm) hf

/-- Cauchy–Schwarz for the `ρ`-weighted inner product. -/
theorem rhoInner_sq_le (ρ : GibbsWeight X) (f g : X → ℝ) :
    rhoInner ρ f g ^ 2 ≤ rhoInner ρ f f * rhoInner ρ g g := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset X)
    (fun x => Real.sqrt (ρ.weight x) * f x) (fun x => Real.sqrt (ρ.weight x) * g x)
  have h1 : ∑ x, (Real.sqrt (ρ.weight x) * f x) * (Real.sqrt (ρ.weight x) * g x)
      = rhoInner ρ f g := by
    unfold rhoInner
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [show (Real.sqrt (ρ.weight x) * f x) * (Real.sqrt (ρ.weight x) * g x)
        = (Real.sqrt (ρ.weight x) * Real.sqrt (ρ.weight x)) * (f x * g x) by ring,
      Real.mul_self_sqrt (ρ.nonneg x)]
    ring
  have h2 : ∑ x, (Real.sqrt (ρ.weight x) * f x) ^ 2 = rhoInner ρ f f := by
    unfold rhoInner
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [show (Real.sqrt (ρ.weight x) * f x) ^ 2
        = (Real.sqrt (ρ.weight x) * Real.sqrt (ρ.weight x)) * (f x * f x) by ring,
      Real.mul_self_sqrt (ρ.nonneg x)]
    ring
  have h3 : ∑ x, (Real.sqrt (ρ.weight x) * g x) ^ 2 = rhoInner ρ g g := by
    unfold rhoInner
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [show (Real.sqrt (ρ.weight x) * g x) ^ 2
        = (Real.sqrt (ρ.weight x) * Real.sqrt (ρ.weight x)) * (g x * g x) by ring,
      Real.mul_self_sqrt (ρ.nonneg x)]
    ring
  rwa [h1, h2, h3] at h

/-! ## Weighted orthogonal projections -/

/-- An orthogonal projection on the `ρ`-weighted observable space, given as a linear,
self-adjoint, idempotent map. -/
structure IsOrthProj (ρ : GibbsWeight X) (P : (X → ℝ) → (X → ℝ)) : Prop where
  /-- linearity on sums -/
  map_add : ∀ f g, P (f + g) = P f + P g
  /-- linearity on scalar multiples -/
  map_smul : ∀ (c : ℝ) (f), P (c • f) = c • P f
  /-- self-adjointness (reversibility, Definition 8(3)) -/
  adjoint : ∀ f g, rhoInner ρ (P f) g = rhoInner ρ f (P g)
  /-- idempotence (the projective or "Liouvillian" family) -/
  idem : ∀ f, P (P f) = P f

namespace IsOrthProj

variable {ρ : GibbsWeight X} {P Q : (X → ℝ) → (X → ℝ)}

/-- An orthogonal projection sends zero to zero. -/
theorem map_zero (hP : IsOrthProj ρ P) : P 0 = 0 := by
  simpa using hP.map_smul (0 : ℝ) (0 : X → ℝ)

/-- An orthogonal projection is additive on differences. -/
theorem map_sub (hP : IsOrthProj ρ P) (f g : X → ℝ) : P (f - g) = P f - P g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, hP.map_add, ← neg_one_smul ℝ g, hP.map_smul]
  simp

/-- An orthogonal projection commutes with negation. -/
theorem map_neg (hP : IsOrthProj ρ P) (f : X → ℝ) : P (-f) = -P f := by
  simpa using hP.map_smul (-1 : ℝ) f

/-- An orthogonal projection is a contraction for the `ρ`-weighted norm. -/
theorem contract (hP : IsOrthProj ρ P) (f : X → ℝ) :
    rhoInner ρ (P f) (P f) ≤ rhoInner ρ f f := by
  have hb : 0 ≤ rhoInner ρ (P f) (P f) := rhoInner_self_nonneg ρ _
  have haeq : rhoInner ρ (P f) (P f) = rhoInner ρ f (P f) := by
    rw [hP.adjoint f (P f), hP.idem]
  have hcs := rhoInner_sq_le ρ f (P f)
  rw [← haeq] at hcs
  have hbb : rhoInner ρ (P f) (P f) * rhoInner ρ (P f) (P f)
      ≤ rhoInner ρ f f * rhoInner ρ (P f) (P f) := by
    nlinarith [hcs]
  rcases eq_or_lt_of_le hb with h0 | hpos
  · rw [← h0]; exact rhoInner_self_nonneg ρ f
  · exact le_of_mul_le_mul_right hbb hpos

/-- The composite of two commuting orthogonal projections is an orthogonal projection. -/
theorem comp (hP : IsOrthProj ρ P) (hQ : IsOrthProj ρ Q)
    (hcomm : ∀ f, P (Q f) = Q (P f)) : IsOrthProj ρ (fun f => P (Q f)) where
  map_add f g := by simp only [hQ.map_add, hP.map_add]
  map_smul c f := by simp only [hQ.map_smul, hP.map_smul]
  adjoint f g := by
    show rhoInner ρ (P (Q f)) g = rhoInner ρ f (P (Q g))
    rw [hP.adjoint (Q f) g, hQ.adjoint f (P g), hcomm g]
  idem f := by
    show P (Q (P (Q f))) = P (Q f)
    rw [← hcomm (Q f), hQ.idem, hP.idem]

/-- The squared residual of a composition is bounded by the sum of the two squared
residuals. The inequality uses only orthogonality of the first projection. When both
projections are orthogonal and commute, the composition is the joint projection. -/
theorem var_comp_le (hP : IsOrthProj ρ P) (_hQ : IsOrthProj ρ Q)
    (_hcomm : ∀ f, P (Q f) = Q (P f)) (f : X → ℝ) :
    rhoInner ρ (f - P (Q f)) (f - P (Q f)) ≤
      rhoInner ρ (f - P f) (f - P f) + rhoInner ρ (f - Q f) (f - Q f) := by
  set a : X → ℝ := f - P f with ha
  set b : X → ℝ := P f - P (Q f) with hb
  have hb' : b = P (f - Q f) := by
    rw [hb, hP.map_sub]
  have hab : rhoInner ρ a b = 0 := by
    rw [hb']
    rw [← hP.adjoint a (f - Q f)]
    have hpa : P a = 0 := by
      rw [ha, hP.map_sub, hP.idem, sub_self]
    rw [hpa, rhoInner_zero_left]
  have hsplit : f - P (Q f) = a + b := by
    rw [ha, hb]; abel
  have hcontr : rhoInner ρ b b ≤ rhoInner ρ (f - Q f) (f - Q f) := by
    rw [hb']; exact hP.contract (f - Q f)
  have hpyth : rhoInner ρ (f - P (Q f)) (f - P (Q f))
      = rhoInner ρ a a + rhoInner ρ b b := by
    rw [hsplit, rhoInner_add_left, rhoInner_add_right, rhoInner_add_right, hab,
      rhoInner_symm ρ b a, hab]
    ring
  rw [hpyth, ha]
  linarith [hcontr]

end IsOrthProj

/-- The identity map is an orthogonal projection. -/
theorem id_isOrthProj (ρ : GibbsWeight X) : IsOrthProj ρ id where
  map_add := fun _ _ => rfl
  map_smul := fun _ _ => rfl
  adjoint := fun _ _ => rfl
  idem := fun _ => rfl

end Qatlib.Papers.CommGibbsSamp14.GibbsStructure
