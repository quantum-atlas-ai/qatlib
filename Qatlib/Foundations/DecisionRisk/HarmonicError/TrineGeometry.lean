/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.DecisionRisk.HarmonicError.WeightedError
import Mathlib.Tactic.FinCases

/-!
# Trine Geometry

Harmonic Error constructions for Decision Risk.
Defines `trineInput`.
Proves `pair_mass_lower`, `harmonic_of_moment`, `trine_scalar_moment`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.DecisionRisk.HarmonicError

/-- The stated finite risk construction satisfies `pair_mass_lower` with all displayed hypotheses retained. -/
lemma pair_mass_lower {x y S : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (_hS : 0 < S) (hxy : x+y ≤ S) :
    x*y/S ≤ pairWeight x y := by
  by_cases h : x+y=0
  · have hx0 : x=0 := by linarith
    have hy0 : y=0 := by linarith
    simp [hx0, hy0, pairWeight]
  · have hp : 0<x+y := lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm h)
    exact div_le_div_of_nonneg_left (mul_nonneg hx hy) hp hxy

/-- Moment criterion satisfied by every physical trine effect likelihood triple. -/
lemma harmonic_of_moment {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hm : x^2+y^2+z^2 ≤ (x+y+z)^2/2) :
    (x+y+z)/4 ≤ pairWeight x y+pairWeight x z+pairWeight y z := by
  by_cases h : x+y+z=0
  · have hx0 : x=0 := by linarith
    have hy0 : y=0 := by linarith
    have hz0 : z=0 := by linarith
    simp [hx0, hy0, hz0, pairWeight]
  · have hp : 0<x+y+z := lt_of_le_of_ne (by linarith) (Ne.symm h)
    have pxy := pair_mass_lower hx hy hp (by linarith : x+y ≤ x+y+z)
    have pxz := pair_mass_lower hx hz hp (by linarith : x+z ≤ x+y+z)
    have pyz := pair_mass_lower hy hz hp (by linarith : y+z ≤ x+y+z)
    have hs : (x+y+z)^2/4 ≤ x*y+x*z+y*z := by nlinarith
    have hdiv : (x+y+z)/4 ≤ (x*y+x*z+y*z)/(x+y+z) := by
      apply (le_div_iff₀ hp).2
      nlinarith
    simp only [add_div] at hdiv
    linarith

/-- The stated finite risk construction satisfies `trine_scalar_moment` with all displayed hypotheses retained. -/
lemma trine_scalar_moment {a b x : ℝ} (h : x^2 ≤ a*b) :
    a^2+((a+3*b)/4-Real.sqrt 3*x/2)^2+
      ((a+3*b)/4+Real.sqrt 3*x/2)^2 ≤ (3*(a+b)/2)^2/2 := by
  have hs : (Real.sqrt (3:ℝ))^2=3 := Real.sq_sqrt (by norm_num)
  have hxs : (Real.sqrt (3:ℝ))^2*x^2=3*x^2 := by rw [hs]
  have heq : (3*(a+b)/2)^2/2 - (a^2+((a+3*b)/4-Real.sqrt 3*x/2)^2+
      ((a+3*b)/4+Real.sqrt 3*x/2)^2) = (3/2:ℝ)*(a*b-x^2) := by
    nlinarith only [hxs]
  nlinarith

/-- The stated finite risk construction satisfies `norm_real_combination` with all displayed hypotheses retained. -/
lemma norm_real_combination {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u v : H) (a b : ℝ) :
    ‖a • u+b • v‖^2 = a^2*‖u‖^2 + 2*a*b*inner ℝ u v+b^2*‖v‖^2 := by
  simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- Exact first moment and second-moment upper bound for physical trine images. -/
theorem trine_image_moments {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u v : H) :
    let w₁ := (-1/2:ℝ) • u+(Real.sqrt 3/2) • v
    let w₂ := (-1/2:ℝ) • u+(-Real.sqrt 3/2) • v
    (‖u‖^2+‖w₁‖^2+‖w₂‖^2 = 3*(‖u‖^2+‖v‖^2)/2) ∧
    ((‖u‖^2)^2+(‖w₁‖^2)^2+(‖w₂‖^2)^2 ≤ (‖u‖^2+‖w₁‖^2+‖w₂‖^2)^2/2) := by
  dsimp only
  have h3 : (Real.sqrt (3:ℝ))^2=3 := Real.sq_sqrt (by norm_num)
  have hb3 : (Real.sqrt (3:ℝ))^2*‖v‖^2=3*‖v‖^2 := by rw [h3]
  have h₁ : ‖(-1/2:ℝ) • u+(Real.sqrt 3/2) • v‖^2 =
      (‖u‖^2+3*‖v‖^2)/4-Real.sqrt 3*inner ℝ u v/2 := by
    have hh := norm_real_combination u v (-1/2) (Real.sqrt 3/2)
    nlinarith only [hh, hb3]
  have h₂ : ‖(-1/2:ℝ) • u+(-Real.sqrt 3/2) • v‖^2 =
      (‖u‖^2+3*‖v‖^2)/4+Real.sqrt 3*inner ℝ u v/2 := by
    have hh := norm_real_combination u v (-1/2) (-Real.sqrt 3/2)
    nlinarith only [hh, hb3]
  constructor
  · rw [h₁,h₂]
    ring
  · rw [h₁,h₂]
    have hc : (inner ℝ u v)^2 ≤ ‖u‖^2*‖v‖^2 := by
      simpa only [real_inner_self_eq_norm_sq, ←pow_two] using real_inner_mul_inner_self_le u v
    have hm := trine_scalar_moment hc
    have hS : ‖u‖^2+((‖u‖^2+3*‖v‖^2)/4-Real.sqrt 3*inner ℝ u v/2)+
        ((‖u‖^2+3*‖v‖^2)/4+Real.sqrt 3*inner ℝ u v/2) = 3*(‖u‖^2+‖v‖^2)/2 := by ring
    rw [hS]
    exact hm


/-- Harmonic weight bound for the three Born likelihoods of a trine effect. -/
theorem trine_image_geometry {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u v : H) :
    let w₁ := (-1/2:ℝ) • u+(Real.sqrt 3/2) • v
    let w₂ := (-1/2:ℝ) • u+(-Real.sqrt 3/2) • v
    (‖u‖^2+‖w₁‖^2+‖w₂‖^2)/4 ≤
      pairWeight (‖u‖^2) (‖w₁‖^2) + pairWeight (‖u‖^2) (‖w₂‖^2) +
        pairWeight (‖w₁‖^2) (‖w₂‖^2) := by
  exact harmonic_of_moment (sq_nonneg _) (sq_nonneg _) (sq_nonneg _)
    (trine_image_moments u v).2

/-- Finite first-outcome aggregation. The conditional weights are unnormalized;
their geometry and total probability are checked separately from the conditional
remaining-copy quantum instruments. -/
theorem finite_branch_lower {ι H K : Type*} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (M : ι → KrausMeasurement H K) (ψ : Fin 3 → H) (q : ι → Fin 3 → ℝ) {t : ℝ}
    (hq : ∀ a i, 0 ≤ q a i) (ht : 0 ≤ t) (hn : ∀ i, ‖ψ i‖ = 1)
    (ho : ∀ i j, i ≠ j → ‖inner ℂ (ψ i) (ψ j)‖ = t)
    (hm : ∀ a, (q a 0)^2+(q a 1)^2+(q a 2)^2 ≤ (q a 0+q a 1+q a 2)^2/2)
    (hs : ∑ a, (q a 0+q a 1+q a 2) = 1) :
    t^2/(4*(1+t)) ≤ ∑ a, decisionError (fun k i => (M a).op k (ψ i)) (q a) := by
  have hb : ∀ a, t^2*((q a 0+q a 1+q a 2)/4) ≤
      (1+t)*decisionError (fun k i => (M a).op k (ψ i)) (q a) := by
    intro a
    have hg := harmonic_of_moment (hq a 0) (hq a 1) (hq a 2) (hm a)
    exact (mul_le_mul_of_nonneg_left hg (sq_nonneg t)).trans
      (kraus_error_bound (M a) ψ (q a) (hq a) ht hn ho)
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hb a)
  simp only [←Finset.mul_sum, div_eq_mul_inv, ←Finset.sum_mul, hs] at hsum
  have hp : 0 < 4*(1+t) := by positivity
  apply (div_le_iff₀ hp).2
  nlinarith only [hsum]

/-- Real-plane trine, used inside a possibly complex quantum state space after
restriction of scalars. No arbitrary basis-rotation oracle is introduced. -/
def trineInput {U : Type*} [AddCommGroup U] [Module ℝ U] (u v : U) (i : Fin 3) : U :=
  if i=0 then u else if i=1 then (-1/2:ℝ) • u+(Real.sqrt 3/2) • v
    else (-1/2:ℝ) • u+(-Real.sqrt 3/2) • v

/-- The stated finite risk construction satisfies `trineInput_zero` with all displayed hypotheses retained. -/
@[simp] lemma trineInput_zero {U : Type*} [AddCommGroup U] [Module ℝ U] (u v : U) :
    trineInput u v 0=u := rfl
/-- The stated finite risk construction satisfies `trineInput_one` with all displayed hypotheses retained. -/
@[simp] lemma trineInput_one {U : Type*} [AddCommGroup U] [Module ℝ U] (u v : U) :
    trineInput u v 1=(-1/2:ℝ) • u+(Real.sqrt 3/2) • v := rfl
/-- The stated finite risk construction satisfies `trineInput_two` with all displayed hypotheses retained. -/
@[simp] lemma trineInput_two {U : Type*} [AddCommGroup U] [Module ℝ U] (u v : U) :
    trineInput u v 2=(-1/2:ℝ) • u+(-Real.sqrt 3/2) • v := rfl

/-- The stated finite risk construction satisfies `trine_input_unit` with all displayed hypotheses retained. -/
lemma trine_input_unit {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (u v : U) (hu : ‖u‖=1) (hv : ‖v‖=1) (huv : inner ℝ u v=0) :
    ∀ i, ‖trineInput u v i‖=1 := by
  have h3 : (Real.sqrt (3:ℝ))^2=3 := Real.sq_sqrt (by norm_num)
  have hn₁ := norm_real_combination u v (-1/2) (Real.sqrt 3/2)
  have hn₂ := norm_real_combination u v (-1/2) (-Real.sqrt 3/2)
  rw [hu,hv,huv] at hn₁ hn₂
  intro i
  fin_cases i
  · change ‖u‖=1
    exact hu
  · change ‖(-1/2:ℝ) • u+(Real.sqrt 3/2) • v‖=1
    nlinarith [norm_nonneg ((-1/2:ℝ) • u+(Real.sqrt 3/2) • v)]
  · change ‖(-1/2:ℝ) • u+(-Real.sqrt 3/2) • v‖=1
    nlinarith [norm_nonneg ((-1/2:ℝ) • u+(-Real.sqrt 3/2) • v)]

/-- Conditional branch weights are actual first-copy Born masses divided by
three. First maps are allowed to be real-linear, a superset of complex-linear
instruments after scalar restriction. The remaining-copy maps are complex Kraus
instruments and may depend arbitrarily on the first classical outcome. -/
theorem finite_first_copy_lower {ι U V H K : Type*} [Fintype ι]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (A : ι → U →ₗ[ℝ] V) (hA : ∀ x, ∑ a, ‖A a x‖^2=‖x‖^2)
    (u v : U) (hu : ‖u‖=1) (hv : ‖v‖=1) (huv : inner ℝ u v=0)
    (M : ι → KrausMeasurement H K) (ψ : Fin 3 → H) {t : ℝ}
    (ht : 0 ≤ t) (hn : ∀ i, ‖ψ i‖=1)
    (ho : ∀ i j, i ≠ j → ‖inner ℂ (ψ i) (ψ j)‖=t) :
    t^2/(4*(1+t)) ≤ ∑ a, decisionError (fun k i => (M a).op k (ψ i))
      (fun i => ‖A a (trineInput u v i)‖^2/3) := by
  apply finite_branch_lower M ψ (fun a i => ‖A a (trineInput u v i)‖^2/3)
    (by intro a i; positivity) ht hn ho
  · intro a
    have hm := (trine_image_moments (A a u) (A a v)).2
    simp only [trineInput_zero,trineInput_one,trineInput_two,map_add,map_smul]
    nlinarith only [hm]
  · simp only [Finset.sum_add_distrib, ←Finset.sum_div, hA,
      trine_input_unit u v hu hv huv, one_pow]
    norm_num

/-- Direct consumer for complex first-copy instruments, with complex-orthogonal input basis. -/
theorem complex_first_copy_lower {ι U V H K : Type*} [Fintype ι]
    [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (A : ι → U →ₗ[ℂ] V) (hA : ∀ x, ∑ a, ‖A a x‖^2=‖x‖^2)
    (u v : U) (hu : ‖u‖=1) (hv : ‖v‖=1) (huv : inner ℂ u v=0)
    (M : ι → KrausMeasurement H K) (ψ : Fin 3 → H) {t : ℝ}
    (ht : 0 ≤ t) (hn : ∀ i, ‖ψ i‖=1)
    (ho : ∀ i j, i ≠ j → ‖inner ℂ (ψ i) (ψ j)‖=t) :
    letI : InnerProductSpace ℝ U := InnerProductSpace.complexToReal
    t^2/(4*(1+t)) ≤ ∑ a, decisionError (fun k i => (M a).op k (ψ i))
      (fun i => ‖A a (trineInput u v i)‖^2/3) := by
  letI : InnerProductSpace ℝ U := InnerProductSpace.complexToReal
  letI : InnerProductSpace ℝ V := InnerProductSpace.complexToReal
  have hreal : inner ℝ u v=0 := by
    change (inner ℂ u v).re=0
    rw [huv]
    rfl
  exact finite_first_copy_lower (fun a => (A a).restrictScalars ℝ) hA u v hu hv hreal
    M ψ ht hn ho
end Qatlib.Foundations.DecisionRisk.HarmonicError
