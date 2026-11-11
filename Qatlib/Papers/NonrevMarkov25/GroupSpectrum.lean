/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MarkovChains.ReverseKernel.Discriminant
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Discriminant difference norms for finite group walks

This module defines row kernels, stationary probabilities, affinities, and an explicit Euclidean
operator-bound predicate. For a finite-group walk with increments `ν (y * x⁻¹)`, it proves
uniform stationarity and identifies the norm of the flat discriminant minus the arithmetic
symmetrization as one minus its uniform mean affinity. The results connect the concrete norm
formulation to the nonreversible-chain setting of [ClaudonPiquemalMonmarche2025].

## Main statements

* `group_difference_norm`: For a finite-group increment walk with probability law `ν`, the
  uniform law is stationary and has self-overlap one, and the discriminant difference has
  operator norm `1 - meanAffinity`.
* `vectorNorm_eq_euclidean`: The explicit vector norm equals the native Euclidean-space norm of
  the corresponding vector.
* `native_group_difference_norm`: For a native row-stochastic group increment matrix, the
  uniform law is stationary with self-overlap one, and the discriminant difference has operator
  norm `1 - meanAffinity`.

## References

* [Claudon et al., 2025][ClaudonPiquemalMonmarche2025]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
namespace Qatlib.Papers.NonrevMarkov25.GroupSpectrum

/-- A finite-state transition matrix with nonnegative entries and every row summing to one. -/
structure RowKernel (S : Type) [Fintype S] where
  transition : Matrix S S ℝ
  nonnegative : ∀ x y,0≤transition x y
  rows : ∀ x,∑ y,transition x y=1

/-- Construct a row kernel from a matrix satisfying the native row-stochastic predicate. -/
def ofStochastic {S : Type} [Fintype S] [DecidableEq S] (P : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S) : RowKernel S :=
  ⟨P,hP.1,Matrix.sum_row_of_mem_rowStochastic hP⟩

/-- The flat discriminant associated with a row kernel transition matrix. -/
def flatMatrix {S : Type} [Fintype S] (K : RowKernel S) : Matrix S S ℝ :=
  Qatlib.Foundations.MarkovChains.ReverseKernel.flat K.transition

/-- The quadratic form of the flat discriminant on the vector of square roots of `π`. -/
def meanAffinity {S : Type} [Fintype S] (K : RowKernel S) (π : S → ℝ) : ℝ :=
  ∑ x,∑ y,Real.sqrt (π x)*flatMatrix K x y*Real.sqrt (π y)

/-- The sum of products of the square roots of the two real-valued weight functions. -/
def coherentOverlap {S : Type} [Fintype S] (μ π : S → ℝ) : ℝ :=
  ∑ x,Real.sqrt (μ x)*Real.sqrt (π x)

/-- The predicate that `π` is nonnegative, sums to one, and is stationary for the row kernel. -/
def StationaryProbability {S : Type} [Fintype S] (K : RowKernel S) (π : S → ℝ) : Prop :=
  (∀ x,0≤π x) ∧ (∑ x,π x=1) ∧ (∀ y,∑ x,π x*K.transition x y=π y)

/-- The square root of the sum of squared moduli of a finite complex vector. -/
def vectorNorm {S : Type} [Fintype S] (v : S → ℂ) : ℝ := Real.sqrt (∑ x,Complex.normSq (v x))

/-- The predicate that multiplication by `A` increases `vectorNorm` by at most the factor `r`. -/
def OperatorBound {S : Type} [Fintype S] (A : Matrix S S ℂ) (r : ℝ) : Prop :=
  ∀ v : S → ℂ,vectorNorm (A*ᵥv)≤r*vectorNorm v

/-- The predicate that `r` is an operator bound for `A` and is no greater than any other such
bound. -/
def OperatorNormEq {S : Type} [Fintype S] (A : Matrix S S ℂ) (r : ℝ) : Prop :=
  OperatorBound A r ∧ ∀ r' : ℝ,OperatorBound A r' → r≤r'

/-- The finite real inner product is at most the product of the square roots of the two sums of
squares. -/
lemma sum_mul_le_sqrt_mul_sqrt {S : Type} [Fintype S] (u w : S → ℝ) :
    ∑ x, u x * w x ≤ Real.sqrt (∑ x, u x ^ 2) * Real.sqrt (∑ x, w x ^ 2) := by
  classical
  by_cases hCpos : ∑ x, u x * w x ≤ 0
  · have h0 : 0 ≤ Real.sqrt (∑ x, u x ^ 2) * Real.sqrt (∑ x, w x ^ 2) := by positivity
    linarith
  push Not at hCpos
  set A : ℝ := ∑ x, u x ^ 2 with hAdef
  set B : ℝ := ∑ x, w x ^ 2 with hBdef
  set C : ℝ := ∑ x, u x * w x with hCdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun x _ => sq_nonneg _)
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun x _ => sq_nonneg _)
  have hBpos : 0 < B := by
    rcases lt_or_eq_of_le hB0 with h | h
    · exact h
    · exfalso
      have hw0 : ∀ x, w x = 0 := by
        intro x
        by_contra hx
        have h1 : 0 < w x ^ 2 := by positivity
        have h2 : w x ^ 2 ≤ B :=
          Finset.single_le_sum (fun y _ => sq_nonneg (w y)) (Finset.mem_univ x)
        linarith
      have hzero : C = 0 := by
        rw [hCdef]
        exact Finset.sum_eq_zero (fun x _ => by rw [hw0 x, mul_zero])
      linarith
  have quad : 0 ≤ ∑ x, ((C / B) * w x - u x) ^ 2 :=
    Finset.sum_nonneg (fun x _ => sq_nonneg _)
  have e1 : ∑ x, w x * w x = B := by
    rw [hBdef]
    exact Finset.sum_congr rfl (fun x _ => (pow_two (w x)).symm)
  have e2 : ∑ x, u x * u x = A := by
    rw [hAdef]
    exact Finset.sum_congr rfl (fun x _ => (pow_two (u x)).symm)
  have expand : ∑ x, ((C / B) * w x - u x) ^ 2
      = (C / B) * (C / B) * B - 2 * (C / B) * C + A := by
    have per : ∀ x : S, ((C / B) * w x - u x) ^ 2
        = ((C / B) * (C / B) * (w x * w x) - 2 * (C / B) * (u x * w x)) + u x * u x := by
      intro x; ring
    rw [Finset.sum_congr rfl (fun x _ => per x), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, e1, hCdef, e2]
  rw [expand] at quad
  have hsimplified : (C / B) * (C / B) * B - 2 * (C / B) * C + A = A - C * C / B := by
    field_simp
    ring
  rw [hsimplified] at quad
  have h2 : C * C / B ≤ A := by linarith
  have h3 : C * C ≤ A * B :=
    calc C * C = C * C / B * B := (div_mul_cancel₀ _ hBpos.ne').symm
      _ ≤ A * B := mul_le_mul_of_nonneg_right h2 hB0
  have h4 : C ≤ Real.sqrt A * Real.sqrt B := by
    have h5 : C ≤ Real.sqrt (A * B) := Real.le_sqrt_of_sq_le (by rw [pow_two]; exact h3)
    rwa [Real.sqrt_mul hA0] at h5
  rw [hAdef, hBdef, hCdef] at h4
  exact h4

/-- The explicitly defined finite complex vector norm is nonnegative. -/
lemma l2norm_nonneg {S : Type} [Fintype S] (v : S → ℂ) : 0 ≤ vectorNorm v :=
  Real.sqrt_nonneg _

/-- The finite complex vector norm satisfies the triangle inequality. -/
lemma l2norm_add_le {S : Type} [Fintype S] (u w : S → ℂ) :
    vectorNorm (u + w) ≤ vectorNorm u + vectorNorm w := by
  have habs : ∀ x : S, ‖u x + w x‖ ≤ ‖u x‖ + ‖w x‖ := fun x => norm_add_le (u x) (w x)
  have hper : ∀ x : S, Complex.normSq (u x + w x) ≤ (‖u x‖ + ‖w x‖) * (‖u x‖ + ‖w x‖) := by
    intro x
    have h1 : Complex.normSq (u x + w x) = ‖u x + w x‖ * ‖u x + w x‖ := by
      rw [Complex.normSq_eq_norm_sq (u x + w x)]
      exact pow_two _
    rw [h1]
    exact mul_self_le_mul_self (norm_nonneg _) (habs x)
  have hsum : ∑ x, Complex.normSq (u x + w x)
      ≤ ∑ x : S, (‖u x‖ + ‖w x‖) * (‖u x‖ + ‖w x‖) :=
    Finset.sum_le_sum (fun x _ => hper x)
  have hA0 : 0 ≤ ∑ x, Complex.normSq (u x) :=
    Finset.sum_nonneg (fun x _ => Complex.normSq_nonneg _)
  have hB0 : 0 ≤ ∑ x, Complex.normSq (w x) :=
    Finset.sum_nonneg (fun x _ => Complex.normSq_nonneg _)
  have hcs : ∑ x : S, (‖u x‖ * ‖w x‖) ≤ vectorNorm u * vectorNorm w := by
    have h := sum_mul_le_sqrt_mul_sqrt (fun x => ‖u x‖) (fun x => ‖w x‖)
    have hu : ∑ x, ‖u x‖ ^ 2 = ∑ x, Complex.normSq (u x) :=
      Finset.sum_congr rfl (fun x _ => (Complex.normSq_eq_norm_sq (u x)).symm)
    have hw : ∑ x, ‖w x‖ ^ 2 = ∑ x, Complex.normSq (w x) :=
      Finset.sum_congr rfl (fun x _ => (Complex.normSq_eq_norm_sq (w x)).symm)
    rw [hu, hw] at h
    exact h
  have hexp : ∑ x : S, (‖u x‖ + ‖w x‖) * (‖u x‖ + ‖w x‖)
      = (∑ x, Complex.normSq (u x)) + 2 * ∑ x : S, (‖u x‖ * ‖w x‖)
        + ∑ x, Complex.normSq (w x) := by
    have per : ∀ x : S, (‖u x‖ + ‖w x‖) * (‖u x‖ + ‖w x‖)
        = (Complex.normSq (u x) + 2 * (‖u x‖ * ‖w x‖)) + Complex.normSq (w x) := by
      intro x
      rw [Complex.normSq_eq_norm_sq (u x), Complex.normSq_eq_norm_sq (w x)]
      simp only [pow_two]
      ring
    rw [Finset.sum_congr rfl (fun x _ => per x), Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.mul_sum]
  have hfinal : (∑ x, Complex.normSq (u x + w x)) ≤ (vectorNorm u + vectorNorm w) * (vectorNorm u + vectorNorm w) := by
    have h2 : (vectorNorm u + vectorNorm w) * (vectorNorm u + vectorNorm w)
        = (∑ x, Complex.normSq (u x)) + 2 * (vectorNorm u * vectorNorm w)
          + ∑ x, Complex.normSq (w x) := by
      have hu2 : vectorNorm u * vectorNorm u = ∑ x, Complex.normSq (u x) := by
        show Real.sqrt (∑ x, Complex.normSq (u x)) * Real.sqrt (∑ x, Complex.normSq (u x)) = _
        rw [← Real.sqrt_mul hA0, Real.sqrt_mul_self hA0]
      have hw2 : vectorNorm w * vectorNorm w = ∑ x, Complex.normSq (w x) := by
        show Real.sqrt (∑ x, Complex.normSq (w x)) * Real.sqrt (∑ x, Complex.normSq (w x)) = _
        rw [← Real.sqrt_mul hB0, Real.sqrt_mul_self hB0]
      rw [← hu2, ← hw2]
      ring
    have h3 : (2 : ℝ) * ∑ x : S, (‖u x‖ * ‖w x‖) ≤ 2 * (vectorNorm u * vectorNorm w) := by
      linarith
    linarith [hsum, hexp, h2, h3]
  show Real.sqrt (∑ x, Complex.normSq ((u + w) x)) ≤ vectorNorm u + vectorNorm w
  apply le_trans (Real.sqrt_le_sqrt hfinal)
  rw [Real.sqrt_mul_self (by
    have h1 := l2norm_nonneg u
    have h2 := l2norm_nonneg w
    linarith)]

/-- The norm of a finite sum of complex vectors is at most the sum of their norms. -/
lemma l2norm_sum_le {S T : Type} [Fintype S] [Fintype T] [DecidableEq T]
    (W : T → (S → ℂ)) (s : Finset T) :
    vectorNorm (∑ g ∈ s, W g) ≤ ∑ g ∈ s, vectorNorm (W g) := by
  induction s using Finset.induction_on with
  | empty => simp [vectorNorm]
  | insert g s hg ih =>
    simp only [Finset.sum_insert hg]
    have h1 := l2norm_add_le (W g) (∑ x ∈ s, W x)
    have h2 : vectorNorm (W g) + vectorNorm (∑ x ∈ s, W x)
        ≤ vectorNorm (W g) + ∑ x ∈ s, vectorNorm (W x) := by linarith
    linarith [h1, h2]

/-- Scaling a finite complex vector multiplies its norm by the modulus of the scalar. -/
lemma l2norm_smul {S : Type} [Fintype S] (c : ℂ) (v : S → ℂ) :
    vectorNorm (c • v) = ‖c‖ * vectorNorm v := by
  have hc : Complex.normSq c = ‖c‖ * ‖c‖ := by
    rw [Complex.normSq_eq_norm_sq c]; exact pow_two (‖c‖)
  have h : ∑ x, Complex.normSq (c * v x) = ‖c‖ * ‖c‖ * ∑ x, Complex.normSq (v x) := by
    have per : ∀ x : S, Complex.normSq (c * v x) = Complex.normSq c * Complex.normSq (v x) :=
      fun x => Complex.normSq_mul c (v x)
    rw [Finset.sum_congr rfl (fun x _ => per x), hc, ← Finset.mul_sum]
  show Real.sqrt (∑ x, Complex.normSq (c * v x)) = ‖c‖ * Real.sqrt (∑ x, Complex.normSq (v x))
  rw [h, Real.sqrt_mul (show (0:ℝ) ≤ ‖c‖ * ‖c‖ by positivity) _,
    Real.sqrt_mul_self (norm_nonneg c)]

/-- Reindexing a vector by left multiplication with a group element preserves its norm. -/
lemma l2norm_mul_right {G : Type} [Group G] [Fintype G] (g : G) (v : G → ℂ) :
    vectorNorm (fun x => v (g * x)) = vectorNorm v := by
  show Real.sqrt (∑ x, Complex.normSq (v (g * x))) = Real.sqrt (∑ x, Complex.normSq (v x))
  exact congrArg Real.sqrt (Fintype.sum_bijective (fun x => g * x) (Group.mulLeft_bijective g)
    (fun x => Complex.normSq (v (g * x))) (fun x => Complex.normSq (v x)) (fun _ => rfl))

/-- For a group increment kernel, each flat entry is the square root of the product of the
forward and reverse increment weights. -/
lemma group_walk_entry {G : Type} [Group G] [Fintype G]
    (K : RowKernel G) (ν : G → ℝ)
    (hP : ∀ x y, K.transition x y = ν (y * x⁻¹)) (x y : G) :
    flatMatrix K x y = Real.sqrt (ν (y * x⁻¹) * ν (x * y⁻¹)) := by
  rw [flatMatrix, Qatlib.Foundations.MarkovChains.ReverseKernel.flat, hP x y, hP y x]

/-- Right multiplication by the inverse of a fixed group element is a bijection. -/
lemma mul_inv_right_bijective {G : Type} [Group G] (x : G) :
    Function.Bijective (fun y : G => y * x⁻¹) := by
  constructor
  · intro y₁ y₂ h
    have h' : y₁ * x⁻¹ = y₂ * x⁻¹ := h
    exact mul_right_cancel h'
  · intro g
    exact ⟨g * x, mul_inv_cancel_right g x⟩

/-- The constant weight function equal to the reciprocal of the finite group cardinality. -/
noncomputable def uniformLaw {G : Type} [Fintype G] : G → ℝ :=
  fun _ => (Fintype.card G : ℝ)⁻¹

/-- The complexified flat discriminant minus the complexified arithmetic symmetrization of the
transition matrix. -/
noncomputable def groupDiscriminantDiff {S : Type} [Fintype S] (K : RowKernel S) :
    Matrix S S ℂ :=
  (fun x y => (flatMatrix K x y : ℂ)) -
    (fun x y => (((K.transition x y + K.transition y x) / 2 : ℝ) : ℂ))

/-- For a finite-group increment walk with probability law `ν`, the uniform law is stationary
and has self-overlap one, and the discriminant difference has operator norm `1 -
meanAffinity`. -/
theorem group_difference_norm
    {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (K : RowKernel G) (ν : G → ℝ) (hν0 : ∀ g, 0 ≤ ν g)
    (hν1 : ∑ g, ν g = 1) (hP : ∀ x y, K.transition x y = ν (y * x⁻¹)) :
    StationaryProbability K (uniformLaw (G := G)) ∧
      coherentOverlap (uniformLaw (G := G)) (uniformLaw (G := G)) = 1 ∧
      OperatorNormEq (groupDiscriminantDiff K)
        (1 - meanAffinity K (uniformLaw (G := G))) := by
  classical
  set πv : G → ℝ := uniformLaw (G := G) with hπv
  have huni : ∀ x : G, πv x = (Fintype.card G : ℝ)⁻¹ := fun x => rfl
  set f : G → ℝ := fun g => Real.sqrt (ν g * ν g⁻¹) with hf
  set hh : G → ℝ := fun g => (ν g + ν g⁻¹) / 2 with hhh
  have hcardpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hcardne : ((Fintype.card G : ℝ)) ≠ 0 := ne_of_gt hcardpos

  have hinv2 : ∀ x y : G, (y * x⁻¹)⁻¹ = x * y⁻¹ := by
    intro x y
    rw [_root_.mul_inv_rev, inv_inv]
  have hD : ∀ x y : G, (flatMatrix K x y : ℂ) = (f (y * x⁻¹) : ℂ) := by
    intro x y
    rw [group_walk_entry K ν hP x y]
    simp only [hf]
    rw [hinv2 x y]
  have hDA : ∀ x y : G,
      (((K.transition x y + K.transition y x) / 2 : ℝ) : ℂ) = (hh (y * x⁻¹) : ℂ) := by
    intro x y
    rw [hP x y, hP y x]
    simp only [hhh]
    rw [hinv2 x y]

  have hfleh : ∀ g, f g ≤ hh g := by
    intro g
    rw [hf, hhh]
    have hnn : (0 : ℝ) ≤ (ν g + ν g⁻¹) / 2 := by linarith [hν0 g, hν0 g⁻¹]
    have h5 : ν g * ν g⁻¹ ≤ ((ν g + ν g⁻¹) / 2) ^ 2 := by
      have h6 : 4 * (ν g * ν g⁻¹) ≤ (ν g + ν g⁻¹) ^ 2 := by
        nlinarith [sq_nonneg (ν g - ν g⁻¹)]
      calc (ν g * ν g⁻¹ : ℝ) = 4 * (ν g * ν g⁻¹) / 4 := by field_simp
        _ ≤ (ν g + ν g⁻¹) ^ 2 / 4 := by
            exact div_le_div_of_nonneg_right h6 (by norm_num : (0:ℝ) ≤ 4)
        _ = ((ν g + ν g⁻¹) / 2) ^ 2 := by field_simp; ring
    calc Real.sqrt (ν g * ν g⁻¹)
        ≤ Real.sqrt (((ν g + ν g⁻¹) / 2) ^ 2) := Real.sqrt_le_sqrt h5
      _ = (ν g + ν g⁻¹) / 2 := Real.sqrt_sq hnn
  have hsumh : ∑ g, hh g = 1 := by
    have hinvsum : ∑ g, ν g⁻¹ = ∑ g, ν g :=
      Fintype.sum_bijective (fun g : G => g⁻¹) inv_bijective
        (fun g : G => ν g⁻¹) (fun g : G => ν g) (fun _ => rfl)
    simp only [hhh]
    have hper : ∀ g : G, (ν g + ν g⁻¹) / 2 = (ν g + ν g⁻¹) * (2 : ℝ)⁻¹ :=
      fun g => (div_eq_mul_inv _ _).symm
    rw [Finset.sum_congr rfl (fun g _ => hper g), ← Finset.sum_mul, Finset.sum_add_distrib,
      hinvsum, hν1]
    norm_num
  have hcardinvnn : (0 : ℝ) ≤ (Fintype.card G : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt hcardpos)
  have hsq2 : Real.sqrt ((Fintype.card G : ℝ)⁻¹) * Real.sqrt ((Fintype.card G : ℝ)⁻¹)
      = (Fintype.card G : ℝ)⁻¹ := by
    rw [← Real.sqrt_mul hcardinvnn, Real.sqrt_mul_self hcardinvnn]
  have hsumf : meanAffinity K πv = ∑ g, f g := by
    have hterm : ∀ x y : G, Real.sqrt (πv x) * flatMatrix K x y * Real.sqrt (πv y)
        = (Fintype.card G : ℝ)⁻¹ * Real.sqrt (K.transition x y * K.transition y x) := by
      intro x y
      simp only [huni x, huni y, flatMatrix]
      calc Real.sqrt ((Fintype.card G : ℝ)⁻¹) * Real.sqrt (K.transition x y * K.transition y x)
            * Real.sqrt ((Fintype.card G : ℝ)⁻¹)
          = (Real.sqrt ((Fintype.card G : ℝ)⁻¹) * Real.sqrt ((Fintype.card G : ℝ)⁻¹))
              * Real.sqrt (K.transition x y * K.transition y x) := by ring
        _ = (Fintype.card G : ℝ)⁻¹ * Real.sqrt (K.transition x y * K.transition y x) := by rw [hsq2]
    have hin : ∀ x : G, ∑ y, Real.sqrt (K.transition x y * K.transition y x) = ∑ g, f g := by
      intro x
      rw [Finset.sum_congr rfl (fun y _ => by rw [hP x y, hP y x])]
      exact Fintype.sum_bijective (fun y => y * x⁻¹) (mul_inv_right_bijective x)
        (fun y => Real.sqrt (ν (y * x⁻¹) * ν (x * y⁻¹))) f
        (fun y => by simp only [hf]; rw [hinv2 x y])
    have hconst : ∀ x : G, ∑ y, (Fintype.card G : ℝ)⁻¹ * Real.sqrt (K.transition x y * K.transition y x)
        = (Fintype.card G : ℝ)⁻¹ * ∑ g, f g := by
      intro x
      rw [← Finset.mul_sum, hin x]
    rw [meanAffinity]
    simp only [hterm, hconst]
    have hfin : ∑ x : G, (Fintype.card G : ℝ)⁻¹ * (∑ g, f g)
        = (Fintype.card G : ℝ) * ((Fintype.card G : ℝ)⁻¹ * ∑ g, f g) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    rw [hfin, ← mul_assoc, mul_inv_cancel₀ hcardne, one_mul]

  have hstat : StationaryProbability K πv := by
    refine ⟨fun x => by rw [huni]; positivity, ?_, fun y => ?_⟩
    · simp only [huni]
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, mul_inv_cancel₀ hcardne]
    · simp only [huni]
      rw [Finset.sum_congr rfl (fun x _ => by rw [hP x y])]
      have hbij : Function.Bijective (fun x : G => y * x⁻¹) :=
        (Group.mulLeft_bijective y).comp inv_bijective
      rw [← Finset.mul_sum, Fintype.sum_bijective (fun x : G => y * x⁻¹) hbij
        (fun x : G => ν (y * x⁻¹)) (fun g : G => ν g) (fun _ => rfl), hν1]
      rw [mul_one]
  have hoverlap : coherentOverlap πv πv = 1 := by
    have hterm : ∀ x : G, Real.sqrt (πv x) * Real.sqrt (πv x) = (Fintype.card G : ℝ)⁻¹ := by
      intro x
      rw [huni x, hsq2]
    rw [coherentOverlap, Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ, mul_inv_cancel₀ hcardne]

  set Hm : Matrix G G ℂ := groupDiscriminantDiff K with hHm
  have hHentry : ∀ x y : G, Hm x y = ((f (y * x⁻¹) - hh (y * x⁻¹) : ℝ) : ℂ) := by
    intro x y
    have h1 : Hm x y = (flatMatrix K x y : ℂ) - (((K.transition x y + K.transition y x) / 2 : ℝ) : ℂ) := by
      simp [hHm, groupDiscriminantDiff]
    rw [h1, hD x y, hDA x y, ← Complex.ofReal_sub]
  have hact : ∀ v : G → ℂ, ∀ x : G,
      (Hm *ᵥ v) x = ∑ g, ((f g - hh g : ℝ) : ℂ) * v (g * x) := by
    intro v x
    have h1 : (Hm *ᵥ v) x = ∑ y, Hm x y * v y := by
      simp [Matrix.mulVec, dotProduct]
    rw [h1, Finset.sum_congr rfl (fun y _ => by rw [hHentry x y])]
    exact Fintype.sum_bijective (fun y => y * x⁻¹) (mul_inv_right_bijective x)
      (fun y => ((f (y * x⁻¹) - hh (y * x⁻¹) : ℝ) : ℂ) * v y)
      (fun g => ((f g - hh g : ℝ) : ℂ) * v (g * x))
      (fun y => by simp only [inv_mul_cancel_right])
  have hsplit : ∀ v : G → ℂ,
      (Hm *ᵥ v) = ∑ g, ((f g - hh g : ℝ) : ℂ) • (fun x => v (g * x)) := by
    intro v
    funext x
    rw [hact v x]
    simp

  have hsumabs : ∑ g, |f g - hh g| = 1 - meanAffinity K πv := by
    have hper : ∀ g : G, |f g - hh g| = hh g - f g := by
      intro g
      rw [abs_of_nonpos (by linarith [hfleh g])]
      ring
    rw [Finset.sum_congr rfl (fun g _ => hper g), Finset.sum_sub_distrib, hsumh, hsumf]

  have hle : OperatorBound Hm (1 - meanAffinity K πv) := by
    intro v
    calc vectorNorm (Hm *ᵥ v)
        = vectorNorm (∑ g, ((f g - hh g : ℝ) : ℂ) • (fun x => v (g * x))) := by rw [hsplit v]
      _ ≤ ∑ g, vectorNorm (((f g - hh g : ℝ) : ℂ) • (fun x => v (g * x))) :=
          l2norm_sum_le _ _
      _ = ∑ g, |f g - hh g| * vectorNorm v := by
          exact Finset.sum_congr rfl (fun g _ => by
            rw [l2norm_smul, l2norm_mul_right]
            exact congrArg (· * vectorNorm v) (Complex.norm_real _))
      _ = (1 - meanAffinity K πv) * vectorNorm v := by
          rw [← Finset.sum_mul, hsumabs]

  have hmin : ∀ r' : ℝ, OperatorBound Hm r' → 1 - meanAffinity K πv ≤ r' := by
    intro r' hr'
    have hS : ∑ g, (f g - hh g) = meanAffinity K πv - 1 := by
      rw [Finset.sum_sub_distrib, hsumh, hsumf]
    have hones : (Hm *ᵥ (fun _ => (1 : ℂ))) = ((∑ g, (f g - hh g) : ℝ) : ℂ) •
        (fun _ => (1 : ℂ)) := by
      funext x
      rw [hsplit]
      simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, mul_one]
      rw [Complex.ofReal_sum]
    have h1 := hr' (fun _ => (1 : ℂ))
    rw [hones, l2norm_smul] at h1
    have hnorm : ‖((∑ g, (f g - hh g) : ℝ) : ℂ)‖ = |∑ g, (f g - hh g)| :=
      Complex.norm_real _
    rw [hnorm] at h1
    have hone0 : 0 < vectorNorm (fun _ : G => (1 : ℂ)) := by
      show 0 < Real.sqrt (∑ x : G, Complex.normSq (1 : ℂ))
      have hone1 : ∑ x : G, Complex.normSq (1 : ℂ) = (Fintype.card G : ℝ) := by
        simp
      rw [hone1]
      exact Real.sqrt_pos_of_pos hcardpos
    have h2 : |∑ g, (f g - hh g)| ≤ r' := by
      by_contra hcon
      push Not at hcon
      have hlt : r' * vectorNorm (fun _ : G => (1 : ℂ))
          < |∑ g, (f g - hh g)| * vectorNorm (fun _ : G => (1 : ℂ)) :=
        mul_lt_mul_of_pos_right hcon hone0
      linarith
    linarith [h2, neg_le_abs (∑ g, (f g - hh g)), hS]
  exact ⟨hstat, hoverlap, ⟨hle, hmin⟩⟩

/-- The explicit vector norm equals the native Euclidean-space norm of the corresponding vector
[ClaudonPiquemalMonmarche2025]. -/
theorem vectorNorm_eq_euclidean {S : Type} [Fintype S] (v : S → ℂ) :
    vectorNorm v=‖(WithLp.toLp 2 v : EuclideanSpace ℂ S)‖ := by
  rw [EuclideanSpace.norm_eq,vectorNorm]
  congr 1
  exact Finset.sum_congr rfl (fun x _ => Complex.normSq_eq_norm_sq (v x))

/-- For a native row-stochastic group increment matrix, the uniform law is stationary with
self-overlap one, and the discriminant difference has operator norm `1 - meanAffinity`
[ClaudonPiquemalMonmarche2025]. -/
theorem native_group_difference_norm {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (P : Matrix G G ℝ) (hP : P ∈ Matrix.rowStochastic ℝ G) (ν : G → ℝ)
    (hν0 : ∀ g,0≤ν g) (hν1 : ∑ g,ν g=1) (hinc : ∀ x y,P x y=ν (y*x⁻¹)) :
    StationaryProbability (ofStochastic P hP) (uniformLaw (G := G)) ∧
    coherentOverlap (uniformLaw (G := G)) (uniformLaw (G := G))=1 ∧
    OperatorNormEq (groupDiscriminantDiff (ofStochastic P hP))
      (1-meanAffinity (ofStochastic P hP) (uniformLaw (G := G))) :=
  group_difference_norm _ ν hν0 hν1 hinc
end Qatlib.Papers.NonrevMarkov25.GroupSpectrum
