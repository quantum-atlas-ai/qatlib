/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteStats.BornEstimator.FiniteLaw

/-!
# Moments of independent finite measurement shots

This module constructs repeated finite outcomes as `Shots`, their product weights as `shotLaw`,
and sums and averages of a statistic. It first proves product identities for weighted means,
second moments, and variances.

For normalized weights, the sum has mean and variance multiplied by the number of shots. For a
positive number of shots, the average preserves the mean and divides the variance by that
number, as needed for the sampling estimates in [XuEtAl2026].

## Main statements

* `shotSum_variance`: For normalized one-shot weights, the variance of the `n`-shot sum is `n`
  times the one-shot variance.
* `shotAverage_mean`: For a positive number of shots and normalized weights, the shot average
  has the same mean as the one-shot statistic.
* `shotAverage_variance`: For a positive number of shots and normalized weights, the variance of
  the shot average is the one-shot variance divided by the number of shots.

## References

* [Xu et al., 2026][XuEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.FiniteStats.BornEstimator
open scoped Classical BigOperators
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

/-- The product of two normalized finite weight functions is normalized. -/
theorem product_normalized (p : Ω → ℝ) (q : Ξ → ℝ)
    (hp : ∑ ω,p ω=1) (hq : ∑ ξ,q ξ=1) : (∑ x : Ω×Ξ,p x.1*q x.2)=1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum,hq,mul_one]
  exact hp

/-- Under normalized product weights, the mean of a sum of coordinate functions is the sum of
their means. -/
theorem product_mean_add (p : Ω → ℝ) (q : Ξ → ℝ)
    (hp : ∑ ω,p ω=1) (hq : ∑ ξ,q ξ=1) (f : Ω → ℝ) (g : Ξ → ℝ) :
    mean (fun x : Ω×Ξ => p x.1*q x.2) (fun x => f x.1+g x.2)=mean p f+mean q g := by
  unfold mean
  rw [Fintype.sum_prod_type]
  have he (ω : Ω) (ξ : Ξ) : p ω*q ξ*(f ω+g ξ)=(p ω*f ω)*q ξ+p ω*(q ξ*g ξ) := by ring
  simp only [he,Finset.sum_add_distrib,← Finset.mul_sum,hq,mul_one]
  rw [← Finset.sum_mul,hp,one_mul]

/-- Under normalized product weights, the second moment of a coordinate sum is the sum of the
two second moments plus twice the product of the means. -/
theorem product_second_add (p : Ω → ℝ) (q : Ξ → ℝ)
    (hp : ∑ ω,p ω=1) (hq : ∑ ξ,q ξ=1) (f : Ω → ℝ) (g : Ξ → ℝ) :
    second (fun x : Ω×Ξ => p x.1*q x.2) (fun x => f x.1+g x.2)=
      second p f+2*mean p f*mean q g+second q g := by
  unfold second mean
  rw [Fintype.sum_prod_type]
  have he (ω : Ω) (ξ : Ξ) : p ω*q ξ*(f ω+g ξ)^2=
      (p ω*f ω^2)*q ξ+(2*(p ω*f ω))*(q ξ*g ξ)+p ω*(q ξ*g ξ^2) := by ring
  simp only [he,Finset.sum_add_distrib,← Finset.mul_sum,hq,mul_one]
  rw [← Finset.sum_mul,← Finset.sum_mul,hp,one_mul,← Finset.mul_sum]

/-- Under normalized product weights, the variance of a sum of coordinate functions is the sum
of their variances. -/
theorem product_variance_add (p : Ω → ℝ) (q : Ξ → ℝ)
    (hp : ∑ ω,p ω=1) (hq : ∑ ξ,q ξ=1) (f : Ω → ℝ) (g : Ξ → ℝ) :
    variance (fun x : Ω×Ξ => p x.1*q x.2) (fun x => f x.1+g x.2)=variance p f+variance q g := by
  rw [variance_eq _ (product_normalized p q hp hq),product_second_add p q hp hq,
    product_mean_add p q hp hq,variance_eq p hp,variance_eq q hq]
  ring

/-- Scaling a function by `a` scales its weighted mean by `a`. -/
theorem mean_scale (p f : Ω → ℝ) (a : ℝ) : mean p (fun ω => a*f ω)=a*mean p f := by
  unfold mean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- Scaling a function by `a` scales its weighted variance by `a²`. -/
theorem variance_scale (p f : Ω → ℝ) (a : ℝ) : variance p (fun ω => a*f ω)=a^2*variance p f := by
  change (∑ ω,p ω*(a*f ω-mean p (fun ω => a*f ω))^2)=a^2*(∑ ω,p ω*(f ω-mean p f)^2)
  rw [mean_scale,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

universe u

/-- The recursively defined outcome space of `n` shots, with a singleton outcome space for zero
shots. -/
def Shots (Ω : Type u) : ℕ → Type u
  | 0 => PUnit.{u+1}
  | n+1 => Ω×Shots Ω n

instance shotsFintype (n : ℕ) : Fintype (Shots Ω n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact @instFintypeProd Ω (Shots Ω n) _ ih

/-- The product weight function on `n` shots, taking value one on the empty sequence. -/
def shotLaw (p : Ω → ℝ) : (n : ℕ) → Shots Ω n → ℝ
  | 0 => fun _ => 1
  | n+1 => fun x => p x.1*shotLaw p n x.2

/-- The sum of the statistic `f` over a recursively represented shot sequence. -/
def shotSum (f : Ω → ℝ) : (n : ℕ) → Shots Ω n → ℝ
  | 0 => fun _ => 0
  | n+1 => fun x => f x.1+shotSum f n x.2

/-- The product weights on any number of shots are normalized if the one-shot weights are
normalized. -/
theorem shotLaw_normalized (p : Ω → ℝ) (hp : ∑ ω,p ω=1) (n : ℕ) : ∑ x,shotLaw p n x=1 := by
  induction n with
  | zero => simp [Shots, shotLaw, Finset.univ_unique]
  | succ n ih => exact product_normalized p (shotLaw p n) hp ih

omit [Fintype Ω] in

/-- The product shot weights are nonnegative if the one-shot weights are nonnegative. -/
theorem shotLaw_nonneg (p : Ω → ℝ) (hp : ∀ ω,0 ≤ p ω) (n : ℕ) (x : Shots Ω n) :
    0 ≤ shotLaw p n x := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (hp x.1) (ih x.2)

/-- For normalized one-shot weights, the mean of the `n`-shot sum is `n` times the one-shot
mean. -/
theorem shotSum_mean (p f : Ω → ℝ) (hp : ∑ ω,p ω=1) (n : ℕ) :
    mean (shotLaw p n) (shotSum f n)=(n:ℝ)*mean p f := by
  induction n with
  | zero => simp [mean,Shots,shotLaw,shotSum]
  | succ n ih =>
    change mean (fun x : Ω×Shots Ω n => p x.1*shotLaw p n x.2)
      (fun x => f x.1+shotSum f n x.2)=_
    rw [product_mean_add p (shotLaw p n) hp (shotLaw_normalized p hp n),ih]
    push_cast
    ring

/-- For normalized one-shot weights, the variance of the `n`-shot sum is `n` times the one-shot
variance. -/
theorem shotSum_variance (p f : Ω → ℝ) (hp : ∑ ω,p ω=1) (n : ℕ) :
    variance (shotLaw p n) (shotSum f n)=(n:ℝ)*variance p f := by
  induction n with
  | zero => simp [variance,mean,Shots,shotLaw,shotSum]
  | succ n ih =>
    change variance (fun x : Ω×Shots Ω n => p x.1*shotLaw p n x.2)
      (fun x => f x.1+shotSum f n x.2)=_
    rw [product_variance_add p (shotLaw p n) hp (shotLaw_normalized p hp n),ih]
    push_cast
    ring

/-- The shot sum divided by the number of shots, using the real inverse of `n`. -/
def shotAverage (f : Ω → ℝ) (n : ℕ) (x : Shots Ω n) : ℝ := (n:ℝ)⁻¹*shotSum f n x

/-- For a positive number of shots and normalized weights, the shot average has the same mean as
the one-shot statistic. -/
theorem shotAverage_mean (p f : Ω → ℝ) (hp : ∑ ω,p ω=1) (n : ℕ) (hn : 0<n) :
    mean (shotLaw p n) (shotAverage f n)=mean p f := by
  unfold shotAverage
  rw [mean_scale,shotSum_mean p f hp n]
  have hnr : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp

/-- For a positive number of shots and normalized weights, the variance of the shot average is
the one-shot variance divided by the number of shots. -/
theorem shotAverage_variance (p f : Ω → ℝ) (hp : ∑ ω,p ω=1) (n : ℕ) (hn : 0<n) :
    variance (shotLaw p n) (shotAverage f n)=variance p f/(n:ℝ) := by
  unfold shotAverage
  rw [variance_scale,shotSum_variance p f hp n]
  have hnr : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp

end Qatlib.Foundations.FiniteStats.BornEstimator
