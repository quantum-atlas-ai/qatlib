/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteStats.BornEstimator.FiniteLaw
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.FiniteStats.BornEstimator
open scoped Classical BigOperators
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

theorem product_normalized (p : Ω → ℝ) (q : Ξ → ℝ)
    (hp : ∑ ω,p ω=1) (hq : ∑ ξ,q ξ=1) : (∑ x : Ω×Ξ,p x.1*q x.2)=1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum,hq,mul_one]
  exact hp

theorem product_mean_add (p : Ω → ℝ) (q : Ξ → ℝ)
    (hp : ∑ ω,p ω=1) (hq : ∑ ξ,q ξ=1) (f : Ω → ℝ) (g : Ξ → ℝ) :
    mean (fun x : Ω×Ξ => p x.1*q x.2) (fun x => f x.1+g x.2)=mean p f+mean q g := by
  unfold mean
  rw [Fintype.sum_prod_type]
  have he (ω : Ω) (ξ : Ξ) : p ω*q ξ*(f ω+g ξ)=(p ω*f ω)*q ξ+p ω*(q ξ*g ξ) := by ring
  simp only [he,Finset.sum_add_distrib,← Finset.mul_sum,hq,mul_one]
  rw [← Finset.sum_mul,hp,one_mul]

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

theorem product_variance_add (p : Ω → ℝ) (q : Ξ → ℝ)
    (hp : ∑ ω,p ω=1) (hq : ∑ ξ,q ξ=1) (f : Ω → ℝ) (g : Ξ → ℝ) :
    variance (fun x : Ω×Ξ => p x.1*q x.2) (fun x => f x.1+g x.2)=variance p f+variance q g := by
  rw [variance_eq _ (product_normalized p q hp hq),product_second_add p q hp hq,
    product_mean_add p q hp hq,variance_eq p hp,variance_eq q hq]
  ring

theorem mean_scale (p f : Ω → ℝ) (a : ℝ) : mean p (fun ω => a*f ω)=a*mean p f := by
  unfold mean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem variance_scale (p f : Ω → ℝ) (a : ℝ) : variance p (fun ω => a*f ω)=a^2*variance p f := by
  change (∑ ω,p ω*(a*f ω-mean p (fun ω => a*f ω))^2)=a^2*(∑ ω,p ω*(f ω-mean p f)^2)
  rw [mean_scale,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

universe u

def Shots (Ω : Type u) : ℕ → Type u
  | 0 => PUnit.{u+1}
  | n+1 => Ω×Shots Ω n

instance shotsFintype (n : ℕ) : Fintype (Shots Ω n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact @instFintypeProd Ω (Shots Ω n) _ ih

def shotLaw (p : Ω → ℝ) : (n : ℕ) → Shots Ω n → ℝ
  | 0 => fun _ => 1
  | n+1 => fun x => p x.1*shotLaw p n x.2

def shotSum (f : Ω → ℝ) : (n : ℕ) → Shots Ω n → ℝ
  | 0 => fun _ => 0
  | n+1 => fun x => f x.1+shotSum f n x.2

theorem shotLaw_normalized (p : Ω → ℝ) (hp : ∑ ω,p ω=1) (n : ℕ) : ∑ x,shotLaw p n x=1 := by
  induction n with
  | zero => simp [Shots, shotLaw, Finset.univ_unique]
  | succ n ih => exact product_normalized p (shotLaw p n) hp ih

omit [Fintype Ω] in

theorem shotLaw_nonneg (p : Ω → ℝ) (hp : ∀ ω,0 ≤ p ω) (n : ℕ) (x : Shots Ω n) :
    0 ≤ shotLaw p n x := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (hp x.1) (ih x.2)

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

def shotAverage (f : Ω → ℝ) (n : ℕ) (x : Shots Ω n) : ℝ := (n:ℝ)⁻¹*shotSum f n x

theorem shotAverage_mean (p f : Ω → ℝ) (hp : ∑ ω,p ω=1) (n : ℕ) (hn : 0<n) :
    mean (shotLaw p n) (shotAverage f n)=mean p f := by
  unfold shotAverage
  rw [mean_scale,shotSum_mean p f hp n]
  have hnr : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp

theorem shotAverage_variance (p f : Ω → ℝ) (hp : ∑ ω,p ω=1) (n : ℕ) (hn : 0<n) :
    variance (shotLaw p n) (shotAverage f n)=variance p f/(n:ℝ) := by
  unfold shotAverage
  rw [variance_scale,shotSum_variance p f hp n]
  have hnr : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp

end Qatlib.Foundations.FiniteStats.BornEstimator
