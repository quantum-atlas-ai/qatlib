/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.FiniteStats.BornEstimator
open scoped Classical BigOperators
variable {Ω V : Type*} [Fintype Ω] [Fintype V]

def mean (p : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω,p ω*f ω

def second (p : Ω → ℝ) (f : Ω → ℝ) : ℝ := mean p (fun ω => f ω^2)

def variance (p : Ω → ℝ) (f : Ω → ℝ) : ℝ := mean p (fun ω => (f ω-mean p f)^2)

theorem variance_eq (p : Ω → ℝ) (hp : ∑ ω,p ω=1) (f : Ω → ℝ) :
    variance p f=second p f-(mean p f)^2 := by
  have he (M : ℝ) : (∑ ω,p ω*(f ω-M)^2)=second p f-2*M*mean p f+M^2 := by
    calc _ = ∑ ω,(p ω*f ω^2-2*M*(p ω*f ω)+M^2*p ω) := by
               apply Finset.sum_congr rfl
               intro ω _
               ring
         _ = _ := by
           simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
           rw [← Finset.mul_sum,← Finset.mul_sum,hp]
           simp only [second,mean,mul_one]
  change (∑ ω,p ω*(f ω-mean p f)^2)=_
  rw [he]
  ring

def lawVector (p f : Ω → ℝ) : EuclideanSpace ℝ Ω := WithLp.toLp 2 (fun ω => Real.sqrt (p ω)*f ω)

theorem lawVector_norm_sq (p f : Ω → ℝ) (hp : ∀ ω,0 ≤ p ω) :
    ‖lawVector p f‖^2=second p f := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold lawVector second mean
  simp only [mul_pow,Real.sq_sqrt (hp _)]

omit [Fintype Ω] in

theorem lawVector_sum (p : Ω → ℝ) (f : V → Ω → ℝ) :
    lawVector p (fun ω => ∑ i,f i ω)=∑ i,lawVector p (f i) := by
  ext ω
  simp [lawVector,Finset.mul_sum]

theorem component_norm (p : Ω → ℝ) (hp : ∀ ω,0 ≤ p ω) (z : Ω → ℝ)
    (r : ℝ) (hr : 0<r) (hz : second p z=r) (c : ℝ) :
    ‖lawVector p (fun ω => c*z ω/r)‖=|c|/Real.sqrt r := by
  have hs : second p (fun ω => c*z ω/r)=c^2/r := by
    unfold second mean at hz ⊢
    calc _ = (c^2/r^2)*(∑ ω,p ω*z ω^2) := by
               rw [Finset.mul_sum]
               apply Finset.sum_congr rfl
               intro ω _
               ring
         _ = c^2/r := by rw [hz];field_simp
  have hn := lawVector_norm_sq p (fun ω => c*z ω/r) hp
  rw [hs] at hn
  have hrn := Real.sqrt_nonneg r
  have hsq := Real.sq_sqrt hr.le
  apply (sq_eq_sq₀ (norm_nonneg _) (div_nonneg (abs_nonneg _) hrn)).mp
  rw [hn,div_pow,sq_abs,hsq]

theorem second_score_le (p : Ω → ℝ) (hp : ∀ ω,0 ≤ p ω)
    (z : V → Ω → ℝ) (r c : V → ℝ) (hr : ∀ i,0<r i)
    (hz : ∀ i,second p (z i)=r i) :
    second p (fun ω => ∑ i,c i*z i ω/r i) ≤ (∑ i,|c i|/Real.sqrt (r i))^2 := by
  have hnorm : ‖lawVector p (fun ω => ∑ i,c i*z i ω/r i)‖ ≤
      ∑ i,|c i|/Real.sqrt (r i) := by
    rw [lawVector_sum]
    calc _ ≤ ∑ i,‖lawVector p (fun ω => c i*z i ω/r i)‖ := norm_sum_le _ _
         _ = _ := by
           apply Finset.sum_congr rfl
           intro i _
           exact component_norm p hp (z i) (r i) (hr i) (hz i) (c i)
  rw [← lawVector_norm_sq _ _ hp]
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

theorem mean_score (p : Ω → ℝ) (z : V → Ω → ℝ) (r c μ : V → ℝ)
    (hr : ∀ i,r i≠0) (hz : ∀ i,mean p (z i)=r i*μ i) :
    mean p (fun ω => ∑ i,c i*z i ω/r i)=∑ i,c i*μ i := by
  unfold mean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc _ = c i/r i*mean p (z i) := by
             unfold mean
             rw [Finset.mul_sum]
             apply Finset.sum_congr rfl
             intro ω _
             ring
       _ = c i*μ i := by rw [hz i];field_simp [hr i]

theorem variance_score_le (p : Ω → ℝ) (hp : ∀ ω,0 ≤ p ω) (hn : ∑ ω,p ω=1)
    (z : V → Ω → ℝ) (r c : V → ℝ) (hr : ∀ i,0<r i)
    (hz : ∀ i,second p (z i)=r i) :
    variance p (fun ω => ∑ i,c i*z i ω/r i) ≤ (∑ i,|c i|/Real.sqrt (r i))^2 := by
  rw [variance_eq p hn]
  exact (sub_le_self _ (sq_nonneg _)).trans (second_score_le p hp z r c hr hz)

end Qatlib.Foundations.FiniteStats.BornEstimator
