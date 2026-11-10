/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.SphereNets.FiniteNet
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.SphereNets.Multilinear
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem opnorm_le_of_sphere {q : ℕ} (f : ContinuousMultilinearMap ℝ (fun _ : Fin q=>E) ℝ)
    (C : ℝ) (hC : 0≤C)
    (hbound : ∀ u : Fin q→E,(∀ i,‖u i‖=1)→|f u|≤C) : ‖f‖≤C := by
  apply f.opNorm_le_bound hC
  intro m
  by_cases hz : ∃ i,m i=0
  · obtain ⟨i,hi⟩ := hz
    rw [f.map_coord_zero i hi,norm_zero]
    positivity
  · have hn : ∀ i,‖m i‖≠0 := fun i hi => hz ⟨i,norm_eq_zero.mp hi⟩
    let u := fun i=>‖m i‖⁻¹ •m i
    have hu : ∀ i,‖u i‖=1 := by
      intro i
      simp only [u,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ (hn i)]
    have hm : m=fun i=>‖m i‖ •u i := by
      funext i
      simp only [u,smul_smul,mul_inv_cancel₀ (hn i),one_smul]
    have heq : f m=(∏ i,‖m i‖)*f u := by
      conv_lhs => rw [hm]
      exact f.map_smul_univ (fun i=>‖m i‖) u
    rw [heq,Real.norm_eq_abs,abs_mul,abs_of_nonneg (Finset.prod_nonneg (fun i _=>norm_nonneg _))]
    have hp : 0≤∏ i,‖m i‖ := Finset.prod_nonneg (fun i _=>norm_nonneg (m i))
    nlinarith [hbound u hu]

theorem unit_tuple_net_bound {q : ℕ} (f : ContinuousMultilinearMap ℝ (fun _ : Fin q=>E) ℝ)
    (s : Finset E) (ε C : ℝ) (hε : 0≤ε)
    (hs : ∀ y∈s,‖y‖=1)
    (hcover : ∀ x:E,‖x‖=1→∃ y∈s,dist x y≤ε)
    (hnet : ∀ v : Fin q→s,|f (fun i=>(v i : E))|≤C)
    (u : Fin q→E) (hu : ∀ i,‖u i‖=1) : |f u|≤C+‖f‖*q*ε := by
  choose v hvS hv using fun i=>hcover (u i) (hu i)
  have hvnorm : ∀ i,‖v i‖=1 := fun i=>hs _ (hvS i)
  have hunorm : ‖u‖≤1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i=>(hu i).le
  have hvnorm' : ‖v‖≤1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i=>(hvnorm i).le
  have huv : ‖u-v‖≤ε := by
    apply (pi_norm_le_iff_of_nonneg hε).2
    intro i
    simpa only [Pi.sub_apply,← dist_eq_norm] using hv i
  have hd := f.norm_image_sub_le u v
  have hm : max ‖u‖ ‖v‖≤1 := max_le hunorm hvnorm'
  have hp : (max ‖u‖ ‖v‖)^(q-1)≤1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ max ‖u‖ ‖v‖) hm (q-1)
  have hd0 : |f u-f v|≤‖f‖*q*(max ‖u‖ ‖v‖)^(q-1)*‖u-v‖ := by
    simpa only [Real.norm_eq_abs,Fintype.card_fin] using hd
  have hcoef : ‖f‖*q*(max ‖u‖ ‖v‖)^(q-1)≤‖f‖*q := by
    nlinarith [mul_nonneg (norm_nonneg f) (Nat.cast_nonneg q)]
  have hd' : |f u-f v|≤‖f‖*q*ε :=
    hd0.trans (mul_le_mul hcoef huv (norm_nonneg _) (by positivity))
  have hb : |f v|≤C := hnet (fun i=>⟨v i,hvS i⟩)
  linarith [abs_sub_abs_le_abs_sub (f u) (f v)]

theorem opnorm_le_twice_net {q : ℕ} (hq : 0<q)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin q=>E) ℝ)
    (s : Finset E) (C : ℝ) (hC : 0≤C)
    (hs : ∀ y∈s,‖y‖=1)
    (hcover : ∀ x:E,‖x‖=1→∃ y∈s,dist x y≤1/(2*q))
    (hnet : ∀ v : Fin q→s,|f (fun i=>(v i : E))|≤C) : ‖f‖≤2*C := by
  have hq' : (q:ℝ)≠0 := by exact_mod_cast hq.ne'
  have h := opnorm_le_of_sphere f (C+‖f‖*q*(1/(2*q))) (by positivity)
    (fun u hu=>unit_tuple_net_bound f s _ C (by positivity) hs hcover hnet u hu)
  have he : ‖f‖*q*(1/(2*q))=‖f‖/2 := by field_simp
  rw [he] at h
  linarith
end Qatlib.Foundations.MatrixGeometry.SphereNets.Multilinear
