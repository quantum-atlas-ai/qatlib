/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.QdLoccModel.RedundantCodingReliability

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.QuditTeleport.QdLoccModel

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.SketchArith.SketchBuild

namespace Qatlib.Concepts.QuditTeleport.MessagingBounds
open Qatlib
open scoped Classical BigOperators

private theorem sample_sum_expect {X : Type} [Fintype X] [DecidableEq X]
    (q : FinDist X) (A : X → ℝ) (k : ℕ) :
    (independentSampleLaw (fun _ : Fin k => q)).expect (fun ω => ∑ i, A (ω i))=
      (k : ℝ)*q.expect A := by
  have hm := independent_weighted_expectation (fun _ : Fin k => q) (fun _ => 1) (fun _ => A)
  have hf : weightedSampleSum (fun _ : Fin k => (1 : ℝ)) (fun _ => A)=
      (fun ω => ∑ i, A (ω i)) := by
    funext ω
    simp [weightedSampleSum]
  rw [hf] at hm
  simpa using hm

private theorem sample_sum_diameter {X : Type} (A : X → ℝ)
    (hA : ∀ x, A x=0 ∨ A x=1) (k : ℕ) (i : Fin k) (ω τ : Fin k → X)
    (hω : ∀ j, j ≠ i → ω j=τ j) : |(∑ j, A (ω j))-(∑ j, A (τ j))| ≤ 1 := by
  rw [← Finset.sum_sub_distrib,Finset.sum_eq_single i]
  · rcases hA (ω i) with h | h <;> rcases hA (τ i) with h' | h' <;>
      norm_num [h,h']
  · intro j _ hj
    rw [hω j hj,sub_self]
  · simp

theorem redundantCodingReliability : RedundantCodingReliability := by
  intro X _ _ qr qs A hA hgap ε hε
  let δ := qr.expect A-qs.expect A
  have hδ : 0 < δ := hgap
  have hδ2 : 0 < δ^2 := sq_pos_of_pos hδ
  obtain ⟨k,hk⟩ := exists_nat_gt (max 0 (-(2*Real.log (ε/2))/δ^2))
  have hkR : (0 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hkN : 0 < k := by exact_mod_cast hkR
  have hkbound := (le_max_right (0 : ℝ) (-(2*Real.log (ε/2))/δ^2)).trans_lt hk
  have hlog : -(k : ℝ)*δ^2/2 ≤ Real.log (ε/2) := by
    have ht := (div_lt_iff₀ hδ2).mp hkbound
    linarith
  have htail : 2*Real.exp (-(k : ℝ)*δ^2/2) ≤ ε := by
    have he := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (by positivity : 0 < ε/2)] at he
    linarith
  let f : (Fin k → X) → ℝ := fun ω => ∑ i, A (ω i)
  let u := (k : ℝ)*δ/2
  have hu : 0 < u := by dsimp [u]; positivity
  have hS : (∑ _i : Fin k, (1 : ℝ)^2)=(k : ℝ) := by simp
  have hrate : -2*u^2/(∑ _i : Fin k, (1 : ℝ)^2)=-(k : ℝ)*δ^2/2 := by
    rw [hS]
    dsimp only [u]
    field_simp
  have hbound (q : FinDist X) :
      (∑ ω ∈ Finset.univ.filter (fun ω => u ≤ |f ω-(k : ℝ)*q.expect A|),
        (independentSampleLaw (fun _ : Fin k => q)).prob ω) ≤ ε := by
    have ht := (finite_product_bounded_differences_tail X k (fun _ => q) f (fun _ => 1) u
      (fun _ => by norm_num) (by rw [hS]; exact hkR) hu (sample_sum_diameter A hA k)).2
    rw [sample_sum_expect,hrate] at ht
    exact ht.trans htail
  refine ⟨k,hkN,?_,?_⟩
  · apply le_trans _ (hbound qr)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ω hω
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      have hh := (Finset.mem_filter.mp hω).2
      have ha := neg_le_abs (f ω-(k : ℝ)*qr.expect A)
      dsimp only [f,u,δ] at *
      nlinarith
    · intro ω _ _
      exact (independentSampleLaw (fun _ : Fin k => qr)).nonneg ω
  · apply le_trans _ (hbound qs)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ω hω
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      have hh := (Finset.mem_filter.mp hω).2
      have ha := le_abs_self (f ω-(k : ℝ)*qs.expect A)
      dsimp only [f,u,δ] at *
      nlinarith
    · intro ω _ _
      exact (independentSampleLaw (fun _ : Fin k => qs)).nonneg ω

end Qatlib.Concepts.QuditTeleport.MessagingBounds
