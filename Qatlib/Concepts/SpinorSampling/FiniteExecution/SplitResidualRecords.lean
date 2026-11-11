/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Model.BornCurrentRecords

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Split Residual Records

Split Residual Records constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.FiniteExecution.SplitResidual
noncomputable section
open scoped BigOperators
open Qatlib

variable {X : Type*} [Fintype X]

/-- Construction for add Linear in the split residual records model. -/
def addLinear (H : X → X → ℝ) (f : X → ℝ) (c : ℝ) (x y : X) : ℝ :=
  H x y+f x+f y+c

/-- Complete original `projection_add_linear` guarantee for `SplitResidualRecords`; all source hypotheses and output obligations are retained. -/
theorem projection_add_linear (p : FinDist X) (H : X → X → ℝ) (f : X → ℝ) (c : ℝ) (x : X) :
    pairKernelProjection p (addLinear H f c) x=pairKernelProjection p H x+f x+p.expect f+c := by
  change p.expect (fun y => H x y+f x+f y+c)=_
  simp only [finite_expect_add, finite_expect_const]
  rfl

/-- Complete original `mean_add_linear` guarantee for `SplitResidualRecords`; all source hypotheses and output obligations are retained. -/
theorem mean_add_linear (p : FinDist X) (H : X → X → ℝ) (f : X → ℝ) (c : ℝ) :
    pairKernelMean p (addLinear H f c)=pairKernelMean p H+2*p.expect f+c := by
  change p.expect (fun x => pairKernelProjection p (addLinear H f c) x)=_
  simp_rw [projection_add_linear]
  simp only [finite_expect_add, finite_expect_const]
  change pairKernelMean p H+p.expect f+p.expect f+c=_
  ring

/-- Complete original `centered_add_linear` guarantee for `SplitResidualRecords`; all source hypotheses and output obligations are retained. -/
theorem centered_add_linear (p : FinDist X) (H : X → X → ℝ) (f : X → ℝ) (c : ℝ) (x y : X) :
    centeredPairKernel p (addLinear H f c) x y=centeredPairKernel p H x y := by
  rw [centeredPairKernel, projection_add_linear, projection_add_linear, mean_add_linear]
  unfold addLinear centeredPairKernel
  ring

/-- Complete original `variance_add_constant` guarantee for `SplitResidualRecords`; all source hypotheses and output obligations are retained. -/
theorem variance_add_constant (p : FinDist X) (f : X → ℝ) (c : ℝ) :
    p.variance (fun x => f x+c)=p.variance f := by
  unfold FinDist.variance
  rw [finite_expect_add, finite_expect_const]
  congr 1
  funext x
  ring

variable {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]

/-- Construction for target Square in the split residual records model. -/
def targetSquare (β : ℝ) (u : S → ℝ) : ℝ :=
  (∑ x : S, (β*u x)^2)/(Fintype.card S : ℝ)

/-- Construction for target Linear in the split residual records model. -/
def targetLinear (α β : ℝ) (u : S → ℝ) (z : S × Bool) : ℝ :=
  -α*β*recordSign z.2*u z.1

/-- Construction for split Kernel in the split residual records model. -/
def splitKernel (α β : ℝ) (u : S → ℝ) : (S × Bool) → (S × Bool) → ℝ :=
  addLinear (residualCollision α 0 (fun _ => 0)) (targetLinear α β u) (targetSquare β u)

omit [Nonempty S] in
/-- Complete original `split_kernel_symmetric` guarantee for `SplitResidualRecords`; all source hypotheses and output obligations are retained. -/
theorem split_kernel_symmetric (α β : ℝ) (u : S → ℝ) (l r : S × Bool) :
    splitKernel α β u l r=splitKernel α β u r l := by
  unfold splitKernel addLinear
  rw [residual_kernel_symmetric (fun _ : S => 0) α 0 l r]
  ring

/-- Complete original `split_centered_target_free` guarantee for `SplitResidualRecords`; all source hypotheses and output obligations are retained. -/
theorem split_centered_target_free (m u : S → ℝ) (hm : ∀ x, |m x| ≤ 1)
    (α β : ℝ) (l r : S × Bool) :
    centeredPairKernel (signedRecordLaw m hm) (splitKernel α β u) l r=
      centeredPairKernel (signedRecordLaw m hm) (residualCollision α 0 (fun _ => 0)) l r :=
  centered_add_linear _ _ _ _ l r

/-- Complete original `split_projection` guarantee for `SplitResidualRecords`; all source hypotheses and output obligations are retained. -/
theorem split_projection (m u : S → ℝ) (hm : ∀ x, |m x| ≤ 1) (α β : ℝ) (l : S × Bool) :
    pairKernelProjection (signedRecordLaw m hm) (splitKernel α β u) l=
      α*recordSign l.2*(α*m l.1-β*u l.1)+
        ((signedRecordLaw m hm).expect (targetLinear α β u)+targetSquare β u) := by
  rw [splitKernel, projection_add_linear]
  change (signedRecordLaw m hm).expect (fun r => residualCollision α 0 (fun _ => 0) l r)+_+_+_=_
  rw [residual_collision_projection]
  unfold targetLinear
  ring

omit [DecidableEq S] in
/-- Complete original `signed_weighted_sign_expect` guarantee for `SplitResidualRecords`; all source hypotheses and output obligations are retained. -/
theorem signed_weighted_sign_expect (m f : S → ℝ) (hm : ∀ x, |m x| ≤ 1) :
    (signedRecordLaw m hm).expect (fun z => recordSign z.2*f z.1)=
      (∑ x : S, m x*f x)/(Fintype.card S : ℝ) := by
  change (∑ z : S × Bool, signedRecordWeight m z*(recordSign z.2*f z.1))=_
  rw [Fintype.sum_prod_type]
  have hc (x : S) : (∑ b : Bool, signedRecordWeight m (x,b)*(recordSign b*f x))=
      m x*f x/(Fintype.card S : ℝ) := by
    calc
      _ = (∑ b : Bool, signedRecordWeight m (x,b)*recordSign b)*f x := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = _ := by
        have ht := signed_record_cell_mean m (fun _ : S => 0) 1 0 x
        simp only [one_mul, zero_mul, sub_zero] at ht
        rw [ht]
        ring
  simpa only [Finset.sum_div] using Finset.sum_congr rfl (fun x _ => hc x)

/-- Complete original `split_kernel_unbiased` guarantee for `SplitResidualRecords`; all source hypotheses and output obligations are retained. -/
theorem split_kernel_unbiased (m u : S → ℝ) (hm : ∀ x, |m x| ≤ 1) (α β : ℝ) :
    pairKernelMean (signedRecordLaw m hm) (splitKernel α β u)=
      (∑ x : S, (α*m x-β*u x)^2)/(Fintype.card S : ℝ) := by
  rw [splitKernel, mean_add_linear]
  have hb := residual_collision_unbiased m (fun _ : S => 0) α 0 hm
  change pairKernelMean (signedRecordLaw m hm) (residualCollision α 0 (fun _ => 0))=_ at hb
  rw [hb]
  have ht : (signedRecordLaw m hm).expect (targetLinear α β u)=
      (∑ x : S, m x*(-α*β*u x))/(Fintype.card S : ℝ) := by
    have hf : targetLinear α β u=fun z : S × Bool => recordSign z.2*(-α*β*u z.1) := by
      funext z
      unfold targetLinear
      ring
    rw [hf]
    exact signed_weighted_sign_expect m (fun x => -α*β*u x) hm
  rw [ht, targetSquare]
  simp only [zero_mul, sub_zero]
  rw [← mul_div_assoc, Finset.mul_sum, ← add_div, ← add_div,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Complete original `split_projection_variance_bound` guarantee for `SplitResidualRecords`; all source hypotheses and output obligations are retained. -/
theorem split_projection_variance_bound (m u : S → ℝ) (hm : ∀ x, |m x| ≤ 1) (α β : ℝ) :
    (signedRecordLaw m hm).variance (pairKernelProjection (signedRecordLaw m hm) (splitKernel α β u)) ≤
      α^2*((∑ x : S, (α*m x-β*u x)^2)/(Fintype.card S : ℝ)) := by
  let p := signedRecordLaw m hm
  have hp : pairKernelProjection p (splitKernel α β u)=
      fun l => α*recordSign l.2*(α*m l.1-β*u l.1)+(p.expect (targetLinear α β u)+targetSquare β u) := by
    funext l
    exact split_projection m u hm α β l
  rw [hp, variance_add_constant]
  apply (finite_variance_le_second p _).trans_eq
  have hs (l : S × Bool) : (α*recordSign l.2*(α*m l.1-β*u l.1))^2=
      α^2*(α*m l.1-β*u l.1)^2 := by
    rcases l with ⟨x,b⟩
    cases b <;> simp [recordSign] <;> ring
  simp_rw [hs]
  rw [finite_expect_mul]
  dsimp only [p]
  exact congrArg (fun z : ℝ => α^2*z)
    (signed_record_site_expect m hm (fun x => (α*m x-β*u x)^2))

/-- Complete original `split_centered_second_bound` guarantee for `SplitResidualRecords`; all source hypotheses and output obligations are retained. -/
theorem split_centered_second_bound (m u : S → ℝ) (hm : ∀ x, |m x| ≤ 1)
    (α β : ℝ) (hα : 0 ≤ α) :
    (signedRecordLaw m hm).expect (fun l => (signedRecordLaw m hm).expect
      (fun r => (centeredPairKernel (signedRecordLaw m hm) (splitKernel α β u) l r)^2)) ≤
      (Fintype.card S : ℝ)*α^4 := by
  simp_rw [split_centered_target_free]
  rw [centered_pair_second_moment _ _ (residual_kernel_symmetric _ _ _)]
  have hv := finite_expect_nonneg (signedRecordLaw m hm)
    (fun l => (pairKernelProjection (signedRecordLaw m hm) (residualCollision α 0 (fun _ => 0)) l-
      (signedRecordLaw m hm).expect (pairKernelProjection (signedRecordLaw m hm)
        (residualCollision α 0 (fun _ => 0))))^2) (fun _ => sq_nonneg _)
  apply (sub_le_self _ (mul_nonneg (by norm_num) hv)).trans
  apply (pair_variance_le_second _ _).trans
  simpa using residual_kernel_second_bound m (fun _ : S => 0) α 0 0 hm
    (by simp) hα (by norm_num)

/-- Complete original `split_ustatistic_variance_bound` guarantee for `SplitResidualRecords`; all source hypotheses and output obligations are retained. -/
theorem split_ustatistic_variance_bound {n : ℕ} (m u : S → ℝ) (hm : ∀ x, |m x| ≤ 1)
    (α β : ℝ) (hα : 0 ≤ α) (hn : 2 ≤ n) :
    (∑ ω : Fin n → S × Bool, (signedRecordLaw m hm).probOf ω*
      (orderedUStatistic (splitKernel α β u) ω-pairKernelMean (signedRecordLaw m hm) (splitKernel α β u))^2) ≤
      4*α^2*((∑ x : S, (α*m x-β*u x)^2)/(Fintype.card S : ℝ))/(n : ℝ)+
        2*(Fintype.card S : ℝ)*α^4/(n*(n-1) : ℕ) := by
  rw [ordered_ustatistic_hoeffding_variance _ _ (split_kernel_symmetric α β u) hn]
  have hproj := split_projection_variance_bound m u hm α β
  have hcenter := split_centered_second_bound m u hm α β hα
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hden0 : (0 : ℝ) ≤ (n*(n-1) : ℕ) := by positivity
  have ha := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hproj (by norm_num : (0 : ℝ) ≤ 4)) hn0
  have hb := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcenter (by norm_num : (0 : ℝ) ≤ 2)) hden0
  convert add_le_add ha hb using 1
  ring

/-- Complete original `split_block_failure` guarantee for `SplitResidualRecords`; all source hypotheses and output obligations are retained. -/
theorem split_block_failure {n : ℕ} (m u : S → ℝ) (hm : ∀ x, |m x| ≤ 1)
    (α β U ε : ℝ) (hu : ∀ x, |u x| ≤ U) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hn : 2 ≤ n) (hε : 0 < ε)
    (hnB : 32*(α^2*(α+β*U)^2)/ε^2 ≤ (n : ℝ))
    (hnD : 8*Real.sqrt ((Fintype.card S : ℝ)*α^4)/ε ≤ (n : ℝ)) :
    (signedRecordLaw m hm).probEvent (fun ω : Fin n → S × Bool =>
      ε < |orderedUStatistic (splitKernel α β u) ω-
        (∑ x : S, (α*m x-β*u x)^2)/(Fintype.card S : ℝ)|) ≤ 3/16 := by
  apply product_block_failure _ _ _ (α^2*(α+β*U)^2) ((Fintype.card S : ℝ)*α^4)
    ε hn (by positivity) hε _ hnB hnD
  have hv := split_ustatistic_variance_bound m u hm α β hα hn
  rw [split_kernel_unbiased] at hv
  apply hv.trans
  have hb := mul_le_mul_of_nonneg_left (residual_mean_bound m u α β U hm hu hα hβ)
    (by positivity : (0 : ℝ) ≤ 4*α^2)
  have hd := div_le_div_of_nonneg_right hb (by positivity : (0 : ℝ) ≤ n)
  convert add_le_add_right hd (2*(Fintype.card S : ℝ)*α^4/(n*(n-1) : ℕ)) using 1 <;> ring

/-- Complete original `split_median_confidence` guarantee for `SplitResidualRecords`; all source hypotheses and output obligations are retained. -/
theorem split_median_confidence {n K : ℕ} (m u : S → ℝ) (hm : ∀ x, |m x| ≤ 1)
    (α β U ε ρ : ℝ) (hu : ∀ x, |u x| ≤ U) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hn : 2 ≤ n) (hε : 0 < ε)
    (hnB : 32*(α^2*(α+β*U)^2)/ε^2 ≤ (n : ℝ))
    (hnD : 8*Real.sqrt ((Fintype.card S : ℝ)*α^4)/ε ≤ (n : ℝ))
    (hK0 : 0 < K) (hρ : 0 < ρ) (hK : (128/25 : ℝ)*Real.log (1/ρ) ≤ (K : ℝ)) :
    (cohortLaw (signedRecordLaw m hm) n).probEvent (fun ω : Fin K → Fin n → S × Bool =>
      ε < |rawBlockMedian (orderedUStatistic (splitKernel α β u)) ω-
        (∑ x : S, (α*m x-β*u x)^2)/(Fintype.card S : ℝ)|) ≤ ρ := by
  apply finite_median_confidence _ _ _ _ ρ hK0 hρ
  · exact split_block_failure m u hm α β U ε hu hα hβ hn hε hnB hnD
  · exact hK

end
end Qatlib.Concepts.SpinorSampling.FiniteExecution.SplitResidual

#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.SplitResidual.centered_add_linear
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.SplitResidual.split_centered_target_free
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.SplitResidual.split_projection_variance_bound
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.SplitResidual.split_centered_second_bound
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.SplitResidual.split_ustatistic_variance_bound
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.SplitResidual.split_kernel_unbiased
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.SplitResidual.split_block_failure
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.SplitResidual.split_median_confidence
