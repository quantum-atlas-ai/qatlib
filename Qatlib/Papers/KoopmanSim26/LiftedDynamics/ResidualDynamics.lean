/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.TimeOrdered.TimeOrderedConsumers
import Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false

namespace Qatlib.Papers.KoopmanSim26.LiftedDynamics.Calculus

theorem lifted_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type} [Fintype I] (x : ℝ → E) (f : E → E) (g : E → QState I)
    (Dg : E → E →L[ℝ] QState I) (t : ℝ)
    (hx : HasDerivAt x (f (x t)) t) (hg : HasFDerivAt g (Dg (x t)) (x t)) :
    HasDerivAt (fun s => g (x s)) (Dg (x t) (f (x t))) t :=
  hg.comp_hasDerivAt t hx

def liftResidual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type} [Fintype I] (A : Matrix I I ℂ) (x : ℝ → E) (f : E → E)
    (g : E → QState I) (Dg : E → E →L[ℝ] QState I) (t : ℝ) : QState I :=
  Dg (x t) (f (x t))-A *ᵥ g (x t)

theorem ordered_const_exp {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (s t : ℝ) :
    orderedEvolution (fun _ => -A) s t=NormedSpace.exp ((t-s) • A) := by
  let V : ℝ → Matrix I I ℂ := fun u => NormedSpace.exp ((u-s) • A)
  have hd (u : ℝ) : HasDerivAt V (A * V u) u := by
    have h := (hasDerivAt_exp_smul_const' (𝕂:=ℝ) A (u-s)).scomp u ((hasDerivAt_id u).sub_const s)
    simpa only [V,one_smul] using! h
  have he := ordered_matrix_ode_unique (fun _ => -A) continuous_const V
    (orderedEvolution (fun _ => -A) s) s (by simp [V])
    (fun u => by simpa only [Matrix.neg_mul,neg_neg] using! hd u)
    (orderedEvolution_hasDerivAt _ continuous_const s)
  exact (congrFun he t).symm

theorem lifted_eq_forced {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (x : ℝ → E) (f : E → E) (g : E → QState I) (Dg : E → E →L[ℝ] QState I)
    (hx : ∀ t,HasDerivAt x (f (x t)) t)
    (hg : ∀ t,HasFDerivAt g (Dg (x t)) (x t))
    (hr : Continuous (liftResidual A x f g Dg)) :
    (fun t => g (x t))=orderedForcedSolution (fun _ => -A) (liftResidual A x f g Dg) 0 (g (x 0)) := by
  apply orderedForcedSolution_unique _ _ continuous_const hr _ _ _ rfl
  intro t
  have hd := lifted_hasDerivAt x f g Dg t (hx t) (hg t)
  convert! hd using 1
  simp only [liftResidual,Matrix.neg_mulVec,neg_neg]
  abel

theorem lifted_residual_duhamel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (x : ℝ → E) (f : E → E) (g : E → QState I) (Dg : E → E →L[ℝ] QState I)
    (hx : ∀ t,HasDerivAt x (f (x t)) t)
    (hg : ∀ t,HasFDerivAt g (Dg (x t)) (x t))
    (hr : Continuous (liftResidual A x f g Dg)) (t : ℝ) :
    g (x t)-NormedSpace.exp (t • A) *ᵥ g (x 0) =
      ∫ s in 0..t,NormedSpace.exp ((t-s) • A) *ᵥ liftResidual A x f g Dg s := by
  have he := congrFun (lifted_eq_forced A x f g Dg hx hg hr) t
  simp only [orderedForcedSolution,ordered_const_exp,sub_zero] at he
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using! he)

theorem exact_lifted_closure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (x : ℝ → E) (f : E → E) (g : E → QState I) (Dg : E → E →L[ℝ] QState I)
    (hx : ∀ t,HasDerivAt x (f (x t)) t)
    (hg : ∀ t,HasFDerivAt g (Dg (x t)) (x t))
    (hclosure : ∀ t,Dg (x t) (f (x t))=A *ᵥ g (x t)) (t : ℝ) :
    g (x t)=NormedSpace.exp (t • A) *ᵥ g (x 0) := by
  have hr : liftResidual A x f g Dg=(fun _ => 0) := by
    funext s
    exact sub_eq_zero.mpr (hclosure s)
  have hc : Continuous (liftResidual A x f g Dg) := by rw [hr];fun_prop
  have he := lifted_residual_duhamel A x f g Dg hx hg hc t
  simp only [hr,Matrix.mulVec_zero,intervalIntegral.integral_zero] at he
  exact sub_eq_zero.mp he

theorem lifted_error_eq_zero_forced {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (x : ℝ → E) (f : E → E) (g : E → QState I) (Dg : E → E →L[ℝ] QState I)
    (hx : ∀ t,HasDerivAt x (f (x t)) t)
    (hg : ∀ t,HasFDerivAt g (Dg (x t)) (x t))
    (hr : Continuous (liftResidual A x f g Dg)) (t : ℝ) :
    g (x t)-NormedSpace.exp (t • A) *ᵥ g (x 0) =
      orderedForcedSolution (fun _ => -A) (liftResidual A x f g Dg) 0 0 t := by
  rw [lifted_residual_duhamel A x f g Dg hx hg hr t]
  simp only [orderedForcedSolution,ordered_const_exp,sub_zero,Matrix.mulVec_zero,zero_add]

theorem lifted_residual_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (hA : ((-A)+(-A).conjTranspose).PosSemidef)
    (x : ℝ → E) (f : E → E) (g : E → QState I) (Dg : E → E →L[ℝ] QState I)
    (hx : ∀ t,HasDerivAt x (f (x t)) t)
    (hg : ∀ t,HasFDerivAt g (Dg (x t)) (x t))
    (hr : Continuous (liftResidual A x f g Dg)) (t : ℝ) (ht : 0 ≤ t) :
    ‖toEuclidean_fromVec (g (x t)-NormedSpace.exp (t • A) *ᵥ g (x 0))‖ ≤
      ∫ s in 0..t,‖toEuclidean_fromVec (liftResidual A x f g Dg s)‖ := by
  rw [lifted_error_eq_zero_forced A x f g Dg hx hg hr t]
  have he := orderedForcedSolution_norm_le (fun _ => -A) (liftResidual A x f g Dg)
    continuous_const hr (fun _ => hA) 0 t ht 0
  have hz : toEuclidean_fromVec (0:QState I)=0 := rfl
  simpa only [hz,norm_zero,zero_add] using! he

theorem matrix_vector_deriv {I : Type} [Fintype I] [DecidableEq I]
    {M : ℝ → Matrix I I ℂ} {u : ℝ → QState I} {M' : Matrix I I ℂ} {u' : QState I} {t : ℝ}
    (hM : HasDerivAt M M' t) (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => M s *ᵥ u s) (M' *ᵥ u t+M t *ᵥ u') t := by
  apply hasDerivAt_pi.mpr
  intro i
  have hm (j : I) := hasDerivAt_pi.mp (hasDerivAt_pi.mp hM i) j
  have hv (j : I) := hasDerivAt_pi.mp hu j
  simpa only [Matrix.mulVec,dotProduct,Finset.sum_add_distrib] using!
    HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) => (hm j).mul (hv j))

theorem lifted_residual_duhamel_on_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (x : ℝ → E) (f : E → E) (g : E → QState I) (Dg : E → E →L[ℝ] QState I)
    (T : ℝ) (hT : 0 ≤ T)
    (hx : ∀ s ∈ Set.Icc 0 T,HasDerivAt x (f (x s)) s)
    (hg : ∀ s ∈ Set.Icc 0 T,HasFDerivAt g (Dg (x s)) (x s))
    (hr : ContinuousOn (liftResidual A x f g Dg) (Set.Icc 0 T)) :
    g (x T)-NormedSpace.exp (T • A) *ᵥ g (x 0) =
      ∫ s in 0..T,NormedSpace.exp ((T-s) • A) *ᵥ liftResidual A x f g Dg s := by
  let M : ℝ → Matrix I I ℂ := fun s => NormedSpace.exp ((T-s) • A)
  have hdM (s : ℝ) : HasDerivAt M (M s * (-A)) s := by
    have h := (hasDerivAt_exp_smul_const (𝕂:=ℝ) A (T-s)).scomp s
      ((hasDerivAt_const (x:=s) T).sub (hasDerivAt_id s))
    simpa only [M,zero_sub,neg_one_smul,Matrix.mul_neg] using! h
  have hcM : Continuous M := continuous_iff_continuousAt.mpr (fun s => (hdM s).continuousAt)
  have hprod : ContinuousOn (fun s => M s *ᵥ liftResidual A x f g Dg s) (Set.Icc 0 T) := by
    rw [continuousOn_iff_continuous_restrict]
    exact (hcM.comp continuous_subtype_val).matrix_mulVec
        (continuousOn_iff_continuous_restrict.mp hr)
  have hint : IntervalIntegrable (fun s => M s *ᵥ liftResidual A x f g Dg s) volume 0 T :=
    hprod.intervalIntegrable_of_Icc hT
  have hd (s : ℝ) (hs : s ∈ Set.Icc 0 T) :
      HasDerivAt (fun u => M u *ᵥ g (x u)) (M s *ᵥ liftResidual A x f g Dg s) s := by
    have h := matrix_vector_deriv (hdM s) (lifted_hasDerivAt x f g Dg s (hx s hs) (hg s hs))
    convert! h using 1
    simp only [liftResidual,Matrix.mulVec_sub,Matrix.mulVec_mulVec,Matrix.mul_neg,Matrix.neg_mulVec]
    abel
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by simpa only [Set.uIcc_of_le hT] using! hs)) hint
  simpa only [M,sub_self,zero_smul,NormedSpace.exp_zero,Matrix.one_mulVec,sub_zero] using! hi.symm

theorem exact_lifted_closure_on_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (x : ℝ → E) (f : E → E) (g : E → QState I) (Dg : E → E →L[ℝ] QState I)
    (T : ℝ) (hT : 0 ≤ T)
    (hx : ∀ s ∈ Set.Icc 0 T,HasDerivAt x (f (x s)) s)
    (hg : ∀ s ∈ Set.Icc 0 T,HasFDerivAt g (Dg (x s)) (x s))
    (hclose : ∀ s ∈ Set.Icc 0 T,Dg (x s) (f (x s))=A *ᵥ g (x s)) :
    g (x T)=NormedSpace.exp (T • A) *ᵥ g (x 0) := by
  have hz (s : ℝ) (hs : s ∈ Set.Icc 0 T) : liftResidual A x f g Dg s=0 :=
    sub_eq_zero.mpr (hclose s hs)
  have hr : ContinuousOn (liftResidual A x f g Dg) (Set.Icc 0 T) :=
    continuousOn_const.congr (fun s hs => hz s hs)
  have he := lifted_residual_duhamel_on_interval A x f g Dg T hT hx hg hr
  have hi : (∫ s in 0..T,NormedSpace.exp ((T-s) • A) *ᵥ liftResidual A x f g Dg s)=0 := by
    calc
      _ = ∫ s in 0..T,(0:QState I) := by
        apply intervalIntegral.integral_congr
        intro s hs
        change NormedSpace.exp ((T-s) • A) *ᵥ liftResidual A x f g Dg s = 0
        rw [hz s (by simpa only [Set.uIcc_of_le hT] using! hs),Matrix.mulVec_zero]
      _ = 0 := intervalIntegral.integral_zero
  rw [hi] at he
  exact sub_eq_zero.mp he

theorem dissipative_exp_norm {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (hA : ((-A)+(-A).conjTranspose).PosSemidef) (t : ℝ) (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • A)‖ ≤ 1 := by
  have h := Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.norm_evolution_le_one
    (-A) hA ht
  simpa only [Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution,
    smul_neg,neg_smul,neg_neg] using! h

theorem lifted_residual_norm_bound_on_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (hA : ((-A)+(-A).conjTranspose).PosSemidef)
    (x : ℝ → E) (f : E → E) (g : E → QState I) (Dg : E → E →L[ℝ] QState I)
    (T : ℝ) (hT : 0 ≤ T)
    (hx : ∀ s ∈ Set.Icc 0 T,HasDerivAt x (f (x s)) s)
    (hg : ∀ s ∈ Set.Icc 0 T,HasFDerivAt g (Dg (x s)) (x s))
    (hr : ContinuousOn (liftResidual A x f g Dg) (Set.Icc 0 T)) :
    ‖toEuclidean_fromVec (g (x T)-NormedSpace.exp (T • A) *ᵥ g (x 0))‖ ≤
      ∫ s in 0..T,‖toEuclidean_fromVec (liftResidual A x f g Dg s)‖ := by
  let M : ℝ → Matrix I I ℂ := fun s => NormedSpace.exp ((T-s) • A)
  have hcM : Continuous M := by
    apply continuous_iff_continuousAt.mpr
    intro s
    have h := (hasDerivAt_exp_smul_const (𝕂:=ℝ) A (T-s)).scomp s
      ((hasDerivAt_const (x:=s) T).sub (hasDerivAt_id s))
    exact h.continuousAt
  have hprod : ContinuousOn (fun s => M s *ᵥ liftResidual A x f g Dg s) (Set.Icc 0 T) := by
    rw [continuousOn_iff_continuous_restrict]
    exact (hcM.comp continuous_subtype_val).matrix_mulVec
        (continuousOn_iff_continuous_restrict.mp hr)
  have hint : IntervalIntegrable (fun s => M s *ᵥ liftResidual A x f g Dg s) volume 0 T :=
    hprod.intervalIntegrable_of_Icc hT
  let e : QState I →L[ℝ] EuclideanSpace ℂ I :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => ℂ)).symm.toContinuousLinearMap.restrictScalars ℝ
  rw [lifted_residual_duhamel_on_interval A x f g Dg T hT hx hg hr]
  change ‖e (∫ s in 0..T,M s *ᵥ liftResidual A x f g Dg s)‖ ≤
    ∫ s in 0..T,‖e (liftResidual A x f g Dg s)‖
  rw [← e.intervalIntegral_comp_comm hint]
  apply intervalIntegral.norm_integral_le_of_norm_le hT
  · apply Filter.Eventually.of_forall
    intro s hs
    have hn := dissipative_exp_norm A hA (T-s) (sub_nonneg.mpr hs.2)
    exact (Matrix.l2_opNorm_mulVec (M s) (e (liftResidual A x f g Dg s))).trans
      ((mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans_eq (one_mul _))
  · exact (e.continuous.comp_continuousOn hr).norm.intervalIntegrable_of_Icc hT

end Qatlib.Papers.KoopmanSim26.LiftedDynamics.Calculus
