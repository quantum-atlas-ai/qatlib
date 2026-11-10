/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchArith.TransposeAccess.FinDistTransport
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Qatlib.Concepts.SketchArith.SketchBuild
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

theorem finite_hoeffding_centered_mgf : ∀ (X : Type) [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X→ℝ) (a b t : ℝ), a≤b → (∀ x,f x∈Set.Icc a b) →
  p.expect (fun x => Real.exp (t*(f x-p.expect f))) ≤ Real.exp (t^2*(b-a)^2/8) := by
  intro X _ _ p f a b t hab hf
  letI : MeasurableSpace X := ⊤
  obtain ⟨μ,hμ⟩ := Qatlib.Concepts.SketchArith.TransposeAccess.FinDist.exists_pmf p
  have hi (g : X→ℝ) : (∫ x,g x ∂μ.toMeasure) = p.expect g := by
    rw [PMF.integral_eq_sum]
    simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect,hμ,ENNReal.toReal_ofReal (p.nonneg _),smul_eq_mul]
  have hs := hasSubgaussianMGF_of_mem_Icc
    (μ:=μ.toMeasure) (X:=f) (measurable_of_countable f).aemeasurable (ae_of_all _ hf)
  have hh := hs.mgf_le t
  simp only [mgf,hi] at hh
  convert hh using 1
  congr 1
  simp only [NNReal.coe_pow,NNReal.coe_div,NNReal.coe_ofNat,coe_nnnorm,
    Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)]
  ring

private theorem finite_product_expect_cons {X : Type} [Fintype X] [DecidableEq X]
    {n : ℕ} (p : Fin (n+1)→FinDist X) (f : (Fin (n+1)→X)→ℝ) :
    (independentSampleLaw p).expect f =
      (independentSampleLaw (fun i : Fin n => p i.succ)).expect
        (fun ω => (p 0).expect (fun x => f (Fin.cons x ω))) := by
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect independentSampleLaw
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => X)).sum_comp]
  simp only [Fintype.sum_prod_type,Fin.consEquiv_apply,Fin.prod_univ_succ,
    Fin.cons_zero,Fin.cons_succ]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  congr 1; funext ω
  apply Finset.sum_congr rfl
  intro x _
  dsimp [Fin.consEquiv]
  ring

private theorem finite_expect_abs_sub {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f g : X→ℝ) (c : ℝ) (h : ∀ x, |f x-g x|≤c) :
    |p.expect f-p.expect g|≤c := by
  calc
    _ = |∑ x,p.prob x*(f x-g x)| := by simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect,mul_sub,Finset.sum_sub_distrib]
    _ ≤ ∑ x,|p.prob x*(f x-g x)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x,p.prob x*|f x-g x| := by simp [abs_mul,abs_of_nonneg (p.nonneg _)]
    _ ≤ ∑ x,p.prob x*c := Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (p.nonneg x)
    _ = c := by rw [← Finset.sum_mul,p.sum_one,one_mul]

private theorem finite_diameter_mgf {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X→ℝ) (c t : ℝ) (hc : 0≤c)
    (hd : ∀ x y,|f x-f y|≤c) :
    p.expect (fun x=>Real.exp (t*(f x-p.expect f)))≤Real.exp (t^2*c^2/8) := by
  have hn : (Finset.univ : Finset X).Nonempty := by
    by_contra h
    have he : (Finset.univ : Finset X)=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hs := p.sum_one
    rw [he,Finset.sum_empty] at hs
    norm_num at hs
  obtain ⟨x0,_,hmin⟩ := Finset.exists_min_image Finset.univ f hn
  have hb : ∀ x,f x∈Set.Icc (f x0) (f x0+c) := by
    intro x
    refine ⟨hmin x (Finset.mem_univ x),?_⟩
    have hh := (le_abs_self (f x-f x0)).trans (hd x x0)
    linarith
  simpa only [add_sub_cancel_left] using
    finite_hoeffding_centered_mgf X p f (f x0) (f x0+c) t (by linarith) hb

theorem finite_product_bounded_differences_mgf {X : Type} [Fintype X] [DecidableEq X]
    (n : ℕ) (p : Fin n→FinDist X) (f : (Fin n→X)→ℝ) (c : Fin n→ℝ) (t : ℝ)
    (hc : ∀ i,0≤c i)
    (hd : ∀ i ω τ,(∀ j,j≠i→ω j=τ j)→|f ω-f τ|≤c i) :
    (independentSampleLaw p).expect (fun ω=>Real.exp (t*(f ω-(independentSampleLaw p).expect f)))≤
      Real.exp (t^2*(∑ i,(c i)^2)/8) := by
  induction n with
  | zero => simp [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect,independentSampleLaw]
  | succ n ih =>
    let q : Fin n→FinDist X := fun i=>p i.succ
    let g : (Fin n→X)→ℝ := fun ω=>(p 0).expect (fun x=>f (Fin.cons x ω))
    have hμ : (independentSampleLaw p).expect f = (independentSampleLaw q).expect g :=
      finite_product_expect_cons p f
    have hg : ∀ i ω τ,(∀ j,j≠i→ω j=τ j)→|g ω-g τ|≤c i.succ := by
      intro i ω τ hω
      apply finite_expect_abs_sub
      intro x
      apply hd i.succ (Fin.cons x ω) (Fin.cons x τ)
      intro j hj
      cases j using Fin.cases with
      | zero => rfl
      | succ j => exact hω j (fun h => hj (congrArg Fin.succ h))
    have hih := ih q g (fun i=>c i.succ) (fun i=>hc i.succ) hg
    have hcond (ω : Fin n→X) :
        (p 0).expect (fun x=>Real.exp (t*(f (Fin.cons x ω)-g ω)))≤Real.exp (t^2*(c 0)^2/8) := by
      apply finite_diameter_mgf _ _ _ _ (hc 0)
      intro x y
      apply hd 0 (Fin.cons x ω) (Fin.cons y ω)
      intro j hj
      cases j using Fin.cases with
      | zero => exact (hj rfl).elim
      | succ j => rfl
    rw [finite_product_expect_cons,hμ]
    have he (ω : Fin n→X) :
        (p 0).expect (fun x=>Real.exp (t*(f (Fin.cons x ω)-(independentSampleLaw q).expect g))) =
        Real.exp (t*(g ω-(independentSampleLaw q).expect g)) *
          (p 0).expect (fun x=>Real.exp (t*(f (Fin.cons x ω)-g ω))) := by
      unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      dsimp only
      have hx : Real.exp (t*(f (Fin.cons x ω)-(independentSampleLaw q).expect g)) =
          Real.exp (t*(g ω-(independentSampleLaw q).expect g)) *
            Real.exp (t*(f (Fin.cons x ω)-g ω)) := by
        rw [← Real.exp_add]; congr 1; ring
      simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect] at hx
      rw [hx]
      ring
    simp only [he]
    calc
      _ ≤ Real.exp (t^2*(c 0)^2/8) *
          (independentSampleLaw q).expect (fun ω=>Real.exp (t*(g ω-(independentSampleLaw q).expect g))) := by
        unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro ω _
        dsimp only
        have hh := mul_le_mul_of_nonneg_left (hcond ω)
          (mul_nonneg ((independentSampleLaw q).nonneg ω) (Real.exp_pos (t*(g ω-(independentSampleLaw q).expect g))).le)
        dsimp only [q,Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect] at hh ⊢
        convert hh using 1 <;> ring
      _ ≤ Real.exp (t^2*(c 0)^2/8) * Real.exp (t^2*(∑ i : Fin n,(c i.succ)^2)/8) :=
        mul_le_mul_of_nonneg_left hih (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add,Fin.sum_univ_succ]; congr 1; ring

private theorem finite_exp_markov {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X→ℝ) (μ u t : ℝ) (ht : 0≤t) :
    (∑ x ∈ Finset.univ.filter (fun x=>μ+u≤f x),p.prob x) ≤
      Real.exp (-t*u)*p.expect (fun x=>Real.exp (t*(f x-μ))) := by
  have hh : Real.exp (t*u)*(∑ x ∈ Finset.univ.filter (fun x=>μ+u≤f x),p.prob x) ≤
      p.expect (fun x=>Real.exp (t*(f x-μ))) := by
    calc
      _ = ∑ x ∈ Finset.univ.filter (fun x=>μ+u≤f x),p.prob x*Real.exp (t*u) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
      _ ≤ ∑ x ∈ Finset.univ.filter (fun x=>μ+u≤f x),p.prob x*Real.exp (t*(f x-μ)) := by
        apply Finset.sum_le_sum
        intro x hx
        apply mul_le_mul_of_nonneg_left _ (p.nonneg x)
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (by linarith [(Finset.mem_filter.mp hx).2]) ht
      _ ≤ p.expect (fun x=>Real.exp (t*(f x-μ))) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro x _ _; exact mul_nonneg (p.nonneg x) (Real.exp_pos _).le
  have hc := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-t*u)).le
  have he : Real.exp (-t*u)*Real.exp (t*u)=1 := by
    rw [← Real.exp_add,show -t*u+t*u=0 by ring,Real.exp_zero]
  simpa only [← mul_assoc,he,one_mul] using hc

private theorem finite_product_upper_tail {X : Type} [Fintype X] [DecidableEq X]
    (r : ℕ) (p : Fin r→FinDist X) (f : (Fin r→X)→ℝ) (c : Fin r→ℝ) (u : ℝ)
    (hc : ∀ i,0≤c i) (hS : 0<∑ i,(c i)^2) (hu : 0<u)
    (hd : ∀ i ω τ,(∀ j,j≠i→ω j=τ j)→|f ω-f τ|≤c i) :
    (∑ ω ∈ Finset.univ.filter (fun ω=>(independentSampleLaw p).expect f+u≤f ω),
      (independentSampleLaw p).prob ω) ≤ Real.exp (-2*u^2/(∑ i,(c i)^2)) := by
  let S := ∑ i,(c i)^2
  let t := 4*u/S
  have ht : 0≤t := by dsimp [t,S]; positivity
  have hmgf := finite_product_bounded_differences_mgf r p f c t hc hd
  calc
    _ ≤ Real.exp (-t*u)*(independentSampleLaw p).expect
        (fun ω=>Real.exp (t*(f ω-(independentSampleLaw p).expect f))) :=
      finite_exp_markov _ _ _ _ _ ht
    _ ≤ Real.exp (-t*u)*Real.exp (t^2*S/8) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      dsimp [t,S]
      field_simp [hS.ne']
      ring

theorem finite_product_bounded_differences_tail : ∀ (X : Type) [Fintype X] [DecidableEq X]
    (r : ℕ) (p : Fin r→FinDist X) (f : (Fin r→X)→ℝ) (c : Fin r→ℝ) (u : ℝ),
  (∀ i,0≤c i) → 0<∑ i,(c i)^2 → 0<u →
  (∀ i ω τ,(∀ j,j≠i→ω j=τ j)→|f ω-f τ|≤c i) →
  let μ:=(independentSampleLaw p).expect f;
  (∑ ω ∈ Finset.univ.filter (fun ω : Fin r→X=>μ+u≤f ω),(independentSampleLaw p).prob ω)≤
    Real.exp (-2*u^2/(∑ i,(c i)^2)) ∧
  (∑ ω ∈ Finset.univ.filter (fun ω : Fin r→X=>u≤|f ω-μ|),(independentSampleLaw p).prob ω)≤
    2*Real.exp (-2*u^2/(∑ i,(c i)^2)) := by
  intro X _ _ r p f c u hc hS hu hd
  dsimp only
  have hpos := finite_product_upper_tail r p f c u hc hS hu hd
  have hneg := finite_product_upper_tail r p (fun ω=>-f ω) c u hc hS hu (by
    intro i ω τ hω
    simpa only [neg_sub_neg,abs_sub_comm] using hd i ω τ hω)
  have hmean : (independentSampleLaw p).expect (fun ω=>-f ω) = -(independentSampleLaw p).expect f := by
    simp [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect,← Finset.sum_neg_distrib]
  rw [hmean] at hneg
  refine ⟨hpos,?_⟩
  have hm : (∑ ω ∈ Finset.univ.filter (fun ω : Fin r→X=>u≤|f ω-(independentSampleLaw p).expect f|),
        (independentSampleLaw p).prob ω) ≤
      (∑ ω ∈ Finset.univ.filter (fun ω=>(independentSampleLaw p).expect f+u≤f ω),
        (independentSampleLaw p).prob ω) +
      (∑ ω ∈ Finset.univ.filter (fun ω=>-(independentSampleLaw p).expect f+u≤-f ω),
        (independentSampleLaw p).prob ω) := by
    simp only [Finset.sum_filter,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ω _
    have hp := (independentSampleLaw p).nonneg ω
    split_ifs with ha hb hn <;> try linarith
    have he := abs_le.mpr (show -u≤f ω-(independentSampleLaw p).expect f ∧
        f ω-(independentSampleLaw p).expect f≤u by constructor <;> linarith)
    have hlt : |f ω-(independentSampleLaw p).expect f|<u := by
      apply abs_lt.mpr; constructor <;> linarith
    linarith
  linarith

theorem finite_avg_coordinate_difference {X : Type} (r : ℕ) (f : X→ℝ)
    (ω τ : Fin r→X) (i : Fin r) (h : ∀ j,j≠i→ω j=τ j) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg f ω-Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg f τ=(f (ω i)-f (τ i))/(r : ℝ) := by
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg
  rw [div_sub_div_same,← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_eq_single i
  · intro j _ hj; rw [h j hj,sub_self]
  · intro hi; exact (hi (Finset.mem_univ i)).elim

theorem finite_iid_bounded_average_tail {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X→ℝ) (r : ℕ) (B δ : ℝ)
    (hr : 0<r) (hB : 0<B) (hδ : 0<δ) (hδ1 : δ<1) (hf : ∀ x,f x∈Set.Icc 0 B) :
    p.probEvent (fun ω : Fin r→X=>Real.sqrt (B^2*Real.log (2/δ)/(2*(r : ℝ)))≤
      |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg f ω-p.expect f|)≤δ := by
  have hrp : 0<(r : ℝ) := Nat.cast_pos.mpr hr
  have hL : 0<Real.log (2/δ) := Real.log_pos (by apply (lt_div_iff₀ hδ).mpr; linarith)
  let u := Real.sqrt (B^2*Real.log (2/δ)/(2*(r : ℝ)))
  have huarg : 0<B^2*Real.log (2/δ)/(2*(r : ℝ)) := by positivity
  have hu : 0<u := Real.sqrt_pos.mpr huarg
  have hsum : (∑ i : Fin r,(B/(r : ℝ))^2)=B^2/(r : ℝ) := by
    simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin]
    field_simp
  have hdiff : ∀ i (ω τ : Fin r→X),(∀ j,j≠i→ω j=τ j)→
      |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg f ω-Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg f τ|≤B/(r : ℝ) := by
    intro i ω τ h
    rw [finite_avg_coordinate_difference r f ω τ i h,abs_div,abs_of_pos hrp]
    apply div_le_div_of_nonneg_right _ hrp.le
    apply abs_le.mpr
    constructor <;> linarith [(hf (ω i)).1,(hf (ω i)).2,(hf (τ i)).1,(hf (τ i)).2]
  have ht := (finite_product_bounded_differences_tail X r (fun _=>p) (Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg f)
    (fun _=>B/(r : ℝ)) u (fun _=>by positivity) (by rw [hsum]; positivity) hu hdiff).2
  have hm : (independentSampleLaw (fun _ : Fin r=>p)).expect (Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg f)=p.expect f :=
    p.expect_avg f hr
  rw [hm] at ht
  change p.probEvent
      (fun ω : Fin r→X=>u≤|Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg f ω-p.expect f|)≤_ at ht
  refine ht.trans ?_
  rw [hsum]
  have he : -2*u^2/(B^2/(r : ℝ)) = -Real.log (2/δ) := by
    dsimp [u]
    rw [Real.sq_sqrt huarg.le]
    field_simp [hB.ne',hrp.ne']
  rw [he,Real.exp_neg,Real.exp_log (by positivity : 0<(2/δ))]
  field_simp
  norm_num

end Qatlib.Concepts.SketchArith.SketchBuild
