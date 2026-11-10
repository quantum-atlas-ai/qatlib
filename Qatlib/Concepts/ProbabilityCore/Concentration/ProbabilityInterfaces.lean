/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.CubeQueryInterfaces
import Qatlib.Concepts.ProbabilityCore.Concentration.GaussianSmallBall
import Qatlib.Concepts.ProbabilityCore.Concentration.NumericSampling
import Qatlib.Concepts.SketchSpectral.SketchAnalysis.SketchOperatorConcentration
import Qatlib.Concepts.BosonFock.PermAnalysis.GaussianComparison
import Mathlib.MeasureTheory.Integral.Pi
import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfacesDefs
import Qatlib.Concepts.SketchArith.SketchBuild.FiniteBoundedDifferences
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SketchArith.TransposeAccess.FinDist
open Qatlib.Concepts.SketchSpectral.SketchAnalysis
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BosonFock.PermAnalysis
open Qatlib.Concepts.ProbabilityCore.DistributionAA
open Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
noncomputable section
universe u v w

namespace Qatlib.Concepts.ProbabilityCore.Concentration

@[ext] theorem FinDist.ext {X : Type*} [Fintype X] {p q : FinDist X}
    (h : ∀ x, p.prob x = q.prob x) : p = q := by
  cases p
  cases q
  congr
  exact funext h

end Qatlib.Concepts.ProbabilityCore.Concentration

namespace Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces

open MeasureTheory
open scoped BigOperators

theorem toPMF_unique {X : Type*} [Fintype X] (p : FinDist X) (μ : PMF X)
    (hμ : ∀ x, μ x = ENNReal.ofReal (p.prob x)) : toPMF p = μ := by
  ext x
  exact (hμ x).symm

@[simp] theorem ofPMF_toPMF_prob {X : Type*} [Fintype X] (p : FinDist X) (x : X) :
    (ofPMF (toPMF p)).prob x = p.prob x :=
  ENNReal.toReal_ofReal (p.nonneg x)

@[simp] theorem toPMF_ofPMF {X : Type*} [Fintype X] (p : PMF X) :
    toPMF (ofPMF p) = p := by
  ext x
  exact ENNReal.ofReal_toReal (p.apply_ne_top x)

theorem integral_eq_expect {X : Type*} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : FinDist X) (f : X → ℝ) :
    ∫ x, f x ∂(toPMF p).toMeasure = p.expect f := by
  rw [PMF.integral_eq_sum]
  simp only [toPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal (p.nonneg _),
    smul_eq_mul, FinDist.expect]

theorem integral_central_moment {X : Type*} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : FinDist X) (f : X → ℝ) (k : ℕ) :
    ∫ x, (f x - p.expect f) ^ k ∂(toPMF p).toMeasure =
      p.expect (fun x => (f x - p.expect f) ^ k) := integral_eq_expect _ _

theorem integral_variance {X : Type*} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : FinDist X) (f : X → ℝ) :
    ∫ x, (f x - p.expect f) ^ 2 ∂(toPMF p).toMeasure = p.variance f :=
  integral_central_moment p f 2

theorem independent_expect_product {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (f : ∀ i, X i → ℝ) :
    (independent p).expect (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (p i).expect (f i) := by
  simp only [FinDist.expect, independent, ← Finset.prod_mul_distrib]
  simpa only [Fintype.piFinset_univ] using!
    (Finset.prod_univ_sum (t := fun i => (Finset.univ : Finset (X i)))
      (f := fun i x => (p i).prob x * f i x)).symm

theorem independent_fin_eq_sampleLaw {n : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (p : Fin n → FinDist X) : independent p = independentSampleLaw p := rfl

theorem independent_toMeasure {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (p : ∀ i, FinDist (X i)) :
    (toPMF (independent p)).toMeasure = Measure.pi (fun i => (toPMF (p i)).toMeasure) := by
  apply Measure.ext_of_singleton
  intro ω
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), Measure.pi_singleton]
  simp only [toPMF, PMF.ofFintype_apply, independent,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact ENNReal.ofReal_prod_of_nonneg fun i _ => (p i).nonneg _

theorem independent_coordinates {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (p : ∀ i, FinDist (X i)) :
    ProbabilityTheory.iIndepFun (fun i (ω : ∀ i, X i) => ω i) (toPMF (independent p)).toMeasure := by
  rw [independent_toMeasure]
  exact ProbabilityTheory.iIndepFun_pi (fun _ => measurable_id.aemeasurable)

theorem eventMass_nonneg {X : Type*} [Fintype X] (p : FinDist X)
    (E : X → Prop) [DecidablePred E] : 0 ≤ eventMass p E :=
  Finset.sum_nonneg fun x _ => p.nonneg x

theorem eventMass_mono {X : Type*} [Fintype X] (p : FinDist X)
    (E F : X → Prop) [DecidablePred E] [DecidablePred F] (h : ∀ x, E x → F x) :
    eventMass p E ≤ eventMass p F := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h x (Finset.mem_filter.mp hx).2⟩
  · intro x _ _
    exact p.nonneg x

theorem chebyshev {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) (ε : ℝ) (hε : 0 < ε) :
    eventMass p (fun x => ε ≤ |f x-p.expect f|) ≤ p.variance f / ε^2 := by
  classical
  have hp : 0 < ε^2 := by positivity
  calc
    _ ≤ ∑ x with ε ≤ |f x-p.expect f|, p.prob x*(f x-p.expect f)^2/ε^2 := by
      apply Finset.sum_le_sum
      intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      have he : ε^2 ≤ (f x-p.expect f)^2 := by
        nlinarith [abs_nonneg (f x-p.expect f), sq_abs (f x-p.expect f)]
      apply (le_div_iff₀ hp).mpr
      exact mul_le_mul_of_nonneg_left he (p.nonneg x)
    _ = (∑ x with ε ≤ |f x-p.expect f|, p.prob x*(f x-p.expect f)^2)/ε^2 :=
      (Finset.sum_div _ _ _).symm
    _ ≤ p.variance f/ε^2 := by
      apply div_le_div_of_nonneg_right _ hp.le
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun x _ _ => mul_nonneg (p.nonneg x) (sq_nonneg _))

theorem chebyshev_strict {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) (ε : ℝ) (hε : 0 < ε) :
    eventMass p (fun x => ε < |f x-p.expect f|) ≤ p.variance f / ε^2 :=
  (eventMass_mono p _ _ (fun _ h => h.le)).trans (chebyshev p f ε hε)

theorem relabel_expect {X : Type*} {Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (e : X ≃ Y) (p : FinDist X) (f : Y → ℝ) :
    (relabel e p).expect f = p.expect (fun x => f (e x)) := by
  simpa only [FinDist.expect, relabel, Equiv.symm_apply_apply] using!
    (Equiv.sum_comp e (fun y => p.prob (e.symm y) * f y)).symm

theorem hoeffding_centered_mgf {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) (a b t : ℝ) (hab : a ≤ b)
    (hf : ∀ x, f x ∈ Set.Icc a b) :
    p.expect (fun x => Real.exp (t*(f x-p.expect f))) ≤ Real.exp (t^2*(b-a)^2/8) := by
  classical
  let e := Fintype.equivFin X
  let q := relabel e p
  let g := fun j => f (e.symm j)
  have hmean : q.expect g = p.expect f := by
    simp only [q, g, relabel_expect, Equiv.symm_apply_apply]
  have h := finite_hoeffding_centered_mgf (Fin (Fintype.card X)) q g a b t hab
    (fun j => hf (e.symm j))
  rw [hmean] at h
  simpa only [q, g, relabel_expect, Equiv.symm_apply_apply] using! h

theorem chernoff_upper {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) (a t : ℝ) (ht : 0 ≤ t) :
    eventMass p (fun x => a ≤ f x) ≤
      Real.exp (-(t*a)) * p.expect (fun x => Real.exp (t*f x)) := by
  classical
  have h : eventMass p (fun x => a ≤ f x) * Real.exp (t*a) ≤
      p.expect (fun x => Real.exp (t*f x)) := by
    calc
      _ = ∑ x with a ≤ f x, p.prob x * Real.exp (t*a) := Finset.sum_mul _ _ _
      _ ≤ ∑ x with a ≤ f x, p.prob x * Real.exp (t*f x) := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hx).2 ht)) (p.nonneg x)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun x _ _ => mul_nonneg (p.nonneg x) (Real.exp_pos _).le)
  have hb := (le_div_iff₀ (Real.exp_pos (t*a))).mpr h
  simpa only [Real.exp_neg, div_eq_mul_inv, mul_comm] using! hb

theorem eventMass_toMeasure {X : Type*} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : FinDist X)
    (E : X → Prop) [DecidablePred E] :
    (toPMF p).toMeasure {x | E x} = ENNReal.ofReal (eventMass p E) := by
  have he : {x | E x} = (Finset.univ.filter E : Set X) := by ext x; simp
  rw [he, PMF.toMeasure_apply_finset]
  simp only [toPMF, PMF.ofFintype_apply]
  exact (ENNReal.ofReal_sum_of_nonneg (fun x _ => p.nonneg x)).symm

theorem variance_eq_mathlib {X : Type*} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : FinDist X) (f : X → ℝ) :
    ProbabilityTheory.variance f (toPMF p).toMeasure = p.variance f := by
  rw [ProbabilityTheory.variance_eq_integral (measurable_of_countable f).aemeasurable,
    integral_eq_expect p f, integral_variance]

theorem independent_expect_coord {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (i : I) (f : X i → ℝ) :
    (independent p).expect (fun ω => f (ω i)) = (p i).expect f := by
  letI : ∀ i, MeasurableSpace (X i) := fun _ => ⊤
  rw [← integral_eq_expect, independent_toMeasure, ← integral_eq_expect]
  exact MeasureTheory.integral_comp_eval (measurable_of_countable f).aestronglyMeasurable

theorem independent_weighted_variance {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (w : I → ℝ) (f : ∀ i, X i → ℝ) :
    (independent p).variance (weightedSum w f) = ∑ i, (w i)^2 * (p i).variance (f i) := by
  letI : ∀ i, MeasurableSpace (X i) := fun _ => ⊤
  rw [← variance_eq_mathlib, independent_toMeasure]
  have h := ProbabilityTheory.variance_sum_pi
    (μ := fun i => (toPMF (p i)).toMeasure) (X := fun i x => w i * f i x)
    (fun _ => MeasureTheory.MemLp.of_discrete)
  rw [show weightedSum w f = ∑ i : I, (fun ω : ∀ i, X i => w i * f i (ω i)) from by
    funext ω; simp only [weightedSum, Finset.sum_apply]]
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  rw [ProbabilityTheory.variance_const_mul, variance_eq_mathlib]

theorem expect_sum {I : Type*} {X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : I → X → ℝ) :
    p.expect (fun x => ∑ i, f i x) = ∑ i, p.expect (f i) := by
  simp only [FinDist.expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_const_mul {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (c : ℝ) (f : X → ℝ) :
    p.expect (fun x => c * f x) = c * p.expect f := by
  simp only [FinDist.expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem independent_weighted_expectation {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (w : I → ℝ) (f : ∀ i, X i → ℝ) :
    (independent p).expect (weightedSum w f) = ∑ i, w i * (p i).expect (f i) := by
  rw [show weightedSum w f = (fun ω : ∀ i, X i => ∑ i, w i * f i (ω i)) from rfl, expect_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [expect_const_mul, independent_expect_coord]

theorem independent_weighted_chebyshev {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (w : I → ℝ) (f : ∀ i, X i → ℝ) (ε : ℝ) (hε : 0 < ε) :
    eventMass (independent p) (fun ω => ε ≤ |weightedSum w f ω-∑ i, w i*(p i).expect (f i)|) ≤
      (∑ i, (w i)^2 * (p i).variance (f i)) / ε^2 := by
  have h := chebyshev (independent p) (weightedSum w f) ε hε
  rwa [independent_weighted_expectation, independent_weighted_variance] at h

theorem independent_weighted_mgf {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (w : I → ℝ) (f : ∀ i, X i → ℝ)
    (a b : I → ℝ) (t : ℝ) (hab : ∀ i, a i ≤ b i) (hf : ∀ i x, f i x ∈ Set.Icc (a i) (b i)) :
    (independent p).expect (fun ω => Real.exp (t*(weightedSum w f ω-
      (independent p).expect (weightedSum w f)))) ≤
      Real.exp (t^2*(∑ i, (w i)^2*(b i-a i)^2)/8) := by
  rw [independent_weighted_expectation]
  have hfactor (ω : ∀ i, X i) :
      Real.exp (t*(weightedSum w f ω-∑ i, w i*(p i).expect (f i))) =
        ∏ i, Real.exp ((t*w i)*(f i (ω i)-(p i).expect (f i))) := by
    rw [← Real.exp_sum]
    congr 1
    unfold weightedSum
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc
    _ = (independent p).expect (fun ω => ∏ i,
        Real.exp ((t*w i)*(f i (ω i)-(p i).expect (f i)))) :=
      congrArg (FinDist.expect (independent p)) (funext hfactor)
    _ = ∏ i, (p i).expect (fun x => Real.exp ((t*w i)*(f i x-(p i).expect (f i)))) :=
      independent_expect_product p (fun i x => Real.exp ((t*w i)*(f i x-(p i).expect (f i))))
    _ ≤ ∏ i, Real.exp ((t*w i)^2*(b i-a i)^2/8) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.sum_nonneg fun x _ => mul_nonneg ((p i).nonneg x) (Real.exp_pos _).le
      · intro i _
        exact hoeffding_centered_mgf (p i) (f i) (a i) (b i) (t*w i) (hab i) (hf i)
    _ = Real.exp (t^2*(∑ i, (w i)^2*(b i-a i)^2)/8) := by
      rw [← Real.exp_sum]
      congr 1
      calc
        _ = ∑ i, (t^2/8)*((w i)^2*(b i-a i)^2) := Finset.sum_congr rfl fun _ _ => by ring
        _ = (t^2/8)*(∑ i, (w i)^2*(b i-a i)^2) := (Finset.mul_sum _ _ _).symm
        _ = _ := by ring

theorem eventMass_or_le {X : Type*} [Fintype X] (p : FinDist X)
    (E F : X → Prop) [DecidablePred E] [DecidablePred F] :
    eventMass p (fun x => E x ∨ F x) ≤ eventMass p E + eventMass p F := by
  simp only [eventMass, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases he : E x <;> by_cases hf : F x <;> simp [he, hf]
  linarith [p.nonneg x]

theorem independent_weighted_hoeffding_signed {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (w : I → ℝ) (f : ∀ i, X i → ℝ)
    (a b : I → ℝ) (u σ : ℝ) (hab : ∀ i, a i ≤ b i)
    (hf : ∀ i x, f i x ∈ Set.Icc (a i) (b i)) (hu : 0 < u) (hσ : σ^2 = 1)
    (hS : 0 < ∑ i, (w i)^2*(b i-a i)^2) :
    eventMass (independent p) (fun ω => u ≤ σ*(weightedSum w f ω-
      (independent p).expect (weightedSum w f))) ≤
      Real.exp (-2*u^2/(∑ i, (w i)^2*(b i-a i)^2)) := by
  classical
  let S := ∑ i, (w i)^2*(b i-a i)^2
  let t := 4*u/S
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hch := chernoff_upper (independent p)
    (fun ω => σ*(weightedSum w f ω-(independent p).expect (weightedSum w f))) u t ht
  have hmg : (independent p).expect (fun ω => Real.exp
      (t*(σ*(weightedSum w f ω-(independent p).expect (weightedSum w f))))) ≤
        Real.exp (t^2*S/8) := by
    calc
      _ = (independent p).expect (fun ω => Real.exp
          ((t*σ)*(weightedSum w f ω-(independent p).expect (weightedSum w f)))) := by
        simp only [mul_assoc]
      _ ≤ Real.exp ((t*σ)^2*S/8) := independent_weighted_mgf p w f a b (t*σ) hab hf
      _ = Real.exp (t^2*S/8) := by rw [mul_pow, hσ, mul_one]
  calc
    _ ≤ Real.exp (-(t*u))*Real.exp (t^2*S/8) :=
      hch.trans (mul_le_mul_of_nonneg_left hmg (Real.exp_pos _).le)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [t, S]
      field_simp [hS.ne']
      ring

theorem independent_weighted_hoeffding {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (w : I → ℝ) (f : ∀ i, X i → ℝ)
    (a b : I → ℝ) (u : ℝ) (hab : ∀ i, a i ≤ b i)
    (hf : ∀ i x, f i x ∈ Set.Icc (a i) (b i)) (hu : 0 < u)
    (hS : 0 < ∑ i, (w i)^2*(b i-a i)^2) :
    eventMass (independent p) (fun ω => u ≤ |weightedSum w f ω-
      (independent p).expect (weightedSum w f)|) ≤
      2*Real.exp (-2*u^2/(∑ i, (w i)^2*(b i-a i)^2)) := by
  classical
  have hpos := independent_weighted_hoeffding_signed p w f a b u 1 hab hf hu (by norm_num) hS
  have hneg := independent_weighted_hoeffding_signed p w f a b u (-1) hab hf hu (by norm_num) hS
  simp only [one_mul] at hpos
  simp only [neg_one_mul] at hneg
  have he : (fun ω => u ≤ |weightedSum w f ω-(independent p).expect (weightedSum w f)|) =
      (fun ω => (u ≤ weightedSum w f ω-(independent p).expect (weightedSum w f)) ∨
        (u ≤ -(weightedSum w f ω-(independent p).expect (weightedSum w f)))) := by
    funext ω
    exact propext (by rw [abs_eq_max_neg, le_max_iff])
  have hbound : eventMass (independent p) (fun ω =>
      (u ≤ weightedSum w f ω-(independent p).expect (weightedSum w f)) ∨
      (u ≤ -(weightedSum w f ω-(independent p).expect (weightedSum w f)))) ≤
      2*Real.exp (-2*u^2/(∑ i, (w i)^2*(b i-a i)^2)) :=
    (eventMass_or_le _ _ _).trans (by linarith)
  simpa only [he] using! hbound

theorem expect_const {X : Type*} [Fintype X] [DecidableEq X] (p : FinDist X) (c : ℝ) :
    p.expect (fun _ => c) = c := by
  rw [FinDist.expect, ← Finset.sum_mul, p.sum_one, one_mul]

theorem independent_weighted_zero_width {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (w : I → ℝ) (f : ∀ i, X i → ℝ)
    (a b : I → ℝ) (u : ℝ) (hf : ∀ i x, f i x ∈ Set.Icc (a i) (b i)) (hu : 0 < u)
    (hS : (∑ i, (w i)^2*(b i-a i)^2) = 0) :
    eventMass (independent p) (fun ω => u ≤ |weightedSum w f ω-
      (independent p).expect (weightedSum w f)|) = 0 := by
  classical
  have hterm (i : I) : (w i)^2*(b i-a i)^2 = 0 :=
    ((Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (sq_nonneg (w j)) (sq_nonneg (b j-a j)))).mp hS) i (Finset.mem_univ i)
  have hc (i : I) (x : X i) : w i*f i x = w i*(p i).expect (f i) := by
    by_cases hw : w i = 0
    · simp [hw]
    · have hba : b i = a i := sub_eq_zero.mp (sq_eq_zero_iff.mp
        ((mul_eq_zero.mp (hterm i)).resolve_left (pow_ne_zero 2 hw)))
      have hconst (y : X i) : f i y = a i :=
        le_antisymm (by simpa only [hba] using! (hf i y).2) (hf i y).1
      have hm : (p i).expect (f i) = a i := by
        rw [show f i = (fun _ => a i) from funext hconst, expect_const]
      rw [hconst x, hm]
  have hpoint (ω : ∀ i, X i) : weightedSum w f ω = (independent p).expect (weightedSum w f) := by
    rw [independent_weighted_expectation]
    exact Finset.sum_congr rfl fun i _ => hc i (ω i)
  simp [eventMass, hpoint, not_le_of_gt hu]

theorem relabel_eventMass {X : Type*} {Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (e : X ≃ Y) (p : FinDist X)
    (E : Y → Prop) [DecidablePred E] :
    eventMass (relabel e p) E = eventMass p (fun x => E (e x)) := by
  simp only [eventMass, Finset.sum_filter, relabel]
  simpa only [Equiv.symm_apply_apply] using!
    (Equiv.sum_comp e (fun y => if E y then p.prob (e.symm y) else 0)).symm

theorem independent_relabel {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} {Y : I → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (p : ∀ i, FinDist (X i)) (e : ∀ i, X i ≃ Y i) :
    relabel (Equiv.piCongrRight e) (independent p) = independent (fun i => relabel (e i) (p i)) := by
  apply FinDist.ext
  intro ω
  rfl

theorem bounded_differences_tail {X : Type} [Fintype X] [DecidableEq X]
    (n : ℕ) (p : Fin n → FinDist X) (f : (Fin n → X) → ℝ) (c : Fin n → ℝ) (u : ℝ)
    (hc : ∀ i, 0 ≤ c i) (hS : 0 < ∑ i, (c i)^2) (hu : 0 < u)
    (hd : ∀ i ω τ, (∀ j, j ≠ i → ω j = τ j) → |f ω-f τ| ≤ c i) :
    eventMass (independent p) (fun ω => u ≤ |f ω-(independent p).expect f|) ≤
      2*Real.exp (-2*u^2/(∑ i, (c i)^2)) :=
  (finite_product_bounded_differences_tail X n p f c u hc hS hu hd).2

theorem median_of_means {X : Type*} [Fintype X] [DecidableEq X] (p : FinDist X) (f : X → ℝ)
    (L M : ℕ) (hL : 0 < L) (hM : 0 < M) (ε : ℝ) (hε : 0 < ε)
    (hvar : 4*p.variance f ≤ (L : ℝ)*ε^2) :
    eventMass (independent (fun _ : Fin M => independent (fun _ : Fin L => p)))
      (fun ω => ε < |p.medianOfMeans f ω-p.expect f|) ≤ 3^(M/2)/2^M :=
  p.median_of_means_concentration f hL hM ε hε hvar

theorem part6_clause1 :
  (∀ {X : Type u} [Fintype X] (p : FinDist X) (μ : PMF X)
    (_hμ : ∀ x, μ x = ENNReal.ofReal (p.prob x)),
    toPMF p = μ) ∧
  (∀ {X : Type u} [Fintype X] (p : FinDist X) (x : X),
    (ofPMF (toPMF p)).prob x = p.prob x) ∧
  (∀ {X : Type u} [Fintype X] (p : PMF X),
    toPMF (ofPMF p) = p) ∧
  (∀ {X : Type u} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : FinDist X) (f : X → ℝ),
    ∫ x, f x ∂(toPMF p).toMeasure = p.expect f) ∧
  (∀ {X : Type u} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : FinDist X) (f : X → ℝ) (k : ℕ),
    ∫ x, (f x - p.expect f) ^ k ∂(toPMF p).toMeasure =
      p.expect (fun x => (f x - p.expect f) ^ k)) ∧
  (∀ {X : Type u} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : FinDist X) (f : X → ℝ),
    ∫ x, (f x - p.expect f) ^ 2 ∂(toPMF p).toMeasure = p.variance f) ∧
  (∀ {X : Type u} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : FinDist X) (f : X → ℝ),
    ProbabilityTheory.variance f (toPMF p).toMeasure = p.variance f) ∧
  (∀ {X : Type u} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : FinDist X)
    (E : X → Prop) [DecidablePred E],
    (toPMF p).toMeasure {x | E x} = ENNReal.ofReal (eventMass p E)) ∧
  (∀ {I : Type v} [Fintype I] [DecidableEq I]
    {X : I → Type u} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (f : ∀ i, X i → ℝ),
    (independent p).expect (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (p i).expect (f i)) ∧
  (∀ {n : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (p : Fin n → FinDist X),
    independent p = independentSampleLaw p) ∧
  (∀ {I : Type v} [Fintype I] [DecidableEq I]
    {X : I → Type u} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (p : ∀ i, FinDist (X i)),
    (toPMF (independent p)).toMeasure = Measure.pi (fun i => (toPMF (p i)).toMeasure)) ∧
  (∀ {I : Type v} [Fintype I] [DecidableEq I]
    {X : I → Type u} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (p : ∀ i, FinDist (X i)),
    ProbabilityTheory.iIndepFun (fun i (ω : ∀ i, X i) => ω i) (toPMF (independent p)).toMeasure) ∧
  (∀ {X : Type u} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) (ε : ℝ) (_hε : 0 < ε),
    eventMass p (fun x => ε ≤ |f x-p.expect f|) ≤ p.variance f / ε^2) ∧
  (∀ {X : Type u} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) (ε : ℝ) (_hε : 0 < ε),
    eventMass p (fun x => ε < |f x-p.expect f|) ≤ p.variance f / ε^2) ∧
  (∀ {X : Type u} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) (a b t : ℝ) (_hab : a ≤ b)
    (_hf : ∀ x, f x ∈ Set.Icc a b),
    p.expect (fun x => Real.exp (t*(f x-p.expect f))) ≤ Real.exp (t^2*(b-a)^2/8)) ∧
  (∀ {X : Type u} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) (a t : ℝ) (_ht : 0 ≤ t),
    eventMass p (fun x => a ≤ f x) ≤
      Real.exp (-(t*a)) * p.expect (fun x => Real.exp (t*f x))) ∧
  (∀ {X : Type u} {Y : Type w} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (e : X ≃ Y) (p : FinDist X) (f : Y → ℝ),
    (relabel e p).expect f = p.expect (fun x => f (e x))) ∧
  (∀ {X : Type u} {Y : Type w} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (e : X ≃ Y) (p : FinDist X)
    (E : Y → Prop) [DecidablePred E],
    eventMass (relabel e p) E = eventMass p (fun x => E (e x))) ∧
  (∀ {I : Type v} [Fintype I] [DecidableEq I]
    {X : I → Type u} {Y : I → Type u} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (p : ∀ i, FinDist (X i)) (e : ∀ i, X i ≃ Y i),
    relabel (Equiv.piCongrRight e) (independent p) = independent (fun i => relabel (e i) (p i))) ∧
  (∀ {I : Type v} [Fintype I] [DecidableEq I]
    {X : I → Type u} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (i : I) (f : X i → ℝ),
    (independent p).expect (fun ω => f (ω i)) = (p i).expect f) ∧
  (∀ {I : Type v} [Fintype I] [DecidableEq I]
    {X : I → Type u} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (w : I → ℝ) (f : ∀ i, X i → ℝ),
    (independent p).expect (weightedSum w f) = ∑ i, w i * (p i).expect (f i)) ∧
  (∀ {I : Type v} [Fintype I] [DecidableEq I]
    {X : I → Type u} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (w : I → ℝ) (f : ∀ i, X i → ℝ),
    (independent p).variance (weightedSum w f) = ∑ i, (w i)^2 * (p i).variance (f i)) ∧
  (∀ {I : Type v} [Fintype I] [DecidableEq I]
    {X : I → Type u} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (w : I → ℝ) (f : ∀ i, X i → ℝ) (ε : ℝ) (_hε : 0 < ε),
    eventMass (independent p) (fun ω => ε ≤ |weightedSum w f ω-∑ i, w i*(p i).expect (f i)|) ≤
      (∑ i, (w i)^2 * (p i).variance (f i)) / ε^2) ∧
  (∀ {I : Type v} [Fintype I] [DecidableEq I]
    {X : I → Type u} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (w : I → ℝ) (f : ∀ i, X i → ℝ)
    (a b : I → ℝ) (t : ℝ) (_hab : ∀ i, a i ≤ b i) (_hf : ∀ i x, f i x ∈ Set.Icc (a i) (b i)),
    (independent p).expect (fun ω => Real.exp (t*(weightedSum w f ω-
      (independent p).expect (weightedSum w f)))) ≤
      Real.exp (t^2*(∑ i, (w i)^2*(b i-a i)^2)/8)) ∧
  (∀ {I : Type v} [Fintype I] [DecidableEq I]
    {X : I → Type u} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (w : I → ℝ) (f : ∀ i, X i → ℝ)
    (a b : I → ℝ) (u σ : ℝ) (_hab : ∀ i, a i ≤ b i)
    (_hf : ∀ i x, f i x ∈ Set.Icc (a i) (b i)) (_hu : 0 < u) (_hσ : σ^2 = 1)
    (_hS : 0 < ∑ i, (w i)^2*(b i-a i)^2),
    eventMass (independent p) (fun ω => u ≤ σ*(weightedSum w f ω-
      (independent p).expect (weightedSum w f))) ≤
      Real.exp (-2*u^2/(∑ i, (w i)^2*(b i-a i)^2))) ∧
  (∀ {I : Type v} [Fintype I] [DecidableEq I]
    {X : I → Type u} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (w : I → ℝ) (f : ∀ i, X i → ℝ)
    (a b : I → ℝ) (u : ℝ) (_hab : ∀ i, a i ≤ b i)
    (_hf : ∀ i x, f i x ∈ Set.Icc (a i) (b i)) (_hu : 0 < u)
    (_hS : 0 < ∑ i, (w i)^2*(b i-a i)^2),
    eventMass (independent p) (fun ω => u ≤ |weightedSum w f ω-
      (independent p).expect (weightedSum w f)|) ≤
      2*Real.exp (-2*u^2/(∑ i, (w i)^2*(b i-a i)^2))) ∧
  (∀ {I : Type v} [Fintype I] [DecidableEq I]
    {X : I → Type u} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (w : I → ℝ) (f : ∀ i, X i → ℝ)
    (a b : I → ℝ) (u : ℝ) (_hf : ∀ i x, f i x ∈ Set.Icc (a i) (b i)) (_hu : 0 < u)
    (_hS : (∑ i, (w i)^2*(b i-a i)^2) = 0),
    eventMass (independent p) (fun ω => u ≤ |weightedSum w f ω-
      (independent p).expect (weightedSum w f)|) = 0) ∧
  (∀ {X : Type} [Fintype X] [DecidableEq X]
    (n : ℕ) (p : Fin n → FinDist X) (f : (Fin n → X) → ℝ) (c : Fin n → ℝ) (u : ℝ)
    (_hc : ∀ i, 0 ≤ c i) (_hS : 0 < ∑ i, (c i)^2) (_hu : 0 < u)
    (_hd : ∀ i ω τ, (∀ j, j ≠ i → ω j = τ j) → |f ω-f τ| ≤ c i),
    eventMass (independent p) (fun ω => u ≤ |f ω-(independent p).expect f|) ≤
      2*Real.exp (-2*u^2/(∑ i, (c i)^2))) ∧
  (∀ {X : Type u} [Fintype X] [DecidableEq X] (p : FinDist X) (f : X → ℝ)
    (L M : ℕ) (_hL : 0 < L) (_hM : 0 < M) (ε : ℝ) (_hε : 0 < ε)
    (_hvar : 4*p.variance f ≤ (L : ℝ)*ε^2),
    eventMass (independent (fun _ : Fin M => independent (fun _ : Fin L => p)))
      (fun ω => ε < |p.medianOfMeans f ω-p.expect f|) ≤ 3^(M/2)/2^M) := by
  exact ⟨toPMF_unique,
    ofPMF_toPMF_prob,
    toPMF_ofPMF,
    integral_eq_expect,
    integral_central_moment,
    integral_variance,
    variance_eq_mathlib,
    eventMass_toMeasure,
    independent_expect_product,
    independent_fin_eq_sampleLaw,
    independent_toMeasure,
    independent_coordinates,
    chebyshev,
    chebyshev_strict,
    hoeffding_centered_mgf,
    chernoff_upper,
    relabel_expect,
    relabel_eventMass,
    independent_relabel,
    independent_expect_coord,
    independent_weighted_expectation,
    independent_weighted_variance,
    independent_weighted_chebyshev,
    independent_weighted_mgf,
    independent_weighted_hoeffding_signed,
    independent_weighted_hoeffding,
    independent_weighted_zero_width,
    bounded_differences_tail,
    median_of_means⟩

section MatrixTransport
open Matrix
open scoped Classical Matrix.Norms.L2Operator

variable {K K' C C' : Type}

theorem sketch_row_reindex [Fintype C] [Fintype C']
    (e : K ≃ K') (f : C ≃ C') (A : Matrix K C ℂ) (k : K') :
    sketchRowSquared (Matrix.reindex e f A) k = sketchRowSquared A (e.symm k) := by
  unfold sketchRowSquared
  exact f.symm.sum_comp (fun j : C => Complex.normSq (A (e.symm k) j))

theorem sketch_energy_reindex [Fintype K] [Fintype K'] [Fintype C] [Fintype C']
    (e : K ≃ K') (f : C ≃ C') (A : Matrix K C ℂ) :
    sketchSquared (Matrix.reindex e f A) = sketchSquared A := by
  unfold sketchSquared
  simp only [sketch_row_reindex]
  exact e.symm.sum_comp (fun k : K => sketchRowSquared A k)

theorem sketch_gram_reindex [Fintype K] [Fintype K']
    (e : K ≃ K') (f : C ≃ C') (A : Matrix K C ℂ) :
    (Matrix.reindex e f A)ᴴ * Matrix.reindex e f A = relabelGate f (Aᴴ * A) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, relabelGate]
  exact e.symm.sum_comp (fun k : K => (starRingEnd ℂ) (A k (f.symm i)) * A k (f.symm j))

theorem sketch_rectangular_norm_reindex [Fintype K] [Fintype K'] [Fintype C] [DecidableEq C] [Fintype C'] [DecidableEq C']
    (e : K ≃ K') (f : C ≃ C') (A : Matrix K C ℂ) :
    ‖Matrix.reindex e f A‖ = ‖A‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [pow_two, pow_two, ← Matrix.l2_opNorm_conjTranspose_mul_self,
    ← Matrix.l2_opNorm_conjTranspose_mul_self, sketch_gram_reindex, l2_norm_relabelGate]

theorem sketch_product_reindex [Fintype K] [Fintype K']
    (e : K ≃ K') (f : C ≃ C') (p : FinDist K)
    (A : Matrix K C ℂ) (r : ℕ) (ω : Fin r → K) :
    sketchProduct (relabel e p) r (Matrix.reindex e f A) (Matrix.reindex e f A)
      (fun t => e (ω t)) = relabelGate f (sketchProduct p r A A ω) := by
  ext i j
  change sketchProduct _ r _ _ _ i j = sketchProduct p r A A ω (f.symm i) (f.symm j)
  simp only [sketchProduct_entry_average, sketchSampleMatrix, relabel,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem sketch_record_law_reindex [Fintype K] [Fintype K']
    (e : K ≃ K') (p : FinDist K) (r : ℕ) :
    independent (fun _ : Fin r => relabel e p) =
      relabel (Equiv.piCongrRight (fun _ : Fin r => e)) (independent (fun _ : Fin r => p)) :=
  (independent_relabel _ _).symm

theorem sketch_bad_mass_reindex [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K'] [Fintype C] [DecidableEq C] [Fintype C'] [DecidableEq C']
    (e : K ≃ K') (f : C ≃ C') (p : FinDist K)
    (A : Matrix K C ℂ) (r : ℕ) (η : ℝ) :
    compactGramOperatorBadMass (relabel e p) r (Matrix.reindex e f A) η =
      compactGramOperatorBadMass p r A η := by
  change eventMass (independent (fun _ : Fin r => relabel e p))
    (fun ω => η < ‖sketchProduct (relabel e p) r (Matrix.reindex e f A)
      (Matrix.reindex e f A) ω - (Matrix.reindex e f A)ᴴ * Matrix.reindex e f A‖) =
    eventMass (independent (fun _ : Fin r => p))
      (fun ω => η < ‖sketchProduct p r A A ω - Aᴴ * A‖)
  rw [sketch_record_law_reindex, relabel_eventMass]
  congr 1
  funext ω
  change (η < ‖sketchProduct (relabel e p) r (Matrix.reindex e f A)
    (Matrix.reindex e f A) (fun t => e (ω t)) - (Matrix.reindex e f A)ᴴ * Matrix.reindex e f A‖) = _
  rw [sketch_product_reindex, sketch_gram_reindex, l2_norm_relabelGate_sub]

theorem sketch_rank_dimension_reindex [Fintype K] [Fintype K'] [Fintype C] [Fintype C']
    (e : K ≃ K') (f : C ≃ C') (A : Matrix K C ℂ) :
    (Matrix.reindex e f A).rank = A.rank ∧ Fintype.card K' = Fintype.card K ∧
      Fintype.card C' = Fintype.card C :=
  ⟨Matrix.rank_reindex e f A, (Fintype.card_congr e).symm, (Fintype.card_congr f).symm⟩

theorem matrix_unitary_coordinates [Fintype C] [DecidableEq C]
    (U A B : Matrix C C ℂ)
    (hU : U ∈ Matrix.unitaryGroup C ℂ) :
    ‖U * A * Uᴴ - U * B * Uᴴ‖ = ‖A-B‖ ∧ (U * A * Uᴴ).rank = A.rank := by
  have hu : Uᴴ ∈ Matrix.unitaryGroup C ℂ := by
    simpa only [Matrix.star_eq_conjTranspose] using! Unitary.star_mem hU
  have he : U * A * Uᴴ - U * B * Uᴴ = U * (A-B) * Uᴴ := by noncomm_ring
  constructor
  · rw [he, CStarRing.norm_mul_mem_unitary _ hu, CStarRing.norm_mem_unitary_mul _ hU]
  · rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _
      (Matrix.isUnit_det_of_left_inverse (by simpa only [Matrix.star_eq_conjTranspose] using! hU.2)),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _
      (Matrix.isUnit_det_of_left_inverse (by simpa only [Matrix.star_eq_conjTranspose] using! hU.1))]

end MatrixTransport

open scoped Matrix.Norms.L2Operator
open Matrix

theorem rounded_sketch_operator_tail :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (K C : Type) [Fintype K] [DecidableEq K]
      [Fintype C] [DecidableEq C] (law : FinDist K) (r bits : ℕ)
      (A : Matrix K C ℂ) (φ η δ : ℝ),
      2 ≤ r → 1 ≤ φ → 0 < η → η ≤ ‖A‖^2 → 0 < δ → δ < 1 →
      (∀ k, sketchRowSquared A k/(φ*sketchSquared A) ≤ law.prob k) →
      c₀*φ^2*sketchSquared A*‖A‖^2*Real.log (r : ℝ)*Real.log (4/δ) ≤ (r : ℝ)*η^2 →
      eventMass (independent (fun _ : Fin r => law))
        (fun ω => η+dyadicOpBudget C bits <
          ‖dyadicRoundMatrix bits (sketchProduct law r A A ω)-Aᴴ*A‖) ≤ δ := by
  obtain ⟨c₀, hc₀, htail⟩ := compact_sketch_operator_tail_nontrivial
  refine ⟨c₀, hc₀, ?_⟩
  intro K C _ _ _ _ law r bits A φ η δ hr hφ hη hηS hδ hδ1 hdom hb
  have hn := dyadic_sample_tail (independent (fun _ : Fin r => law))
    (sketchProduct law r A A) (Aᴴ*A) bits η
  exact hn.trans (htail K C law r A φ η δ hr hφ hη hηS hδ hδ1 hdom hb)

open scoped InnerProductSpace ComplexOrder

theorem part7_clause1 :
  (∀ {C : Type} [Fintype C] [DecidableEq C] {r : ℕ}
    (B : Fin r → Matrix C C ℂ) (q : ℕ) (_hq : 1 ≤ q) (_hB : ∀ i, (B i).IsHermitian),
    (2 : ℝ)^(-(r:ℤ))*(∑ s,(Matrix.trace (sketchSignMatrix B s^(2*q))).re) ≤
      ((2*q-1 : ℕ):ℝ)^q*(Matrix.trace ((∑ i,B i*B i)^q)).re) ∧
  (∀ {C : Type} [Fintype C] [DecidableEq C] (V : Matrix C C ℂ)
    (_hV : V.PosSemidef) (q : ℕ) (_hq : 0 < q),
    (Matrix.trace (V^q)).re ≤ (V.rank : ℝ)*‖V‖^q) ∧
  (∀ {C : Type} [Fintype C] [DecidableEq C] {r : ℕ}
    (a : Fin r → ℂ) (u v : Fin r → C → ℂ),
    (∑ i,a i • Matrix.vecMulVec (u i) (v i)).rank ≤ r) ∧
  (∀ {C : Type} [Fintype C] [DecidableEq C] {r : ℕ}
    (y : Fin r → C → ℂ),
    (∑ i,(Matrix.vecMulVec (y i) (star (y i)))^2).rank ≤ r) ∧
  (∀ {C : Type} [Fintype C] [DecidableEq C] {r : ℕ}
    (y : Fin r → C → ℂ) (R : ℝ) (_hR : 0 ≤ R)
    (_hy : ∀ i,‖toEuclidean_fromVec (y i)‖ ≤ R) (p : ℕ) (_hp : 1 ≤ p) (_hr : 2 ≤ r),
    (2:ℝ)^(-(r:ℤ))*(∑ s,‖(r:ℝ)⁻¹ • sketchSignMatrix
      (fun i=>Matrix.vecMulVec (y i) (star (y i))) s‖^p) ≤
    (4*Real.sqrt ((p:ℝ)+Real.log (r:ℝ))*R/(r:ℝ))^p*
      (Real.sqrt ‖∑ i,Matrix.vecMulVec (y i) (star (y i))‖)^p) ∧
  (∀ {K C : Type} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    (law : FinDist K) (y : K → C → ℂ) (R : ℝ) (r p : ℕ)
    (_hr : 2 ≤ r) (_hp : 1 ≤ p) (_hR : 0 ≤ R)
    (_hy : ∀ k,‖toEuclidean_fromVec (y k)‖ ≤ R)
    (_hmean : ‖∑ k,law.prob k • Matrix.vecMulVec (y k) (star (y k))‖ ≤ 1),
    (independentSampleLaw (fun _ : Fin r=>law)).expect (fun ω=>
      min ‖(r:ℝ)⁻¹ • (∑ i,Matrix.vecMulVec (y (ω i)) (star (y (ω i))))-
        (∑ k,law.prob k • Matrix.vecMulVec (y k) (star (y k)))‖ 1 ^p) ≤
      (128*R*Real.sqrt (Real.log (r:ℝ)/(r:ℝ))*Real.sqrt (p:ℝ))^p) ∧
  (∃ c₀ : ℝ,0<c₀ ∧ ∀ (K C : Type) [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
      (law : FinDist K) (r : ℕ) (A : Matrix K C ℂ) (φ η δ : ℝ),
      2≤r → 1≤φ → 0<η → η≤‖A‖^2 → 0<δ → δ<1 →
      (∀ k,sketchRowSquared A k/(φ*sketchSquared A)≤law.prob k) →
      c₀*φ^2*sketchSquared A*‖A‖^2*Real.log (r:ℝ)*Real.log (4/δ)≤(r:ℝ)*η^2 →
      compactGramOperatorBadMass law r A η≤δ) ∧
  (∀ (K C : Type) [Fintype K] [DecidableEq K]
    [Fintype C] [DecidableEq C] (p : FinDist K) (r : ℕ) (η : ℝ), 0 ≤ η →
    compactGramOperatorBadMass p r (0 : Matrix K C ℂ) η = 0) ∧
  (∀ {K : Type} [Fintype K] (p : FinDist K) (r : ℕ) (ω : Fin r→K),
    compactSketchBuild p r ω = (List.ofFn (compactSketchData p r ω),r,r)) ∧
  (∀ {K C D : Type} {r : ℕ} (d : Fin r→K×ℝ)
    (X : Matrix K C ℂ) (Y : Matrix K D ℂ) (i : C) (j : D),
    compactProductEntry d X Y i j =
      (∑ t : Fin r,star ((compactSketchEntry d X t i).1)*(compactSketchEntry d Y t j).1,2*r)) ∧
  (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →L[ℝ] E) (L : F →L[ℝ] E) (a b : F),
    0 < (gaussianBilinearCF T L a 0).re ∧
      0 < (gaussianBilinearCF T L 0 b).re ∧
        0 < (gaussianBilinearCF T L 0 0).re ∧
          ∀ t : ℝ, gaussianBilinearCF T L (t • a) 0 =
            gaussianBilinearCF T L 0 0 *
              (gaussianBilinearCF T L a 0 / gaussianBilinearCF T L 0 0) ^ ((t ^ 2 : ℝ) : ℂ) ∧
            ∀ t : ℝ, gaussianBilinearCF T L 0 (t • b) =
              gaussianBilinearCF T L 0 0 *
                (gaussianBilinearCF T L 0 b / gaussianBilinearCF T L 0 0) ^ ((t ^ 2 : ℝ) : ℂ)) ∧
  (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →L[ℝ] E) (L : F →L[ℝ] E) (a b : F)
    (θ : ℝ) (_hθ₁ : 0 ≤ θ) (_hθ₂ : θ ≤ 1),
    ‖gaussianBilinearCF T L (Real.sqrt θ • a) (Real.sqrt (1 - θ) • b)‖ =
      (gaussianBilinearCF T L a 0).re ^ θ * (gaussianBilinearCF T L 0 b).re ^ (1 - θ)) ∧
  (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F] (Ω : Type w) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (T : Ω → (E →L[ℝ] E)) (L : Ω → (F →L[ℝ] E)) (_hT : Measurable T) (_hL : Measurable L)
    (a b : F) (θ : ℝ) (_hθ₁ : 0 ≤ θ) (_hθ₂ : θ ≤ 1),
    (∫ ω, ‖gaussianBilinearCF (T ω) (L ω)
        (Real.sqrt θ • a) (Real.sqrt (1 - θ) • b)‖ ∂ν ≤
      (∫ ω, (gaussianBilinearCF (T ω) (L ω) a 0).re ∂ν) ^ θ *
        (∫ ω, (gaussianBilinearCF (T ω) (L ω) 0 b).re ∂ν) ^ (1 - θ)) ∧
      ((∫ ω, (gaussianBilinearCF (T ω) (L ω) a 0).re ∂ν) ^ θ *
        (∫ ω, (gaussianBilinearCF (T ω) (L ω) 0 b).re ∂ν) ^ (1 - θ) ≤
        max (∫ ω, (gaussianBilinearCF (T ω) (L ω) a 0).re ∂ν)
          (∫ ω, (gaussianBilinearCF (T ω) (L ω) 0 b).re ∂ν))) ∧
  (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μX μY : Measure E) [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    (_h : ∀ t : E, (charFun μX t).re ≤ (charFun μY t).re),
    matrixLaplaceLE μY μX) ∧
  (∀ (bits : ℕ) (a b : ℚ),
    dyadicEncode bits ((a : ℂ) + (b : ℂ)*Complex.I) = dyadicEncodeRat bits (a,b)) ∧
  (∀ (bits : ℕ) (x : ℝ),
    |(⌊(2 : ℝ)^bits*x⌋ : ℝ)/(2 : ℝ)^bits-x| ≤ 1/(2 : ℝ)^bits) ∧
  (∀ (bits : ℕ) (z : ℂ),
    ‖dyadicRoundComplex bits z-z‖ ≤ 2/(2 : ℝ)^bits) ∧
  (∀ {I : Type} [Fintype I] [DecidableEq I]
    (bits : ℕ) (A : Matrix I I ℂ),
    ‖dyadicRoundMatrix bits A-A‖ ≤ dyadicOpBudget I bits) ∧
  (∀ {X : Type u} [Fintype X] {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist X) (A : X → Matrix I I ℂ) (T : Matrix I I ℂ) (bits : ℕ) (η : ℝ),
    eventMass p (fun ω => η+dyadicOpBudget I bits < ‖dyadicRoundMatrix bits (A ω)-T‖) ≤
      eventMass p (fun ω => η < ‖A ω-T‖)) ∧
  (∀ {I J : Type u} (e : I ≃ J) (bits : ℕ) (A : Matrix I I ℂ),
    dyadicRoundMatrix bits (Matrix.reindex e e A) =
      Matrix.reindex e e (dyadicRoundMatrix bits A)) ∧
  (∀ (K K' C C' : Type) [Fintype C] [Fintype C']
    (e : K ≃ K') (f : C ≃ C') (A : Matrix K C ℂ) (k : K'),
    sketchRowSquared (Matrix.reindex e f A) k = sketchRowSquared A (e.symm k)) ∧
  (∀ (K K' C C' : Type) [Fintype K] [Fintype K'] [Fintype C] [Fintype C']
    (e : K ≃ K') (f : C ≃ C') (A : Matrix K C ℂ),
    sketchSquared (Matrix.reindex e f A) = sketchSquared A) ∧
  (∀ (K K' C C' : Type) [Fintype K] [Fintype K']
    (e : K ≃ K') (f : C ≃ C') (A : Matrix K C ℂ),
    (Matrix.reindex e f A)ᴴ * Matrix.reindex e f A = relabelGate f (Aᴴ * A)) ∧
  (∀ (K K' C C' : Type) [Fintype K] [Fintype K'] [Fintype C] [DecidableEq C] [Fintype C'] [DecidableEq C']
    (e : K ≃ K') (f : C ≃ C') (A : Matrix K C ℂ),
    ‖Matrix.reindex e f A‖ = ‖A‖) ∧
  (∀ (K K' C C' : Type) [Fintype K] [Fintype K']
    (e : K ≃ K') (f : C ≃ C') (p : FinDist K)
    (A : Matrix K C ℂ) (r : ℕ) (ω : Fin r → K),
    sketchProduct (relabel e p) r (Matrix.reindex e f A) (Matrix.reindex e f A)
      (fun t => e (ω t)) = relabelGate f (sketchProduct p r A A ω)) ∧
  (∀ (K K' C C' : Type) [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K'] [Fintype C] [DecidableEq C] [Fintype C'] [DecidableEq C']
    (e : K ≃ K') (f : C ≃ C') (p : FinDist K)
    (A : Matrix K C ℂ) (r : ℕ) (η : ℝ),
    compactGramOperatorBadMass (relabel e p) r (Matrix.reindex e f A) η =
      compactGramOperatorBadMass p r A η) ∧
  (∀ (K K' C C' : Type) [Fintype K] [Fintype K'] [Fintype C] [Fintype C']
    (e : K ≃ K') (f : C ≃ C') (A : Matrix K C ℂ),
    (Matrix.reindex e f A).rank = A.rank ∧ Fintype.card K' = Fintype.card K ∧
      Fintype.card C' = Fintype.card C) ∧
  (∀ (K K' : Type) [Fintype K] [Fintype K']
    (e : K ≃ K') (p : FinDist K) (r : ℕ),
    independent (fun _ : Fin r => relabel e p) =
      relabel (Equiv.piCongrRight (fun _ : Fin r => e)) (independent (fun _ : Fin r => p))) ∧
  (∀ (C : Type) [Fintype C] [DecidableEq C]
    (U A B : Matrix C C ℂ)
    (_hU : U ∈ Matrix.unitaryGroup C ℂ),
    ‖U * A * Uᴴ - U * B * Uᴴ‖ = ‖A-B‖ ∧ (U * A * Uᴴ).rank = A.rank) ∧
  (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (K C : Type) [Fintype K] [DecidableEq K]
      [Fintype C] [DecidableEq C] (law : FinDist K) (r bits : ℕ)
      (A : Matrix K C ℂ) (φ η δ : ℝ),
      2 ≤ r → 1 ≤ φ → 0 < η → η ≤ ‖A‖^2 → 0 < δ → δ < 1 →
      (∀ k, sketchRowSquared A k/(φ*sketchSquared A) ≤ law.prob k) →
      c₀*φ^2*sketchSquared A*‖A‖^2*Real.log (r : ℝ)*Real.log (4/δ) ≤ (r : ℝ)*η^2 →
      eventMass (independent (fun _ : Fin r => law))
        (fun ω => η+dyadicOpBudget C bits <
          ‖dyadicRoundMatrix bits (sketchProduct law r A A ω)-Aᴴ*A‖) ≤ δ) := by
  exact ⟨sketchSign_trace_moment,
    sketch_psd_trace_power_rank_bound,
    sketch_weighted_outer_sum_rank,
    sketch_covariance_variance_rank,
    sketch_covariance_rademacher_average_moment,
    sketch_covariance_truncated_moment,
    compact_sketch_operator_tail_nontrivial,
    compactGramOperatorBadMass_zero,
    compactSketchBuild_eq,
    compactProductEntry_eq,
    (by intro E _ _ _ _ _ F _ _; exact gaussianCF_oneSidedQuadraticScaling),
    (by intro E _ _ _ _ _ F _ _; exact gaussianCF_geometricInterpolation),
    (by intro E _ _ _ _ _ F _ _ Ω _; exact gaussianCF_twoCoordinateCompression),
    (by intro E _ _ _ _ _; exact fourier_to_laplace),
    dyadicEncode_rat,
    dyadic_scalar_error,
    dyadic_complex_error,
    dyadic_matrix_error,
    dyadic_sample_tail,
    dyadic_reindex,
    (by intro K K' C C' _ _; exact sketch_row_reindex),
    (by intro K K' C C' _ _ _ _; exact sketch_energy_reindex),
    (by intro K K' C C' _ _; exact sketch_gram_reindex),
    (by intro K K' C C' _ _ _ _ _ _; exact sketch_rectangular_norm_reindex),
    (by intro K K' C C' _ _; exact sketch_product_reindex),
    (by intro K K' C C' _ _ _ _ _ _ _ _; exact sketch_bad_mass_reindex),
    (by intro K K' C C' _ _ _ _; exact sketch_rank_dimension_reindex),
    (by intro K K' _ _; exact sketch_record_law_reindex),
    (by intro C _ _; exact matrix_unitary_coordinates),
    rounded_sketch_operator_tail⟩

theorem cubeLaw_integral (n : ℕ) (w : (Fin n → Bool) → ℝ) (hw : CubeWeight n w)
    [MeasurableSpace (Fin n → Bool)] [MeasurableSingletonClass (Fin n → Bool)]
    (f : (Fin n → Bool) → ℝ) :
    (∫ x, f x ∂(toPMF (cubeLaw n w hw)).toMeasure) = cubeExpect n w f := by
  rw [integral_eq_expect, cubeLaw_expect]

theorem tree_law_relabel {n : ℕ} (e : Equiv.Perm (Fin n)) (t : FiniteDecisionTree n)
    (q : FinDist (Fin n → Bool)) :
    (relabel (Equiv.arrowCongr e (Equiv.refl Bool)) q).expect (t.relabel e).accept =
      q.expect t.accept ∧
    (relabel (Equiv.arrowCongr e (Equiv.refl Bool)) q).expect
      (fun x => ((t.relabel e).queries x : ℝ)) = q.expect (fun x => (t.queries x : ℝ)) := by
  constructor
  · rw [relabel_expect]
    apply congrArg q.expect
    funext x
    change (if ((t.relabel e).execute (fun i => x (e.symm i))).1 then (1 : ℝ) else 0) = _
    rw [FiniteDecisionTree.execute_relabel]
    rfl
  · rw [relabel_expect]
    apply congrArg q.expect
    funext x
    change (((t.relabel e).execute (fun i => x (e.symm i))).2.length : ℝ) = _
    rw [FiniteDecisionTree.execute_relabel, List.length_map]
    rfl

open ProbabilityTheory
open scoped NNReal ENNReal
set_option warningAsError false

theorem part8_clause1 :
  (∀ {n : ℕ} (i : Fin n) (l r : FiniteDecisionTree n) (x : Fin n → Bool),
    (FiniteDecisionTree.query i l r).output x = if x i then r.output x else l.output x) ∧
  (∀ {n : ℕ} (i : Fin n) (l r : FiniteDecisionTree n) (x : Fin n → Bool),
    (FiniteDecisionTree.query i l r).queries x = 1+(if x i then r.queries x else l.queries x)) ∧
  (∀ {n : ℕ} (t : FiniteDecisionTree n) (x : Fin n → Bool),
    t.queries x ≤ t.depth) ∧
  (∀ {n : ℕ} (t : FiniteDecisionTree n) (x : Fin n → Bool),
    ∀ v ∈ (t.execute x).2, v.2 = x v.1) ∧
  (∀ {n : ℕ} (e : Equiv.Perm (Fin n)) (t : FiniteDecisionTree n)
    (x : Fin n → Bool),
    (t.relabel e).execute (fun i => x (e.symm i)) =
      ((t.execute x).1, (t.execute x).2.map (fun v => (e v.1,v.2)))) ∧
  (∀ {n : ℕ} (e : Equiv.Perm (Fin n)) (t : FiniteDecisionTree n),
    (t.relabel e).depth = t.depth) ∧
  (∀ {n : ℕ} (t : FiniteDecisionTree n) (x : Fin n → Bool),
    t.accept x ∈ Set.Icc 0 1) ∧
  (∀ {n : ℕ} (t : FiniteDecisionTree n) (x : Fin n → Bool),
    MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) t.polynomial = t.accept x) ∧
  (∀ {n : ℕ} (t : FiniteDecisionTree n),
    t.polynomial.totalDegree ≤ t.depth) ∧
  (∀ {n : ℕ} (t : FiniteDecisionTree n),
    CubeDegreeLE t.depth t.accept) ∧
  (∀ (n : ℕ) (w : (Fin n → Bool) → ℝ) (_hw : CubeWeight n w)
    (f : (Fin n → Bool) → ℝ),
    (cubeLaw n w _hw).expect f = cubeExpect n w f) ∧
  (∀ (n : ℕ) (w : (Fin n → Bool) → ℝ) (_hw : CubeWeight n w)
    (f : (Fin n → Bool) → ℝ),
    (cubeLaw n w _hw).variance f = cubeVar n w f) ∧
  (∀ (n : ℕ) (w : (Fin n → Bool) → ℝ) (_hw : CubeWeight n w)
    (f : (Fin n → Bool) → ℝ) (i : Fin n),
    (cubeLaw n w _hw).expect (fun x => (f x-f (cubeFlip x i))^2) = cubeInf n w f i) ∧
  (∀ (n : ℕ) (p : ℝ) (_hp : p ∈ Set.Icc 0 1) (x : Fin n → Bool),
    (biasedCubeLaw n p _hp).prob x = muWeight p n x) ∧
  (∀ (n : ℕ) (p : ℝ) (_hp : p ∈ Set.Icc 0 1)
    (f : (Fin n → Bool) → ℝ),
    (biasedCubeLaw n p _hp).expect f = cubeExpect n (muWeight p n) f) ∧
  (∀ (n : ℕ) (x : Fin n → Bool),
    (biasedCubeLaw n (1/2) (by constructor <;> norm_num)).prob x = (2 : ℝ)⁻¹^n) ∧
  (∀ (n k : ℕ) (_hk : k ≤ n) (x : Fin n → Bool),
    (sliceCubeLaw n k _hk).prob x = sliceWeight n k x) ∧
  (∀ {Ω : Type u} [Fintype Ω] {n : ℕ}
    (p : FinDist Ω) (t : Ω → FiniteDecisionTree n) (x : Fin n → Bool),
    MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) (randomizedTreePolynomial p t) =
      randomizedTreeAccept p t x) ∧
  (∀ {Ω : Type u} [Fintype Ω] {n : ℕ}
    (p : FinDist Ω) (t : Ω → FiniteDecisionTree n),
    (randomizedTreePolynomial p t).totalDegree ≤ forestDepth t) ∧
  (∀ {Ω : Type u} [Fintype Ω] {n : ℕ}
    (p : FinDist Ω) (t : Ω → FiniteDecisionTree n),
    CubeDegreeLE (forestDepth t) (randomizedTreeAccept p t)) ∧
  (∀ {Ω : Type u} [Fintype Ω] {n : ℕ}
    (p : FinDist Ω) (t : Ω → FiniteDecisionTree n) (x : Fin n → Bool),
    randomizedTreeAccept p t x ∈ Set.Icc 0 1) ∧
  (∀ {Ω : Type u} [Fintype Ω] {n : ℕ}
    (p : FinDist Ω) (t : Ω → FiniteDecisionTree n) (x : Fin n → Bool),
    0 ≤ randomizedTreeQueries p t x ∧ randomizedTreeQueries p t x ≤ forestDepth t) ∧
  (∀ {Ω : Type u} [Fintype Ω] {n : ℕ} (p : FinDist Ω)
    (q : FinDist (Fin n → Bool)) (g : Ω → (Fin n → Bool) → ℝ),
    (seedInputLaw p q).expect (fun z => g z.1 z.2) = q.expect (fun x => p.expect (fun ω => g ω x))) ∧
  (∀ (n : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W)) (ψ : QState (PolynomialWorkspace (Fin n) W))
    (E : Finset (PolynomialWorkspace (Fin n) W)),
    CubeDegreeLE (2*QueryCount C) (fun f =>
      MeasureProb (Run (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ)) C ψ) E)) ∧
  (∀ {n : ℕ} (t : FiniteDecisionTree n)
    (w : (Fin n → Bool) → ℝ) (_hw : CubeWeight n w),
    cubeTotalInf n w t.accept ≤ 8*(t.depth : ℝ)^2) ∧
  (∀ {Ω : Type u} [Fintype Ω] {n : ℕ}
    (p : FinDist Ω) (t : Ω → FiniteDecisionTree n) (w : (Fin n → Bool) → ℝ)
    (_hw : CubeWeight n w),
    cubeTotalInf n w (randomizedTreeAccept p t) ≤ 8*(forestDepth t : ℝ)^2) ∧
  (∀ (n : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W)) (ψ : QState (PolynomialWorkspace (Fin n) W))
    (E : Finset (PolynomialWorkspace (Fin n) W))
    (_hC : ∀ U, Step.gate U ∈ C → U ∈ Matrix.unitaryGroup (PolynomialWorkspace (Fin n) W) ℂ)
    (_hψ : Normalized ψ) (f : Fin n → Bool),
    MeasureProb (Run (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ)) C ψ) E ∈ Set.Icc 0 1) ∧
  (∀ (n : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W)) (ψ : QState (PolynomialWorkspace (Fin n) W))
    (E : Finset (PolynomialWorkspace (Fin n) W))
    (_hC : ∀ U, Step.gate U ∈ C → U ∈ Matrix.unitaryGroup (PolynomialWorkspace (Fin n) W) ℂ)
    (_hψ : Normalized ψ) (w : (Fin n → Bool) → ℝ) (_hw : CubeWeight n w),
    cubeTotalInf n w (fun f => MeasureProb
      (Run (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ)) C ψ) E) ≤
        8*((2*QueryCount C : ℕ) : ℝ)^2) ∧
  (∀ (n : ℕ) (w : (Fin n → Bool) → ℝ) (_hw : CubeWeight n w)
    [MeasurableSpace (Fin n → Bool)] [MeasurableSingletonClass (Fin n → Bool)]
    (f : (Fin n → Bool) → ℝ),
    (∫ x, f x ∂(toPMF (cubeLaw n w _hw)).toMeasure) = cubeExpect n w f) ∧
  (∀ {n : ℕ} (e : Equiv.Perm (Fin n)) (t : FiniteDecisionTree n)
    (q : FinDist (Fin n → Bool)),
    (relabel (Equiv.arrowCongr e (Equiv.refl Bool)) q).expect (t.relabel e).accept =
      q.expect t.accept ∧
    (relabel (Equiv.arrowCongr e (Equiv.refl Bool)) q).expect
      (fun x => ((t.relabel e).queries x : ℝ)) = q.expect (fun x => (t.queries x : ℝ))) ∧
  (∀ (I W : Type) [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W] (C : Circuit (PolynomialWorkspace I W)) (ψ : QState (PolynomialWorkspace I W))
    (E : Finset (PolynomialWorkspace I W)),
    (booleanAcceptancePolynomial C ψ E).totalDegree ≤ 2 * QueryCount C ∧
      (∀ d : I →₀ ℕ, (booleanAcceptancePolynomial C ψ E).coeff d ≠ 0 → ∀ i, d i ≤ 1) ∧
      ∀ f : I → Bool,
        MvPolynomial.eval (fun i => if f i then (1 : ℝ) else 0)
            (booleanAcceptancePolynomial C ψ E) =
          MeasureProb (Run (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ)) C ψ) E) ∧
  (∀ {p : ℝ} (_hp0 : 0 ≤ p) (_hp1 : p ≤ 1) (n : ℕ)
    (f : (Fin n → Bool) → ℝ),
    cubeVar n (muWeight p n) f ≤ cubeTotalInf n (muWeight p n) f) ∧
  (∀ {n : ℕ} {p : ℝ} (_hp0 : 0 < p) (_hp1 : p < 1)
    (_hn : 0 < n) (f : (Fin n → Bool) → ℝ),
    ∃ i : Fin n, cubeVar n (nuWeight p n) f ≤ 2*(n : ℝ)^2*cubeInf n (nuWeight p n) f i) ∧
  (∀ (m : ℝ) (v : ℝ≥0) (x : ℝ),
    gaussianPDFReal m v x ≤ (Real.sqrt (2*Real.pi*v))⁻¹) ∧
  (∀ (m : ℝ) (v : ℝ≥0) (_hv : v ≠ 0) (a b : ℝ) (_hab : a ≤ b),
    gaussianReal m v (Set.Icc a b) ≤ ENNReal.ofReal ((b-a)/Real.sqrt (2*Real.pi*v))) ∧
  (∀ (m : ℝ) (v : ℝ≥0) (_hv : v ≠ 0) (a ε : ℝ) (_hε : 0 ≤ ε),
    gaussianReal m v {x | |x-a| ≤ ε} ≤ ENNReal.ofReal (2*ε/Real.sqrt (2*Real.pi*v))) ∧
  (∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (m : ℝ) (v : ℝ≥0)
    (_hX : HasLaw X (gaussianReal m v) P) (_hv : v ≠ 0) (a ε : ℝ) (_hε : 0 ≤ ε),
    P {ω | |X ω-a| ≤ ε} ≤ ENNReal.ofReal (2*ε/Real.sqrt (2*Real.pi*v))) ∧
  (∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (m : ℝ) (v : ℝ≥0)
    (_hX : HasLaw X (gaussianReal m v) P) (_hv : v ≠ 0)
    (bits : ℕ) (a ε : ℝ) (_hε : 0 ≤ ε),
    P {ω | |(⌊(2 : ℝ)^bits*X ω⌋ : ℝ)/(2 : ℝ)^bits-a| ≤ ε} ≤
      ENNReal.ofReal (2*(ε+1/(2 : ℝ)^bits)/Real.sqrt (2*Real.pi*v))) ∧
  (∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ),
    Measurable (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) Q)) ∧
  (∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ),
    IsProbabilityMeasure ((stdGaussian (EuclideanSpace ℝ (Fin n))).map
      (fun x => MvPolynomial.eval (fun i => x i) Q))) ∧
  (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (L : StrongDual ℝ E),
    HasLaw L (gaussianReal 0 (‖L‖^2).toNNReal) (stdGaussian E)) ∧
  (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (L : StrongDual ℝ E) (_hL : L ≠ 0)
    (a ε : ℝ) (_hε : 0 ≤ ε),
    stdGaussian E {x | |L x-a| ≤ ε} ≤
      ENNReal.ofReal (2*ε/Real.sqrt (2*Real.pi*((‖L‖^2).toNNReal : ℝ)))) ∧
  (∀ (μ : ℝ),
    gaussianReal μ 0 = Measure.dirac μ) := by
  exact ⟨FiniteDecisionTree.output_query,
    FiniteDecisionTree.queries_query,
    FiniteDecisionTree.queries_le_depth,
    FiniteDecisionTree.execute_answers,
    FiniteDecisionTree.execute_relabel,
    FiniteDecisionTree.depth_relabel,
    FiniteDecisionTree.accept_range,
    FiniteDecisionTree.polynomial_eval,
    FiniteDecisionTree.polynomial_degree,
    FiniteDecisionTree.cube_degree,
    cubeLaw_expect,
    cubeLaw_variance,
    cubeLaw_influence,
    biasedCubeLaw_prob,
    biasedCubeLaw_expect,
    uniformCubeLaw_prob,
    sliceCubeLaw_prob,
    randomized_polynomial_eval,
    randomized_polynomial_degree,
    randomized_cube_degree,
    randomized_accept_range,
    randomized_queries_bound,
    seed_input_expect,
    circuit_cube_degree,
    tree_total_influence,
    randomized_total_influence,
    circuit_accept_range,
    circuit_total_influence,
    cubeLaw_integral,
    tree_law_relabel,
    (by intro I W _ _ _ _; exact acceptance_boolean_multilinearization_preserves_run),
    cube_mu_variance_le_total_inf,
    cube_nu_exists_large_influence,
    gaussian_density_bound,
    gaussian_interval_bound,
    gaussian_small_ball,
    actual_gaussian_small_ball,
    rounded_gaussian_small_ball,
    gaussian_polynomial_measurable,
    gaussian_polynomial_probability,
    (by intro E _ _ _ _ _; exact stdGaussian_linear_law),
    (by intro E _ _ _ _ _; exact stdGaussian_linear_small_ball),
    gaussianReal_zero_var⟩

end Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
