/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.CorrelationPlan

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Bounded Average Plan

Bounded Average Plan constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
open scoped BigOperators
open Qatlib

/-- Construction for bounded Average Q in the bounded average plan model. -/
def boundedAverageQ {X : Type} {n : ℕ} (f : X → ℚ) (ω : Fin n → X) : ℚ :=
  (∑ i : Fin n, f (ω i))/(n : ℚ)

/-- This is the cross-record schedule in high_confidence_plan, including skip. -/
def linearCountQ (A ε ρ : ℚ) : ℕ :=
  if A=0 ∨ A≤ε then 0 else
    ceilNatQ (max 2 (2*(ceilLog2Q (2/ρ) : ℚ)/(ε/A)^2))

noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

omit [Fintype X] [DecidableEq X] in
/-- Complete original `bounded_average_cast` guarantee for `BoundedAveragePlan`; all source hypotheses and output obligations are retained. -/
theorem bounded_average_cast {n : ℕ} (f : X → ℚ) (ω : Fin n → X) :
    (boundedAverageQ f ω : ℝ)=FinDist.avg (fun x => (f x : ℝ)) ω := by
  simp only [boundedAverageQ, FinDist.avg, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast]

omit [DecidableEq X] in
/-- Complete original `bounded_expect_abs` guarantee for `BoundedAveragePlan`; all source hypotheses and output obligations are retained. -/
theorem bounded_expect_abs (p : FinDist X) (f : X → ℝ) (A : ℝ)
    (hf : ∀ x, |f x|≤A) : |p.expect f|≤A := by
  have hl := finite_expect_mono p (fun _ => -A) f (fun x => (abs_le.mp (hf x)).1)
  have hu := finite_expect_mono p f (fun _ => A) (fun x => (abs_le.mp (hf x)).2)
  rw [finite_expect_const] at hl hu
  exact abs_le.mpr ⟨hl,hu⟩

/-- Complete original `bounded_average_tail` guarantee for `BoundedAveragePlan`; all source hypotheses and output obligations are retained. -/
theorem bounded_average_tail (p : FinDist X) (f : X → ℝ) (n : ℕ) (A ε : ℝ)
    (hn : 0<n) (hA : 0<A) (hε : 0<ε) (hf : ∀ x, |f x|≤A) :
    finiteBadMass (cohortLaw p n) (FinDist.avg f) (p.expect f) ε ≤
      2*Real.exp (-(n : ℝ)*ε^2/(2*A^2)) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hsum : (∑ _i : Fin n, (2*A/(n : ℝ))^2)=4*A^2/(n : ℝ) := by
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    field_simp
    ring
  have hdiff (i : Fin n) (ω τ : Fin n → X) (h : ∀ j, j≠i → ω j=τ j) :
      |FinDist.avg f ω-FinDist.avg f τ|≤2*A/(n : ℝ) := by
    rw [finite_avg_coordinate_difference n f ω τ i h, abs_div, abs_of_pos hnR]
    apply div_le_div_of_nonneg_right _ hnR.le
    exact (abs_sub _ _).trans (by linarith [hf (ω i),hf (τ i)])
  have ht := (finite_product_bounded_differences_tail X n (fun _ => p)
    (FinDist.avg f) (fun _ => 2*A/(n : ℝ)) ε (fun _ => by positivity)
    (by rw [hsum]; positivity) hε hdiff).2
  have hm : (independentSampleLaw (fun _ : Fin n => p)).expect (FinDist.avg f)=p.expect f :=
    p.expect_avg f hn
  rw [hm, hsum] at ht
  change (∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε≤|FinDist.avg f ω-p.expect f|),
    (cohortLaw p n).prob ω)≤_ at ht
  have hsubset : Finset.univ.filter (fun ω : Fin n → X => ε < |FinDist.avg f ω-p.expect f|) ⊆
      Finset.univ.filter (fun ω : Fin n → X => ε≤|FinDist.avg f ω-p.expect f|) := by
    intro ω hω
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hω).2.le⟩
  have heq : -2*ε^2/(4*A^2/(n : ℝ)) = -(n : ℝ)*ε^2/(2*A^2) := by field_simp; ring
  rw [heq] at ht
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun ω _ _ => (cohortLaw p n).nonneg ω)).trans ht

/-- Complete original `linear_count_guards` guarantee for `BoundedAveragePlan`; all source hypotheses and output obligations are retained. -/
theorem linear_count_guards (A ε ρ : ℚ) (hA : 0<A) (hε : 0<ε) (hεA : ε<A) :
    2≤linearCountQ A ε ρ ∧
      2*(A : ℝ)^2*(ceilLog2Q (2/ρ) : ℝ) ≤
        (linearCountQ A ε ρ : ℝ)*(ε : ℝ)^2 := by
  have hskip : ¬(A=0 ∨ A≤ε) := by
    rintro (h|h) <;> linarith
  let q := max 2 (2*(ceilLog2Q (2/ρ) : ℚ)/(ε/A)^2)
  have hq : (0 : ℚ)≤q := (by norm_num : (0 : ℚ)≤2).trans (le_max_left _ _)
  have hc := (ceil_nat_bounds q hq).1
  have h2 : (2 : ℝ)≤ceilNatQ q := by
    have h2q : (2 : ℚ)≤q := le_max_left _ _
    have hr : (2 : ℝ)≤q := by exact_mod_cast h2q
    exact hr.trans hc
  have hbudget : 2*(ceilLog2Q (2/ρ) : ℝ)/((ε : ℝ)/(A : ℝ))^2≤(ceilNatQ q : ℝ) := by
    have hh : 2*(ceilLog2Q (2/ρ) : ℚ)/(ε/A)^2≤q := le_max_right _ _
    have hhR : 2*(ceilLog2Q (2/ρ) : ℝ)/((ε : ℝ)/(A : ℝ))^2≤(q : ℝ) := by exact_mod_cast hh
    exact hhR.trans hc
  have hAR : (0 : ℝ)<A := Rat.cast_pos.mpr hA
  have hεR : (0 : ℝ)<ε := Rat.cast_pos.mpr hε
  have hb := (div_le_iff₀ (show (0 : ℝ)<((ε : ℝ)/(A : ℝ))^2 by positivity)).mp hbudget
  have hb' : 2*(A : ℝ)^2*(ceilLog2Q (2/ρ) : ℝ) ≤ (ceilNatQ q : ℝ)*(ε : ℝ)^2 := by
    rw [div_pow] at hb
    have hh := (le_div_iff₀ (sq_pos_of_pos hAR)).mp
      (show 2*(ceilLog2Q (2/ρ) : ℝ)≤(ceilNatQ q : ℝ)*(ε : ℝ)^2/(A : ℝ)^2 by
        simpa only [mul_div_assoc] using hb)
    nlinarith only [hh]
  have hdef : linearCountQ A ε ρ=ceilNatQ q := by simp only [linearCountQ, ite_eq_right hskip, q]
  rw [hdef]
  exact ⟨by exact_mod_cast h2, hb'⟩

/-- Complete original `planned_bounded_average_confidence` guarantee for `BoundedAveragePlan`; all source hypotheses and output obligations are retained. -/
theorem planned_bounded_average_confidence (p : FinDist X) (f : X → ℚ) (A ε ρ : ℚ)
    (hA : 0≤A) (hε : 0<ε) (hρ : 0<ρ)
    (hf : ∀ x, |f x|≤A) :
    finiteBadMass (cohortLaw p (linearCountQ A ε ρ))
      (fun ω => (boundedAverageQ f ω : ℝ)) (p.expect (fun x => (f x : ℝ))) (ε : ℝ)≤(ρ : ℝ) := by
  have hfR (x : X) : |(f x : ℝ)|≤(A : ℝ) := by exact_mod_cast hf x
  simp_rw [bounded_average_cast]
  generalize hn : linearCountQ A ε ρ=n
  by_cases hskip : A=0 ∨ A≤ε
  · have hAε : A≤ε := by
      rcases hskip with h|h
      · rw [h]; exact hε.le
      · exact h
    have hbound := bounded_expect_abs p (fun x => (f x : ℝ)) (A : ℝ) hfR
    have hboundε : |p.expect (fun x => (f x : ℝ))|≤(ε : ℝ) :=
      hbound.trans (by exact_mod_cast hAε)
    have hn0 : n=0 := hn.symm.trans (by simp only [linearCountQ, ite_eq_left hskip])
    clear hn
    subst n
    have hempty : ∀ ω : Fin 0 → X,
        ¬(ε : ℝ) < |FinDist.avg (fun x => (f x : ℝ)) ω-p.expect (fun x => (f x : ℝ))| := by
      intro ω
      simpa only [FinDist.avg, Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero,
        div_zero, zero_sub, abs_neg, not_lt] using hboundε
    simp only [finiteBadMass, hempty, Finset.filter_false, Finset.sum_empty]
    exact (Rat.cast_pos.mpr hρ).le
  · have hA0 : 0<A := lt_of_le_of_ne hA (Ne.symm (fun h => hskip (Or.inl h)))
    have hεA : ε<A := lt_of_not_ge (fun h => hskip (Or.inr h))
    obtain ⟨hn2,hbudget⟩ := linear_count_guards A ε ρ hA0 hε hεA
    rw [hn] at hn2 hbudget
    have hAR : (0 : ℝ)<A := Rat.cast_pos.mpr hA0
    have hεR : (0 : ℝ)<ε := Rat.cast_pos.mpr hε
    have hρR : (0 : ℝ)<ρ := Rat.cast_pos.mpr hρ
    have hlog : Real.log (2/(ρ : ℝ))≤(ceilLog2Q (2/ρ) : ℝ) := by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using ceil_log2_log_bound (2/ρ) (by positivity)
    have hratio : Real.log (2/(ρ : ℝ))≤
        (n : ℝ)*(ε : ℝ)^2/(2*(A : ℝ)^2) := by
      apply hlog.trans
      apply (le_div_iff₀ (by positivity : (0 : ℝ)<2*(A : ℝ)^2)).mpr
      nlinarith only [hbudget]
    have ht := bounded_average_tail p (fun x => (f x : ℝ)) n
      (A : ℝ) (ε : ℝ) (by omega) hAR hεR hfR
    have he := Real.exp_le_exp.mpr (neg_le_neg hratio)
    have heval : Real.exp (-Real.log (2/(ρ : ℝ)))=(ρ : ℝ)/2 := by
      rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ)<2/(ρ : ℝ)), inv_div]
    rw [heval] at he
    calc
      _ ≤ 2*Real.exp (-(n : ℝ)*(ε : ℝ)^2/(2*(A : ℝ)^2)) := ht
      _ ≤ 2*((ρ : ℝ)/2) := by
        have heq : -(n : ℝ)*(ε : ℝ)^2/(2*(A : ℝ)^2)=
            -((n : ℝ)*(ε : ℝ)^2/(2*(A : ℝ)^2)) := by ring
        rw [heq]
        exact mul_le_mul_of_nonneg_left he (by norm_num)
      _ = _ := by ring

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.bounded_average_cast
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.bounded_expect_abs
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.bounded_average_tail
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.linear_count_guards
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.planned_bounded_average_confidence
