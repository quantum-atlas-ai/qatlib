/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.UniformMatchedSampling

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Matched Sampling Law

Matched Sampling Law constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section
open scoped BigOperators
open Qatlib

variable {S : Type} [Fintype S] [DecidableEq S]

/-- Construction for without Replacement Mass in the matched sampling law model. -/
def withoutReplacementMass : (R : Finset S) → (n : ℕ) → (Fin n → S) → ℝ
  | _, 0, _ => 1
  | R, n+1, ω => if ω 0 ∈ R then
      withoutReplacementMass (R.erase (ω 0)) n (fun i => ω i.succ)/(R.card : ℝ) else 0

omit [Fintype S] in
/-- Complete original `without_replacement_mass_nonneg` guarantee for `MatchedSamplingLaw`; all source hypotheses and output obligations are retained. -/
theorem without_replacement_mass_nonneg (R : Finset S) (n : ℕ) (ω : Fin n → S) :
    0 ≤ withoutReplacementMass R n ω := by
  induction n generalizing R with
  | zero => norm_num [withoutReplacementMass]
  | succ n ih =>
    rw [withoutReplacementMass]
    split_ifs
    · exact div_nonneg (ih _ _) (by positivity)
    · exact le_rfl

/-- Complete original `sum_mem_indicator` guarantee for `MatchedSamplingLaw`; all source hypotheses and output obligations are retained. -/
theorem sum_mem_indicator (R : Finset S) (f : S → ℝ) :
    (∑ x : S, if x ∈ R then f x else 0)=∑ x ∈ R, f x := by
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp

/-- Complete original `without_replacement_mass_sum` guarantee for `MatchedSamplingLaw`; all source hypotheses and output obligations are retained. -/
theorem without_replacement_mass_sum (R : Finset S) (n : ℕ) (hn : n ≤ R.card) :
    (∑ ω : Fin n → S, withoutReplacementMass R n ω)=1 := by
  induction n generalizing R with
  | zero => simp [withoutReplacementMass]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => S)).sum_comp]
    simp only [Fintype.sum_prod_type]
    change (∑ x : S, ∑ η : Fin n → S, withoutReplacementMass R (n+1) (Fin.cons x η))=1
    have hrow (x : S) : (∑ η : Fin n → S,
        withoutReplacementMass R (n+1) (Fin.cons x η))=
        if x ∈ R then 1/(R.card : ℝ) else 0 := by
      by_cases hx : x ∈ R
      · simp only [withoutReplacementMass, Fin.cons_zero, Fin.cons_succ, ite_eq_left hx]
        rw [← Finset.sum_div, ih (R.erase x) (by rw [Finset.card_erase_of_mem hx]; omega)]
      · simp [withoutReplacementMass, hx]
    simp_rw [hrow]
    rw [sum_mem_indicator]
    have hc : (R.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : R.card ≠ 0)
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp

/-- Construction for without Replacement Law in the matched sampling law model. -/
def withoutReplacementLaw (R : Finset S) (n : ℕ) (hn : n ≤ R.card) : FinDist (Fin n → S) where
  prob := withoutReplacementMass R n
  nonneg := without_replacement_mass_nonneg R n
  sum_one := without_replacement_mass_sum R n hn

/-- Complete original `without_replacement_expect_eq` guarantee for `MatchedSamplingLaw`; all source hypotheses and output obligations are retained. -/
theorem without_replacement_expect_eq (R : Finset S) (n : ℕ) (F : List S → ℝ) :
    (∑ ω : Fin n → S, withoutReplacementMass R n ω*F (List.ofFn ω))=
      withoutReplacementExpect R n F := by
  induction n generalizing R F with
  | zero => simp [withoutReplacementMass, withoutReplacementExpect]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => S)).sum_comp]
    simp only [Fintype.sum_prod_type]
    change (∑ x : S, ∑ η : Fin n → S, withoutReplacementMass R (n+1) (Fin.cons x η)*
      F (List.ofFn (Fin.cons x η)))=withoutReplacementExpect R (n+1) F
    have hrow (x : S) : (∑ η : Fin n → S,
        withoutReplacementMass R (n+1) (Fin.cons x η)*F (List.ofFn (Fin.cons x η)))=
        if x ∈ R then withoutReplacementExpect (R.erase x) n (fun xs => F (x::xs))/(R.card : ℝ) else 0 := by
      by_cases hx : x ∈ R
      · simp only [withoutReplacementMass, Fin.cons_zero, Fin.cons_succ, ite_eq_left hx,
          List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
        have hp (η : Fin n → S) :
            withoutReplacementMass (R.erase x) n η/(R.card : ℝ)*F (x::List.ofFn η)=
              (withoutReplacementMass (R.erase x) n η*F (x::List.ofFn η))/(R.card : ℝ) := by ring
        simp_rw [hp]
        rw [← Finset.sum_div, ih (R.erase x) (fun xs => F (x::xs))]
      · simp [withoutReplacementMass, hx]
    simp_rw [hrow]
    rw [sum_mem_indicator, withoutReplacementExpect, Finset.sum_div]

/-- Complete original `without_replacement_law_mgf` guarantee for `MatchedSamplingLaw`; all source hypotheses and output obligations are retained. -/
theorem without_replacement_law_mgf (R : Finset S) (n : ℕ) (hn : n ≤ R.card)
    (f : S → ℝ) (hf : ∀ x ∈ R, |f x| ≤ 1) (t : ℝ) :
    (withoutReplacementLaw R n hn).expect (fun ω => Real.exp
      (t*((∑ i : Fin n, f (ω i))-(n : ℝ)*setAverage R f))) ≤ Real.exp ((n : ℝ)*t^2/2) := by
  have he := without_replacement_expect_eq R n (fun xs => Real.exp
    (t*((xs.map f).sum-(n : ℝ)*setAverage R f)))
  simp only [List.map_ofFn, List.sum_ofFn] at he
  change (∑ ω : Fin n → S, withoutReplacementMass R n ω*Real.exp
    (t*((∑ i : Fin n, f (ω i))-(n : ℝ)*setAverage R f))) ≤ _
  calc
    _ = withoutReplacementExpect R n (fun xs => Real.exp
        (t*((xs.map f).sum-(n : ℝ)*setAverage R f))) := by
      simpa only [Function.comp_apply] using he
    _ ≤ _ := without_replacement_centered_mgf R n hn f hf t

variable {X : Type} [Fintype X]

/-- Complete original `finite_subgaussian_bad_mass` guarantee for `MatchedSamplingLaw`; all source hypotheses and output obligations are retained. -/
theorem finite_subgaussian_bad_mass (p : FinDist X) (F : X → ℝ) (μ : ℝ) (n : ℕ)
    (ε : ℝ) (hn : 0 < n) (hε : 0 < ε)
    (hmgf : ∀ t : ℝ, p.expect (fun x => Real.exp (t*((n : ℝ)*(F x-μ)))) ≤
      Real.exp ((n : ℝ)*t^2/2)) :
    finiteBadMass p F μ ε ≤ 2*Real.exp (-(n : ℝ)*ε^2/2) := by
  classical
  let s : X → ℝ := fun x => (n : ℝ)*(F x-μ)
  let c := Real.exp (-(n : ℝ)*ε^2)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp (x : X) : (if ε < |F x-μ| then (1 : ℝ) else 0) ≤
      c*(Real.exp (ε*s x)+Real.exp ((-ε)*s x)) := by
    by_cases hb : ε < |F x-μ|
    · rw [ite_eq_left hb]
      rcases lt_or_ge (F x-μ) 0 with hr | hr
      · rw [abs_of_neg hr] at hb
        have hd : 0 ≤ -ε-(F x-μ) := by linarith
        have hprod := mul_nonneg (mul_nonneg hnR.le hε.le) hd
        have he : 0 ≤ -(n : ℝ)*ε^2+(-ε)*s x := by dsimp [s]; nlinarith
        have hx : 1 ≤ c*Real.exp ((-ε)*s x) := by
          dsimp [c]
          rw [← Real.exp_add]
          exact Real.one_le_exp_iff.mpr he
        exact hx.trans (mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (Real.exp_pos (ε*s x)).le) (Real.exp_pos _).le)
      · rw [abs_of_nonneg hr] at hb
        have hd : 0 ≤ (F x-μ)-ε := by linarith
        have hprod := mul_nonneg (mul_nonneg hnR.le hε.le) hd
        have he : 0 ≤ -(n : ℝ)*ε^2+ε*s x := by dsimp [s]; nlinarith
        have hx : 1 ≤ c*Real.exp (ε*s x) := by
          dsimp [c]
          rw [← Real.exp_add]
          exact Real.one_le_exp_iff.mpr he
        exact hx.trans (mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (Real.exp_pos ((-ε)*s x)).le) (Real.exp_pos _).le)
    · rw [ite_eq_right hb]
      dsimp [c]
      positivity
  rw [← finite_bad_indicator_mean]
  calc
    _ ≤ p.expect (fun x => c*(Real.exp (ε*s x)+Real.exp ((-ε)*s x))) :=
      finite_expect_mono p _ _ hp
    _ = c*(p.expect (fun x => Real.exp (ε*s x))+p.expect (fun x => Real.exp ((-ε)*s x))) := by
      rw [finite_expect_mul, finite_expect_add]
    _ ≤ c*(Real.exp ((n : ℝ)*ε^2/2)+Real.exp ((n : ℝ)*ε^2/2)) :=
      mul_le_mul_of_nonneg_left (add_le_add (hmgf ε) (by
        simpa only [neg_sq] using hmgf (-ε))) (Real.exp_pos _).le
    _ = 2*(Real.exp (-(n : ℝ)*ε^2)*Real.exp ((n : ℝ)*ε^2/2)) := by dsimp [c]; ring
    _ = 2*Real.exp (-(n : ℝ)*ε^2/2) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Complete original `without_replacement_average_tail` guarantee for `MatchedSamplingLaw`; all source hypotheses and output obligations are retained. -/
theorem without_replacement_average_tail (R : Finset S) (n : ℕ) (hn : n ≤ R.card)
    (hn0 : 0 < n) (f : S → ℝ) (hf : ∀ x ∈ R, |f x| ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    finiteBadMass (withoutReplacementLaw R n hn) (FinDist.avg f) (setAverage R f) ε ≤
      2*Real.exp (-(n : ℝ)*ε^2/2) := by
  apply finite_subgaussian_bad_mass _ _ _ n ε hn0 hε
  intro t
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hs (ω : Fin n → S) : (n : ℝ)*(FinDist.avg f ω-setAverage R f)=
      (∑ i : Fin n, f (ω i))-(n : ℝ)*setAverage R f := by
    unfold FinDist.avg
    calc
      _ = ((∑ i : Fin n, f (ω i))/(n : ℝ))*(n : ℝ)-(n : ℝ)*setAverage R f := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hnR]
  simp_rw [hs]
  exact without_replacement_law_mgf R n hn f hf t

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.without_replacement_mass_nonneg
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.without_replacement_mass_sum
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.without_replacement_expect_eq
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.without_replacement_law_mgf
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.finite_subgaussian_bad_mass
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.without_replacement_average_tail
