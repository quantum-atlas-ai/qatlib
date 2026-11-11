/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.ActualNested

/-!
# Finite term-code precision in PRN payoffs

`trueTarget` averages a payoff of the sum of real-valued terms evaluated at the generated PRN
residues. The module compares this target with the finite-code target under a Lipschitz payoff
and propagates either individual or uniform term-encoding errors. See [KanekoEtAl2020].

## Main statements

* `actual_code_error`: error bounded by the average sum of term-code discrepancies.
* `uniform_code_error`: a uniform term error gives total error at most `L*2^d*eps`.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerOracle
open Qatlib.Papers.MonteCarloInt20.MainResults.ActualNested
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.MonteCarloInt20.QaeLaw.CodePrecision

/-- The uniform sample average of the payoff applied to the sum of real-valued terms at their
PRN residues. -/
def trueTarget {n s d : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (f : Reg s → Reg d → ZMod (2^n) → ℝ) (g : ℝ → ℝ) : ℝ :=
  (1/(2:ℝ)^s)*∑ j : Reg s,g (∑ i : Reg d,f j i (residue a c seed j i))

/-- For an `L`-Lipschitz payoff, the finite-code target error is bounded by the sample average
of `L` times the sum of absolute term-encoding errors. -/
theorem actual_code_error {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1))
    (f : Reg s → Reg d → ZMod (2^n) → ℝ) (g : ℝ → ℝ) (L : NNReal) (hg : LipschitzWith L g) :
    |finiteTarget a c seed termCode ((2:ℝ)^d) g-trueTarget a c seed f g| ≤
      (1/(2:ℝ)^s)*∑ j : Reg s,(L:ℝ)*∑ i : Reg d,
        |((termCode j i (residue a c seed j i)).val:ℝ)/(2:ℝ)^p-f j i (residue a c seed j i)| := by
  rw [source_sum_target]
  unfold trueTarget
  rw [← mul_sub,← Finset.sum_sub_distrib,abs_mul,abs_of_nonneg (show 0≤1/(2:ℝ)^s by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  have h := hg.dist_le_mul (∑ i : Reg d,((termCode j i (residue a c seed j i)).val:ℝ)/(2:ℝ)^p)
    (∑ i : Reg d,f j i (residue a c seed j i))
  rw [Real.dist_eq,Real.dist_eq,← Finset.sum_sub_distrib] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) L.coe_nonneg)

/-- If every evaluated term code has error at most `eps`, an `L`-Lipschitz payoff has target
error at most `L*2^d*eps`. See [KanekoEtAl2020]. -/
theorem uniform_code_error {n s d p : ℕ} (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1))
    (f : Reg s → Reg d → ZMod (2^n) → ℝ) (g : ℝ → ℝ) (L : NNReal) (hg : LipschitzWith L g)
    (eps : ℝ) (hCode : ∀ j i,|((termCode j i (residue a c seed j i)).val:ℝ)/(2:ℝ)^p-f j i (residue a c seed j i)|≤eps) :
    |finiteTarget a c seed termCode ((2:ℝ)^d) g-trueTarget a c seed f g|≤(L:ℝ)*(2:ℝ)^d*eps := by
  apply (actual_code_error a c seed termCode f g L hg).trans
  have hInner (j : Reg s) : (∑ i : Reg d,|((termCode j i (residue a c seed j i)).val:ℝ)/(2:ℝ)^p-f j i (residue a c seed j i)|)≤(2:ℝ)^d*eps := by
    calc
      _ ≤ ∑ _i : Reg d,eps := Finset.sum_le_sum (fun i _ => hCode j i)
      _ = _ := by simp [Reg]
  calc
    _ ≤ (1/(2:ℝ)^s)*∑ _j : Reg s,(L:ℝ)*((2:ℝ)^d*eps) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hInner j) L.coe_nonneg)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,nsmul_eq_mul]
      push_cast
      have h : (2:ℝ)^s≠0 := pow_ne_zero _ (by norm_num)
      field_simp

end Qatlib.Papers.MonteCarloInt20.QaeLaw.CodePrecision
