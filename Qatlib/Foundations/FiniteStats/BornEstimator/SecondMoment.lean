/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteStats.BornEstimator.Eigenstate
import Qatlib.Foundations.FiniteStats.BornEstimator.BornLaw
import Qatlib.Foundations.FiniteStats.BornEstimator.IndependentShots

/-!
# Second-moment operators and spectral variance bounds

This module defines `secondOperator` by weighting joint measurement effects with squared scores.
Its expectation equals the score's second moment, giving an operator formula for the variance of
an independent-shot average.

The maximum eigenvalue `largestEigenvalue` bounds every state expectation and hence the averaged
variance. For inverse-inclusion scores, `largest_score_operator_le` gives a bound determined by
coefficients and inclusion weights, as used in [XuEtAl2026].

## Main statements

* `second_eq_exp_operator`: The second moment under the joint Born weights equals the
  expectation of the second-moment operator.
* `born_average_variance_le_largest`: For normalized context weights and positive `N`, the
  shot-average variance is at most the largest eigenvalue of the second-moment operator divided
  by `N`.
* `largest_score_operator_le`: For nonnegative context weights and positive inclusion weights,
  the largest eigenvalue of the inverse-inclusion score's second-moment operator is at most the
  square of the sum of `|c i|/√(inclusion M q i)`.

## References

* [Xu et al., 2026][XuEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.FiniteStats.BornEstimator
open scoped Classical BigOperators RealInnerProductSpace
variable {V K Ω d : Type*} [DecidableEq V] [Fintype K] [Fintype Ω] [Fintype d] [DecidableEq d]

/-- The Hermitian operator obtained by summing measurement effects weighted by the context
weight and the squared outcome score. -/
def secondOperator {S : V → HermitianMat d ℂ} (M : JointScheme (K:=K) (Ω:=Ω) S)
    (q : K → ℝ) (f : K×Ω → ℝ) : HermitianMat d ℂ :=
  ∑ k,∑ s,(q k*f (k,s)^2) • (M.measurement k).mats s

/-- The second-moment operator is positive semidefinite when context weights are nonnegative. -/
theorem secondOperator_nonneg {S : V → HermitianMat d ℂ} (M : JointScheme (K:=K) (Ω:=Ω) S)
    (q : K → ℝ) (hq : ∀ k,0 ≤ q k) (f : K×Ω → ℝ) : 0 ≤ secondOperator M q f := by
  apply Finset.sum_nonneg
  intro k _
  apply Finset.sum_nonneg
  intro s _
  exact smul_nonneg (mul_nonneg (hq k) (sq_nonneg _)) ((M.measurement k).nonneg s)

/-- The second moment under the joint Born weights equals the expectation of the second-moment
operator. -/
theorem second_eq_exp_operator {S : V → HermitianMat d ℂ} (M : JointScheme (K:=K) (Ω:=Ω) S)
    (q : K → ℝ) (ρ : MState d) (f : K×Ω → ℝ) :
    second (bornLaw M q ρ) f=ρ.exp_val (secondOperator M q f) := by
  unfold second mean bornLaw secondOperator MState.exp_val
  rw [Fintype.sum_prod_type]
  simp_rw [inner_sum,real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro s _
  change q k*⟪(M.measurement k).mats s,ρ.M⟫*f (k,s)^2=
    (q k*f (k,s)^2)*⟪ρ.M,(M.measurement k).mats s⟫
  rw [real_inner_comm (ρ.M)]
  ring

/-- For normalized context weights and positive `N`, the `N`-shot average variance equals the
operator second moment minus the squared score mean, divided by `N`. -/
theorem born_average_variance_operator {S : V → HermitianMat d ℂ}
    (M : JointScheme (K:=K) (Ω:=Ω) S) (q : K → ℝ) (hq : ∑ k,q k=1)
    (ρ : MState d) (f : K×Ω → ℝ) (N : ℕ) (hN : 0<N) :
    variance (shotLaw (bornLaw M q ρ) N) (shotAverage f N)=
      (ρ.exp_val (secondOperator M q f)-(mean (bornLaw M q ρ) f)^2)/(N:ℝ) := by
  rw [shotAverage_variance _ _ (bornLaw_normalized M q hq ρ) N hN,
    variance_eq _ (bornLaw_normalized M q hq ρ),second_eq_exp_operator]

/-- The largest eigenvalue of a Hermitian matrix on a nonempty finite index type. -/
def largestEigenvalue [Nonempty d] (A : HermitianMat d ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty A.H.eigenvalues

omit [DecidableEq V] [Fintype K] [Fintype Ω] in

/-- Every eigenvalue is at most the largest eigenvalue. -/
theorem eigenvalue_le_largest [Nonempty d] (A : HermitianMat d ℂ) (i : d) :
    A.H.eigenvalues i ≤ largestEigenvalue A := Finset.le_sup' _ (Finset.mem_univ i)

omit [DecidableEq V] [Fintype K] [Fintype Ω] in

/-- The expectation of a Hermitian matrix in any density operator is at most its largest
eigenvalue. -/
theorem exp_le_largest [Nonempty d] (A : HermitianMat d ℂ) (ρ : MState d) :
    ρ.exp_val A ≤ largestEigenvalue A := by
  have hA :=
      HermitianMat.eigenvalues_le_imp_le_smul_one A (largestEigenvalue A) (eigenvalue_le_largest A)
  have h := MState.exp_val_le_exp_val ρ hA
  simpa only [MState.exp_val_smul,MState.exp_val_one,mul_one] using h

/-- For normalized context weights and positive `N`, the shot-average variance is at most the
largest eigenvalue of the second-moment operator divided by `N`. -/
theorem born_average_variance_le_largest [Nonempty d] {S : V → HermitianMat d ℂ}
    (M : JointScheme (K:=K) (Ω:=Ω) S) (q : K → ℝ) (hq : ∑ k,q k=1)
    (ρ : MState d) (f : K×Ω → ℝ) (N : ℕ) (hN : 0<N) :
    variance (shotLaw (bornLaw M q ρ) N) (shotAverage f N) ≤ largestEigenvalue (secondOperator M q f)/(N:ℝ) := by
  rw [born_average_variance_operator M q hq ρ f N hN]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact (sub_le_self _ (sq_nonneg _)).trans (exp_le_largest _ ρ)

/-- For nonnegative context weights and positive inclusion weights, the largest eigenvalue of
the inverse-inclusion score's second-moment operator is at most the square of the sum of `|c
i|/√(inclusion M q i)`. -/
theorem largest_score_operator_le [Fintype V] [Nonempty d] {S : V → HermitianMat d ℂ}
    (M : JointScheme (K:=K) (Ω:=Ω) S) (q : K → ℝ) (hq : ∀ k,0 ≤ q k)
    (c : V → ℝ) (hp : ∀ i,0 < inclusion M q i) :
    largestEigenvalue (secondOperator M q (fun ω => ∑ i,c i*M.sign ω.1 i ω.2/inclusion M q i)) ≤
      (∑ i,|c i|/Real.sqrt (inclusion M q i))^2 := by
  unfold largestEigenvalue
  apply Finset.sup'_le
  intro i _
  let A := secondOperator M q (fun ω => ∑ i,c i*M.sign ω.1 i ω.2/inclusion M q i)
  let ρ := MState.pure (eigenKet A i)
  have hs := second_score_le (bornLaw M q ρ) (bornLaw_nonneg M q hq ρ)
    (fun i ω => M.sign ω.1 i ω.2) (inclusion M q) c hp (born_sign_second M q ρ)
  rw [second_eq_exp_operator] at hs
  change (MState.pure (eigenKet A i)).exp_val A ≤ _ at hs
  rw [eigenstate_exp] at hs
  exact hs

end Qatlib.Foundations.FiniteStats.BornEstimator
