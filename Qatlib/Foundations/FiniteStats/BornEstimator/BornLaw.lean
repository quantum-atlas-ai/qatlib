/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteStats.BornEstimator.FiniteLaw
import QuantumInfo.Measurements.POVM

/-!
# Born laws and unbiased inclusion-weighted scores

This module describes finite joint-measurement schemes through `JointScheme`, recording
contexts, POVMs, signs, and observable marginals. The function `bornLaw` combines context
weights with Born probabilities, and `inclusion` records the weight of contexts containing an
observable.

The sign moments yield the unbiasedness of inverse-inclusion scores and a variance bound in
terms of their inclusion weights. This is the finite estimator framework relevant to
[XuEtAl2026].

## Main statements

* `JointScheme`: A family of context POVMs with real outcome signs whose squares indicate
  context membership and whose signed marginals recover the selected Hermitian observables.
* `born_score_unbiased`: If every inclusion weight is nonzero, the inverse-inclusion score has
  mean equal to the corresponding linear combination of observable expectations.
* `born_score_variance_le`: For nonnegative normalized context weights and positive inclusion
  weights, the inverse-inclusion score variance is at most the square of the sum of `|c i| /
  √(inclusion M q i)`.

## References

* [Xu et al., 2026][XuEtAl2026]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.FiniteStats.BornEstimator
open scoped Classical BigOperators RealInnerProductSpace
variable {V K Ω d : Type*} [Fintype V] [DecidableEq V] [Fintype K]
  [Fintype Ω] [Fintype d] [DecidableEq d]

/-- A family of context POVMs with real outcome signs whose squares indicate context membership
and whose signed marginals recover the selected Hermitian observables. -/
structure JointScheme (S : V → HermitianMat d ℂ) where
  context : K → Finset V
  measurement : K → POVM Ω d
  sign : K → V → Ω → ℝ
  sign_sq : ∀ k i s,(sign k i s)^2=if i∈context k then 1 else 0
  marginal : ∀ k i,(∑ s,sign k i s • (measurement k).mats s)=if i∈context k then S i else 0

/-- The total context weight of contexts containing observable `i`. -/
def inclusion {S : V → HermitianMat d ℂ} (M : JointScheme (K:=K) (Ω:=Ω) S)
    (q : K → ℝ) (i : V) : ℝ := ∑ k,q k*(if i∈M.context k then 1 else 0)

/-- The joint weight of a context and an outcome, given by its context weight times the POVM
Born probability in `ρ`. -/
def bornLaw {S : V → HermitianMat d ℂ} (M : JointScheme (K:=K) (Ω:=Ω) S)
    (q : K → ℝ) (ρ : MState d) (ω : K×Ω) : ℝ :=
  q ω.1*(((M.measurement ω.1).measure ρ) ω.2 : ℝ)

omit [Fintype V] [Fintype K] in

/-- Nonnegative context weights give nonnegative joint Born weights. -/
theorem bornLaw_nonneg {S : V → HermitianMat d ℂ} (M : JointScheme (K:=K) (Ω:=Ω) S)
    (q : K → ℝ) (hq : ∀ k,0 ≤ q k) (ρ : MState d) (ω : K×Ω) :
    0 ≤ bornLaw M q ρ ω := mul_nonneg (hq ω.1) (((M.measurement ω.1).measure ρ) ω.2).property.1

omit [Fintype V] in

/-- Context weights summing to one give joint Born weights summing to one. -/
theorem bornLaw_normalized {S : V → HermitianMat d ℂ} (M : JointScheme (K:=K) (Ω:=Ω) S)
    (q : K → ℝ) (hq : ∑ k,q k=1) (ρ : MState d) : ∑ ω,bornLaw M q ρ ω=1 := by
  unfold bornLaw
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum,ProbDistribution.normalized,mul_one]
  exact hq

omit [Fintype V] in

/-- The second moment of an observable's outcome sign under the joint Born weights equals its
inclusion weight. -/
theorem born_sign_second {S : V → HermitianMat d ℂ} (M : JointScheme (K:=K) (Ω:=Ω) S)
    (q : K → ℝ) (ρ : MState d) (i : V) :
    second (bornLaw M q ρ) (fun ω => M.sign ω.1 i ω.2)=inclusion M q i := by
  unfold second mean bornLaw inclusion
  rw [Fintype.sum_prod_type]
  simp_rw [M.sign_sq,mul_assoc,← Finset.mul_sum,← Finset.sum_mul,ProbDistribution.normalized,one_mul]

omit [Fintype V] in

/-- The mean of an observable's outcome sign equals its inclusion weight times its expectation
in `ρ`. -/
theorem born_sign_mean {S : V → HermitianMat d ℂ} (M : JointScheme (K:=K) (Ω:=Ω) S)
    (q : K → ℝ) (ρ : MState d) (i : V) :
    mean (bornLaw M q ρ) (fun ω => M.sign ω.1 i ω.2)=inclusion M q i*ρ.exp_val (S i) := by
  have hm (k : K) : (∑ s,(((M.measurement k).measure ρ) s : ℝ)*M.sign k i s)=
      (if i∈M.context k then 1 else 0)*ρ.exp_val (S i) := by
    change (∑ s,⟪(M.measurement k).mats s,ρ.M⟫*M.sign k i s)=_
    calc _ = ⟪∑ s,M.sign k i s • (M.measurement k).mats s,ρ.M⟫ := by
               rw [sum_inner]
               apply Finset.sum_congr rfl
               intro s _
               rw [real_inner_smul_left]
               ring
         _ = _ := by
           rw [M.marginal]
           split_ifs <;> simp [MState.exp_val,real_inner_comm]
  unfold mean bornLaw inclusion
  rw [Fintype.sum_prod_type]
  simp_rw [mul_assoc,← Finset.mul_sum,hm]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- If every inclusion weight is nonzero, the inverse-inclusion score has mean equal to the
corresponding linear combination of observable expectations. -/
theorem born_score_unbiased {S : V → HermitianMat d ℂ} (M : JointScheme (K:=K) (Ω:=Ω) S)
    (q : K → ℝ) (ρ : MState d) (c : V → ℝ) (hp : ∀ i,inclusion M q i≠0) :
    mean (bornLaw M q ρ) (fun ω => ∑ i,c i*M.sign ω.1 i ω.2/inclusion M q i)=
      ∑ i,c i*ρ.exp_val (S i) :=
  mean_score _ _ _ _ _ hp (born_sign_mean M q ρ)

/-- For nonnegative normalized context weights and positive inclusion weights, the
inverse-inclusion score variance is at most the square of the sum of `|c i| / √(inclusion M
q i)`. -/
theorem born_score_variance_le {S : V → HermitianMat d ℂ} (M : JointScheme (K:=K) (Ω:=Ω) S)
    (q : K → ℝ) (hq : ∀ k,0 ≤ q k) (hn : ∑ k,q k=1) (ρ : MState d)
    (c : V → ℝ) (hp : ∀ i,0 < inclusion M q i) :
    variance (bornLaw M q ρ) (fun ω => ∑ i,c i*M.sign ω.1 i ω.2/inclusion M q i) ≤
      (∑ i,|c i|/Real.sqrt (inclusion M q i))^2 :=
  variance_score_le _ (bornLaw_nonneg M q hq ρ) (bornLaw_normalized M q hn ρ)
    _ _ _ hp (born_sign_second M q ρ)

end Qatlib.Foundations.FiniteStats.BornEstimator
