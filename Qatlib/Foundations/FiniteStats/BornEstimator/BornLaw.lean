/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteStats.BornEstimator.FiniteLaw
import QuantumInfo.Measurements.POVM
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.FiniteStats.BornEstimator
open scoped Classical BigOperators RealInnerProductSpace
variable {V K Ω d : Type*} [Fintype V] [DecidableEq V] [Fintype K]
  [Fintype Ω] [Fintype d] [DecidableEq d]

structure JointScheme (S : V → HermitianMat d ℂ) where
  context : K → Finset V
  measurement : K → POVM Ω d
  sign : K → V → Ω → ℝ
  sign_sq : ∀ k i s,(sign k i s)^2=if i∈context k then 1 else 0
  marginal : ∀ k i,(∑ s,sign k i s • (measurement k).mats s)=if i∈context k then S i else 0

def inclusion {S : V → HermitianMat d ℂ} (M : JointScheme (K:=K) (Ω:=Ω) S)
    (q : K → ℝ) (i : V) : ℝ := ∑ k,q k*(if i∈M.context k then 1 else 0)

def bornLaw {S : V → HermitianMat d ℂ} (M : JointScheme (K:=K) (Ω:=Ω) S)
    (q : K → ℝ) (ρ : MState d) (ω : K×Ω) : ℝ :=
  q ω.1*(((M.measurement ω.1).measure ρ) ω.2 : ℝ)

omit [Fintype V] [Fintype K] in

theorem bornLaw_nonneg {S : V → HermitianMat d ℂ} (M : JointScheme (K:=K) (Ω:=Ω) S)
    (q : K → ℝ) (hq : ∀ k,0 ≤ q k) (ρ : MState d) (ω : K×Ω) :
    0 ≤ bornLaw M q ρ ω := mul_nonneg (hq ω.1) (((M.measurement ω.1).measure ρ) ω.2).property.1

omit [Fintype V] in

theorem bornLaw_normalized {S : V → HermitianMat d ℂ} (M : JointScheme (K:=K) (Ω:=Ω) S)
    (q : K → ℝ) (hq : ∑ k,q k=1) (ρ : MState d) : ∑ ω,bornLaw M q ρ ω=1 := by
  unfold bornLaw
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum,ProbDistribution.normalized,mul_one]
  exact hq

omit [Fintype V] in

theorem born_sign_second {S : V → HermitianMat d ℂ} (M : JointScheme (K:=K) (Ω:=Ω) S)
    (q : K → ℝ) (ρ : MState d) (i : V) :
    second (bornLaw M q ρ) (fun ω => M.sign ω.1 i ω.2)=inclusion M q i := by
  unfold second mean bornLaw inclusion
  rw [Fintype.sum_prod_type]
  simp_rw [M.sign_sq,mul_assoc,← Finset.mul_sum,← Finset.sum_mul,ProbDistribution.normalized,one_mul]

omit [Fintype V] in

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

theorem born_score_unbiased {S : V → HermitianMat d ℂ} (M : JointScheme (K:=K) (Ω:=Ω) S)
    (q : K → ℝ) (ρ : MState d) (c : V → ℝ) (hp : ∀ i,inclusion M q i≠0) :
    mean (bornLaw M q ρ) (fun ω => ∑ i,c i*M.sign ω.1 i ω.2/inclusion M q i)=
      ∑ i,c i*ρ.exp_val (S i) :=
  mean_score _ _ _ _ _ hp (born_sign_mean M q ρ)

theorem born_score_variance_le {S : V → HermitianMat d ℂ} (M : JointScheme (K:=K) (Ω:=Ω) S)
    (q : K → ℝ) (hq : ∀ k,0 ≤ q k) (hn : ∑ k,q k=1) (ρ : MState d)
    (c : V → ℝ) (hp : ∀ i,0 < inclusion M q i) :
    variance (bornLaw M q ρ) (fun ω => ∑ i,c i*M.sign ω.1 i ω.2/inclusion M q i) ≤
      (∑ i,|c i|/Real.sqrt (inclusion M q i))^2 :=
  variance_score_le _ (bornLaw_nonneg M q hq ρ) (bornLaw_normalized M q hn ρ)
    _ _ _ hp (born_sign_second M q ρ)

end Qatlib.Foundations.FiniteStats.BornEstimator
