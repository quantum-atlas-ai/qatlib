/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.GraphFraction.CoverLP.PowerAllocation
import Qatlib.Foundations.FiniteStats.BornEstimator.SecondMoment
import Qatlib.Foundations.FiniteStats.BornEstimator.IndependentShots
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ShadowTomog26.EnergyEstimate
open scoped Classical BigOperators
open Qatlib.Foundations.GraphFraction.CoverLP
open Qatlib.Foundations.FiniteStats.BornEstimator
variable {V Ω d : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype Ω] [Fintype d] [DecidableEq d]

omit [Nonempty V] in

theorem inclusion_eq_coverage (G : SimpleGraph V) {S : V → HermitianMat d ℂ}
    (M : JointScheme (K:=Context G) (Ω:=Ω) S)
    (hM : ∀ I,M.context I=I.val) (q : Context G → ℝ) (i : V) :
    inclusion M q i=coverage G q i := by
  unfold inclusion coverage incidence
  simp_rw [hM]

def energyScore (G : SimpleGraph V) {S : V → HermitianMat d ℂ}
    (M : JointScheme (K:=Context G) (Ω:=Ω) S) (q : Context G → ℝ)
    (c : V → ℝ) (ω : Context G×Ω) : ℝ := ∑ i,c i*M.sign ω.1 i ω.2/inclusion M q i

theorem optimal_born_energy_estimator (G : SimpleGraph V) {S : V → HermitianMat d ℂ}
    (M : JointScheme (K:=Context G) (Ω:=Ω) S) (hM : ∀ I,M.context I=I.val)
    (c : V → ℝ) (hc : ∀ i,c i≠0) (N : ℕ) (hN : 0<N) :
    let C : ℝ := ∑ i,|c i|^((2:ℝ)/3)
    let a : V → ℝ := fun i => |c i|^((2:ℝ)/3)/C
    ∃ q : Context G → ℝ,q∈stdSimplex ℝ (Context G) ∧
      (∀ i,0 < inclusion M q i) ∧
      ∀ ρ : MState d,
        (mean (shotLaw (bornLaw M q ρ) N) (shotAverage (energyScore G M q c) N)=
          ∑ i,c i*ρ.exp_val (S i)) ∧
        variance (shotLaw (bornLaw M q ρ) N) (shotAverage (energyScore G M q c) N) ≤
          coverValue G a*C^3/(N:ℝ) := by
  (try dsimp only)
  obtain ⟨hχ,q,hq,hp,hcov,hamp⟩ := attained_power_strategy G c hc
  have hi : ∀ i,0 < inclusion M q i := by
    intro i
    rw [inclusion_eq_coverage G M hM]
    exact hp i
  refine ⟨q,hq,hi,?_⟩
  intro ρ
  have hn := bornLaw_normalized M q hq.2 ρ
  constructor
  · rw [shotAverage_mean _ _ hn N hN]
    exact born_score_unbiased M q ρ c (fun i => (hi i).ne')
  · rw [shotAverage_variance _ _ hn N hN]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    have hv := born_score_variance_le M q hq.1 hq.2 ρ c hi
    change variance (bornLaw M q ρ) (energyScore G M q c) ≤ _ at hv
    exact hv.trans (by simpa only [inclusion_eq_coverage G M hM] using hamp)

theorem optimal_born_operator_estimator [Nonempty d] (G : SimpleGraph V) {S : V → HermitianMat d ℂ}
    (M : JointScheme (K:=Context G) (Ω:=Ω) S) (hM : ∀ I,M.context I=I.val)
    (c : V → ℝ) (hc : ∀ i,c i≠0) (N : ℕ) (hN : 0<N) :
    let C : ℝ := ∑ i,|c i|^((2:ℝ)/3)
    let a : V → ℝ := fun i => |c i|^((2:ℝ)/3)/C
    ∃ q : Context G → ℝ,q∈stdSimplex ℝ (Context G) ∧ (∀ i,0 < inclusion M q i) ∧
      0 ≤ secondOperator M q (energyScore G M q c) ∧
      largestEigenvalue (secondOperator M q (energyScore G M q c)) ≤ coverValue G a*C^3 ∧
      ∀ ρ : MState d,
        mean (shotLaw (bornLaw M q ρ) N) (shotAverage (energyScore G M q c) N)=∑ i,c i*ρ.exp_val (S i) ∧
        variance (shotLaw (bornLaw M q ρ) N) (shotAverage (energyScore G M q c) N)=
          (ρ.exp_val (secondOperator M q (energyScore G M q c))-(∑ i,c i*ρ.exp_val (S i))^2)/(N:ℝ) ∧
        variance (shotLaw (bornLaw M q ρ) N) (shotAverage (energyScore G M q c) N) ≤
          largestEigenvalue (secondOperator M q (energyScore G M q c))/(N:ℝ) := by
  (try dsimp only)
  obtain ⟨hχ,q,hq,hp,hcov,hamp⟩ := attained_power_strategy G c hc
  have hi : ∀ i,0 < inclusion M q i := by
    intro i
    rw [inclusion_eq_coverage G M hM]
    exact hp i
  refine ⟨q,hq,hi,secondOperator_nonneg M q hq.1 _,?_,?_⟩
  · exact (largest_score_operator_le M q hq.1 c hi).trans
      (by simpa only [inclusion_eq_coverage G M hM] using hamp)
  · intro ρ
    have hmean := born_score_unbiased M q ρ c (fun i => (hi i).ne')
    refine ⟨?_,?_,born_average_variance_le_largest M q hq.2 ρ _ N hN⟩
    · rw [shotAverage_mean _ _ (bornLaw_normalized M q hq.2 ρ) N hN]
      exact hmean
    · rw [born_average_variance_operator M q hq.2 ρ _ N hN]
      change (_-(mean (bornLaw M q ρ) (fun ω => ∑ i,c i*M.sign ω.1 i ω.2/inclusion M q i))^2)/_= _
      rw [hmean]

end Qatlib.Papers.ShadowTomog26.EnergyEstimate
