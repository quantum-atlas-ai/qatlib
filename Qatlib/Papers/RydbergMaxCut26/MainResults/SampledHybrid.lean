/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.MainResults.RationalSelector
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Matrix Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.MainResults.SampledHybrid
open Qatlib.Papers.RydbergMaxCut26.MainResults.FiniteHybrid
open Qatlib.Papers.RydbergMaxCut26.MainResults.RationalSelector
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.MainResults.PauliReadout

noncomputable def joint {Ω X Y : Type*} [Fintype Ω] [Fintype X] [Fintype Y]
    (q : FinDist Ω) (r : FinDist X) (s : Ω → FinDist Y) : FinDist (Ω×(X×Y)) where
  prob z := q.prob z.1*r.prob z.2.1*(s z.1).prob z.2.2
  nonneg z := mul_nonneg (mul_nonneg (q.nonneg _) (r.nonneg _)) ((s _).nonneg _)
  sum_one := by
    simp only [Fintype.sum_prod_type,← Finset.mul_sum]
    simp only [fun ω => (s ω).sum_one,mul_one,← Finset.mul_sum,r.sum_one,q.sum_one]

theorem joint_expect {Ω X Y : Type*} [Fintype Ω] [Fintype X] [Fintype Y]
    [DecidableEq Ω] [DecidableEq X] [DecidableEq Y]
    (q : FinDist Ω) (r : FinDist X) (s : Ω → FinDist Y) (f : Ω×(X×Y) → ℝ) :
    (joint q r s).expect f=q.expect (fun ω => r.expect (fun x => (s ω).expect (fun y => f (ω,x,y)))) := by
  simp only [FinDist.expect,joint,Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

noncomputable def sampledLaw {Ω X Y : Type*} [Fintype Ω] [Fintype X] [Fintype Y]
    [DecidableEq Ω] (q : FinDist Ω) (r : FinDist X) (s : Ω → FinDist Y)
    (scoreR : X → ℚ) (scoreP : Y → ℚ) : FinDist (Ω×Bool) :=
  push (joint q r s) (fun z => (z.1,chooseQ (scoreR z.2.1) (scoreP z.2.2)))

theorem sampled_expected_error {n : ℕ} {Ω X Y : Type} [Fintype Ω] [Fintype X] [Fintype Y]
    [DecidableEq Ω] [DecidableEq X] [DecidableEq Y]
    (q : FinDist Ω) (r : FinDist X) (s : Ω → FinDist Y)
    (scoreR : X → ℚ) (scoreP : Y → ℚ) (H ρ : Matrix (Reg n) (Reg n) ℂ)
    (σ : Ω → Matrix (Reg n) (Reg n) ℂ) :
    (sampledLaw q r s scoreR scoreP).expect (fun z => energy H (outputDensity ρ σ z)) ≤
      q.expect (fun ω => min (energy H ρ) (energy H (σ ω)))+
      r.expect (fun x => |(scoreR x:ℝ)-energy H ρ|)+
      q.expect (fun ω => (s ω).expect (fun y => |(scoreP y:ℝ)-energy H (σ ω)|)) := by
  rw [sampledLaw,push_expect]
  have h := expect_mono (joint q r s)
    (fun z => energy H (outputDensity ρ σ (z.1,chooseQ (scoreR z.2.1) (scoreP z.2.2))))
    (fun z => min (energy H ρ) (energy H (σ z.1))+
      |(scoreR z.2.1:ℝ)-energy H ρ|+|(scoreP z.2.2:ℝ)-energy H (σ z.1)|)
    (fun z => by
      dsimp only [outputDensity]
      split <;> simpa only [*,ite_true,ite_false] using!
        chooseQ_error (energy H ρ) (energy H (σ z.1)) (scoreR z.2.1) (scoreP z.2.2))
  refine h.trans_eq ?_
  rw [joint_expect]
  simp only [FinDist.expect,mul_add,Finset.sum_add_distrib]
  simp only [← Finset.sum_mul,fun ω => (s ω).sum_one,r.sum_one,q.sum_one,one_mul]

noncomputable def pauliSampledLaw {n N : ℕ} {Ω E : Type} [Fintype Ω] [Fintype E] [DecidableEq Ω]
    (q : FinDist Ω) (ends : E → Fin n×Fin n) (w : E → ℚ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (σ : Ω → Matrix (Reg n) (Reg n) ℂ) (hσ : ∀ ω,(σ ω).PosSemidef ∧ (σ ω).trace=1) : FinDist (Ω×Bool) :=
  sampledLaw q (shotsLaw n N ρ hρ htr) (fun ω => shotsLaw n N (σ ω) (hσ ω).1 (hσ ω).2)
    (meanScoreQ ends w) (meanScoreQ ends w)

theorem pauli_expected_error {n N : ℕ} {Ω E : Type} [Fintype Ω] [Fintype E] [DecidableEq Ω]
    (q : FinDist Ω) (ends : E → Fin n×Fin n) (w : E → ℚ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (σ : Ω → Matrix (Reg n) (Reg n) ℂ) (hσ : ∀ ω,(σ ω).PosSemidef ∧ (σ ω).trace=1) (hN : 0<N) :
    (pauliSampledLaw (N:=N) q ends w ρ hρ htr σ hσ).expect
      (fun z => energy (qmcHamiltonian ends (fun e => (w e:ℝ))) (outputDensity ρ σ z)) ≤
      q.expect (fun ω => min (energy (qmcHamiltonian ends (fun e => (w e:ℝ))) ρ)
        (energy (qmcHamiltonian ends (fun e => (w e:ℝ))) (σ ω)))+
      Real.sqrt ((readoutLaw n ρ hρ htr).variance (fun o => (energyScoreQ ends w o:ℝ))/(N:ℝ))+
      q.expect (fun ω => Real.sqrt ((readoutLaw n (σ ω) (hσ ω).1 (hσ ω).2).variance
        (fun o => (energyScoreQ ends w o:ℝ))/(N:ℝ))) := by
  refine (sampled_expected_error q (shotsLaw n N ρ hρ htr)
    (fun ω => shotsLaw n N (σ ω) (hσ ω).1 (hσ ω).2)
    (meanScoreQ ends w) (meanScoreQ ends w) _ ρ σ).trans ?_
  exact add_le_add (add_le_add_right (readout_mean_error ends w ρ hρ htr hN) _)
    (expect_mono q _ _ (fun ω => readout_mean_error ends w (σ ω) (hσ ω).1 (hσ ω).2 hN))
end Qatlib.Papers.RydbergMaxCut26.MainResults.SampledHybrid
