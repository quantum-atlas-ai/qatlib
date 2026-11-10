/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.NestedPreparation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn
open Qatlib.Papers.MonteCarloInt20.QaeLaw.Payoff
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.MonteCarloInt20.MainResults.NestedAccuracy

def nestedMean {I : Type} [Fintype I] [DecidableEq I]
    (n M : ℕ) (hM : 2 ≤ M) (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I)
    (hA : ∀ j,A j ∈ unitaryGroup I ℂ) (D : ℝ) (g : ℝ → ℝ) : ℝ :=
  (1/(2:ℝ)^n)*∑ j : Reg n,∑ k : Fin M,(aeLaw M (A j) i₀ (S j) (hA j) hM).prob k*g (D*aeEstimate M k)

def idealMean (n : ℕ) (θ : Reg n → ℝ) (D : ℝ) (g : ℝ → ℝ) : ℝ :=
  (1/(2:ℝ)^n)*∑ j : Reg n,g (D*target (θ j))

def nestedLaw {I : Type} [Fintype I] [DecidableEq I]
    (n M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I)
    (hA : ∀ j,A j ∈ unitaryGroup I ℂ) (D : ℝ) (g : ℝ → ℝ)
    (hg : ∀ k : Fin M,g (D*aeEstimate M k) ∈ Set.Icc (0:ℝ) 1) : FinDist (Fin N) :=
  meanLaw N (samplePreparation n M A i₀ S) (ZeroStr n,innerSeed M (by omega) i₀)
    (fun p => g (D*aeEstimate M p.2.1)) (samplePreparation_unitary n M hM A i₀ S hA)
    (fun p => hg p.2.1) hN

def outerWindow (N : ℕ) (μ : ℝ) : ℝ :=
  2*Real.pi*Real.sqrt (μ*(1-μ))/(N:ℝ)+Real.pi^2/(N:ℝ)^2

theorem sample_mean_identity {I : Type} [Fintype I] [DecidableEq I]
    (n M : ℕ) (hM : 2 ≤ M) (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I)
    (hA : ∀ j,A j ∈ unitaryGroup I ℂ) (D : ℝ) (g : ℝ → ℝ)
    (hg : ∀ k : Fin M,g (D*aeEstimate M k) ∈ Set.Icc (0:ℝ) 1) :
    (∑ p,BornProb (ApplyGate (samplePreparation n M A i₀ S)
      (Ket (ZeroStr n,innerSeed M (by omega) i₀))) p*g (D*aeEstimate M p.2.1))=
      nestedMean n M hM A i₀ S hA D g := by
  have h := (payoff_actual_rotation_and_mean (samplePreparation n M A i₀ S)
    (ZeroStr n,innerSeed M (by omega) i₀) (fun p => g (D*aeEstimate M p.2.1))
    (samplePreparation_unitary n M hM A i₀ S hA) (fun p => hg p.2.1)).2
  exact h.symm.trans (nested_flag_born n M hM A i₀ S hA D g hg)

theorem nested_bhmt {I : Type} [Fintype I] [DecidableEq I]
    (n M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I)
    (hA : ∀ j,A j ∈ unitaryGroup I ℂ) (D : ℝ) (g : ℝ → ℝ)
    (hg : ∀ k : Fin M,g (D*aeEstimate M k) ∈ Set.Icc (0:ℝ) 1) :
    8/Real.pi^2 ≤ ∑ z ∈ Finset.univ.filter (fun z : Fin N =>
      |aeEstimate N z-nestedMean n M hM A i₀ S hA D g| ≤
        outerWindow N (nestedMean n M hM A i₀ S hA D g)),
      (nestedLaw n M N hM hN A i₀ S hA D g hg).prob z := by
  have h := quantum_mean_actual_ae_accuracy N hN (samplePreparation n M A i₀ S)
    (ZeroStr n,innerSeed M (by omega) i₀) (fun p => g (D*aeEstimate M p.2.1))
    (samplePreparation_unitary n M hM A i₀ S hA) (fun p => hg p.2.1)
  (try dsimp only at h)
  rw [sample_mean_identity n M hM A i₀ S hA D g hg] at h
  exact h

def innerBudget (n M : ℕ) (θ : Reg n → ℝ) (D : ℝ) (gp : ℝ → ℝ) (K : NNReal) : ℝ :=
  (1/(2:ℝ)^n)*∑ j : Reg n,(|gp (D*target (θ j))| *|D|+(K:ℝ)*D^2)/(M:ℝ)

theorem nested_inner_bias {I : Type} [Fintype I] [DecidableEq I]
    (n M : ℕ) (hM : 2 ≤ M) (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I)
    (hA : ∀ j,A j ∈ unitaryGroup I ℂ) (θ : Reg n → ℝ)
    (hθ0 : ∀ j,0 < θ j) (hθ1 : ∀ j,θ j < 1/2)
    (ha : ∀ j,MeasureProb (preparedAAState (A j) i₀) (S j)=Real.sin (θ j*Real.pi)^2)
    (D : ℝ) (g gp : ℝ → ℝ) (K : NNReal)
    (hg : ∀ x,HasDerivAt g (gp x) x) (hgp : LipschitzWith K gp) :
    |nestedMean n M hM A i₀ S hA D g-idealMean n θ D g| ≤ innerBudget n M θ D gp K := by
  unfold nestedMean idealMean innerBudget
  rw [← mul_sub,← Finset.sum_sub_distrib,abs_mul,abs_of_nonneg (show 0 ≤ 1/(2:ℝ)^n by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  exact Qatlib.Papers.MonteCarloInt20.QaeLaw.Actual.actual_smooth_payoff_error M hM (A j) i₀ (S j) (hA j)
    (θ j) (hθ0 j) (hθ1 j) (ha j) D g gp K hg hgp

theorem nested_total_error {I : Type} [Fintype I] [DecidableEq I]
    (n M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I)
    (hA : ∀ j,A j ∈ unitaryGroup I ℂ) (θ : Reg n → ℝ)
    (hθ0 : ∀ j,0 < θ j) (hθ1 : ∀ j,θ j < 1/2)
    (ha : ∀ j,MeasureProb (preparedAAState (A j) i₀) (S j)=Real.sin (θ j*Real.pi)^2)
    (D : ℝ) (g gp : ℝ → ℝ) (K : NNReal)
    (hg : ∀ x,HasDerivAt g (gp x) x) (hgp : LipschitzWith K gp)
    (hrange : ∀ k : Fin M,g (D*aeEstimate M k) ∈ Set.Icc (0:ℝ) 1) :
    8/Real.pi^2 ≤ ∑ z ∈ Finset.univ.filter (fun z : Fin N =>
      |aeEstimate N z-idealMean n θ D g| ≤
        outerWindow N (nestedMean n M hM A i₀ S hA D g)+innerBudget n M θ D gp K),
      (nestedLaw n M N hM hN A i₀ S hA D g hrange).prob z := by
  have hinner := nested_inner_bias n M hM A i₀ S hA θ hθ0 hθ1 ha D g gp K hg hgp
  have hs : Finset.univ.filter (fun z : Fin N =>
      |aeEstimate N z-nestedMean n M hM A i₀ S hA D g| ≤ outerWindow N (nestedMean n M hM A i₀ S hA D g)) ⊆
      Finset.univ.filter (fun z : Fin N => |aeEstimate N z-idealMean n θ D g| ≤
        outerWindow N (nestedMean n M hM A i₀ S hA D g)+innerBudget n M θ D gp K) := by
    intro z hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have hz' := (Finset.mem_filter.mp hz).2
    have ht := abs_sub_le (aeEstimate N z) (nestedMean n M hM A i₀ S hA D g) (idealMean n θ D g)
    linarith
  exact (nested_bhmt n M N hM hN A i₀ S hA D g hrange).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hs (fun z _ _ =>
      (nestedLaw n M N hM hN A i₀ S hA D g hrange).nonneg z))

end Qatlib.Papers.MonteCarloInt20.MainResults.NestedAccuracy
