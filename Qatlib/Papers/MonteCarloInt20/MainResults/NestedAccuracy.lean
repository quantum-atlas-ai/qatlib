/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.NestedPreparation

/-!
# Bias and success bounds for nested amplitude estimation

`nestedMean` is the uniform sample average of the payoff evaluated under each actual inner
amplitude-estimation law. `nestedLaw` applies outer amplitude estimation to this payoff
preparation, formalizing the nested construction associated with [KanekoEtAl2020].

The error bounds separate the outer estimation window from the inner bias. The latter uses a
differentiable payoff with Lipschitz derivative and interior phase parameters.

## Main statements

* `nested_bhmt`: bounds the outer estimation error with probability at least `8 / π²`.
* `nested_inner_bias`: bounds the difference from `idealMean` by `innerBudget`.
* `nested_total_error`: combines the outer window and inner bias.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

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

/-- The uniform sample average of the payoff expectations under the actual inner
amplitude-estimation output laws. -/
def nestedMean {I : Type} [Fintype I] [DecidableEq I]
    (n M : ℕ) (hM : 2 ≤ M) (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I)
    (hA : ∀ j,A j ∈ unitaryGroup I ℂ) (D : ℝ) (g : ℝ → ℝ) : ℝ :=
  (1/(2:ℝ)^n)*∑ j : Reg n,∑ k : Fin M,(aeLaw M (A j) i₀ (S j) (hA j) hM).prob k*g (D*aeEstimate M k)

/-- The uniform sample average of `g` applied to `D` times the phase target. -/
def idealMean (n : ℕ) (θ : Reg n → ℝ) (D : ℝ) (g : ℝ → ℝ) : ℝ :=
  (1/(2:ℝ)^n)*∑ j : Reg n,g (D*target (θ j))

/-- The outer amplitude-estimation law for the coherent sample and inner-estimate payoff
preparation, assuming payoff values lie in `[0, 1]`. -/
def nestedLaw {I : Type} [Fintype I] [DecidableEq I]
    (n M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (A : Reg n → Matrix I I ℂ) (i₀ : I) (S : Reg n → Finset I)
    (hA : ∀ j,A j ∈ unitaryGroup I ℂ) (D : ℝ) (g : ℝ → ℝ)
    (hg : ∀ k : Fin M,g (D*aeEstimate M k) ∈ Set.Icc (0:ℝ) 1) : FinDist (Fin N) :=
  meanLaw N (samplePreparation n M A i₀ S) (ZeroStr n,innerSeed M (by omega) i₀)
    (fun p => g (D*aeEstimate M p.2.1)) (samplePreparation_unitary n M hM A i₀ S hA)
    (fun p => hg p.2.1) hN

/-- The amplitude-estimation error window `2 * π * √(μ * (1 - μ)) / N + π ^ 2 / N ^ 2`. -/
def outerWindow (N : ℕ) (μ : ℝ) : ℝ :=
  2*Real.pi*Real.sqrt (μ*(1-μ))/(N:ℝ)+Real.pi^2/(N:ℝ)^2

/-- The Born-weighted payoff expectation of the coherent sample preparation equals `nestedMean`. -/
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

/-- For `M, N ≥ 2`, unitary sample preparations, and payoff values in `[0, 1]`, the outer
estimate lies within `outerWindow` of `nestedMean` with probability at least `8 / π²`. -/
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

/-- The sample average of the derivative and Lipschitz-remainder bounds on inner payoff bias,
divided by `M`. -/
def innerBudget (n M : ℕ) (θ : Reg n → ℝ) (D : ℝ) (gp : ℝ → ℝ) (K : NNReal) : ℝ :=
  (1/(2:ℝ)^n)*∑ j : Reg n,(|gp (D*target (θ j))| *|D|+(K:ℝ)*D^2)/(M:ℝ)

/-- For `M ≥ 2`, phases strictly between zero and one half encoding the preparation
probabilities, and a payoff with the stated Lipschitz derivative, the difference between
`nestedMean` and `idealMean` is at most `innerBudget`. -/
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

/-- Under the stated unitary, interior-phase, smoothness, and payoff-range hypotheses with `M, N
≥ 2`, the outer estimate lies within `outerWindow` plus `innerBudget` of `idealMean` with
probability at least `8 / π²`. -/
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
