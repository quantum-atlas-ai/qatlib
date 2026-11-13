/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.Convert
import Qatlib.Concepts.QsvtCore.HamiltonianSim.HermitianEvolutionLipschitzStat
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NoncommRing
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Lipschitz continuity of Hermitian evolution

This module proves `HermitianEvolutionLipschitz`: replacing a finite Hermitian Hamiltonian by
another changes its time evolution by at most the Hamiltonian distance times the absolute time.
The mathematical background is developed in [GilyenSuLowWiebe2019].

## Main statements

* `hermitianEvolutionLipschitz_answer`: the operator norm perturbation estimate for Hermitian
  evolution.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QsvtCore.HamiltonianSim

open Matrix
open scoped Matrix.Norms.L2Operator

set_option maxHeartbeats 1000000 in

/-- Hermitian time evolution satisfies `‖HamiltonianEvolution H t - HamiltonianEvolution H' t‖ ≤
|t| * ‖H - H'‖`, as in [Gilyén et al., Lemma 61][GilyenSuLowWiebe2019]. -/
theorem hermitianEvolutionLipschitz_answer : HermitianEvolutionLipschitz := by
  intro I _ _ H H' hH hH' t
  have hcoe : ∀ s : ℝ, (Complex.ofReal s) = s • (1:ℂ) := by
    intro s
    simp [mul_one]
  have hE : ∀ s : ℝ, Qatlib.Foundations.PureStateMath.HamiltonianEvolution H s
      = NormedSpace.exp (s • ((-Complex.I) • H)) := by
    intro s
    unfold Qatlib.Foundations.PureStateMath.HamiltonianEvolution
    rw [mul_comm, mul_smul]
    have h1 : (Complex.ofReal s) = s • (1:ℂ) := hcoe s
    rw [h1, IsScalarTower.smul_assoc, one_smul]
  have hE' : ∀ s : ℝ, Qatlib.Foundations.PureStateMath.HamiltonianEvolution H' s
      = NormedSpace.exp (s • ((-Complex.I) • H')) := by
    intro s
    unfold Qatlib.Foundations.PureStateMath.HamiltonianEvolution
    rw [mul_comm, mul_smul]
    have h1 : (Complex.ofReal s) = s • (1:ℂ) := hcoe s
    rw [h1, IsScalarTower.smul_assoc, one_smul]
  have hXD : ((-Complex.I) • (H - H'))
      = ((-Complex.I) • H) - ((-Complex.I) • H') := smul_sub _ _ _
  have hdU : ∀ s : ℝ, HasDerivAt (fun u => NormedSpace.exp (u • ((-Complex.I) • H)))
      (NormedSpace.exp (s • ((-Complex.I) • H)) * ((-Complex.I) • H)) s :=
    fun s => hasDerivAt_exp_smul_const _ s
  have hdU' : ∀ s : ℝ, HasDerivAt (fun u => NormedSpace.exp (u • ((-Complex.I) • H')))
      (((-Complex.I) • H') * NormedSpace.exp (s • ((-Complex.I) • H'))) s :=
    fun s => hasDerivAt_exp_smul_const' _ s
  have hd2 : ∀ s : ℝ, HasDerivAt (fun u => NormedSpace.exp ((t - u) • ((-Complex.I) • H')))
      ((-1:ℝ) • (((-Complex.I) • H') * NormedSpace.exp ((t - s) • ((-Complex.I) • H')))) s := by
    intro s
    convert! (hdU' (t - s)).scomp s
      (HasDerivAt.sub (hasDerivAt_const s t) (hasDerivAt_id s)) using 1
    try simp
  have hF : ∀ s : ℝ, HasDerivAt
      (fun u => NormedSpace.exp (u • ((-Complex.I) • H)) *
        NormedSpace.exp ((t - u) • ((-Complex.I) • H')))
      (NormedSpace.exp (s • ((-Complex.I) • H)) *
        (((-Complex.I) • H - (-Complex.I) • H') *
          NormedSpace.exp ((t - s) • ((-Complex.I) • H')))) s := by
    intro s
    have h1 := (hdU s).mul (hd2 s)
    have h2 : NormedSpace.exp (s • ((-Complex.I) • H)) * ((-Complex.I) • H) *
        NormedSpace.exp ((t - s) • ((-Complex.I) • H')) +
        NormedSpace.exp (s • ((-Complex.I) • H)) *
        ((-1:ℝ) • (((-Complex.I) • H') *
          NormedSpace.exp ((t - s) • ((-Complex.I) • H'))))
        = NormedSpace.exp (s • ((-Complex.I) • H)) *
        (((-Complex.I) • H - (-Complex.I) • H') *
          NormedSpace.exp ((t - s) • ((-Complex.I) • H'))) := by
      rw [neg_one_smul, mul_neg]
      noncomm_ring
    rw [← h2]
    exact h1
  have hcont1 : Continuous (fun s : ℝ => NormedSpace.exp (s • ((-Complex.I) • H))) := by
    have hd1 : Differentiable ℝ (fun s : ℝ => NormedSpace.exp (s • ((-Complex.I) • H))) :=
      fun s => (hdU s).differentiableAt
    exact hd1.continuous
  have hcont3 : Continuous (fun u : ℝ => NormedSpace.exp (u • ((-Complex.I) • H'))) := by
    have hd3 : Differentiable ℝ (fun u : ℝ => NormedSpace.exp (u • ((-Complex.I) • H'))) :=
      fun s => (hdU' s).differentiableAt
    exact hd3.continuous
  have hcont2 : Continuous (fun s : ℝ => NormedSpace.exp ((t - s) • ((-Complex.I) • H'))) :=
    hcont3.comp (continuous_const.sub continuous_id)
  have hcontF' : Continuous (fun s : ℝ => NormedSpace.exp (s • ((-Complex.I) • H)) *
      (((-Complex.I) • H - (-Complex.I) • H') *
        NormedSpace.exp ((t - s) • ((-Complex.I) • H')))) :=
    hcont1.mul (continuous_const.mul hcont2)
  have hFt : (fun u : ℝ => NormedSpace.exp (u • ((-Complex.I) • H)) *
      NormedSpace.exp ((t - u) • ((-Complex.I) • H'))) t
      = NormedSpace.exp (t • ((-Complex.I) • H)) := by
    simp only [sub_self, zero_smul, NormedSpace.exp_zero, mul_one]
  have hF0 : (fun u : ℝ => NormedSpace.exp (u • ((-Complex.I) • H)) *
      NormedSpace.exp ((t - u) • ((-Complex.I) • H'))) 0
      = NormedSpace.exp (t • ((-Complex.I) • H')) := by
    simp only [sub_zero, zero_smul, NormedSpace.exp_zero, one_mul]
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u : ℝ => NormedSpace.exp (u • ((-Complex.I) • H)) *
      NormedSpace.exp ((t - u) • ((-Complex.I) • H')))
    (f' := fun s : ℝ => NormedSpace.exp (s • ((-Complex.I) • H)) *
      (((-Complex.I) • H - (-Complex.I) • H') *
        NormedSpace.exp ((t - s) • ((-Complex.I) • H'))))
    (a := 0) (b := t)
    (fun s _ => hF s) (hcontF'.intervalIntegrable 0 t)
  dsimp only at hFt hF0
  rw [hFt, hF0] at hint
  have hunit : ∀ s : ℝ, Qatlib.Foundations.PureStateMath.HamiltonianEvolution H s ∈ Matrix.unitaryGroup I ℂ :=
    fun s => Qatlib.Foundations.PureStateMath.hamiltonianEvolution_unitary hH s
  have hunit' : ∀ s : ℝ, Qatlib.Foundations.PureStateMath.HamiltonianEvolution H' s ∈ Matrix.unitaryGroup I ℂ :=
    fun s => Qatlib.Foundations.PureStateMath.hamiltonianEvolution_unitary hH' s
  have hnb : ∀ s : ℝ, ‖NormedSpace.exp (s • ((-Complex.I) • H)) *
      (((-Complex.I) • H - (-Complex.I) • H') *
        NormedSpace.exp ((t - s) • ((-Complex.I) • H')))‖ ≤ ‖H - H'‖ := by
    intro s
    rw [CStarRing.norm_mem_unitary_mul
        (((-Complex.I) • H - (-Complex.I) • H') *
          NormedSpace.exp ((t - s) • ((-Complex.I) • H')))
        (by rw [← hE s]; exact hunit s),
      CStarRing.norm_mul_mem_unitary ((-Complex.I) • H - (-Complex.I) • H')
        (by rw [← hE' (t - s)]; exact hunit' (t - s)),
      ← hXD, norm_smul, norm_neg, Complex.norm_I, one_mul]
  have hfin : ‖(∫ s : ℝ in 0..t, NormedSpace.exp (s • ((-Complex.I) • H)) *
      (((-Complex.I) • H - (-Complex.I) • H') *
        NormedSpace.exp ((t - s) • ((-Complex.I) • H'))))‖ ≤ ‖H - H'‖ * |t - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ => hnb s)
  rw [hE t, hE' t, ← hint]
  exact le_trans hfin (by rw [sub_zero, mul_comm])

end Qatlib.Concepts.QsvtCore.HamiltonianSim
