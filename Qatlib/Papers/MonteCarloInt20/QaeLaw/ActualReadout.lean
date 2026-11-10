/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.QaeLaw.SmoothPayoff
import Qatlib.Papers.MonteCarloInt20.QaeLaw.StepPayoff
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix
open Qatlib.Papers.MonteCarloInt20.QaeLaw.Fourier Qatlib.Papers.MonteCarloInt20.QaeLaw.Payoff
open Qatlib.Papers.MonteCarloInt20.QaeLaw.Smooth Qatlib.Papers.MonteCarloInt20.QaeLaw.Step
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.MonteCarloInt20.QaeLaw.Actual

theorem estimate_eq_aeEstimate (M : ℕ) (k : Fin M) : estimate M k=aeEstimate M k := by
  unfold estimate aeEstimate
  congr 2
  ring

theorem actual_smooth_payoff_error {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1/2)
    (ha : MeasureProb (preparedAAState A j) S=Real.sin (θ*Real.pi)^2)
    (D : ℝ) (g gp : ℝ → ℝ) (K : NNReal)
    (hg : ∀ x,HasDerivAt g (gp x) x) (hgp : LipschitzWith K gp) :
    |(∑ k,(aeLaw M A j S hA hM).prob k*g (D*aeEstimate M k))-g (D*target θ)| ≤
      (|gp (D*target θ)| *|D|+(K:ℝ)*D^2)/(M:ℝ) := by
  have he : (∑ k,(aeLaw M A j S hA hM).prob k*g (D*aeEstimate M k))=
      ∑ k,rawMass M θ k*g (D*estimate M k) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [actual_prepared_qae_law M hM A j S hA θ hθ0 hθ1 ha,estimate_eq_aeEstimate]
  rw [he]
  exact smooth_payoff_error M θ D (by omega) g gp K hg hgp

theorem actual_quadratic_payoff_error {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1/2)
    (ha : MeasureProb (preparedAAState A j) S=Real.sin (θ*Real.pi)^2) (D : ℝ) :
    |(∑ k,(aeLaw M A j S hA hM).prob k*(D*aeEstimate M k)^2)-(D*target θ)^2| ≤
      (|2*(D*target θ)| *|D|+2*D^2)/(M:ℝ) := by
  apply actual_smooth_payoff_error M hM A j S hA θ hθ0 hθ1 ha D (fun x => x^2) (fun x => 2*x) 2
  · intro x
    simpa using! (hasDerivAt_id x).pow 2
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq,Real.dist_eq,← mul_sub,abs_mul]
    norm_num

theorem actual_step_payoff_error {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1/2)
    (ha : MeasureProb (preparedAAState A j) S=Real.sin (θ*Real.pi)^2)
    (D τ δ : ℝ) (hδ : 0 < δ) (hmargin : δ ≤ |D*target θ-τ|) :
    |(∑ k,(aeLaw M A j S hA hM).prob k*strictStep τ (D*aeEstimate M k))-strictStep τ (D*target θ)| ≤
      D^2/((M:ℝ)*δ^2) := by
  have he : (∑ k,(aeLaw M A j S hA hM).prob k*strictStep τ (D*aeEstimate M k))=
      ∑ k,rawMass M θ k*strictStep τ (D*estimate M k) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [actual_prepared_qae_law M hM A j S hA θ hθ0 hθ1 ha,estimate_eq_aeEstimate]
  rw [he]
  exact step_payoff_margin_error M θ D τ δ (by omega) hδ hmargin

end Qatlib.Papers.MonteCarloInt20.QaeLaw.Actual
