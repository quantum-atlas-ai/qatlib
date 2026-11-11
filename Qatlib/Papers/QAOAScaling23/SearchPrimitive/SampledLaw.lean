/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.SearchPrimitive.ActualTrial

/-!
# Preserving output factors under finite-coin sampling

`coin_factor` shows that a common event-probability factor across attempted laws is preserved by
fuel-limited finite-coin sampling. Applying this to amplification trials gives the marked-output
factorization for the native sampled experiment.

This development accompanies the study of QAOA-assisted minimum finding in [ShaydulinEtAl2024].

## Main statements

* `coin_factor`: If every attempted law has event `P` equal to event `Q` times a common factor
  `c`, the corresponding successful-output events retain that factor after finite-coin sampling.
* `sampled_biased_law`: For marked `i` and marked mass `sin θ` squared with `0 < θ < π/2`, the
  sampled probability of `i` equals the total marked-candidate probability times its relative
  prepared Born weight.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical ENNReal
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
namespace Qatlib.Papers.QAOAScaling23.SearchPrimitive

/-- If every attempted law has event `P` equal to event `Q` times a common factor `c`, the
corresponding successful-output events retain that factor after finite-coin sampling. -/
theorem coin_factor {A : Type} (b m fuel : ℕ) (F : Fin m→CostedLaw A)
    (P Q : A→Prop) (c : ℝ≥0∞)
    (h : ∀j,event (F j) (fun y=>P y.1)=event (F j) (fun y=>Q y.1)*c) :
    event (finiteCoinThenAttempt b m fuel F) (fun z=>∃a,z.1=some a ∧ P a)=
      event (finiteCoinThenAttempt b m fuel F) (fun z=>∃a,z.1=some a ∧ Q a)*c := by
  rw [finite_coin_attempt_event,finite_coin_attempt_event,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [h j,mul_assoc]

/-- For marked `i` and marked mass `sin θ` squared with `0 < θ < π/2`, the sampled probability
of `i` equals the total marked-candidate probability times its relative prepared Born
weight. -/
theorem sampled_biased_law {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (S : Finset I)
    (θ : ℝ) (hθ0 : 0<θ) (hθ1 : θ<Real.pi/2)
    (hmass : MeasureProb (preparedAAState U seed) S=(Real.sin θ)^2)
    (b m fuel : ℕ) (i : I) (hi : i∈S) :
    event (preparedAASampled U hU seed S b m fuel) (fun z=>∃g,z.1=some (i,g))=
      event (preparedAASampled U hU seed S b m fuel)
        (fun z=>∃y g,z.1=some (y,g) ∧ y∈S)*
      ENNReal.ofReal (BornProb (preparedAAState U seed) i/MeasureProb (preparedAAState U seed) S) := by
  have hL : ∀z : Option (I×ℕ)×ℕ×ℕ,
      (∃g,z.1=some (i,g))↔(∃a,z.1=some a ∧ a.1=i) := by
    intro z
    constructor
    · rintro ⟨g,hg⟩
      exact ⟨(i,g),hg,rfl⟩
    · rintro ⟨a,ha,hai⟩
      exact ⟨a.2,by simpa only [← hai] using ha⟩
  have hR : ∀z : Option (I×ℕ)×ℕ×ℕ,
      (∃y g,z.1=some (y,g) ∧ y∈S)↔(∃a,z.1=some a ∧ a.1∈S) := by
    intro z
    constructor
    · rintro ⟨y,g,hz,hy⟩
      exact ⟨(y,g),hz,hy⟩
    · rintro ⟨a,ha,hai⟩
      exact ⟨a.1,a.2,ha,hai⟩
  rw [event_congr hL,event_congr hR]
  exact coin_factor b m fuel (fun j=>preparedAATrial U hU seed S j)
    (fun a : I×ℕ=>a.1=i) (fun a : I×ℕ=>a.1∈S) _
    (fun j=>trial_biased_law U hU seed S θ hθ0 hθ1 hmass j i hi)
end Qatlib.Papers.QAOAScaling23.SearchPrimitive
