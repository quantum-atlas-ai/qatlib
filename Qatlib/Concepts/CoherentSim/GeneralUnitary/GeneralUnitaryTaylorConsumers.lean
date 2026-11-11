/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.GeneralUnitary.GeneralUnitaryTaylor

/-!
# Coherent Taylor simulation for unitary decompositions

This module applies factorial Taylor simulation to unitary decompositions whose weighted sum is
Hermitian. It proves coherent accuracy and resource counts and controls the same program under
unitary oracle noise, including exact cancellation with its adjoint, using the method of
[BerryEtAl2015Taylor].

## Main statements

* `general_unitary_taylor_actual_simulation`: Coherent simulation when the weighted sum is
  Hermitian.
* `general_unitary_taylor_same_program_noise`: Perturbation bounds and exact forward-adjoint
  cancellation.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.CoherentSim.FactorialTaylor
open Qatlib.Concepts.CoherentSim.TaylorBounds
open Qatlib.Concepts.CoherentSim.TaylorEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 800000
attribute [local irreducible] Qatlib.Concepts.CoherentSim.FactorialTaylor.factorialTaylorCutoff Qatlib.Concepts.CoherentSim.FactorialTaylor.factorialTaylorPrecision
noncomputable section
namespace Qatlib.Concepts.CoherentSim.GeneralUnitary
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

omit [DecidableEq J] in

/-- The chosen segment count makes the coefficient mass times the absolute segment duration at
most `1 / 2`. -/
private theorem generalTaylor_segment_small (h : J → ℝ) (t : ℝ) (Λ T : ℕ)
    (hΛ : (∑ j, |h j|) ≤ Λ) (hT : |t| ≤ T) :
    (∑ j, |h j|) * |t / (taylorSegments Λ T : ℝ)| ≤ 1 / 2 := by
  have hs : 0 < (taylorSegments Λ T : ℝ) := by
    exact_mod_cast (taylor_actual_segment_parameters Λ T 0).2.1
  have hb : 2 * (Λ : ℝ) * (T : ℝ) ≤ (taylorSegments Λ T : ℝ) := by
    exact_mod_cast (le_max_right 1 (2 * Λ * T))
  rw [abs_div, abs_of_pos hs, ← mul_div_assoc, div_le_iff₀ hs]
  have hp : (∑ j, |h j|) * |t| ≤ (Λ : ℝ) * T :=
    mul_le_mul hΛ hT (abs_nonneg _) (Nat.cast_nonneg _)
  linarith

/-- A positive number of exact equal-duration evolution segments composes to evolution for the
total duration. -/
private theorem generalTaylor_ideal_power (H : Matrix I I ℂ) (t : ℝ) (s : ℕ) (hs : 0 < s) :
    (hamiltonianEvolution H (t / s)) ^ s = hamiltonianEvolution H t := by
  have hp : ∀ n : ℕ, (hamiltonianEvolution H (t / s)) ^ n =
      hamiltonianEvolution H ((n : ℝ) * (t / s)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ih]
        change HamiltonianEvolution H ((n : ℝ) * (t / s)) *
          HamiltonianEvolution H (t / s) = _
        rw [← hamiltonianEvolution_add]
        congr 1
        push_cast
        ring
  rw [hp]
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [mul_div_cancel₀ _ hs0]

/-- For unitary summands with Hermitian weighted sum, the factorial Taylor circuit is well
formed and has relative vector error at most `2⁻ᵏ`. The forward circuit and its adjoint have
the specified query and gate counts. See [BerryEtAl2015Taylor]. -/
theorem general_unitary_taylor_actual_simulation :
    ∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
      (h : J → ℝ) (U : J → Matrix I I ℂ) (j₀ : J) (t : ℝ) (Λ T k : ℕ),
      (∀ j, U j ∈ Matrix.unitaryGroup I ℂ) →
      (∑ j, (h j : ℂ) • U j).IsHermitian → (∑ j, |h j|) ≤ Λ → |t| ≤ T →
      let s := taylorSegments Λ T
      let K := factorialTaylorCutoff (factorialTaylorPrecision s k)
      let cs := factorialTaylorWord (I := I) h j₀ t Λ T k
      WellFormedAdjointCircuit cs ∧ adjointQueryCount cs = 3*s*K ∧
        adjointGateCount cs = s*(6*K+13) ∧
        adjointQueryCount (adjointCircuit cs) = 3*s*K ∧
        adjointGateCount (adjointCircuit cs) = s*(6*K+13) ∧
        (∀ ψ : QState I, ‖toEuclidean_fromVec
          (evaluate (taylorQuery U K) cs *ᵥ (taylorFrame j₀ K *ᵥ ψ) -
            taylorFrame j₀ K *ᵥ (hamiltonianEvolution (∑ j, (h j : ℂ) • U j) t *ᵥ ψ))‖ ≤
              (1/2 : ℝ)^k * ‖toEuclidean_fromVec ψ‖) := by
  intro J I _ _ _ _ h U j₀ t Λ T k hU hHtotal hΛ hT
  let s := taylorSegments Λ T
  let K := factorialTaylorCutoff (factorialTaylorPrecision s k)
  let H : Matrix I I ℂ := ∑ j, (h j : ℂ) • U j
  let R := taylorFrame (I := I) j₀ K
  let body := taylorLCUWord (I := I) h j₀ (t / s) K
  let O := taylorQuery U K
  let V := hamiltonianEvolution H (t / s)
  have hs : 0 < s := (taylor_actual_segment_parameters Λ T k).2.1
  have hsmall := generalTaylor_segment_small h t Λ T hΛ hT
  have hb := (taylor_lcu_actual_prepare_select_and_counts (I := I) h j₀ (t / s) K hsmall).2.1
  have hV : V ∈ Matrix.unitaryGroup I ℂ := hamiltonianEvolution_unitary hHtotal _
  have hO : O ∈ Matrix.unitaryGroup _ ℂ := taylorQuery_unitary U hU K
  let ε : ℝ := 2/((K+1).factorial : ℝ)
  have henc : BlockEncoding V (evaluate O body) R R 2 ε :=
    general_unitary_taylor_actual_segment_encoding J I h U j₀ (t/s) K hU hsmall
  have hexp := coherent_oaa_expanded_subroutine O body R hb henc.right_isometry
  have hrep := repeat_adjoint_word_semantics_cost O
    (substituteAdjointCircuit body (coherentOAAWord R)) s
  obtain ⟨hq, hg⟩ := factorialTaylor_word_counts (I := I) h j₀ t Λ T k
  refine ⟨hrep.2.2.2 hexp.2.2.2, hq, hg, by simpa using! hq, by simpa using! hg, ?_⟩
  intro ψ
  have herr := (coherent_oaa_expanded_repeat_error_and_cost O body V R
    ε hO hb hV henc s ψ).2.2
  have hideal : V ^ s = hamiltonianEvolution H t := generalTaylor_ideal_power H t s hs
  rw [hideal] at herr
  exact herr.trans
      (mul_le_mul_of_nonneg_right (factorial_taylor_tail_and_coherent_precision.2 s k) (norm_nonneg _))

/-- Unitary oracle perturbations of size `δ` give relative simulation error at most `2⁻ᵏ + 3 * s
* K * δ`, with total forward-adjoint query cost `6 * s * K`. Evaluating the adjoint after
the same perturbed forward circuit exactly recovers the embedded input. See
[BerryEtAl2015Taylor]. -/
theorem general_unitary_taylor_same_program_noise :
    ∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
      (h : J → ℝ) (U V : J → Matrix I I ℂ) (j₀ : J) (t δ : ℝ) (Λ T k : ℕ),
      (∀ j, U j ∈ Matrix.unitaryGroup I ℂ) → (∑ j, (h j : ℂ) • U j).IsHermitian →
      (∀ j, V j ∈ Matrix.unitaryGroup I ℂ) → 0 ≤ δ → (∀ j, ‖U j-V j‖ ≤ δ) →
      (∑ j, |h j|) ≤ Λ → |t| ≤ T →
      let s := taylorSegments Λ T
      let K := factorialTaylorCutoff (factorialTaylorPrecision s k)
      let cs := factorialTaylorWord (I := I) h j₀ t Λ T k
      (∀ ψ : QState I, ‖toEuclidean_fromVec
        (evaluate (taylorQuery V K) cs *ᵥ (taylorFrame j₀ K *ᵥ ψ) -
          taylorFrame j₀ K *ᵥ (hamiltonianEvolution (∑ j, (h j : ℂ) • U j) t *ᵥ ψ))‖ ≤
            ((1/2 : ℝ)^k+3*s*K*δ)*‖toEuclidean_fromVec ψ‖) ∧
      adjointQueryCount cs+adjointQueryCount (adjointCircuit cs) = 6*s*K ∧
      (∀ ψ : QState I,
        evaluate (taylorQuery V K) (adjointCircuit cs) *ᵥ
          (evaluate (taylorQuery V K) cs *ᵥ (taylorFrame j₀ K *ᵥ ψ)) =
            taylorFrame j₀ K *ᵥ ψ) := by
  intro J I _ _ _ _ h U V j₀ t δ Λ T k hU hHtotal hV hδ hUV hΛ hT
  let s := taylorSegments Λ T
  let K := factorialTaylorCutoff (factorialTaylorPrecision s k)
  let cs := factorialTaylorWord (I:=I) h j₀ t Λ T k
  let R := taylorFrame (I:=I) j₀ K
  let OU := taylorQuery U K
  let OV := taylorQuery V K
  obtain ⟨hwf,hq,_,_,_,herr⟩ := general_unitary_taylor_actual_simulation
    J I h U j₀ t Λ T k hU hHtotal hΛ hT
  have hOU := taylorQuery_unitary U hU K
  have hOV := taylorQuery_unitary V hV K
  have hop : ‖evaluate OV cs-evaluate OU cs‖ ≤ (adjointQueryCount cs:ℝ)*δ :=
    evaluate_operator_error_le_queries cs OU OV δ hwf hOU hOV hδ
      (factorialTaylor_query_noise U V K δ hδ hUV)
  refine ⟨?_, ?_, ?_⟩
  · intro ψ
    have hdiff := l2_norm_mulVec_fromVec_le (evaluate OV cs-evaluate OU cs) (R*ᵥψ)
    rw [Matrix.sub_mulVec,isometry_mulVec_norm (taylorFrame_isIsometry j₀ K) ψ] at hdiff
    have hdiff' := hdiff.trans (mul_le_mul_of_nonneg_right hop (norm_nonneg _))
    have hsplit : evaluate OV cs*ᵥ(R*ᵥψ)-R*ᵥ(hamiltonianEvolution (∑ j, (h j:ℂ) • U j) t*ᵥψ) =
        (evaluate OV cs*ᵥ(R*ᵥψ)-evaluate OU cs*ᵥ(R*ᵥψ)) +
        (evaluate OU cs*ᵥ(R*ᵥψ)-R*ᵥ(hamiltonianEvolution (∑ j, (h j:ℂ) • U j) t*ᵥψ)) := by abel
    change ‖toEuclidean_fromVec (evaluate OV cs*ᵥ(R*ᵥψ)-
      R*ᵥ(hamiltonianEvolution (∑ j, (h j:ℂ) • U j) t*ᵥψ))‖ ≤ _
    rw [hsplit]
    have hadd : ∀ a b : QState (TaylorWordLabel J K × (Bool × (J × I))), toEuclidean_fromVec (a+b) =
        toEuclidean_fromVec a + toEuclidean_fromVec b := by intros; rfl
    rw [hadd]
    have hbound := (norm_add_le _ _).trans (add_le_add hdiff' (herr ψ))
    rw [hq] at hbound
    exact hbound.trans_eq (by push_cast; ring)
  · (try dsimp only)
    change adjointQueryCount cs+adjointQueryCount (adjointCircuit cs) = 6*s*K
    have hqc : adjointQueryCount cs = 3*s*K := hq
    simp only [adjointQueryCount_adjointCircuit, hqc]
    ring
  · intro ψ
    have hunit : (evaluate OV cs)ᴴ * evaluate OV cs = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using!
        (Matrix.mem_unitaryGroup_iff'.mp (hwf.evaluate_unitary hOV))
    rw [evaluate_adjointCircuit, Matrix.mulVec_mulVec, hunit, Matrix.one_mulVec]

end Qatlib.Concepts.CoherentSim.GeneralUnitary
