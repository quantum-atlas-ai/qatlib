/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QsVtMain.ConventionBridge
import Qatlib.Concepts.QsvtCore.QsVtStability.RootRobustQSVTConsumers

/-!
# Source-convention QSVT word consumers

This module connects real polynomial phase synthesis to explicit alternating words and their
controlled-family compilation. For a bounded odd polynomial of exact degree `d`,
`source_convention_actual_word_consumer_spec` supplies phases, length and parity constraints, a
robust real singular-value transform, and exact compiler counts.

The word-level consumers also bound success mass and normalized output error for normalized
inputs, using the alternating phase-modulation framework of [GilyenSuLowWiebe2019].

## Main statements

* `source_convention_actual_word_consumer_spec`: assemble phase synthesis, robust encoding,
  compiler semantics, and output estimates.
* `source_convention_actual_word_consumer`: specialize the word guarantees to a normalized
  input.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.QsvtCore.QsVtStability

namespace Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery
open Matrix Polynomial
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator
variable {H : Type} [Fintype H] [DecidableEq H]

/-- For a bounded odd polynomial of positive exact degree `d` and a contractive normalized block
encoding, constructs `d` source-convention phases with minimal length and prescribed parity,
robust singular-transform encoding, exact compiler counts, and statewise output guarantees. -/
theorem source_convention_actual_word_consumer_spec :
  ∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
    (α ε : ℝ) (p : Polynomial ℝ) (d : ℕ),
    BlockEncoding A U L R α ε → ‖(α⁻¹ : ℝ) • A‖ ≤ 1 → 0 < d → d % 2 = 1 →
    p.degree = (d : WithBot ℕ) → HasRealParity d p →
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) →
    ∃ Φ : List ℝ, Φ.length = d ∧
      (∀ x : ℝ, ((sourcePhaseResponse Φ).eval (x : ℂ)).re = p.eval x) ∧
      (∀ Ψ : List ℝ, (∀ x : ℝ, ((sourcePhaseResponse Ψ).eval (x : ℂ)).re = p.eval x) →
        d ≤ Ψ.length ∧ Ψ.length % 2 = d % 2) ∧
      cppCounts (cppCompile (sourceRealFamily Φ)) = (d,2*(d/2),2*((d+1)/2),d) ∧
      BlockEncoding
        (oddSingularTransform ((α⁻¹ : ℝ) • A) (fun x => ((p.eval x : ℝ) : ℂ)))
        (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
        (sourceAverageClean L) (sourceAverageClean R) 1 (4*d*Real.sqrt (ε/α)) ∧
      ∀ ψ : QState I, Normalized ψ →
      (let zs := Φ.map anglePhase
       let W := phasedAlternating U (rangeProjector R) (rangeProjector L) 1 zs
       let y := compress L W R *ᵥ ψ
       let v := oddSingularTransform ((α⁻¹ : ℝ) • A)
         (fun x : ℝ => (sourcePhaseResponse Φ).eval (x : ℂ)) *ᵥ ψ
       let τ := ‖toEuclidean_fromVec v‖
       let η := 4 * (d : ℝ) * Real.sqrt (ε / α)
       (η < τ → (τ - η) ^ 2 ≤ ‖toEuclidean_fromVec y‖ ^ 2 ∧
          ‖toEuclidean_fromVec (((‖toEuclidean_fromVec y‖⁻¹ : ℝ) : ℂ) • y -
            ((τ⁻¹ : ℝ) : ℂ) • v)‖ ≤ 2 * η / τ) ∧
       (cppEvaluate U (rangeProjector R) (rangeProjector L)
           (cppCompile (sourceRealFamily Φ)) ∈ unitaryGroup (Bool × (Bool × H)) ℂ ∧
         (cppEvaluate U (rangeProjector R) (rangeProjector L) (cppCompile (sourceRealFamily Φ)) *
             cppFamilyClean : Matrix (Bool × (Bool × H)) (Bool × H) ℂ) =
           cppFamilyClean * select (fun b : Bool =>
             phasedAlternating U (rangeProjector R) (rangeProjector L) 1
               ((sourceRealFamily Φ).map (fun f => anglePhase (f b)))) ∧
         (cppCounts (cppCompile (sourceRealFamily Φ))).1 = d) ∧
       adjointQueryCount (compileQSVT (rangeProjector R) (rangeProjector L) 1 zs) = d) := by
  intro I O _ _ _ _ A U L R α ε p d h hA hd hodd hdeg hpar hb
  obtain ⟨Φ, hlen, hre, hmin⟩ := source_minimal_degree_existence p d hd hdeg hpar hb
  have hz : ∀ z ∈ Φ.map anglePhase, IsPhase z := by
    intro z hzm
    obtain ⟨φ, _hφ, rfl⟩ := List.mem_map.mp hzm
    exact anglePhase_isPhase φ
  have hP := rangeProjector_isOrthogonalProjector h.right_isometry
  have hQ := rangeProjector_isOrthogonalProjector h.left_isometry
  have hcpp := cpp_family_actual_compilation_and_counts Bool H U
    (rangeProjector R) (rangeProjector L) (sourceRealFamily Φ) h.unitary hP hQ
  have hreal := source_cpp_encoded_corner_root_error_of_response
    H I O A U L R α ε p d Φ h hA hlen hre hdeg.le hpar hb
  refine ⟨Φ, hlen, hre, hmin, hreal.1, hreal.2.1 hodd, ?_⟩
  intro ψ hψ
  (try dsimp only)
  refine ⟨?_, ⟨hcpp.1, hcpp.2.1, ?_⟩, ?_⟩
  · have hout := complex_boundary_same_word_conditional_output H I O A U L R α ε 1
      (Φ.map anglePhase) h hA (by simp [IsPhase]) hz
      (by simpa only [List.length_map, hlen] using! hodd) ψ hψ
    simpa only [List.length_map, hlen, interiorResponse, sourcePhaseResponse] using! hout
  · simpa only [sourceRealFamily, List.length_map, hlen] using! congrArg Prod.fst hcpp.2.2
  · simpa only [List.length_map, hlen] using!
      queryCount_compileQSVT (rangeProjector R) (rangeProjector L) 1 (Φ.map anglePhase)

/-- For each normalized input, constructs a source-convention word of length `d` with
success-mass and normalized-output bounds, unitary controlled-family compilation, and
exactly `d` oracle queries [Gilyén et al., Lemma 19][GilyenSuLowWiebe2019]. -/
theorem source_convention_actual_word_consumer :
  ∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
    (α ε : ℝ) (p : Polynomial ℝ) (d : ℕ),
    BlockEncoding A U L R α ε → ‖(α⁻¹ : ℝ) • A‖ ≤ 1 → 0 < d → d % 2 = 1 →
    p.degree = (d : WithBot ℕ) → HasRealParity d p →
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) →
    ∀ ψ : QState I, Normalized ψ →
    ∃ Φ : List ℝ, Φ.length = d ∧
      (let zs := Φ.map anglePhase
       let W := phasedAlternating U (rangeProjector R) (rangeProjector L) 1 zs
       let y := compress L W R *ᵥ ψ
       let v := oddSingularTransform ((α⁻¹ : ℝ) • A)
         (fun x : ℝ => (sourcePhaseResponse Φ).eval (x : ℂ)) *ᵥ ψ
       let τ := ‖toEuclidean_fromVec v‖
       let η := 4 * (d : ℝ) * Real.sqrt (ε / α)
       (η < τ → (τ - η) ^ 2 ≤ ‖toEuclidean_fromVec y‖ ^ 2 ∧
          ‖toEuclidean_fromVec (((‖toEuclidean_fromVec y‖⁻¹ : ℝ) : ℂ) • y -
            ((τ⁻¹ : ℝ) : ℂ) • v)‖ ≤ 2 * η / τ) ∧
       (cppEvaluate U (rangeProjector R) (rangeProjector L)
           (cppCompile (sourceRealFamily Φ)) ∈ unitaryGroup (Bool × (Bool × H)) ℂ ∧
         (cppEvaluate U (rangeProjector R) (rangeProjector L) (cppCompile (sourceRealFamily Φ)) *
             cppFamilyClean : Matrix (Bool × (Bool × H)) (Bool × H) ℂ) =
           cppFamilyClean * select (fun b : Bool =>
             phasedAlternating U (rangeProjector R) (rangeProjector L) 1
               ((sourceRealFamily Φ).map (fun f => anglePhase (f b)))) ∧
         (cppCounts (cppCompile (sourceRealFamily Φ))).1 = d) ∧
       adjointQueryCount (compileQSVT (rangeProjector R) (rangeProjector L) 1 zs) = d) := by
  intro I O _ _ _ _ A U L R α ε p d h hA hd hodd hdeg hpar hb ψ hψ
  obtain ⟨Φ, hlen, _hre, _hmin, _hcounts, _hreal, hword⟩ :=
    source_convention_actual_word_consumer_spec I O A U L R α ε p d
      h hA hd hodd hdeg hpar hb
  exact ⟨Φ, hlen, hword ψ hψ⟩

end Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery
