/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem5ApproximateCountingQuan
import Qatlib.Concepts.SearchStopping.Gate.Section6SourceGateSubgoalTigh
import Mathlib.Tactic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open scoped Classical
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Matrix

namespace Qatlib.Papers.QSearchBoyer96.MainResults

theorem actual_counted_fourier_sampling_support (N P : ℕ) (hN : 0 < N) (hP : 2 ≤ P)
    (S : Finset (Fin N)) :
    QueryCount (countedAECircuit P (QFTMatrix N) (⟨0,hN⟩ : Fin N)) = P-1 ∧
    GateCount (countedAECircuit P (QFTMatrix N) (⟨0,hN⟩ : Fin N)) = 5*(P-1)+3 ∧
    IsUnitaryCircuit (countedAECircuit P (QFTMatrix N) (⟨0,hN⟩ : Fin N)) ∧
    (8/Real.pi^2:ℝ) ≤
      ∑ z ∈ Finset.univ.filter (fun z : Fin P =>
        |(N:ℝ)*aeEstimate P z-(S.card:ℝ)| ≤
          2*Real.pi*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/(P:ℝ)+
            Real.pi^2*(N:ℝ)/(P:ℝ)^2),
        (aeLaw P (QFTMatrix N) ⟨0,hN⟩ S (qftMatrix_unitary hN) hP).prob z := by
  have h := prepared_ae_expanded_access_and_output P hP (QFTMatrix N)
    (⟨0,hN⟩ : Fin N) S (qftMatrix_unitary hN)
  exact ⟨h.1,h.2.1,h.2.2.1,amplitude_counting_actual_consumer N P hN hP S⟩

theorem actual_counting_iterate_is_grover (N : ℕ) (hN : 0 < N)
    (S : Finset (Fin N)) :
    preparedAAIterate (QFTMatrix N) (⟨0,hN⟩ : Fin N) S =
      Diffusion (Fin N) * SetOracle S := by
  have hconj := (prepared_aa_reflection_and_access (QFTMatrix N)
    (⟨0,hN⟩ : Fin N) S (qftMatrix_unitary hN)).2.2.1
  have hprep : preparedAAState (QFTMatrix N) (⟨0,hN⟩ : Fin N) = Uniform (Fin N) :=
    by
      rw [preparedAAState,qftMatrix_ket_zero]
      funext i
      simp only [Qatlib.Foundations.PureStateMath.Uniform,Fintype.card_fin]
  have hsqrt : (Real.sqrt (Fintype.card (Fin N)) : ℂ)^2 =
      (Fintype.card (Fin N) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    norm_cast
  have houter : outerProduct (Uniform (Fin N)) = AverageProjection (Fin N) := by
    ext i j
    simp only [outerProduct_apply,Uniform,AverageProjection,Matrix.of_apply]
    rw [map_inv₀,Complex.conj_ofReal,← pow_two,inv_pow,hsqrt]
  have hmark : preparedMark S = SetOracle S := by
    ext i j
    simp only [preparedMark, SetOracle, PhaseOracle, Qatlib.Foundations.InstrumentCore.Measurement.Projector, Matrix.sub_apply,
      Matrix.smul_apply,Matrix.diagonal_apply,Matrix.one_apply,smul_eq_mul]
    by_cases hij : i=j
    · subst j
      by_cases hi : i ∈ S <;> norm_num [hi]
    · simp [hij]
  unfold preparedAAIterate
  rw [hconj,hprep,houter,hmark]
  rfl

noncomputable def sourceCountingOutput (N P : ℕ) (hN : 0 < N) (hP : 2 ≤ P)
    (S : Finset (Fin N)) : (Fin P × Bool × Fin N) → ℂ :=
  Run (aeControlledGate P (preparedMark S))
    (countedAECircuit P (QFTMatrix N) (⟨0,hN⟩ : Fin N))
    (TensorState (Ket (⟨0,by omega⟩ : Fin P)) (TensorState (Ket false) (Ket ⟨0,hN⟩)))

theorem source_counting_actual_born (N P : ℕ) (hN : 0 < N) (hP : 2 ≤ P)
    (S : Finset (Fin N)) :
    Normalized (sourceCountingOutput N P hN hP S) ∧
    (∀ z : Fin P, (aeLaw P (QFTMatrix N) ⟨0,hN⟩ S (qftMatrix_unitary hN) hP).prob z =
      MeasureProb (sourceCountingOutput N P hN hP S) {p | p.1 = z}) ∧
    (∀ (z : Fin P) (i : Fin N), sourceCountingOutput N P hN hP S (z,true,i) = 0) := by
  have h := prepared_ae_expanded_access_and_output P hP (QFTMatrix N)
    (⟨0,hN⟩ : Fin N) S (qftMatrix_unitary hN)
  simpa only [sourceCountingOutput, aeControlledGate] using h.2.2.2

theorem source_counting_born_accuracy (N P : ℕ) (hN : 0 < N) (hP : 2 ≤ P)
    (S : Finset (Fin N)) :
    (8/Real.pi^2:ℝ) ≤
      ∑ z ∈ Finset.univ.filter (fun z : Fin P =>
        |(N:ℝ)*aeEstimate P z-(S.card:ℝ)| ≤
          2*Real.pi*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/(P:ℝ)+
            Real.pi^2*(N:ℝ)/(P:ℝ)^2),
        MeasureProb (sourceCountingOutput N P hN hP S) {p | p.1 = z} := by
  simpa only [← (source_counting_actual_born N P hN hP S).2.1] using
    (actual_counted_fourier_sampling_support N P hN hP S).2.2.2

end Qatlib.Papers.QSearchBoyer96.MainResults
