/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.PhaseReadout.BoundarySpectralSectors
import Qatlib.Concepts.SpectralFilter.WalkBoundary.SzegedyAccessConsumers
import Qatlib.Concepts.QsvtCore.QueryLowerBound.SubroutineExpansion
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.WalkSearch.CountedWalk
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Concepts.SpectralFilter.WalkBoundary
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open scoped Classical BigOperators

noncomputable def endpointRowReflectionWord {I : Type} [Fintype I] [DecidableEq I]
    (M k : ℕ) (j : I) : List (AdjointStep (PhaseReflectionSpace (I×I) M k)) :=
  substituteAdjointCircuit
    (phaseLiftWord (fun V : Matrix (Bool×(I×I)) (Bool×(I×I)) ℂ =>
        parallelOracle (J := Fin k → Fin M) V)
      (compileControlled (countedSzegedyWord j)))
    (phaseReflectionWord M k)

theorem boundary_szegedy_actual_row_reflection_expansion : ∀ (I : Type) [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (j : I) (U : Matrix (I×I) (I×I) ℂ) (M k : ℕ),
    IsTransitionMatrix P → U ∈ Matrix.unitaryGroup (I×I) ℂ → 2 ≤ M →
    (∀ i, U*ᵥTensorState (Ket i) (Ket j)=SzegedyIsometry P*ᵥKet i) →
    WellFormedAdjointCircuit (endpointRowReflectionWord M k j) ∧
    adjointQueryCount (endpointRowReflectionWord M k j)=8*k*(M-1) ∧
    adjointGateCount (endpointRowReflectionWord M k j)=12*k*(M-1)+4*k+1 ∧
    evaluate (parallelOracle (J := Fin k → Fin M) (controlOracle U))
      (endpointRowReflectionWord M k j)=
    evaluate (parallelOracle (controlOracle (SzegedyWalk P))) (phaseReflectionWord M k) := by
  intro I _ _ P j U M k hP hU hM hprep
  let F := fun V : Matrix (Bool×(I×I)) (Bool×(I×I)) ℂ => parallelOracle (J:=Fin k→Fin M) V
  let body := phaseLiftWord F (compileControlled (countedSzegedyWord j))
  have h1 : F 1=1 := parallel_select_one
  have hm : ∀ V W,F (V*W)=F V*F W := fun V W=>(parallel_select_mul (fun _=>V) (fun _=>W)).symm
  have ha : ∀ V,F Vᴴ=(F V)ᴴ := fun V=>(parallelOracle_adjoint V).symm
  have hsem : evaluate (F (controlOracle U)) body=F (controlOracle (SzegedyWalk P)) := by
    rw [phaseLiftWord_evaluate F h1 hm ha,evaluate_compileControlled,
      counted_szegedy_actual_walk_semantics P j U hP hU hprep]
  have hb : adjointQueryCount body=4 ∧ adjointGateCount body=4 := by
    dsimp only [body]
    rw [(phaseLiftWord_counts _ _).1,(phaseLiftWord_counts _ _).2,
      queryCount_compileControlled,gateCount_compileControlled]
    exact (counted_szegedy_actual_word_and_counts j).2
  have hbody : WellFormedAdjointCircuit body :=
    phaseLiftWord_wellFormed F (fun V hV=>parallelOracle_unitary hV)
      (compileControlled_wellFormed (countedSzegedyWord_wellFormed j))
  have hs := substitute_adjoint_evaluate_cost (F (controlOracle U)) body (phaseReflectionWord M k)
  have hc := phase_reflection_actual_queries_and_macros (I:=I×I) M k hM
  change WellFormedAdjointCircuit (substituteAdjointCircuit body (phaseReflectionWord M k)) ∧
    adjointQueryCount (substituteAdjointCircuit body (phaseReflectionWord M k))=8*k*(M-1) ∧
    adjointGateCount (substituteAdjointCircuit body (phaseReflectionWord M k))=12*k*(M-1)+4*k+1 ∧
    evaluate (F (controlOracle U)) (substituteAdjointCircuit body (phaseReflectionWord M k))=
      evaluate (F (controlOracle (SzegedyWalk P))) (phaseReflectionWord M k)
  refine ⟨hs.2.2.2 hbody hc.1,?_,?_,?_⟩
  · rw [hs.2.1,hb.1,hc.2.1]; ring
  · rw [hs.2.2.1,hb.2,hc.2.1,hc.2.2]; ring
  · rw [hs.1,hsem]

theorem boundary_periodic_minus_gram_actual_primitive_consumer : ∀ (M k : ℕ), 2 ≤ M →
    let v : QState Bool := fun b => if b then -(Real.sqrt 2 : ℂ)⁻¹ else (Real.sqrt 2 : ℂ)⁻¹
    let w := SzegedyIsometry periodicFlipTransition*ᵥv
    let word := endpointRowReflectionWord M k false
    ((SzegedyIsometry periodicFlipTransition)ᴴ*SzegedyIsometryB periodicFlipTransition)*ᵥv=-v ∧
    ApplyGate (evaluate (parallelOracle (J := Fin k → Fin M)
      (controlOracle periodicFlipPreparation)) word) (phaseReflectionEmbed M k w)=
      phaseReflectionEmbed M k w ∧
    MeasureProb (ApplyGate (evaluate (parallelOracle (controlOracle (SzegedyWalk periodicFlipTransition)))
      (phaseDetectionWord M k)) (phaseReflectionEmbed M k w)) (phaseZeroEvent M k)=1 ∧
    adjointQueryCount word=8*k*(M-1) ∧ adjointGateCount word=12*k*(M-1)+4*k+1 := by
  intro M k hM
  let v : QState Bool := fun b=>if b then -(Real.sqrt 2 : ℂ)⁻¹ else (Real.sqrt 2 : ℂ)⁻¹
  let w := SzegedyIsometry periodicFlipTransition*ᵥv
  have hP := periodicFlipTransition_isTransition
  have hgram : ((SzegedyIsometry periodicFlipTransition)ᴴ*SzegedyIsometryB periodicFlipTransition)*ᵥv=-v := by
    rw [szegedy_gram_eq_discriminant _ hP]
    funext b
    cases b <;> simp [Matrix.mulVec,dotProduct,SzegedyDiscriminant,periodicFlipTransition,v]
  have he := two_isometry_extreme_gram_endpoint Bool (Bool×Bool)
    (SzegedyIsometry periodicFlipTransition) (SzegedyIsometryB periodicFlipTransition) v (-1)
    (szegedyIsometry_conjTranspose_mul _ hP) (szegedyIsometryB_conjTranspose_mul _ hP)
    (Or.inr rfl) (by simpa only [neg_one_smul] using hgram)
  have hw : ApplyGate (SzegedyWalk periodicFlipTransition) w=w := by
    simpa only [ApplyGate,szegedyWalk_eq_twoReflections _ hP] using he.2
  have hv : Normalized v := by
    have hv' : v=Minus := by funext b; cases b <;> simp [v,Minus,Hadamard]
    rw [hv']; exact normalized_minus
  have hn : Normalized w := by
    rw [normalized_iff_inner_self]
    rw [inner_mulVec_left_rect,Matrix.mulVec_mulVec,szegedyIsometry_conjTranspose_mul _ hP,Matrix.one_mulVec]
    exact (normalized_iff_inner_self v).mp hv
  have hread := boundary_actual_zero_phase_readout_and_reflection (Bool×Bool)
    (SzegedyWalk periodicFlipTransition) w M k (szegedyWalk_unitary _ hP) hn hw hM
  have hexp := boundary_szegedy_actual_row_reflection_expansion Bool periodicFlipTransition false
    periodicFlipPreparation M k hP periodicFlipPreparation_unitary hM periodicFlipPreparation_prepares
  refine ⟨hgram,?_,hread.2.1,hexp.2.1,hexp.2.2.1⟩
  rw [hexp.2.2.2]
  exact hread.2.2

theorem boundary_idle_extra_one_actual_consumer : ∀ (M k : ℕ), 2 ≤ M →
    let P : Bool → Bool → ℝ := fun _ _ => 1/2
    let w : QState (Bool×Bool) := fun p => if p.1=p.2 then (1/2 : ℂ) else -(1/2 : ℂ)
    (SzegedyIsometry P)ᴴ*ᵥw=0 ∧ (SzegedyIsometryB P)ᴴ*ᵥw=0 ∧ Normalized w ∧
    ApplyGate (SzegedyWalk P) w=w ∧
    MeasureProb (ApplyGate (evaluate (parallelOracle (controlOracle (SzegedyWalk P)))
      (phaseDetectionWord M k)) (phaseReflectionEmbed M k w)) (phaseZeroEvent M k)=1 ∧
    phaseReflectionState (SzegedyWalk P) M k w=phaseReflectionEmbed M k w := by
  intro M k hM
  let P : Bool→Bool→ℝ := fun _ _=>1/2
  let w : QState (Bool×Bool) := fun p=>if p.1=p.2 then (1/2 : ℂ) else -(1/2 : ℂ)
  have hP : IsTransitionMatrix P := by
    refine ⟨fun _ _=>by norm_num [P],?_⟩
    intro b; norm_num [P,Fintype.sum_bool]
  have ha : (SzegedyIsometry P)ᴴ*ᵥw=0 := by
    funext i
    cases i <;> simp [Matrix.mulVec,dotProduct,Matrix.conjTranspose_apply,Fintype.sum_prod_type,
      SzegedyIsometry,P,w]
  have hb : (SzegedyIsometryB P)ᴴ*ᵥw=0 := by
    funext i
    cases i <;> simp [Matrix.mulVec,dotProduct,Matrix.conjTranspose_apply,Fintype.sum_prod_type,
      szegedyIsometryB_apply,P,w]
  have hn : Normalized w := by
    norm_num [Normalized,w,Fintype.sum_prod_type,Fintype.sum_bool,Complex.norm_def]
  have hfix := (two_isometry_idle_sector_fixed Bool Bool (Bool×Bool) (SzegedyIsometry P)
    (SzegedyIsometryB P) w (szegedyIsometry_conjTranspose_mul P hP)
    (szegedyIsometryB_conjTranspose_mul P hP) ha hb).2.2
  have hw : ApplyGate (SzegedyWalk P) w=w := by
    simpa only [ApplyGate,szegedyWalk_eq_twoReflections P hP] using hfix
  have hread := boundary_actual_zero_phase_readout_and_reflection (Bool×Bool) (SzegedyWalk P) w M k
    (szegedyWalk_unitary P hP) hn hw hM
  exact ⟨ha,hb,hn,hw,hread.2.1,hread.2.2⟩

end Qatlib.Concepts.SpectralFilter.WalkBoundary
