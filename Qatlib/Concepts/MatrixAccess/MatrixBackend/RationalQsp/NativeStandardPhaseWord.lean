/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeStandardPhaseConvention
import Qatlib.Concepts.SignalPrimitive.PhaseFrontend.ComputedPhaseQSVT
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.PureStateMath.Reflection

/-! The same converted standard phase packet drives the actual original-matrix
QSVT word. Uniform response error is consumed directly, without requiring a
monomial-coefficient score or inventing a phase-synthesis execution cost. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords

open Qatlib
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Matrix Polynomial
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Physical macro word on the supplied projectors; no synthesis rerun. -/
def nativeStandardPhaseWord {H : Type} [Fintype H] [DecidableEq H]
    (P Q : Matrix H H ℂ) (data : PhaseData) : List (AdjointStep (Bool × H)) :=
  computedPhaseWord P Q (nativePacketFromStandard data)

/-- Gatewise legality is available for either projector order, including the
actual swapped word executed in the even branch. -/
theorem native_standard_phase_word_wellFormed {H : Type} [Fintype H] [DecidableEq H]
    (P Q : Matrix H H ℂ) (data : PhaseData)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (hb : ‖gaussianRatComplex data.base‖=1)
    (hz : ∀ z∈data.phases,‖gaussianRatComplex z‖=1) :
    WellFormedAdjointCircuit (nativeStandardPhaseWord P Q data) := by
  have hu := nativePacketFromStandard_unit data hb hz
  have hp := data_phase_valid (nativePacketFromStandard data) hu.1 hu.2
  exact compileRealPartQSVT_wellFormed hP hQ hp.1 _ hp.2

/-- Counts concern the emitted word, for either projector order and length0. -/
theorem native_standard_phase_word_counts {H : Type} [Fintype H] [DecidableEq H]
    (P Q : Matrix H H ℂ) (data : PhaseData) :
    adjointQueryCount (nativeStandardPhaseWord P Q data)=data.phases.length ∧
      adjointGateCount (nativeStandardPhaseWord P Q data)=data.phases.length+1 := by
  simpa only [nativeStandardPhaseWord,computedPhaseWord,List.length_map,
    nativePacketFromStandard_length] using
      counts_compileRealPartQSVT P Q
        (gaussianRatComplex (nativePacketFromStandard data).base)
        ((nativePacketFromStandard data).phases.map gaussianRatComplex)

/-- Unit Gaussian phases and an actual standard-W uniform response guarantee
give an original-encoding matrix transform with the same packet and query count.
For even length the oracle is adjointed and the two projectors are swapped.
No degree bound, coefficient score, phase producer or bit-time claim is assumed. -/
theorem native_standard_phase_word_transform
    {H I O : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
    (data : PhaseData) (f : ℝ → ℝ) (ε : ℝ)
    (henc : ProjectedUnitaryEncoding A U L R)
    (hb : ‖gaussianRatComplex data.base‖=1)
    (hz : ∀ z∈data.phases,‖gaussianRatComplex z‖=1) (hε : 0≤ε)
    (hresponse : ∀ x∈Set.Icc (-1 : ℝ) 1,
      |((standardResponseP (gaussianRatComplex data.base)
        (data.phases.map gaussianRatComplex)).eval (x : ℂ)).im-f x|≤ε) :
    let cs := nativeStandardPhaseWord (rangeProjector R) (rangeProjector L) data
    WellFormedAdjointCircuit cs ∧
      adjointQueryCount cs=data.phases.length ∧ adjointGateCount cs=data.phases.length+1 ∧
      (data.phases.length%2=1 →
        BlockEncoding (oddSingularTransform A (fun x => (f x : ℂ)))
          (evaluate (parallelOracle U) cs) (averageFrame L) (averageFrame R) 1 ε) ∧
      (data.phases.length%2=0 →
        BlockEncoding (rightSingularTransform A (fun x => (f x : ℂ)))
          (evaluate (parallelOracle Uᴴ)
            (nativeStandardPhaseWord (rangeProjector L) (rangeProjector R) data))
          (averageFrame R) (averageFrame R) 1 ε) := by
  have hu := nativePacketFromStandard_unit data hb hz
  have hp := data_phase_valid (nativePacketFromStandard data) hu.1 hu.2
  have hlen : ((nativePacketFromStandard data).phases.map gaussianRatComplex).length=
      data.phases.length := by simp [nativePacketFromStandard_length]
  have ha := nativePacketFromStandard_uniform data f ε hresponse
  have hscalar (i : Fin (Fintype.card I)) :
      ‖(((responseP (gaussianRatComplex (nativePacketFromStandard data).base)
          ((nativePacketFromStandard data).phases.map gaussianRatComplex)).eval
          (matrixSingularValues A i : ℂ)).re : ℂ)-(f (matrixSingularValues A i) : ℂ)‖≤ε := by
    rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    apply ha
    have hs := encoded_singularValues_mem_unitInterval henc i.val
    exact ⟨by linarith [hs.1],hs.2⟩
  have hcount := counts_compileRealPartQSVT (rangeProjector R) (rangeProjector L)
    (gaussianRatComplex (nativePacketFromStandard data).base)
    ((nativePacketFromStandard data).phases.map gaussianRatComplex)
  refine ⟨compileRealPartQSVT_wellFormed
    (rangeProjector_isOrthogonalProjector henc.right_isometry)
    (rangeProjector_isOrthogonalProjector henc.left_isometry) hp.1 _ hp.2,
    by simpa only [nativeStandardPhaseWord,computedPhaseWord,hlen] using hcount.1,
    by simpa only [nativeStandardPhaseWord,computedPhaseWord,hlen] using hcount.2,?_,?_⟩
  · intro hodd
    have hactual := realPartQSVT_odd_singularEncoding henc hp.1 _ hp.2
      (by simpa only [hlen] using hodd)
    have he : ‖oddSingularTransform A (fun x => (f x : ℂ))-
        oddSingularTransform A (fun x =>
          (((responseP (gaussianRatComplex (nativePacketFromStandard data).base)
            ((nativePacketFromStandard data).phases.map gaussianRatComplex)).eval (x : ℂ)).re : ℂ))‖≤ε :=
      oddSingularTransform_error_le A _ _ hε (fun i => by rw [norm_sub_rev]; exact hscalar i)
    simpa only [zero_add,nativeStandardPhaseWord,computedPhaseWord,evaluate_compileRealPartQSVT]
      using (ProjectedUnitaryEncoding.toBlockEncoding hactual).perturb hε he
  · intro heven
    have hactual := realPartQSVT_even_right_singularEncoding henc hp.1 _ hp.2
      (by simpa only [hlen] using heven)
    have he : ‖rightSingularTransform A (fun x => (f x : ℂ))-
        rightSingularTransform A (fun x =>
          (((responseP (gaussianRatComplex (nativePacketFromStandard data).base)
            ((nativePacketFromStandard data).phases.map gaussianRatComplex)).eval (x : ℂ)).re : ℂ))‖≤ε :=
      rightSingularTransform_error_le A _ _ hε (fun i => by rw [norm_sub_rev]; exact hscalar i)
    simpa only [zero_add,nativeStandardPhaseWord,computedPhaseWord,evaluate_compileRealPartQSVT]
      using (ProjectedUnitaryEncoding.toBlockEncoding hactual).perturb hε he

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
