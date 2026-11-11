/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceProposer
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceAllPackets
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceAllCheckedWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

open Qatlib.Foundations.QueryWordCore.Circuit

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.PureStateMath.Reflection

/-! Generated rational-polynomial QSP packets in the actual source branch order.
Original-input amplifier targets remain downstream consumers. Finite Bool decisions replace a
Classical runtime zero predicate; accepted root payloads are internal.
These value guarantees do not change the frozen finitePhaseSynthesis
scoring/table-ledger contract or prove host/total bit/physical fees. -/
set_option autoImplicit false
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords

namespace GeneratedSourceInternal
namespace ActualProjectionAllGeneratedPackets
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

/-- Data and invariants for Packet in the native generated source packets model. -/
private structure Packet where
  standard : PhaseData
  native : PhaseData
  trace : List ℕ

/-- Construction for zero Check in the native generated source packets model. -/
private def zeroCheck (cs : List ℚ) (N : ℕ) (E : ℚ) : Bool :=
  (List.ofFn (sourceCoefficient cs N E)).all (fun q => decide (q=0))

/-- Construction for pack in the native generated source packets model. -/
private def pack (standard : PhaseData) : Packet := ⟨standard,nativePacketFromStandard standard,[]⟩

/-- Construction for produce in the native generated source packets model. -/
private def produce (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0) : Option Packet :=
  if N=0 then some (pack (sourceZeroDegreeBoundaryPacket cs E))
  else if zeroCheck cs N E=true then some (pack (sourceZeroBoundaryPacket N))
  else if sourceDegree cs N E=0 then some (pack (sourceConstantBoundaryPacket cs N E))
  else (rootProjectionGeneratedNonconstantPacket cs N E hparity).map
    (fun result => ⟨result.1,result.2.1,result.2.2⟩)

/-- The finite construction in `NativeGeneratedSourcePackets` satisfies `zero_check_iff` under the displayed hypotheses. -/
private theorem zero_check_iff (cs : List ℚ) (N : ℕ) (E : ℚ) :
    zeroCheck cs N E=true ↔ ∀ j : Fin (N+1),sourceCoefficient cs N E j=0 := by
  constructor
  · intro h j
    exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_ofFn.mpr ⟨j,rfl⟩))
  · intro h
    apply List.all_eq_true.mpr
    intro q hq
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
    exact decide_eq_true (h j)

/-- The finite construction in `NativeGeneratedSourcePackets` satisfies `zero_degree` under the displayed hypotheses. -/
private theorem zero_degree (cs : List ℚ) (N : ℕ) (E : ℚ) (hz : zeroCheck cs N E=true) :
    sourceDegree cs N E=0 := by
  by_contra hn
  obtain ⟨j,hj,_⟩ := sourceArrayDegree_leading (sourceCoefficient cs N E) (Nat.pos_of_ne_zero hn)
  exact hj ((zero_check_iff cs N E).mp hz j)

/-- Abbreviation for empty Family in the native generated source packets model. -/
private abbrev emptyFamily : Fin 0 → RootIntegerFactorData := Fin.elim0

/-- The finite construction in `NativeGeneratedSourcePackets` satisfies `degenerate_equal` under the displayed hypotheses. -/
private theorem degenerate_equal (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hdeg : N=0 ∨ sourceDegree cs N E=0) :
    ∃ standard,produce cs N E hparity=some (pack standard) ∧
      standard=sourceAllBoundaryPacket cs N E emptyFamily := by
  by_cases hN : N=0
  · refine ⟨sourceZeroDegreeBoundaryPacket cs E,?_,?_⟩
    · simp only [produce,ite_eq_left hN]
    · simp only [sourceAllBoundaryPacket,ite_eq_left hN]
  · have hd : sourceDegree cs N E=0 := hdeg.resolve_left hN
    by_cases hz : zeroCheck cs N E=true
    · refine ⟨sourceZeroBoundaryPacket N,?_,?_⟩
      · simp only [produce,ite_eq_right hN,ite_eq_left hz]
      · simp only [sourceAllBoundaryPacket,ite_eq_right hN,ite_eq_left ((zero_check_iff cs N E).mp hz)]
    · have hz' : ¬∀ j : Fin (N+1),sourceCoefficient cs N E j=0 :=
        fun h => hz ((zero_check_iff cs N E).mpr h)
      refine ⟨sourceConstantBoundaryPacket cs N E,?_,?_⟩
      · simp only [produce,ite_eq_right hN,ite_eq_right hz,ite_eq_left hd]
      · simp only [sourceAllBoundaryPacket,ite_eq_right hN,ite_eq_right hz',ite_eq_left hd]

/-- Construction for Good in the native generated source packets model. -/
private def Good (cs : List ℚ) (N : ℕ) (E : ℚ) (result : Packet) : Prop :=
  result.native=nativePacketFromStandard result.standard ∧
    result.standard.phases.length=N ∧ ‖gaussianRatComplex result.standard.base‖=1 ∧
    (∀ z∈result.standard.phases,‖gaussianRatComplex z‖=1) ∧
    result.native.phases.length=N ∧ ‖gaussianRatComplex result.native.base‖=1 ∧
    (∀ z∈result.native.phases,‖gaussianRatComplex z‖=1) ∧
    (∀ x∈Set.Icc (-1 : ℝ) 1,
      |((responseP (gaussianRatComplex result.native.base) (result.native.phases.map gaussianRatComplex)).eval (x : ℂ)).re-
        (nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 13*(sourceInputU cs N E : ℝ)/32) ∧
    (nativeChebyshevMass (sourceResidual cs result.standard) : ℝ) ≤ 13*(E : ℝ)/32 ∧
    nativeChebyshevPacketCheck cs (sourceResidual cs result.standard) result.standard E=true

/-- The finite construction in `NativeGeneratedSourcePackets` satisfies `original_all_generated_packet` under the displayed hypotheses. -/
private theorem original_all_generated_packet (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0 < E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1) :
    ∃ result,produce cs N E hparity=some result ∧ Good cs N E result := by
  by_cases hdeg : N=0 ∨ sourceDegree cs N E=0
  · obtain ⟨standard,hproduce,hstd⟩ := degenerate_equal cs N E hparity hdeg
    have hcert : 0 < N → 0 < sourceDegree cs N E → SourceNonconstantRawCertificate cs N E 1 emptyFamily := by
      intro hN hd
      rcases hdeg with h|h <;> omega
    obtain ⟨hlen,hbase,hphases⟩ := source_all_boundary_packet_spec cs N E emptyFamily hparity
    have hnunit := nativePacketFromStandard_unit (sourceAllBoundaryPacket cs N E emptyFamily) hbase hphases
    refine ⟨pack standard,hproduce,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [pack,hstd] using hlen
    · simpa only [pack,hstd] using hbase
    · simpa only [pack,hstd] using hphases
    · simpa only [pack,hstd,nativePacketFromStandard_length] using hlen
    · simpa only [pack,hstd] using hnunit.1
    · simpa only [pack,hstd] using hnunit.2
    · simpa only [pack,hstd] using source_all_native_uniform cs N E hE htail hparity hnorm 1 emptyFamily hcert
    · simpa only [pack,hstd] using source_all_residual_mass_bound cs N E hE htail hparity hnorm 1 emptyFamily hcert
    · simpa only [pack,hstd] using source_all_posterior_accepts cs N E hE htail hparity hnorm 1 emptyFamily hcert
  · have hN : N≠0 := fun h => hdeg (Or.inl h)
    have hd : sourceDegree cs N E≠0 := fun h => hdeg (Or.inr h)
    have hz : zeroCheck cs N E≠true := fun h => hd (zero_degree cs N E h)
    obtain ⟨standard,native,trace,hproduce,hgood⟩ :=
      source_original_generated_nonconstant_packet cs N E hE htail hparity (Nat.pos_of_ne_zero hd) hnorm
    refine ⟨⟨standard,native,trace⟩,?_,hgood⟩
    simp only [produce,ite_eq_right hN,ite_eq_right hz,ite_eq_right hd,hproduce,Option.map_some]

end ActualProjectionAllGeneratedPackets

namespace ActualProjectionAllGeneratedWord
open ActualProjectionAllGeneratedPackets
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

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped Matrix.Norms.L2Operator

/-- The finite construction in `NativeGeneratedSourcePackets` satisfies `original_all_generated_word` under the displayed hypotheses. -/
private theorem original_all_generated_word
    {H I O : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
 (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (henc : ProjectedUnitaryEncoding A U L R) :
    ∃ result,produce cs N E hparity=some result ∧ Good cs N E result ∧
    let data := result.standard
    let word := nativeStandardPhaseWord (rangeProjector R) (rangeProjector L) data
    WellFormedAdjointCircuit (nativeStandardPhaseWord (rangeProjector L) (rangeProjector R) data) ∧
      WellFormedAdjointCircuit word ∧
      adjointQueryCount word=N ∧ adjointGateCount word=N+1 ∧
      adjointQueryCount (nativeStandardPhaseWord (rangeProjector L) (rangeProjector R) data)=N ∧
      adjointGateCount (nativeStandardPhaseWord (rangeProjector L) (rangeProjector R) data)=N+1 ∧
      (N%2=1 →
        BlockEncoding (oddSingularTransform A (fun x => (((nativeChebyshevPolynomialFrom 0 cs).eval x : ℝ) : ℂ)))
          (evaluate (parallelOracle U) word) (averageFrame L) (averageFrame R) 1 (E : ℝ)) ∧
      (N%2=0 →
        BlockEncoding (rightSingularTransform A (fun x => (((nativeChebyshevPolynomialFrom 0 cs).eval x : ℝ) : ℂ)))
          (evaluate (parallelOracle Uᴴ)
            (nativeStandardPhaseWord (rangeProjector L) (rangeProjector R) data))
          (averageFrame R) (averageFrame R) 1 (E : ℝ)) := by
  obtain ⟨result,hproduce,hgood⟩ := original_all_generated_packet cs N E hE htail hparity hnorm
  refine ⟨result,hproduce,hgood,?_⟩
  obtain ⟨_,hlen,_,_,_,_,_,_,_,hcheck⟩ := hgood
  have hw := native_chebyshev_checked_word_transform A U L R cs
    (sourceResidual cs result.standard) result.standard E henc hcheck
  have hc := native_standard_phase_word_counts (rangeProjector L) (rangeProjector R) result.standard
  simp only [hlen] at hw hc
  obtain ⟨hwellL,hwellR,hq,hg,hodd,heven⟩ := hw
  exact ⟨hwellL,hwellR,hq,hg,hc.1,hc.2,hodd,heven⟩

end ActualProjectionAllGeneratedWord


end GeneratedSourceInternal

section GeneratedAllPackets
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

/-- Source-order N=0, finite rounded-coefficient all-zero, constant and
nonconstant dispatch. Numerical isolation and accepted factors are internal;
there is no caller root certificate, phase packet or fuel plan. -/
def rootProjectionGeneratedPacket (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0) :
    Option (PhaseData×PhaseData×List ℕ) :=
  (GeneratedSourceInternal.ActualProjectionAllGeneratedPackets.produce cs N E hparity).map
    (fun result => (result.standard,result.native,result.trace))

/-- All actual source branches preserve the complete original input and
produce their own packet with full uniform/residual/check guarantees. -/
theorem source_original_generated_packet (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0 < E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1) :
    ∃ (standard native : PhaseData) (trace : List ℕ),
      rootProjectionGeneratedPacket cs N E hparity=some (standard,native,trace) ∧
      native=nativePacketFromStandard standard ∧
      standard.phases.length=N ∧ ‖gaussianRatComplex standard.base‖=1 ∧
      (∀ z∈standard.phases,‖gaussianRatComplex z‖=1) ∧
      native.phases.length=N ∧ ‖gaussianRatComplex native.base‖=1 ∧
      (∀ z∈native.phases,‖gaussianRatComplex z‖=1) ∧
      (∀ x∈Set.Icc (-1 : ℝ) 1,
        |((responseP (gaussianRatComplex native.base) (native.phases.map gaussianRatComplex)).eval (x : ℂ)).re-
          (nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 13*(Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceInputU cs N E : ℝ)/32) ∧
      (nativeChebyshevMass (Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceResidual cs standard) : ℝ) ≤ 13*(E : ℝ)/32 ∧
      nativeChebyshevPacketCheck cs (Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput.sourceResidual cs standard) standard E=true := by
  obtain ⟨result,hp,hg⟩ :=
    GeneratedSourceInternal.ActualProjectionAllGeneratedPackets.original_all_generated_packet cs N E hE htail hparity hnorm
  refine ⟨result.standard,result.native,result.trace,?_,hg⟩
  simp only [rootProjectionGeneratedPacket,hp,Option.map_some]

end GeneratedAllPackets

section GeneratedAllWord
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

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped Matrix.Norms.L2Operator

/-- The finite construction in `NativeGeneratedSourcePackets` satisfies `source_original_generated_word` under the displayed hypotheses. -/
theorem source_original_generated_word
    {H I O : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
 (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (henc : ProjectedUnitaryEncoding A U L R) :
    ∃ (standard native : PhaseData) (trace : List ℕ),
      rootProjectionGeneratedPacket cs N E hparity=some (standard,native,trace) ∧
    let data := standard
    let word := nativeStandardPhaseWord (rangeProjector R) (rangeProjector L) data
    WellFormedAdjointCircuit (nativeStandardPhaseWord (rangeProjector L) (rangeProjector R) data) ∧
      WellFormedAdjointCircuit word ∧
      adjointQueryCount word=N ∧ adjointGateCount word=N+1 ∧
      adjointQueryCount (nativeStandardPhaseWord (rangeProjector L) (rangeProjector R) data)=N ∧
      adjointGateCount (nativeStandardPhaseWord (rangeProjector L) (rangeProjector R) data)=N+1 ∧
      (N%2=1 →
        BlockEncoding (oddSingularTransform A (fun x => (((nativeChebyshevPolynomialFrom 0 cs).eval x : ℝ) : ℂ)))
          (evaluate (parallelOracle U) word) (averageFrame L) (averageFrame R) 1 (E : ℝ)) ∧
      (N%2=0 →
        BlockEncoding (rightSingularTransform A (fun x => (((nativeChebyshevPolynomialFrom 0 cs).eval x : ℝ) : ℂ)))
          (evaluate (parallelOracle Uᴴ)
            (nativeStandardPhaseWord (rangeProjector L) (rangeProjector R) data))
          (averageFrame R) (averageFrame R) 1 (E : ℝ)) := by
  obtain ⟨result,hp,_,hw⟩ :=
    GeneratedSourceInternal.ActualProjectionAllGeneratedWord.original_all_generated_word
      A U L R cs N E hE htail hparity hnorm henc
  refine ⟨result.standard,result.native,result.trace,?_,hw⟩
  simp only [rootProjectionGeneratedPacket,hp,Option.map_some]

end GeneratedAllWord


end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
