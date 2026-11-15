/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiSdpActualAlgorithmStat
public import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiPolynomialActualAlgorithmTransport
public import Qatlib.Concepts.OrderedOracle.TiSdpBridge.Theorem9SDPCharacterizationTransport

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Matrix
open scoped Classical BigOperators

/-- A translation-invariant polynomial algorithm yields the stated actual SDP algorithm with its
circuit, readout, and resource guarantees. -/
theorem tiSdpActualAlgorithm_of_algorithm
    (hAlg : TiPolynomialActualAlgorithm) : TiSdpActualAlgorithm := by
  intro n k _ ε hSDP
  obtain ⟨p,hp0,hnorm,hzero,hfin,hroot⟩ := tiSDPFeasible_implies_tiPolyConditions n k ε hSDP
  have hall (t : ℕ) (ht : t ∈ Finset.Icc 0 k) : ∑ i,Complex.normSq (p t i)=1 := by
    by_cases ht0 : t=0
    · subst t; exact hzero
    · apply hnorm
      simp only [Finset.mem_Icc] at ht ⊢
      omega
  obtain ⟨hword,hprep,hq,hg,hpq,hpg,hcomm,hu,hket,horth,hrun⟩ := hAlg n k p hp0 hall hroot
  refine ⟨p,hp0,hall,hroot,hword,hprep,hq,hg,hpq,hpg,hcomm,hu,hket,horth,?_⟩
  intro j
  obtain ⟨ho,hquery,hprepared,hn,hmass,hcorrect,hfold⟩ := hrun j
  exact ⟨ho,hprepared.trans hquery,hn,hmass,hcorrect,hfold,by rw [hcorrect]; exact hfin⟩

/-- Every feasible translation-invariant SDP instance yields an actual ordered-search algorithm
with the stated normalization, success, and resource guarantees. -/
theorem tiSdpActualAlgorithm : TiSdpActualAlgorithm :=
  tiSdpActualAlgorithm_of_algorithm tiPolynomialActualAlgorithm

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
