/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiPolynomialActualAlgorithmStat
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiReadoutHelpers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Matrix
open scoped Classical BigOperators

theorem tiPolynomialActualAlgorithm : TiPolynomialActualAlgorithm := by
  intro n k _ p hp0 _hnorm hm
  have hN : 0<2*n := by have := NeZero.pos n; omega
  have hword := ti_polynomial_word_unitary n k p hm
  have hprep : IsUnitaryCircuit (tiPolynomialPreparedWord n k p) := by
    rw [tiPolynomialPreparedWord,isUnitaryCircuit_gate]
    exact ⟨qftMatrix_unitary hN,hword⟩
  have hu : Normalized (Uniform (Fin (2*n))) := normalized_uniform (by simpa using hN)
  have hket : Normalized (Ket (0 : Fin (2*n))) := normalized_ket _
  obtain ⟨hq,hg,hpq,hpg⟩ := ti_polynomial_word_counts n k p
  refine ⟨hword,hprep,hq,hg,hpq,hpg,ti_polynomial_word_commutes n k p,
    hu,hket,ti_readout_orthogonal n k,?_⟩
  intro j
  have ho := phaseOracle_unitary (ospBit n j)
  have hquery := ti_polynomial_run_all n k p hp0 hm j
  have hprepared := ti_polynomial_prepared_run n k p j
  let ψ := Run (PhaseOracle (ospBit n j)) (tiPolynomialPreparedWord n k p) (Ket 0)
  have hψ : Normalized ψ := hprep.normalized_run ho hket
  have hsector : ApplyGate ((tiTranslation n)^n) ψ=(-1:ℂ)^k • ψ := by
    dsimp only [ψ]
    rw [hprepared,hquery]
    exact ti_translated_sector n k j.val (p k)
  have hmass := ti_sector_readout_mass n k ψ hψ hsector
  have hcorrect : Complex.normSq (Inner (tiPolynomialReadoutVector n k (ospFun n j)) ψ)=
      Complex.normSq (p k 0) := by
    dsimp only [ψ]
    rw [hprepared,hquery]
    exact ti_translated_readout_correct n k (p k) j
  have hfold := (ti_sector_folded_eq_readout n k ψ hsector (ospFun n j)).trans hcorrect
  exact ⟨ho,hquery,hprepared,hψ,hmass,hcorrect,hfold⟩

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
