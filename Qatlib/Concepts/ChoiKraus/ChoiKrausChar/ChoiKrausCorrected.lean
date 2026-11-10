/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChoiKraus.ChoiKrausChar.ChannelStructure
import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureKraus
import Qatlib.Concepts.ChannelTheory.Naimark.ChannelStructureMeasurement
import Qatlib.Concepts.ChannelTheory.Naimark.ChannelStructureNaimark
import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureStinespring
import Qatlib.Concepts.ChannelTheory.TwirlChannel
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.ChoiKraus.ChoiKrausChar
open Matrix
open scoped ComplexOrder

theorem cp_tp_iff_complete_kraus {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    (CompletelyPositive T ∧ TracePreserving T) ↔
      ∃ (n : ℕ) (K : Fin n → Matrix (Fin E) (Fin D) ℂ),
        KrausForm T K ∧ KrausComplete K ∧ n ≤ D * E := by
  constructor
  · rintro ⟨hcp, htp⟩
    obtain ⟨n, K, hK, hn⟩ := (clause2_conj2 T).mp hcp
    exact ⟨n, K, hK, krausComplete_of_tracePreserving hK htp, hn⟩
  · rintro ⟨n, K, hK, hC, _⟩
    exact ⟨completelyPositive_of_krausForm hK, tracePreserving_of_krausComplete hK hC⟩

theorem choiKrausCorrected :
  ∀ (D E : ℕ) (T : Operator D →ₗ[ℂ] Operator E),
    (CompletelyPositive T ↔ (ChoiMatrix T).PosSemidef) ∧
    (CompletelyPositive T ↔
      ∃ (n : ℕ) (K : Fin n → Matrix (Fin E) (Fin D) ℂ), KrausForm T K ∧ n ≤ D * E) ∧
    (∀ (n : ℕ) (K : Fin n → Matrix (Fin E) (Fin D) ℂ),
      KrausForm T K → (TracePreserving T ↔ KrausComplete K)) ∧
    ((CompletelyPositive T ∧ TracePreserving T) ↔
      ∃ (n : ℕ) (K : Fin n → Matrix (Fin E) (Fin D) ℂ),
        KrausForm T K ∧ KrausComplete K ∧ n ≤ D * E) ∧
    (D = 0 → CompletelyPositive T ∧ TracePreserving T) ∧
    (E = 0 → (TracePreserving T ↔ D = 0)) ∧
    ((∃ Q : QuantumChannel D E, Q.map = T) ↔ CompletelyPositive T ∧ TracePreserving T) ∧
    (CompletelyPositive T ↔ MatrixMap.IsCompletelyPositive T) ∧
    (TracePreserving T ↔ MatrixMap.IsTracePreserving T) ∧
    ((ChoiMatrix T).PosSemidef ↔ (MatrixMap.choi_matrix T).PosSemidef) ∧
    (∀ Q : QuantumChannel D E,
      (ChoiMatrix Q.map).PosSemidef ∧
      ∃ (n : ℕ) (K : Fin n → Matrix (Fin E) (Fin D) ℂ),
        KrausForm Q.map K ∧ KrausComplete K ∧ n ≤ D * E) ∧
    (∀ (n : ℕ) (K : Fin n → Matrix (Fin E) (Fin D) ℂ), KrausComplete K →
      ∃ Q : QuantumChannel D E,
        KrausForm Q.map K ∧
        MatrixMap.IsCompletelyPositive Q.map ∧ MatrixMap.IsTracePreserving Q.map) := by
  intro D E T
  refine ⟨clause2_conj1 T, clause2_conj2 T, ?_, cp_tp_iff_complete_kraus T,
    ?_, ?_, quantumChannel_iff_cp_tp T, completelyPositive_iff_physlibMap T,
    tracePreserving_iff_physlibMap T, choi_posSemidef_iff_physlib T,
    clause2_conj11, clause2_conj12⟩
  · intro n K hK
    exact tracePreserving_iff_krausComplete hK
  · intro hD
    exact ⟨completelyPositive_of_input_zero hD T, tracePreserving_of_input_zero hD T⟩
  · intro hE
    exact tracePreserving_iff_input_zero_of_output_zero hE T

end Qatlib.Concepts.ChoiKraus.ChoiKrausChar
