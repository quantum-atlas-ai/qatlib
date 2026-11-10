/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Execution.KnownKraus.KrausUnitaryDilation
import Qatlib.Concepts.Execution.KnownKraus.KrausDilationReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false
namespace Qatlib.Concepts.Execution.KnownKraus
open Matrix
open scoped Classical

theorem known_kraus_measurement_realization {d s : ℕ} (K : Fin s → Operator d)
    (hK : ∑ a, (K a).conjTranspose * K a = 1) (zero : Fin s) :
    ∃ W : Matrix (Fin d × Fin s) (Fin d × Fin s) ℂ,
      W ∈ Matrix.unitaryGroup (Fin d × Fin s) ℂ ∧
      ∀ (t : ℕ) (label : Fin s → Fin t) (accept : Fin t → Bool),
        observedWellFormed (relabelObserved finProdFinEquiv
          (krausReadoutProgram W label accept)) ∧
        observedQueryBudget (relabelObserved finProdFinEquiv
          (krausReadoutProgram W label accept)) = 0 ∧
        ∀ (O : Operator (d*s)) (rho : Operator d),
          (observedMixedTraces O (relabelObserved finProdFinEquiv
            (krausReadoutProgram W label accept))
            (relabelGate finProdFinEquiv (TensorGate rho (outerProduct (Qatlib.Foundations.PureStateMath.Ket zero))))).map
              (reduceKrausMixedTrace (d := d) (s := s)) =
            List.ofFn (fun o : Fin t =>
              (⟨∑ a : Fin s, if label a = o then K a*rho*(K a).conjTranspose else 0,
                accept o, 0, 1, 1, [(t,o.val)]⟩ : MixedBranchTrace d)) := by
  obtain ⟨W,hWU,hW⟩ := kraus_unitary_dilation K hK zero
  refine ⟨W,hWU,?_⟩
  intro t label accept
  have hphysical := kraus_readout_valid_budget W hWU label accept
  refine ⟨relabelObserved_wellFormed finProdFinEquiv _ hphysical.1, ?_, ?_⟩
  · rw [relabelObserved_budget]
    exact hphysical.2
  · intro O rho
    exact kraus_readout_mixed_traces K zero W hW label accept O rho

end Qatlib.Concepts.Execution.KnownKraus
