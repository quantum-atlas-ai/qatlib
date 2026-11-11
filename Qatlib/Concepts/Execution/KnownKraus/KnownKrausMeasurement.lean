/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Execution.KnownKraus.KrausUnitaryDilation
import Qatlib.Concepts.Execution.KnownKraus.KrausDilationReadout

/-!
# Realization of known Kraus measurements

`known_kraus_measurement_realization` implements a finite complete family of square Kraus
operators by a unitary dilation followed by an ancilla measurement. This is a finite-dimensional
measurement construction as described in [NielsenChuang2010].

The unitary is chosen before the outcome labeling, acceptance rule, oracle, and input operator.
After tracing out the ancilla, each recorded branch is the corresponding coarse Kraus sum and
records zero queries, one known gate, and one measurement.

## Main statements

* `known_kraus_measurement_realization`: a single unitary realizes all coarse labelings of a
  complete Kraus family with query budget zero.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

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

/-- Every finite complete square Kraus family has a unitary realization that implements all
coarse outcome labelings with query budget zero. The reduced mixed traces are the
corresponding coarse Kraus sums, each recording zero queries, one gate, and one measurement
[NielsenChuang2010]. -/
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
