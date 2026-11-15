/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.OrderedOracle.TiSdpBridge.Corollary20InvariantSolutionsStat
public import Qatlib.Concepts.OrderedOracle.TiSdpBridge.Proposition19CyclicSymmetryTran
public import Qatlib.Concepts.OrderedOracle.TiSdpBridge.BSSSdpSymmetry

@[expose] public section
open Qatlib.Concepts.OrderedOracle.TiSdpBridge

set_option autoImplicit false
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Qatlib
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Qatlib.Concepts.OrderedOracle.TiSdpBridge

/-- Every feasible ordered-search BSS instance admits an invariant feasible matrix family. -/
theorem corollary20InvariantSolutions : Corollary20InvariantSolutions := by
  intro n k _ ε h
  obtain ⟨M,N,Γ,hf,hinv⟩ := bssFeasible_exists_symmetry_invariant (ospBit n) (ospFun n) k ε h
  have h := hinv (finShiftEquiv (2*n)) (finShiftEquiv (2*n)).symm (finShiftEquiv n)
    (proposition19CyclicSymmetry n)
  refine ⟨M,N,Γ,?_,hf⟩
  refine ⟨?_,h.2.1,?_⟩
  · intro i t x x'
    have hh := h.1 ((finShiftEquiv (2*n)).symm i) t x x'
    simpa only [Equiv.symm_symm,Equiv.apply_symm_apply] using hh
  · intro y x x'
    have hh := h.2.2 ((finShiftEquiv n).symm y) x x'
    simpa only [Equiv.apply_symm_apply] using hh
end Qatlib.Concepts.OrderedOracle.TiSdpBridge
