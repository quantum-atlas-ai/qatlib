/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativePredicateReflection

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
/-! Coherent target fibers for the actual signed-MCX word. The fiber wire
is absent from the controls, MCX target, and allocated clean pool. This is
the separation needed when uncomputing after a rational pivot rotation. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical

/-- The emitted program has the displayed exact basis or coherent-fibre action. -/
theorem nativeSignedMcx_fiber {N : ℕ} (pattern : List (Fin N × Bool))
    (work pivot : Fin N) (pool : List (Fin N))
    (hnd : (pattern.map Prod.fst++[work]++pool).Nodup)
    (hbudget : pattern.length-2 ≤ pool.length) (hpw : pivot≠work)
    (hcontrols : ∀ p∈pattern,p.1≠pivot) (hp : pivot∉pool)
    (x : Reg N) (hc : ∀ w∈pool,x w=false) (φ : QState Bool) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (nativeSignedMcx pattern work pool))
      (multiWireState pivot x φ) =
      multiWireState pivot
        (Function.update x work (x work ^^ pattern.all (fun p => x p.1 == p.2))) φ := by
  have hcb (b : Bool) : ∀ w∈pool,(Function.update x pivot b) w=false := by
    intro w hw
    have hwp : w≠pivot := by intro he; exact hp (he ▸ hw)
    rw [Function.update_of_ne hwp]
    exact hc w hw
  have hb (b : Bool) :
      Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (nativeSignedMcx pattern work pool))
        (Qatlib.Foundations.PureStateMath.Ket (Function.update x pivot b)) =
        Qatlib.Foundations.PureStateMath.Ket (Function.update
          (Function.update x work (x work ^^ pattern.all (fun p => x p.1 == p.2))) pivot b) := by
    rw [nativeSignedMcx_basis pattern work pool hnd hbudget _ (hcb b),
      nativePattern_update pattern x pivot b hcontrols, Function.update_of_ne hpw.symm,
      Function.update_comm hpw]
  simp only [run_reflectionCompile] at hb
  simp only [multiWireState, run_reflectionCompile, reflectionApplyGate_add,
    reflectionApplyGate_smul, hb]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
