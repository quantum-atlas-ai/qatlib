/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeSignedMcxFiber
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
/-! Refine the source's known CRY_Q circle gate by the pinned exact six-gate
controlled-U(2) word, between two actual signed MCXs. These are exact known
one-qubit gates, not a fixed finite gate-set synthesis or bit-cost claim. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical

/-- Construction for native Circle Angles in the native predicate circle model. -/
def nativeCircleAngles (r : Circle) : KnownQubitAngles := knownQubitAnglesOfUnitary (rotation r)

/-- The finite native construction `nativeCircleAngles_correct` satisfies the displayed exact coordinate or algebraic relation. -/
theorem nativeCircleAngles_correct (r : Circle) :
    knownQubitUnitary (nativeCircleAngles r) = rotation r :=
  (knownQubitEuler_explicit_angles_cover_unitaries (rotation r) (rotation_unitary r)).1

/-- Construction for native Predicate Circle Word in the native predicate circle model. -/
def nativePredicateCircleWord {N : ℕ} (pattern : List (Fin N × Bool))
    (work pivot : Fin N) (pool : List (Fin N)) (r : Circle) : List (ReflectionGate N) :=
  nativeSignedMcx pattern work pool ++ multiKnownPairSteps work pivot (nativeCircleAngles r) ++
    nativeSignedMcx pattern work pool

/-- Compute the nonpivot predicate, rotate its full coherent pivot fiber,
then repeat the same actual MCX to restore work and every pool coordinate. -/
theorem nativePredicateCircle_fiber {N : ℕ} (pattern : List (Fin N × Bool))
    (work pivot : Fin N) (pool : List (Fin N)) (r : Circle)
    (hnd : (pattern.map Prod.fst++[work]++pool).Nodup)
    (hbudget : pattern.length-2 ≤ pool.length) (hpw : pivot≠work)
    (hpcontrols : ∀ p∈pattern,p.1≠pivot) (hp : pivot∉pool)
    (x : Reg N) (hc : ∀ w∈pool,x w=false) (hw : x work=false) (φ : QState Bool) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (nativePredicateCircleWord pattern work pivot pool r))
      (multiWireState pivot x φ) =
      multiWireState pivot x
        (ApplyGate (if pattern.all (fun p => x p.1 == p.2) then rotation r else 1) φ) := by
  let b := pattern.all (fun p => x p.1 == p.2)
  let y := Function.update x work b
  have hn : (pattern.map Prod.fst++(work::pool)).Nodup := by
    simpa only [List.append_assoc, List.singleton_append] using hnd
  have htpool := (List.nodup_cons.mp (List.nodup_append.mp hn).2.1).1
  have hcontrols (p : Fin N × Bool) (hm : p∈pattern) : p.1≠work :=
    (List.nodup_append.mp hn).2.2 p.1 (List.mem_map.mpr ⟨p,hm,rfl⟩) work (by simp)
  have hcy : ∀ w∈pool,y w=false := by
    intro w hm
    have he : w≠work := by intro he; exact htpool (he ▸ hm)
    exact (Function.update_of_ne he b x).trans (hc w hm)
  have hrestore : Function.update y work (y work ^^ pattern.all (fun p => y p.1 == p.2)) = x := by
    dsimp [y]
    rw [Function.update_self, nativePattern_update pattern x work b hcontrols]
    change Function.update (Function.update x work b) work (b ^^ b) = x
    simp only [Bool.xor_self, Function.update_idem]
    rw [← hw]
    exact Function.update_eq_self work x
  have hfront : Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (nativeSignedMcx pattern work pool)) (multiWireState pivot x φ) =
      multiWireState pivot y φ := by
    simpa only [hw, Bool.false_xor] using
      nativeSignedMcx_fiber pattern work pivot pool hnd hbudget hpw hpcontrols hp x hc φ
  have hback (ψ : QState Bool) : Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (nativeSignedMcx pattern work pool)) (multiWireState pivot y ψ) =
      multiWireState pivot x ψ := by
    rw [nativeSignedMcx_fiber pattern work pivot pool hnd hbudget hpw hpcontrols hp y hcy ψ,
      hrestore]
  simp only [nativePredicateCircleWord, reflectionCompile_append, run_append]
  rw [hfront, multiKnownPairSteps_action work pivot hpw.symm, hback]
  simp only [y, Function.update_self, nativeCircleAngles_correct]
  rfl

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem nativePredicateCircle_legal {N : ℕ} (pattern : List (Fin N × Bool))
    (work pivot : Fin N) (pool : List (Fin N)) (r : Circle)
    (hnd : (pattern.map Prod.fst++[work]++pool).Nodup)
    (hbudget : pattern.length-2 ≤ pool.length) (hpw : pivot≠work) :
    reflectionLegal (nativePredicateCircleWord pattern work pivot pool r) := by
  rw [nativePredicateCircleWord, reflectionLegal_append, reflectionLegal_append]
  exact ⟨⟨nativeSignedMcx_legal pattern work pool hnd hbudget,
    multiKnownPairSteps_legal work pivot hpw.symm _⟩,
    nativeSignedMcx_legal pattern work pool hnd hbudget⟩

/-- The same emitted program has the displayed exact query and elementary-gate counts. -/
theorem nativePredicateCircle_counts {N : ℕ} (pattern : List (Fin N × Bool))
    (work pivot : Fin N) (pool : List (Fin N)) (r : Circle)
    (hbudget : pattern.length-2 ≤ pool.length) :
    QueryCount (reflectionCompile (nativePredicateCircleWord pattern work pivot pool r)) = 0 ∧
    GateCount (reflectionCompile (nativePredicateCircleWord pattern work pivot pool r)) =
      2*(2*(nativeNegativeWires pattern).length+
        (if pattern.length≤1 then 1 else 15*(2*pattern.length-3)))+6 := by
  refine ⟨queryCount_reflectionCompile _,?_⟩
  rw [gateCount_reflectionCompile]
  simp only [nativePredicateCircleWord, List.length_append,
    nativeSignedMcx_length pattern work pool hbudget, multiKnownPairSteps, List.length_cons,
    List.length_nil]
  omega

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
