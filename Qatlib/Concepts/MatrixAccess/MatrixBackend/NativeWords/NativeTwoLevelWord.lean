/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.LinearCombination
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativePredicateCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativePivotMoves
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeOriginReflection

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
/-! The actual pivot-CNOT/predicate/CRY_Q/uncompute/reverse-CNOT source word.
The two endpoints are physical addresses; the binary integer/Option label
identification is a subsequent interface, not a correctness premise here. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical

/-- Construction for native Pair Address in the native two level word model. -/
def nativePairAddress {N : ℕ} (pivot : Fin N) (targets : List (Fin N)) (x : Reg N) (b : Bool) : Reg N :=
  fun w => if w=pivot ∨ w∈targets then b else x w

/-- The finite native construction `nativePivot_endpoint` satisfies the displayed exact coordinate or algebraic relation. -/
theorem nativePivot_endpoint {N : ℕ} (pivot : Fin N) (targets : List (Fin N))
    (hp : pivot∉targets) (x : Reg N)
    (hz : ∀ w∈targets,nativePivotBasis pivot targets x w=false) (b : Bool) :
    nativePivotBasis pivot targets (Function.update (nativePivotBasis pivot targets x) pivot b) =
      nativePairAddress pivot targets x b := by
  funext w
  by_cases hwp : w=pivot
  · subst w
    simp [nativePivotBasis, nativePairAddress, hp]
  · by_cases ht : w∈targets
    · have hh : (x w ^^ x pivot)=false := by simpa [nativePivotBasis, ht] using hz w ht
      simp [nativePivotBasis, nativePairAddress, hwp, ht, hh]
    · simp [nativePivotBasis, nativePairAddress, hwp, ht]

/-- Construction for native Two Level Word in the native two level word model. -/
def nativeTwoLevelWord {N : ℕ} (controls : List (Fin N)) (work pivot : Fin N)
    (pool targets : List (Fin N)) (r : Circle) : List (ReflectionGate N) :=
  nativePivotMoves pivot targets ++
    nativePredicateCircleWord (nativeZeroPattern controls) work pivot pool r ++
    nativePivotMoves pivot targets.reverse

/-- Exactly the source two-level action. In the enabled branch the addresses
set the pivot and its source CNOT targets simultaneously to zero or one;
all other coordinates, including work/pool and spectators, retain x. -/
theorem nativeTwoLevelWord_basis {N : ℕ} (controls : List (Fin N)) (work pivot : Fin N)
    (pool targets : List (Fin N)) (r : Circle)
    (hnd : (controls++[work]++pool).Nodup) (hbudget : controls.length-2 ≤ pool.length)
    (htnd : targets.Nodup) (htsub : ∀ w∈targets,w∈controls)
    (hpw : pivot≠work) (hpc : pivot∉controls) (hp : pivot∉pool)
    (x : Reg N) (hc : ∀ w∈pool,x w=false) (hw : x work=false) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (nativeTwoLevelWord controls work pivot pool targets r)) (Qatlib.Foundations.PureStateMath.Ket x) =
      if controls.all (fun w => !nativePivotBasis pivot targets x w) then
        rotation r false (x pivot) • Qatlib.Foundations.PureStateMath.Ket (nativePairAddress pivot targets x false) +
        rotation r true (x pivot) • Qatlib.Foundations.PureStateMath.Ket (nativePairAddress pivot targets x true)
      else Qatlib.Foundations.PureStateMath.Ket x := by
  let y := nativePivotBasis pivot targets x
  have hpt : pivot∉targets := fun ht => hpc (htsub pivot ht)
  have hn : (controls++(work::pool)).Nodup := by
    simpa only [List.append_assoc, List.singleton_append] using hnd
  have hd := (List.nodup_append.mp hn).2.2
  have hwt : work∉targets := fun ht => hd work (htsub work ht) work (by simp) rfl
  have hcy : ∀ w∈pool,y w=false := by
    intro w hm
    have he : w∉targets := fun ht => hd w (htsub w ht) w (by simp [hm]) rfl
    exact (nativePivotBasis_outside pivot targets x w he).trans (hc w hm)
  have hwy : y work=false := (nativePivotBasis_outside pivot targets x work hwt).trans hw
  have hcp (p : Fin N × Bool) (hm : p∈nativeZeroPattern controls) : p.1≠pivot := by
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    exact fun he => hpc (he ▸ hw)
  have hmid : Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (nativePredicateCircleWord (nativeZeroPattern controls) work pivot pool r))
      (Qatlib.Foundations.PureStateMath.Ket y) = multiWireState pivot y
        (ApplyGate (if controls.all (fun w => !y w) then rotation r else 1) (Qatlib.Foundations.PureStateMath.Ket (y pivot))) := by
    simpa [nativeZeroPattern, List.all_map] using
      nativePredicateCircle_fiber (nativeZeroPattern controls) work pivot pool r
        (by simpa [nativeZeroPattern, List.map_map, Function.comp_def] using hnd)
        (by simpa [nativeZeroPattern] using hbudget) hpw hcp hp y hcy hwy (Qatlib.Foundations.PureStateMath.Ket (y pivot))
  simp only [nativeTwoLevelWord, reflectionCompile_append, run_append]
  rw [nativePivotMoves_basis pivot targets htnd hpt, hmid]
  by_cases hm : controls.all (fun w => !y w)=true
  · rw [ite_eq_left hm, ite_eq_left hm]
    have hz (w : Fin N) (ht : w∈targets) : nativePivotBasis pivot targets x w=false := by
      have hh := List.all_eq_true.mp hm w (htsub w ht)
      simpa [y] using hh
    have hb (b : Bool) : ApplyGate (reflectionProgramMatrix (nativePivotMoves pivot targets.reverse))
        (Qatlib.Foundations.PureStateMath.Ket (Function.update y pivot b)) = Qatlib.Foundations.PureStateMath.Ket (nativePairAddress pivot targets x b) := by
      rw [← run_reflectionCompile, nativePivotMoves_reverse_basis pivot targets htnd hpt,
        nativePivot_endpoint pivot targets hpt x hz b]
    simp only [multiWireState, run_reflectionCompile, reflectionApplyGate_add, reflectionApplyGate_smul, hb]
    simp only [ApplyGate, Qatlib.Concepts.BlockEncoding.LinearCombination.mulVec_ket_apply, y, nativePivotBasis_pivot pivot targets hpt x]
  · rw [ite_eq_right hm, ite_eq_right hm, applyGate_one, multiWireState_ket]
    exact nativePivotMoves_uncompute pivot targets htnd hpt x

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem nativeTwoLevelWord_legal {N : ℕ} (controls : List (Fin N)) (work pivot : Fin N)
    (pool targets : List (Fin N)) (r : Circle)
    (hnd : (controls++[work]++pool).Nodup) (hbudget : controls.length-2 ≤ pool.length)
    (htsub : ∀ w∈targets,w∈controls) (hpw : pivot≠work) (hpc : pivot∉controls) :
    reflectionLegal (nativeTwoLevelWord controls work pivot pool targets r) := by
  have hpt : pivot∉targets := fun ht => hpc (htsub pivot ht)
  rw [nativeTwoLevelWord, reflectionLegal_append, reflectionLegal_append]
  exact ⟨⟨nativePivotMoves_legal pivot targets hpt,
    nativePredicateCircle_legal (nativeZeroPattern controls) work pivot pool r
      (by simpa [nativeZeroPattern, List.map_map, Function.comp_def] using hnd)
      (by simpa [nativeZeroPattern] using hbudget) hpw⟩,
    nativePivotMoves_legal pivot targets.reverse (by simpa using hpt)⟩

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
