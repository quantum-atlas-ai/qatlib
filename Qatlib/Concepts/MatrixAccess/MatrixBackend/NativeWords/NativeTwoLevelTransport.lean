/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeTwoLevelWord

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-! Constructed physical pair operator and clean coherent-frame transport
of the actual two-level word. Binary label/Option identification and table
composition remain distinct from this wire-parametric source refinement. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical

/-- Construction for native Pair Column in the native two level transport model. -/
def nativePairColumn {N : ℕ} (controls : List (Fin N)) (pivot : Fin N)
    (targets : List (Fin N)) (r : Circle) (x : Reg N) : QState (Reg N) :=
  if controls.all (fun w => !nativePivotBasis pivot targets x w) then
    rotation r false (x pivot) • Qatlib.Foundations.PureStateMath.Ket (nativePairAddress pivot targets x false) +
    rotation r true (x pivot) • Qatlib.Foundations.PureStateMath.Ket (nativePairAddress pivot targets x true)
  else Qatlib.Foundations.PureStateMath.Ket x

/-- Construction for native Pair Gate in the native two level transport model. -/
def nativePairGate {N : ℕ} (controls : List (Fin N)) (pivot : Fin N)
    (targets : List (Fin N)) (r : Circle) : Matrix (Reg N) (Reg N) ℂ :=
  fun row col => nativePairColumn controls pivot targets r col row

/-- The emitted program has the displayed exact basis or coherent-fibre action. -/
theorem nativePairGate_ket {N : ℕ} (controls : List (Fin N)) (pivot : Fin N)
    (targets : List (Fin N)) (r : Circle) (x : Reg N) :
    ApplyGate (nativePairGate controls pivot targets r) (Qatlib.Foundations.PureStateMath.Ket x) =
      nativePairColumn controls pivot targets r x := by
  funext row
  exact Qatlib.Concepts.BlockEncoding.LinearCombination.mulVec_ket_apply _ x row

/-- The emitted program has the displayed exact basis or coherent-fibre action. -/
theorem nativeTwoLevelWord_state {N : ℕ} (controls : List (Fin N)) (work pivot : Fin N)
    (pool targets : List (Fin N)) (r : Circle)
    (hnd : (controls++[work]++pool).Nodup) (hbudget : controls.length-2 ≤ pool.length)
    (htnd : targets.Nodup) (htsub : ∀ w∈targets,w∈controls)
    (hpw : pivot≠work) (hpc : pivot∉controls) (hp : pivot∉pool)
    (ψ : QState (Reg N)) (hsupport : ∀ x,ψ x≠0 → (∀ w∈pool,x w=false) ∧ x work=false) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (nativeTwoLevelWord controls work pivot pool targets r)) ψ =
      ApplyGate (nativePairGate controls pivot targets r) ψ := by
  rw [run_reflectionCompile]
  conv_lhs => rw [state_ket_expansion ψ]
  conv_rhs => rw [state_ket_expansion ψ]
  simp only [ApplyGate, Matrix.mulVec_sum, Matrix.mulVec_smul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ψ x=0
  · simp [hx]
  · obtain ⟨hc,hw⟩ := hsupport x hx
    change ψ x • ApplyGate _ (Qatlib.Foundations.PureStateMath.Ket x) = ψ x • ApplyGate _ (Qatlib.Foundations.PureStateMath.Ket x)
    rw [← run_reflectionCompile,
      nativeTwoLevelWord_basis controls work pivot pool targets r hnd hbudget htnd htsub hpw hpc hp x hc hw,
      nativePairGate_ket]
    rfl

/-- The actual native matrix satisfies the stated frame-transport identity. -/
theorem nativeTwoLevelWord_frame {N : ℕ} {I : Type*} (controls : List (Fin N)) (work pivot : Fin N)
    (pool targets : List (Fin N)) (r : Circle)
    (hnd : (controls++[work]++pool).Nodup) (hbudget : controls.length-2 ≤ pool.length)
    (htnd : targets.Nodup) (htsub : ∀ w∈targets,w∈controls)
    (hpw : pivot≠work) (hpc : pivot∉controls) (hp : pivot∉pool)
    (F : Matrix (Reg N) I ℂ)
    (hsupport : ∀ x i,F x i≠0 → (∀ w∈pool,x w=false) ∧ x work=false) :
    reflectionProgramMatrix (nativeTwoLevelWord controls work pivot pool targets r) * F =
      nativePairGate controls pivot targets r * F := by
  ext x i
  have hh := nativeTwoLevelWord_state controls work pivot pool targets r hnd hbudget htnd htsub
    hpw hpc hp (fun x => F x i) (fun x hx => hsupport x i hx)
  rw [run_reflectionCompile] at hh
  exact congrFun hh x

/-- The same emitted program has the displayed exact query and elementary-gate counts. -/
theorem nativeTwoLevelWord_counts {N : ℕ} (controls : List (Fin N)) (work pivot : Fin N)
    (pool targets : List (Fin N)) (r : Circle) (hbudget : controls.length-2 ≤ pool.length) :
    QueryCount (reflectionCompile (nativeTwoLevelWord controls work pivot pool targets r)) = 0 ∧
    GateCount (reflectionCompile (nativeTwoLevelWord controls work pivot pool targets r)) =
      2*targets.length+2*(2*controls.length+
        (if controls.length≤1 then 1 else 15*(2*controls.length-3)))+6 := by
  have hlen : (nativePredicateCircleWord (nativeZeroPattern controls) work pivot pool r).length =
      2*(2*controls.length+(if controls.length≤1 then 1 else 15*(2*controls.length-3)))+6 := by
    have hc := (nativePredicateCircle_counts (nativeZeroPattern controls) work pivot pool r
      (by simpa [nativeZeroPattern] using hbudget)).2
    rw [gateCount_reflectionCompile] at hc
    simpa [nativeZeroPattern, nativeNegativeWires, List.filter_map, List.map_map,
      Function.comp_def] using hc
  refine ⟨queryCount_reflectionCompile _,?_⟩
  rw [gateCount_reflectionCompile]
  simp only [nativeTwoLevelWord, List.length_append, hlen, nativePivotMoves,
    List.length_map, List.length_reverse]
  omega

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
