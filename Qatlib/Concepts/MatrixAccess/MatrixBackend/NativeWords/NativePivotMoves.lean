/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.ReflectionCompile.CleanZeroReflection

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-! The source's CNOT index moves: one common pivot control and distinct
target wires. The actual word and its reverse both realize this involution,
with every other physical wire retained. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical

/-- Construction for native Pivot Moves in the native pivot moves model. -/
def nativePivotMoves {N : ℕ} (pivot : Fin N) (targets : List (Fin N)) : List (ReflectionGate N) :=
  targets.map (fun t => .inr (pivot,t))

/-- Construction for native Pivot Basis in the native pivot moves model. -/
def nativePivotBasis {N : ℕ} (pivot : Fin N) (targets : List (Fin N)) (x : Reg N) : Reg N :=
  fun w => if w∈targets then x w ^^ x pivot else x w

/-- The emitted program has the displayed exact basis or coherent-fibre action. -/
theorem nativePivotMoves_basis {N : ℕ} (pivot : Fin N) (targets : List (Fin N))
    (hnd : targets.Nodup) (hp : pivot∉targets) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (nativePivotMoves pivot targets))
      (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (nativePivotBasis pivot targets x) := by
  induction targets generalizing x with
  | nil => rfl
  | cons t ts ih =>
    have hpt : pivot≠t := by intro he; exact hp (by simp [he])
    have hptail : pivot∉ts := fun hm => hp (by simp [hm])
    have httail : t∉ts := (List.nodup_cons.mp hnd).1
    have he : nativePivotMoves pivot (t::ts) = [.inr (pivot,t)]++nativePivotMoves pivot ts := rfl
    rw [he, reflectionCompile_append, run_append]
    change Run 1 (reflectionCompile (nativePivotMoves pivot ts))
      (ApplyGate (cnotGate N pivot t) (Qatlib.Foundations.PureStateMath.Ket x)) = _
    rw [applyGate_cnotGate_ket N pivot t hpt, ih hnd.tail hptail]
    congr 1
    funext w
    by_cases hwt : w=t
    · subst w
      simp [nativePivotBasis, httail]
    · by_cases hmem : w∈ts
      · simp [nativePivotBasis, hwt, hpt, hmem]
      · simp [nativePivotBasis, hwt, hmem]

/-- The finite native construction `nativePivotBasis_pivot` satisfies the displayed exact coordinate or algebraic relation. -/
theorem nativePivotBasis_pivot {N : ℕ} (pivot : Fin N) (targets : List (Fin N))
    (hp : pivot∉targets) (x : Reg N) : nativePivotBasis pivot targets x pivot=x pivot := by
  simp [nativePivotBasis, hp]

/-- The explicit unselected-address or padding condition gives the stated coordinate behaviour. -/
theorem nativePivotBasis_outside {N : ℕ} (pivot : Fin N) (targets : List (Fin N))
    (x : Reg N) (w : Fin N) (hw : w∉targets) : nativePivotBasis pivot targets x w=x w := by
  simp [nativePivotBasis, hw]

/-- The actual native inverse or adjoint satisfies the displayed operator identity. -/
theorem nativePivotBasis_involutive {N : ℕ} (pivot : Fin N) (targets : List (Fin N))
    (hp : pivot∉targets) : Function.Involutive (nativePivotBasis pivot targets) := by
  intro x
  funext w
  by_cases hw : w∈targets
  · simp [nativePivotBasis, hw, hp]
  · simp [nativePivotBasis, hw]

/-- The actual reverse program restores the original register under its stated premises. -/
theorem nativePivotMoves_reverse_basis {N : ℕ} (pivot : Fin N) (targets : List (Fin N))
    (hnd : targets.Nodup) (hp : pivot∉targets) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (nativePivotMoves pivot targets.reverse))
      (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (nativePivotBasis pivot targets x) := by
  rw [nativePivotMoves_basis pivot targets.reverse (by simpa using hnd) (by simpa using hp)]
  congr 1
  funext w
  simp [nativePivotBasis]

/-- The actual reverse program restores the original register under its stated premises. -/
theorem nativePivotMoves_uncompute {N : ℕ} (pivot : Fin N) (targets : List (Fin N))
    (hnd : targets.Nodup) (hp : pivot∉targets) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (nativePivotMoves pivot targets.reverse))
      (Qatlib.Foundations.PureStateMath.Ket (nativePivotBasis pivot targets x)) = Qatlib.Foundations.PureStateMath.Ket x := by
  rw [nativePivotMoves_reverse_basis pivot targets hnd hp,
    nativePivotBasis_involutive pivot targets hp]

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem nativePivotMoves_legal {N : ℕ} (pivot : Fin N) (targets : List (Fin N))
    (hp : pivot∉targets) : reflectionLegal (nativePivotMoves pivot targets) := by
  intro g hg
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hg
  exact fun he => hp (he ▸ ht)

/-- The same emitted program has the displayed exact query and elementary-gate counts. -/
theorem nativePivotMoves_counts {N : ℕ} (pivot : Fin N) (targets : List (Fin N)) :
    QueryCount (reflectionCompile (nativePivotMoves pivot targets)) = 0 ∧
    GateCount (reflectionCompile (nativePivotMoves pivot targets)) = targets.length := by
  refine ⟨queryCount_reflectionCompile _,?_⟩
  rw [gateCount_reflectionCompile]
  simp [nativePivotMoves]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
