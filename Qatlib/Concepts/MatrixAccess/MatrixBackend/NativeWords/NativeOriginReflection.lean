/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativePredicateReflection

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
/-! The emitter's actual all-zero-label reflection, with physical seed and
clean work/pool. Its projector fixes the specified label wires to zero and
retains arbitrary spectator data; there is no supplied predicate oracle. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical

/-- Construction for native Zero Pattern in the native origin reflection model. -/
def nativeZeroPattern {N : ℕ} (labels : List (Fin N)) : List (Fin N × Bool) :=
  labels.map (fun w => (w,false))

/-- Construction for native Origin Word in the native origin reflection model. -/
def nativeOriginWord {N : ℕ} (labels : List (Fin N)) (work seed : Fin N)
    (pool : List (Fin N)) : List (ReflectionGate N) :=
  nativePredicateReflection (nativeZeroPattern labels) work seed pool

/-- Identity on all spectators, projection onto zero on the specified labels. -/
def nativeLabelZeroProjector {N : ℕ} (labels : List (Fin N)) : Matrix (Reg N) (Reg N) ℂ :=
  Matrix.diagonal (fun x => if labels.all (fun w => !x w) then 1 else 0)

/-- The finite native construction `nativeLabelZeroProjector_orthogonal` satisfies the displayed exact coordinate or algebraic relation. -/
theorem nativeLabelZeroProjector_orthogonal {N : ℕ} (labels : List (Fin N)) :
    IsOrthogonalProjector (nativeLabelZeroProjector labels) := by
  constructor
  · change nativeLabelZeroProjector labels * nativeLabelZeroProjector labels =
      nativeLabelZeroProjector labels
    rw [nativeLabelZeroProjector, Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    split <;> norm_num
  · change (nativeLabelZeroProjector labels)ᴴ = nativeLabelZeroProjector labels
    rw [nativeLabelZeroProjector, Matrix.diagonal_conjTranspose]
    congr 1
    funext x
    by_cases h : labels.all (fun w => !x w) = true <;> simp_all

/-- The constructed finite matrix is unitary under the stated hypotheses. -/
theorem nativeLabelZeroReflection_unitary {N : ℕ} (labels : List (Fin N)) :
    ReflectionAbout (nativeLabelZeroProjector labels) ∈ unitaryGroup (Reg N) ℂ :=
  reflectionAbout_unitary (nativeLabelZeroProjector_orthogonal labels)

/-- The finite native construction `nativeLabelZero_reflection` satisfies the displayed exact coordinate or algebraic relation. -/
theorem nativeLabelZero_reflection {N : ℕ} (labels : List (Fin N)) :
    Matrix.diagonal (fun x : Reg N => if labels.all (fun w => !x w) then (1 : ℂ) else -1) =
      ReflectionAbout (nativeLabelZeroProjector labels) := by
  ext x y
  by_cases hxy : x=y
  · subst y
    simp only [ReflectionAbout, nativeLabelZeroProjector, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    split <;> norm_num
  · simp [ReflectionAbout, nativeLabelZeroProjector, hxy]

/-- The emitted program has the displayed exact basis or coherent-fibre action. -/
theorem nativeOriginWord_state {N : ℕ} (labels : List (Fin N)) (work seed : Fin N)
    (pool : List (Fin N)) (hnd : (labels++[work]++pool).Nodup)
    (hbudget : labels.length-2 ≤ pool.length) (ψ : QState (Reg N))
    (hsupport : ∀ x,ψ x≠0 → (∀ w∈pool,x w=false) ∧ x work=false ∧ x seed=true) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (nativeOriginWord labels work seed pool)) ψ =
      ApplyGate (ReflectionAbout (nativeLabelZeroProjector labels)) ψ := by
  rw [← nativeLabelZero_reflection]
  have hp := nativePredicateReflection_state (nativeZeroPattern labels) work seed pool
    (by simpa [nativeZeroPattern, List.map_map, Function.comp_def] using hnd)
    (by simpa [nativeZeroPattern] using hbudget) ψ hsupport
  simpa [nativeOriginWord, nativeZeroPattern, List.all_map] using hp

/-- Physical clean-frame transport for every coherent column, so arbitrary
original data frames and entangled spectators can be retained. -/
theorem nativeOriginWord_frame {N : ℕ} {I : Type*} (labels : List (Fin N)) (work seed : Fin N)
    (pool : List (Fin N)) (hnd : (labels++[work]++pool).Nodup)
    (hbudget : labels.length-2 ≤ pool.length) (F : Matrix (Reg N) I ℂ)
    (hsupport : ∀ x i,F x i≠0 → (∀ w∈pool,x w=false) ∧ x work=false ∧ x seed=true) :
    reflectionProgramMatrix (nativeOriginWord labels work seed pool) * F =
      ReflectionAbout (nativeLabelZeroProjector labels) * F := by
  ext x i
  have hh := nativeOriginWord_state labels work seed pool hnd hbudget (fun x => F x i)
    (fun x hx => hsupport x i hx)
  rw [run_reflectionCompile] at hh
  exact congrFun hh x

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem nativeOriginWord_legal {N : ℕ} (labels : List (Fin N)) (work seed : Fin N)
    (pool : List (Fin N)) (hnd : (labels++[work]++pool).Nodup)
    (hbudget : labels.length-2 ≤ pool.length) : reflectionLegal (nativeOriginWord labels work seed pool) :=
  nativePredicateReflection_legal _ work seed pool
    (by simpa [nativeZeroPattern, List.map_map, Function.comp_def] using hnd)
    (by simpa [nativeZeroPattern] using hbudget)

/-- The same emitted program has the displayed exact query and elementary-gate counts. -/
theorem nativeOriginWord_counts {N : ℕ} (labels : List (Fin N)) (work seed : Fin N)
    (pool : List (Fin N)) (hbudget : labels.length-2 ≤ pool.length) :
    QueryCount (reflectionCompile (nativeOriginWord labels work seed pool)) = 0 ∧
    GateCount (reflectionCompile (nativeOriginWord labels work seed pool)) =
      2*(2*labels.length+(if labels.length≤1 then 1 else 15*(2*labels.length-3)))+2 := by
  simpa [nativeOriginWord, nativeZeroPattern, nativeNegativeWires, List.filter_map,
    List.map_map, Function.comp_def] using nativePredicateReflection_counts (nativeZeroPattern labels) work seed pool
      (by simpa [nativeZeroPattern] using hbudget)

/-- The finite native construction `nativeLabelZeroProjector_nil` satisfies the displayed exact coordinate or algebraic relation. -/
theorem nativeLabelZeroProjector_nil (N : ℕ) :
    nativeLabelZeroProjector ([] : List (Fin N)) = 1 := by
  ext x y
  simp [nativeLabelZeroProjector, Matrix.diagonal_apply, Matrix.one_apply]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
