/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeSignedMcx

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
/-! The actual middle predicate/Z/seed word of the Householder emitter.
The phase seed is a physical wire: its value is retained in the general
basis theorem, and only the seed-one specialization is the reflection. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical

/-- Construction for native Predicate Reflection in the native predicate reflection model. -/
def nativePredicateReflection {N : ℕ} (pattern : List (Fin N × Bool))
    (work seed : Fin N) (pool : List (Fin N)) : List (ReflectionGate N) :=
  nativeSignedMcx pattern work pool ++ [.inl (work,PauliZ)] ++
    nativeSignedMcx pattern work pool ++ [.inl (seed,PauliZ)]

/-- The emitted program has the displayed exact basis or coherent-fibre action. -/
theorem nativeZ_basis {N : ℕ} (w : Fin N) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile [.inl (w,PauliZ)]) (Qatlib.Foundations.PureStateMath.Ket x) =
      (if x w then (-1 : ℂ) else 1) • Qatlib.Foundations.PureStateMath.Ket x := by
  change ApplyGate (wireGate N w PauliZ) (Qatlib.Foundations.PureStateMath.Ket x) = _
  rw [applyGate_wireGate_ket]
  have hx : Function.update x w (x w) = x := Function.update_eq_self w x
  cases hb : x w
  all_goals rw [hb] at hx
  all_goals simp [PauliZ, hx]

/-- Updating a noncontrol wire leaves the signed predicate unchanged. -/
theorem nativePattern_update {N : ℕ} (pattern : List (Fin N × Bool)) (x : Reg N)
    (w : Fin N) (b : Bool) (hw : ∀ p∈pattern,p.1≠w) :
    pattern.all (fun p => Function.update x w b p.1 == p.2) =
      pattern.all (fun p => x p.1 == p.2) := by
  induction pattern with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.all_cons, Function.update_of_ne (hw p (by simp)),
      ih (fun q hq => hw q (by simp [hq]))]

/-- The physical seed sign is explicit. Controls and every spectator, work
and pool wire return to their input values; the initial work bit is zero. -/
theorem nativePredicateReflection_basis_general {N : ℕ} (pattern : List (Fin N × Bool))
    (work seed : Fin N) (pool : List (Fin N))
    (hnd : (pattern.map Prod.fst++[work]++pool).Nodup)
    (hbudget : pattern.length-2 ≤ pool.length) (x : Reg N)
    (hclean : ∀ w∈pool,x w=false) (hwork : x work=false) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (nativePredicateReflection pattern work seed pool)) (Qatlib.Foundations.PureStateMath.Ket x) =
      ((if x seed then (-1 : ℂ) else 1) *
        (if pattern.all (fun p => x p.1 == p.2) then (-1 : ℂ) else 1)) • Qatlib.Foundations.PureStateMath.Ket x := by
  let b := pattern.all (fun p => x p.1 == p.2)
  have hn : (pattern.map Prod.fst++(work::pool)).Nodup := by
    simpa only [List.append_assoc, List.singleton_append] using hnd
  have htpool := (List.nodup_cons.mp (List.nodup_append.mp hn).2.1).1
  have hcontrols (p : Fin N × Bool) (hp : p∈pattern) : p.1≠work :=
    (List.nodup_append.mp hn).2.2 p.1 (List.mem_map.mpr ⟨p,hp,rfl⟩) work (by simp)
  have hc : ∀ w∈pool,(Function.update x work b) w=false := by
    intro w hw
    have he : w≠work := by intro he; exact htpool (he ▸ hw)
    rw [Function.update_of_ne he]
    exact hclean w hw
  have hfront : Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (nativeSignedMcx pattern work pool)) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x work b) := by
    simpa [hwork, b] using nativeSignedMcx_basis pattern work pool hnd hbudget x hclean
  have hback : Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (nativeSignedMcx pattern work pool)) (Qatlib.Foundations.PureStateMath.Ket (Function.update x work b)) =
      Qatlib.Foundations.PureStateMath.Ket x := by
    rw [nativeSignedMcx_basis pattern work pool hnd hbudget _ hc,
      nativePattern_update pattern x work b hcontrols]
    congr 1
    funext w
    by_cases hw : w=work
    · subst w
      simp [b, hwork]
    · simp [Function.update_of_ne hw]
  simp only [nativePredicateReflection, reflectionCompile_append, run_append]
  rw [hfront, nativeZ_basis, run_reflectionCompile_smul, hback,
    run_reflectionCompile_smul, nativeZ_basis]
  simp only [Function.update_self, smul_smul]
  rw [mul_comm]

/-- The emitted program has the displayed exact basis or coherent-fibre action. -/
theorem nativePredicateReflection_basis {N : ℕ} (pattern : List (Fin N × Bool))
    (work seed : Fin N) (pool : List (Fin N))
    (hnd : (pattern.map Prod.fst++[work]++pool).Nodup)
    (hbudget : pattern.length-2 ≤ pool.length) (x : Reg N)
    (hclean : ∀ w∈pool,x w=false) (hwork : x work=false) (hseed : x seed=true) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (nativePredicateReflection pattern work seed pool)) (Qatlib.Foundations.PureStateMath.Ket x) =
      (if pattern.all (fun p => x p.1 == p.2) then (1 : ℂ) else -1) • Qatlib.Foundations.PureStateMath.Ket x := by
  rw [nativePredicateReflection_basis_general pattern work seed pool hnd hbudget x hclean hwork]
  split <;> simp_all

/-- The same physical action on arbitrary coherent states supported in the
clean seed-one subspace, including entangled spectator data. -/
theorem nativePredicateReflection_state {N : ℕ} (pattern : List (Fin N × Bool))
    (work seed : Fin N) (pool : List (Fin N))
    (hnd : (pattern.map Prod.fst++[work]++pool).Nodup)
    (hbudget : pattern.length-2 ≤ pool.length) (ψ : QState (Reg N))
    (hsupport : ∀ x,ψ x≠0 → (∀ w∈pool,x w=false) ∧ x work=false ∧ x seed=true) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (nativePredicateReflection pattern work seed pool)) ψ =
      ApplyGate (Matrix.diagonal (fun x =>
        if pattern.all (fun p => x p.1 == p.2) then (1 : ℂ) else -1)) ψ := by
  rw [run_reflectionCompile]
  conv_lhs => rw [state_ket_expansion ψ]
  conv_rhs => rw [state_ket_expansion ψ]
  simp only [ApplyGate, Matrix.mulVec_sum, Matrix.mulVec_smul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ψ x=0
  · simp [hx]
  · obtain ⟨hc,hw,hs⟩ := hsupport x hx
    change ψ x • ApplyGate _ (Qatlib.Foundations.PureStateMath.Ket x) = ψ x • ApplyGate _ (Qatlib.Foundations.PureStateMath.Ket x)
    rw [← run_reflectionCompile,
      nativePredicateReflection_basis pattern work seed pool hnd hbudget x hc hw hs,
      applyGate_diagonal_ket]

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem nativePredicateReflection_legal {N : ℕ} (pattern : List (Fin N × Bool))
    (work seed : Fin N) (pool : List (Fin N))
    (hnd : (pattern.map Prod.fst++[work]++pool).Nodup)
    (hbudget : pattern.length-2 ≤ pool.length) :
    reflectionLegal (nativePredicateReflection pattern work seed pool) := by
  have hz (w : Fin N) : reflectionLegal [.inl (w,PauliZ)] := by
    intro g hg
    have he : g = .inl (w,PauliZ) := by simpa using hg
    subst g
    exact pauliZ_unitary
  simp only [nativePredicateReflection, reflectionLegal_append]
  exact ⟨⟨⟨nativeSignedMcx_legal pattern work pool hnd hbudget,hz work⟩,
    nativeSignedMcx_legal pattern work pool hnd hbudget⟩,hz seed⟩

/-- The same emitted program has the displayed exact query and elementary-gate counts. -/
theorem nativePredicateReflection_counts {N : ℕ} (pattern : List (Fin N × Bool))
    (work seed : Fin N) (pool : List (Fin N)) (hbudget : pattern.length-2 ≤ pool.length) :
    QueryCount (reflectionCompile (nativePredicateReflection pattern work seed pool)) = 0 ∧
    GateCount (reflectionCompile (nativePredicateReflection pattern work seed pool)) =
      2*(2*(nativeNegativeWires pattern).length +
        (if pattern.length≤1 then 1 else 15*(2*pattern.length-3)))+2 := by
  refine ⟨queryCount_reflectionCompile _,?_⟩
  rw [gateCount_reflectionCompile]
  simp only [nativePredicateReflection, List.length_append, List.length_cons, List.length_nil,
    nativeSignedMcx_length pattern work pool hbudget]
  omega

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
