/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.MultiControl.Corollary710Stat

/-!
# Elementary synthesis of multi-controlled special unitaries

This module proves `corollary7_10`, a linear elementary-gate bound for multi-controlled qubit
unitaries of determinant one, in the setting of [BarencoEtAl1995]. The construction uses a
separate spectator wire and preserves the background register; `elementary_and_target` lifts
conjunction-toggle semantics from basis vectors to arbitrary target fibres.

## Main statements

* `elementary_and_target`: Extension of a basis conjunction toggle to a target fibre.
* `corollary7_10`: A legal, query-free implementation with length at most `240 * (m + 2)`.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.CircuitImpl.MultiControl

open Matrix

/-- Boolean sequences agreeing on the first `m` entries have the same prefix conjunction. -/
private theorem elementary_prefix_congr (a b : ℕ → Bool) (m : ℕ)
    (h : ∀ i < m, a i = b i) : noWorkPrefixAnd a m = noWorkPrefixAnd b m := by
  apply Bool.eq_iff_iff.mpr
  simp only [noWorkPrefixAnd, List.all_eq_true, List.mem_range]
  constructor
  · intro ha i hi
    rw [← h i hi]
    exact ha i hi
  · intro hb i hi
    rw [h i hi]
    exact hb i hi

/-- Running a compiled reflection-gate word preserves addition of states. -/
private theorem elementary_run_add {N : ℕ} (gs : List (ReflectionGate N))
    (ψ φ : QState (Reg N)) : Run 1 (reflectionCompile gs) (ψ + φ) =
      Run 1 (reflectionCompile gs) ψ + Run 1 (reflectionCompile gs) φ := by
  simp only [run_reflectionCompile, ApplyGate, Matrix.mulVec_add]

/-- A gate word that performs a conjunction-controlled target toggle on basis states acts on an
arbitrary target fibre by the corresponding controlled `PauliX`. -/
private theorem elementary_and_target {N : ℕ} (c : ℕ → Fin N) (m : ℕ) (t : Fin N)
    (hct : ∀ i < m, c i ≠ t) (gs : List (ReflectionGate N))
    (hgs : ∀ x : Reg N, Run 1 (reflectionCompile gs) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ noWorkPrefixAnd (fun i => x (c i)) m)))
    (x : Reg N) (φ : QState Bool) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile gs) (multiWireState t x φ) =
      multiWireState t x (ApplyGate
        (if noWorkPrefixAnd (fun i => x (c i)) m then PauliX else 1) φ) := by
  have he (v : Bool) : noWorkPrefixAnd (fun i => Function.update x t v (c i)) m =
      noWorkPrefixAnd (fun i => x (c i)) m :=
    elementary_prefix_congr _ _ _ (fun i hi => Function.update_of_ne (hct i hi) _ _)
  have hk (v : Bool) : Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile gs)
      (Qatlib.Foundations.PureStateMath.Ket (Function.update x t v)) =
        Qatlib.Foundations.PureStateMath.Ket (Function.update x t (v ^^ noWorkPrefixAnd (fun i => x (c i)) m)) := by
    rw [hgs, Function.update_self, he, Function.update_idem]
  simp only [multiWireState, elementary_run_add, run_reflectionCompile_smul, hk]
  have hflip (b : Bool) : ApplyGate PauliX φ b = φ (!b) :=
    applyGate_permMatrix Bool.not_not φ b
  cases ha : noWorkPrefixAnd (fun i => x (c i)) m <;>
    simp [applyGate_one, hflip, add_comm]

/-- Every qubit unitary of determinant one with `m` distinct controls and a separate spectator
wire has a legal, query-free implementation of length at most `240 * (m + 2)` [Barenco et
al., Corollary 7.10][BarencoEtAl1995]. -/
theorem corollary7_10 : Corollary7_10 := by
  intro N m c s t hc hcs hct hst W hW hdet
  cases m with
  | zero =>
    refine ⟨[.inl (t, W)], ?_, by simp, queryCount_reflectionCompile _,
      gateCount_reflectionCompile _, ?_⟩
    · intro g hg
      obtain rfl := List.mem_singleton.mp hg
      exact hW
    · intro x φ
      simp only [reflectionCompile, List.map_cons, List.map_nil, run_gate, run_nil,
        reflectionGateMatrix]
      simpa [noWorkPrefixAnd] using! multiWireState_single t x W φ
  | succ m =>
    let p := knownQubitAnglesOfUnitary W
    have hp : knownQubitUnitary p = W := (knownQubitEuler_explicit_angles_cover_unitaries W hW).1
    have hd : p.delta = 0 := by simp [p, knownQubitAnglesOfUnitary, hdet, Complex.arg_one]
    let A := knownQubitUnitary (knownControlA p)
    let B := knownQubitUnitary (knownControlB p)
    let C := knownQubitUnitary (knownControlC p)
    have hABC : A * B * C = 1 := (knownQubitControl_ABC_phase_factorization p).1
    have hAXBXC : A * PauliX * B * PauliX * C = W := by
      have h := (knownQubitControl_ABC_phase_factorization p).2.1
      simpa only [hd, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul, hp] using! h
    have hcm : Set.InjOn c (Set.Iio m) := fun i hi j hj he =>
      hc (show i < m + 1 by change i < m at hi; omega)
        (show j < m + 1 by change j < m at hj; omega) he
    have hcs' : ∀ i < m, c i ≠ s := fun i hi => hcs i (by omega)
    have hct' : ∀ i < m, c i ≠ t := fun i hi => hct i (by omega)
    have hlast : c m ≠ t := hct m (by omega)
    obtain ⟨xs, hxs, hxlen, hx⟩ := noWork_single_dirty_and_table c s t m hcm hcs' hct' hst
    let pa := knownQubitAnglesOfUnitary A
    let pb := knownQubitAnglesOfUnitary B
    let pc := knownQubitAnglesOfUnitary C
    have hpa : knownQubitUnitary pa = A :=
      (knownQubitEuler_explicit_angles_cover_unitaries A (knownQubitUnitary_unitary _)).1
    have hpb : knownQubitUnitary pb = B :=
      (knownQubitEuler_explicit_angles_cover_unitaries B (knownQubitUnitary_unitary _)).1
    have hpc : knownQubitUnitary pc = C :=
      (knownQubitEuler_explicit_angles_cover_unitaries C (knownQubitUnitary_unitary _)).1
    let as := multiKnownPairSteps (c m) t pa
    let bs := multiKnownPairSteps (c m) t pb
    let cs := multiKnownPairSteps (c m) t pc
    have has := multiKnownPairSteps_legal (c m) t hlast pa
    have hbs := multiKnownPairSteps_legal (c m) t hlast pb
    have hcss := multiKnownPairSteps_legal (c m) t hlast pc
    refine ⟨cs ++ xs ++ bs ++ xs ++ as, ?_, ?_, queryCount_reflectionCompile _,
      gateCount_reflectionCompile _, ?_⟩
    · simp only [reflectionLegal_append]
      exact ⟨⟨⟨⟨hcss, hxs⟩, hbs⟩, hxs⟩, has⟩
    · have ha : as.length = 6 := rfl
      have hb : bs.length = 6 := rfl
      have hcc : cs.length = 6 := rfl
      simp only [List.length_append, ha, hb, hcc]
      omega
    · intro x φ
      simp only [reflectionCompile_append, run_append]
      rw [multiKnownPairSteps_action (c m) t hlast pc, hpc,
        elementary_and_target c m t hct' xs hx,
        multiKnownPairSteps_action (c m) t hlast pb, hpb,
        elementary_and_target c m t hct' xs hx,
        multiKnownPairSteps_action (c m) t hlast pa, hpa, noWorkPrefixAnd_succ]
      cases ha : noWorkPrefixAnd (fun i => x (c i)) m <;> cases hb : x (c m) <;>
        simp only [Bool.false_and, Bool.true_and, if_true, if_false,
          Bool.false_eq_true, applyGate_one, ← applyGate_mul, Matrix.one_mul]
      · rw [← Matrix.mul_assoc, hABC, applyGate_one]
      · rw [pauliX_mul_self, applyGate_one]
      · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAXBXC]

end Qatlib.Concepts.CircuitImpl.MultiControl
