/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalSynthesis
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped BigOperators

namespace Qatlib.Papers.ManyBodySim96.MainResults

def wireFill {a b : ℕ} (e : Fin a ↪ Fin b) (z : Reg b) (x : Reg a) : Reg b :=
  Function.extend e x z

@[simp] theorem wireFill_at {a b : ℕ} (e : Fin a ↪ Fin b) (z : Reg b)
    (x : Reg a) (i : Fin a) : wireFill e z x (e i) = x i :=
  e.injective.extend_apply _ _ _

theorem wireFill_update {a b : ℕ} (e : Fin a ↪ Fin b) (z : Reg b)
    (x : Reg a) (t : Fin a) (v : Bool) :
    Function.update (wireFill e z x) (e t) v = wireFill e z (Function.update x t v) := by
  funext j
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i,rfl⟩ := hj
    by_cases hi : i = t
    · subst i; simp
    · rw [Function.update_of_ne (fun h => hi (e.injective h)),
        wireFill_at, wireFill_at, Function.update_of_ne hi]
  · have hne : j ≠ e t := fun h => hj ⟨t,h.symm⟩
    rw [Function.update_of_ne hne]
    simp only [wireFill, Function.extend_apply' _ _ j hj]

theorem wireFill_self {a b : ℕ} (e : Fin a ↪ Fin b) (z : Reg b) :
    wireFill e z (fun i => z (e i)) = z := by
  funext j
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i,rfl⟩ := hj
    exact wireFill_at e z _ i
  · simp only [wireFill, Function.extend_apply' _ _ j hj]

def wireFiber {a b : ℕ} (e : Fin a ↪ Fin b) (z : Reg b) (ψ : QState (Reg a)) :
    QState (Reg b) := ∑ x, ψ x • Ket (wireFill e z x)

theorem wireFiber_ket {a b : ℕ} (e : Fin a ↪ Fin b) (z : Reg b) (x : Reg a) :
    wireFiber e z (Ket x) = Ket (wireFill e z x) := by
  simp [wireFiber, Qatlib.Foundations.PureStateMath.Ket]

theorem wireFiber_smul {a b : ℕ} (e : Fin a ↪ Fin b) (z : Reg b)
    (c : ℂ) (ψ : QState (Reg a)) : wireFiber e z (c • ψ) = c • wireFiber e z ψ := by
  simp [wireFiber, Finset.smul_sum, smul_smul]

theorem wireFiber_add {a b : ℕ} (e : Fin a ↪ Fin b) (z : Reg b)
    (ψ χ : QState (Reg a)) :
    wireFiber e z (ψ + χ) = wireFiber e z ψ + wireFiber e z χ := by
  simp [wireFiber, add_smul, Finset.sum_add_distrib]

theorem wireFiber_sum {a b : ℕ} {J : Type*} [Fintype J]
    (e : Fin a ↪ Fin b) (z : Reg b) (ψ : J → QState (Reg a)) :
    wireFiber e z (∑ j, ψ j) = ∑ j, wireFiber e z (ψ j) := by
  simp only [wireFiber, Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

theorem wireGate_fiber_ket {a b : ℕ} (e : Fin a ↪ Fin b) (z : Reg b)
    (g : ReflectionGate a) (hg : reflectionGateLegal g) (x : Reg a) :
    ApplyGate (reflectionGateMatrix (knownWireGateMap e g)) (Ket (wireFill e z x)) =
      wireFiber e z (ApplyGate (reflectionGateMatrix g) (Ket x)) := by
  rcases g with ⟨t,U⟩ | ⟨c,t⟩
  · simp only [knownWireGateMap, reflectionGateMatrix, applyGate_wireGate_ket,
      wireFill_at, wireFill_update, wireFiber_add, wireFiber_smul, wireFiber_ket]
  · simp only [knownWireGateMap, reflectionGateMatrix]
    rw [applyGate_cnotGate_ket b (e c) (e t) (fun h => hg (e.injective h)),
      applyGate_cnotGate_ket a c t hg, wireFiber_ket,
      wireFill_at, wireFill_update]
    simp only [wireFill_at]

theorem wireGate_fiber {a b : ℕ} (e : Fin a ↪ Fin b) (z : Reg b)
    (g : ReflectionGate a) (hg : reflectionGateLegal g) (ψ : QState (Reg a)) :
    ApplyGate (reflectionGateMatrix (knownWireGateMap e g)) (wireFiber e z ψ) =
      wireFiber e z (ApplyGate (reflectionGateMatrix g) ψ) := by
  conv_rhs => arg 3; arg 2; rw [state_ket_expansion ψ]
  simp only [ApplyGate, Matrix.mulVec_sum, Matrix.mulVec_smul,
    wireFiber_sum, wireFiber_smul]
  change (reflectionGateMatrix (knownWireGateMap e g)) *ᵥ
    (∑ x, ψ x • Ket (wireFill e z x)) = _
  rw [Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul]
  apply Finset.sum_congr rfl
  intro x _
  rw [show reflectionGateMatrix (knownWireGateMap e g) *ᵥ Ket (wireFill e z x) =
    wireFiber e z (reflectionGateMatrix g *ᵥ Ket x) from wireGate_fiber_ket e z g hg x]

theorem wireProgram_fiber {a b : ℕ} (e : Fin a ↪ Fin b) (z : Reg b)
    (gs : List (ReflectionGate a)) (hgs : reflectionLegal gs) (ψ : QState (Reg a)) :
    Run 1 (reflectionCompile (gs.map (knownWireGateMap e))) (wireFiber e z ψ) =
      wireFiber e z (Run 1 (reflectionCompile gs) ψ) := by
  induction gs generalizing ψ with
  | nil => simp [reflectionCompile]
  | cons g gs ih =>
    simp only [List.map_cons, reflectionCompile, run_gate]
    rw [wireGate_fiber e z g (hgs g List.mem_cons_self)]
    exact ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg)) _

theorem wireProgram_resources {a b : ℕ} (e : Fin a ↪ Fin b)
    (gs : List (ReflectionGate a)) (hgs : reflectionLegal gs) :
    reflectionLegal (gs.map (knownWireGateMap e)) ∧
    GateCount (reflectionCompile (gs.map (knownWireGateMap e))) = gs.length ∧
    QueryCount (reflectionCompile (gs.map (knownWireGateMap e))) = 0 := by
  exact ⟨knownWireMapList_legal e gs hgs,
    by simp only [gateCount_reflectionCompile, List.length_map], queryCount_reflectionCompile _⟩

theorem wireProgram_whole_state {a b : ℕ} (e : Fin a ↪ Fin b)
    (gs : List (ReflectionGate a)) (hgs : reflectionLegal gs) (Ψ : QState (Reg b)) :
    Run 1 (reflectionCompile (gs.map (knownWireGateMap e))) Ψ =
      ∑ y : Reg b, Ψ y • wireFiber e y
        (Run 1 (reflectionCompile gs) (Ket (fun i => y (e i)))) := by
  conv_lhs => arg 3; rw [state_ket_expansion Ψ]
  rw [run_reflectionCompile_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [run_reflectionCompile_smul]
  congr 1
  have h := wireProgram_fiber e y gs hgs (Ket (fun i => y (e i)))
  simpa only [wireFiber_ket, wireFill_self] using! h

theorem known_local_unitary_wire_synthesis (a b : ℕ)
    (e : Fin (a+(a+1)) ↪ Fin b) (U : Matrix (Reg a) (Reg a) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Reg a) ℂ) :
    ∃ gs : List (ReflectionGate b), reflectionLegal gs ∧
      gs.length ≤ 128*(a+1)^2*4^a ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      ∀ (z : Reg b) (ψ : QState (Reg a)),
        Run 1 (reflectionCompile gs) (wireFiber e z (knownFrameEmbed a ψ)) =
          wireFiber e z (knownFrameEmbed a (U *ᵥ ψ)) := by
  obtain ⟨ls,hlegal,hlen,hquery,hcount,hrun⟩ :=
    known_unitary_actual_clean_local_synthesis a U hU
  refine ⟨ls.map (knownWireGateMap e), knownWireMapList_legal e ls hlegal,
    ?_, gateCount_reflectionCompile _, queryCount_reflectionCompile _, ?_⟩
  · simpa only [List.length_map] using! hlen
  · intro z ψ
    rw [wireProgram_fiber e z ls hlegal, hrun ψ]

theorem known_local_unitary_entangled_synthesis {J : Type*} [Fintype J]
    (a b : ℕ) (e : Fin (a+(a+1)) ↪ Fin b) (U : Matrix (Reg a) (Reg a) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Reg a) ℂ) :
    ∃ gs : List (ReflectionGate b), reflectionLegal gs ∧
      gs.length ≤ 128*(a+1)^2*4^a ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      ∀ (z : J → Reg b) (ψ : J → QState (Reg a)),
        Run 1 (reflectionCompile gs) (∑ j, wireFiber e (z j) (knownFrameEmbed a (ψ j))) =
          ∑ j, wireFiber e (z j) (knownFrameEmbed a (U *ᵥ ψ j)) := by
  obtain ⟨gs,hlegal,hlen,hcount,hquery,hrun⟩ := known_local_unitary_wire_synthesis a b e U hU
  refine ⟨gs,hlegal,hlen,hcount,hquery,?_⟩
  intro z ψ
  rw [run_reflectionCompile_sum]
  exact Finset.sum_congr rfl (fun j _ => hrun (z j) (ψ j))

theorem known_two_qubit_wire_synthesis (b : ℕ)
    (e : Fin (2+(2+1)) ↪ Fin b) (U : Matrix (Reg 2) (Reg 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Reg 2) ℂ) :
    ∃ gs : List (ReflectionGate b), reflectionLegal gs ∧
      gs.length ≤ 18432 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      ∀ (z : Reg b) (ψ : QState (Reg 2)),
        Run 1 (reflectionCompile gs) (wireFiber e z (knownFrameEmbed 2 ψ)) =
          wireFiber e z (knownFrameEmbed 2 (U *ᵥ ψ)) := by
  exact known_local_unitary_wire_synthesis 2 b e U hU

theorem known_local_hamiltonian_wire_synthesis (a b : ℕ)
    (e : Fin (a+(a+1)) ↪ Fin b) (H : Matrix (Reg a) (Reg a) ℂ)
    (hH : H.IsHermitian) (t : ℝ) :
    ∃ gs : List (ReflectionGate b), reflectionLegal gs ∧
      gs.length ≤ 128*(a+1)^2*4^a ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      ∀ (z : Reg b) (ψ : QState (Reg a)),
        Run 1 (reflectionCompile gs) (wireFiber e z (knownFrameEmbed a ψ)) =
          wireFiber e z (knownFrameEmbed a (HamiltonianEvolution H t *ᵥ ψ)) := by
  exact known_local_unitary_wire_synthesis a b e _ (hamiltonianEvolution_unitary hH t)

end Qatlib.Papers.ManyBodySim96.MainResults
