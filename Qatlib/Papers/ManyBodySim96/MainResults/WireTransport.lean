/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalSynthesis

/-!
# Transport of local circuits to selected wires

`wireFill` and `wireFiber` embed local configurations and states into a larger register along an
injective wire map. Transported legal reflection programs preserve their action and resource
counts, including on arbitrary sums of embedded states. The synthesis results realize supplied
local unitaries and Hamiltonian evolutions on states embedded through `knownFrameEmbed`.

The mathematical setting is that of [Wiesner1996].

## Main statements

* `wireProgram_whole_state`: On any global input, the transported program acts as the sum of the
  corresponding local actions on each input basis configuration's selected wires, weighted by
  its amplitude.
* `known_local_unitary_entangled_synthesis`: The bounded legal wire implementation of a supplied
  local unitary acts correctly on every finite sum of fiber-embedded frame states, including
  sums with different exterior configurations.
* `known_local_hamiltonian_wire_synthesis`: The exact evolution of a supplied Hermitian
  `a`-qubit Hamiltonian has a legal, query-free implementation on selected frame wires with at
  most `128 * (a + 1) ^ 2 * 4 ^ a` gates.

## References

* [Wiesner, 1996][Wiesner1996]
-/

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

/-- Fills the wires selected by `e` with the local configuration `x`, using `z` on the remaining
wires. -/
def wireFill {a b : ℕ} (e : Fin a ↪ Fin b) (z : Reg b) (x : Reg a) : Reg b :=
  Function.extend e x z

/-- Reading a selected wire after filling returns the corresponding local bit. -/
@[simp] theorem wireFill_at {a b : ℕ} (e : Fin a ↪ Fin b) (z : Reg b)
    (x : Reg a) (i : Fin a) : wireFill e z x (e i) = x i :=
  e.injective.extend_apply _ _ _

/-- Updating a selected wire after filling is the same as first updating the corresponding local
bit. -/
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

/-- Filling selected wires with their values from `z` reconstructs `z`. -/
theorem wireFill_self {a b : ℕ} (e : Fin a ↪ Fin b) (z : Reg b) :
    wireFill e z (fun i => z (e i)) = z := by
  funext j
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i,rfl⟩ := hj
    exact wireFill_at e z _ i
  · simp only [wireFill, Function.extend_apply' _ _ j hj]

/-- Embeds a local state as the sum of its amplitudes on the filled global basis configurations. -/
def wireFiber {a b : ℕ} (e : Fin a ↪ Fin b) (z : Reg b) (ψ : QState (Reg a)) :
    QState (Reg b) := ∑ x, ψ x • Ket (wireFill e z x)

/-- The fiber embedding sends a local basis ket to the ket of its filled global configuration. -/
theorem wireFiber_ket {a b : ℕ} (e : Fin a ↪ Fin b) (z : Reg b) (x : Reg a) :
    wireFiber e z (Ket x) = Ket (wireFill e z x) := by
  simp [wireFiber, Qatlib.Foundations.PureStateMath.Ket]

/-- The fiber embedding commutes with complex scalar multiplication. -/
theorem wireFiber_smul {a b : ℕ} (e : Fin a ↪ Fin b) (z : Reg b)
    (c : ℂ) (ψ : QState (Reg a)) : wireFiber e z (c • ψ) = c • wireFiber e z ψ := by
  simp [wireFiber, Finset.smul_sum, smul_smul]

/-- The fiber embedding preserves addition of states. -/
theorem wireFiber_add {a b : ℕ} (e : Fin a ↪ Fin b) (z : Reg b)
    (ψ χ : QState (Reg a)) :
    wireFiber e z (ψ + χ) = wireFiber e z ψ + wireFiber e z χ := by
  simp [wireFiber, add_smul, Finset.sum_add_distrib]

/-- The fiber embedding preserves finite sums of states. -/
theorem wireFiber_sum {a b : ℕ} {J : Type*} [Fintype J]
    (e : Fin a ↪ Fin b) (z : Reg b) (ψ : J → QState (Reg a)) :
    wireFiber e z (∑ j, ψ j) = ∑ j, wireFiber e z (ψ j) := by
  simp only [wireFiber, Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

/-- A legal reflection gate transported to selected wires acts on a filled basis ket as the
fiber embedding of the local gate action. -/
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

/-- A transported legal reflection gate commutes with the fiber embedding of every local state. -/
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

/-- Running a legal reflection program on selected wires commutes with embedding the local state
into its wire fiber. -/
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

/-- Transporting a legal reflection program preserves legality and gives a compiled circuit with
one gate per original instruction and no queries. -/
theorem wireProgram_resources {a b : ℕ} (e : Fin a ↪ Fin b)
    (gs : List (ReflectionGate a)) (hgs : reflectionLegal gs) :
    reflectionLegal (gs.map (knownWireGateMap e)) ∧
    GateCount (reflectionCompile (gs.map (knownWireGateMap e))) = gs.length ∧
    QueryCount (reflectionCompile (gs.map (knownWireGateMap e))) = 0 := by
  exact ⟨knownWireMapList_legal e gs hgs,
    by simp only [gateCount_reflectionCompile, List.length_map], queryCount_reflectionCompile _⟩

/-- On any global input, the transported program acts as the sum of the corresponding local
actions on each input basis configuration's selected wires, weighted by its amplitude. -/
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

/-- A supplied unitary on `a` qubits has a legal, query-free implementation on the selected `a +
(a + 1)` wires, with at most `128 * (a + 1) ^ 2 * 4 ^ a` gates and the stated action on
fiber-embedded frame states. -/
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

/-- The bounded legal wire implementation of a supplied local unitary acts correctly on every
finite sum of fiber-embedded frame states, including sums with different exterior
configurations. [Wiesner1996] -/
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

/-- A supplied two-qubit unitary has a legal, query-free implementation on five selected wires
with at most `18432` gates and the stated action on fiber-embedded frame states.
[Wiesner1996] -/
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

/-- The exact evolution of a supplied Hermitian `a`-qubit Hamiltonian has a legal, query-free
implementation on selected frame wires with at most `128 * (a + 1) ^ 2 * 4 ^ a` gates.
[Wiesner1996] -/
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
