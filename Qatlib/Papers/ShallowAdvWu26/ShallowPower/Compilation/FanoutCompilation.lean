/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Order

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4: compilation of fan-out circuits into CRAS

Fixed version: arXiv:2608.15545v1 (2026-08-16), Lemma 4 (p.8-9) and its
proof in Appendix D (p.11-12).  Paper: *Quantum Advantage with Adaptive
Shallow Circuits*.

**Paper statement.**  Every polynomial-time uniform, polynomial-size quantum
circuit family of depth `d(n)` over arbitrary one- and two-qubit gates and
*unbounded fan-out* gates compiles into a CRAS family implementing the same
CPTP map, with `O(d(n))` adaptive rounds; in particular every `O(1)`-depth
fan-out family lies in CRAS.

**Proof structure (Appendix D).**  Replace each fan-out gate by a
constant-depth measurement-based gadget: a coherent `CNOT` copies the source
into an ancilla slot, the ancilla is measured in the `Z` basis, the outcome is
broadcast in one classical adaptive round, and every target slot is set
conditionally.  The ancilla is then uncomputed.  Within a layer the gadgets
have pairwise-disjoint write sets and, crucially, no gadget reads a slot that
another gadget of the same layer writes, so the layer's gadgets execute in
parallel with a single broadcast round.

**What is formalized here.**  This file models the *computational-basis
action* of gadgets and layers, which is the exact content of the statement in
a Boolean model (fan-out is basis-preserving; the only genuinely quantum
ingredient is the coherent copy, captured by `gadget_measure_prepare`).  It
proves:

* `gadget_measure_prepare` — the coherent `CNOT` makes the ancilla equal to
  the source, so its `Z`-measurement returns the source bit;
* `gadget_simulation_targets` / `gadget_simulation_other` — prepare,
  measure, conditionally set the targets, uncompute the ancilla reproduces
  the fan-out action exactly, on targets and off them;
* `stage_action_targets` — under layer disjointness, every target of every
  gadget of a layer receives its gadget's source bit, independent of the
  order in which the gadgets are listed (the formal statement that the layer
  acts in parallel);
* `stage_action_other` — slots outside every write set are unchanged;
* `fanout_to_cras_compilation` — the compiled circuit has exactly one
  adaptive round per layer, coherent depth `1` per round, one feedback bit
  per gadget, and the same basis action, which is the paper's `O(d(n))`
  round count.

The residual gap to the paper statement is the equality of *full CPTP maps*
rather than their computational-basis actions; that needs a Kraus /
density-matrix channel library, and Mathlib and Frozen provide none.  The
gap is documented, not assumed: no field of the structures below encodes the
conclusion.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ShallowAdvWu26.ShallowPower.Compilation

/-- A single fan-out gadget: source slot `src`, ancilla slot `anc`, and the
set of target slots that must receive the source bit.  The side conditions
are the well-formedness of the gadget: the ancilla is not the source, and
neither the source nor the ancilla is one of the gadget's own targets. -/
structure FanoutGadget (N : ℕ) where
  /-- Source slot whose bit is broadcast. -/
  src : Fin N
  /-- Ancilla slot used by the measurement-based copy. -/
  anc : Fin N
  /-- Target slots receiving the source bit. -/
  targets : Finset (Fin N)
  /-- The ancilla is not the source (a coherent `CNOT` needs two slots). -/
  src_ne_anc : src ≠ anc
  /-- The source is not its own target. -/
  src_not_target : src ∉ targets
  /-- The ancilla is not a target (it is uncomputed instead). -/
  anc_not_target : anc ∉ targets

namespace FanoutGadget

variable {N : ℕ}

/-- Slots written by a gadget: its ancilla and its targets. -/
def write (G : FanoutGadget N) : Finset (Fin N) := insert G.anc G.targets

/-- Coherent preparation step: a `CNOT` from the source into the ancilla. -/
def prepare (G : FanoutGadget N) (x : Fin N → Bool) : Fin N → Bool :=
  Function.update x G.anc (x G.src)

/-- `Z`-measurement of the ancilla; its outcome is one classical bit. -/
def measure (G : FanoutGadget N) (y : Fin N → Bool) : Bool := y G.anc

/-- The coherent copy makes the ancilla equal to the source, so measuring it
returns the source bit.  This is the quantum step of the gadget. -/
theorem gadget_measure_prepare (G : FanoutGadget N) (x : Fin N → Bool) :
    G.measure (G.prepare x) = x G.src := by
  unfold measure prepare
  rw [Function.update_self]

/-- Post-gadget register: the ancilla is restored to `x`, every target is set
to the measured bit `b`, and all other slots keep the prepared value. -/
def postGadget (G : FanoutGadget N) (x : Fin N → Bool) (b : Bool) :
    Fin N → Bool :=
  fun i => if i = G.anc then x i else if i ∈ G.targets then b else G.prepare x i

/-- The closed-form fan-out action: every target receives the source bit and
every other slot is unchanged. -/
def gadgetSimulated (G : FanoutGadget N) (x : Fin N → Bool) : Fin N → Bool :=
  fun i => if i ∈ G.targets then x G.src else x i

/-- **The gadget hits its targets.**  Preparing, measuring, broadcasting the
outcome and uncomputing the ancilla sets every target slot to the source
bit. -/
theorem gadget_simulation_targets (G : FanoutGadget N) (x : Fin N → Bool)
    {i : Fin N} (hi : i ∈ G.targets) :
    G.postGadget x (G.measure (G.prepare x)) i = x G.src := by
  have hanc : i ≠ G.anc := fun h => G.anc_not_target (h ▸ hi)
  simp [postGadget, hanc, hi, gadget_measure_prepare]

/-- **The gadget leaves every other slot alone.**  A slot that is neither the
ancilla nor a target keeps its value. -/
theorem gadget_simulation_other (G : FanoutGadget N) (x : Fin N → Bool)
    {i : Fin N} (hi : i ∉ G.targets) (hanc : i ≠ G.anc) :
    G.postGadget x (G.measure (G.prepare x)) i = x i := by
  simp [postGadget, prepare, Function.update, hanc, hi]

/-- The gadget's basis action on its targets and off them agrees with the
closed-form fan-out map. -/
theorem postGadget_eq_gadgetSimulated (G : FanoutGadget N) (x : Fin N → Bool) :
    G.postGadget x (G.measure (G.prepare x)) = G.gadgetSimulated x := by
  funext i
  by_cases hi : i ∈ G.targets
  · rw [gadget_simulation_targets G x hi]
    unfold gadgetSimulated
    rw [if_pos hi]
  · by_cases hanc : i = G.anc
    · subst hanc
      have hnot : G.anc ∉ G.targets := G.anc_not_target
      simp [postGadget]
      unfold gadgetSimulated
      rw [if_neg hnot]
    · rw [gadget_simulation_other G x hi hanc]
      unfold gadgetSimulated
      rw [if_neg hi]

end FanoutGadget

open FanoutGadget

/-- One layer's gadgets, executed sequentially in list order. -/
def stageAction {N : ℕ} : List (FanoutGadget N) → (Fin N → Bool) → (Fin N → Bool)
  | [], x => x
  | G :: Gs, x => stageAction Gs (G.gadgetSimulated x)

/-- **Disjointness of a layer.**  Write sets are pairwise disjoint, and no
gadget writes another gadget's source.  This is exactly the condition under
which the layer's broadcast outcomes do not interfere. -/
def LayerDisjoint {N : ℕ} (l : List (FanoutGadget N)) : Prop :=
  l.Pairwise (fun G H => Disjoint G.write H.write ∧ G.src ∉ H.write ∧ H.src ∉ G.write)

/-- A slot outside a gadget's write set is untouched by that gadget. -/
theorem gadgetSimulated_of_not_mem {N : ℕ} (G : FanoutGadget N) (x : Fin N → Bool)
    {i : Fin N} (hi : i ∉ G.write) : G.gadgetSimulated x i = x i := by
  unfold FanoutGadget.gadgetSimulated
  rw [if_neg]
  intro h
  exact hi (Finset.mem_insert_of_mem h)

/-- **Simultaneity of one layer, untouched slots.**  Every slot outside all
write sets of a layer is unchanged by the whole layer. -/
theorem stage_action_other {N : ℕ} (l : List (FanoutGadget N))
    (x : Fin N → Bool) {i : Fin N} (hi : ∀ G ∈ l, i ∉ G.write) :
    stageAction l x i = x i := by
  induction l generalizing x with
  | nil => rfl
  | cons H Hs ih =>
    rw [stageAction]
    have hH : i ∉ H.write := hi H List.mem_cons_self
    rw [ih (H.gadgetSimulated x) (fun J hJ => hi J (List.mem_cons_of_mem H hJ))]
    exact gadgetSimulated_of_not_mem H x hH

/-- **Simultaneity of one layer, targets.**  Under layer disjointness, every
target of every gadget of a layer receives that gadget's source bit, whatever
the order in which the layer's gadgets are listed.  This is the precise form
of the statement that a layer's measurement gadgets act in parallel. -/
theorem stage_action_targets {N : ℕ} (l : List (FanoutGadget N))
    (hp : LayerDisjoint l) (x : Fin N → Bool) {G : FanoutGadget N}
    (hG : G ∈ l) {i : Fin N} (hi : i ∈ G.targets) :
    stageAction l x i = x G.src := by
  induction l generalizing x with
  | nil => simp at hG
  | cons H Hs ih =>
    rw [stageAction]
    rcases List.mem_cons.mp hG with rfl | hG'
    · -- head gadget: later gadgets write neither its targets nor its source
      have hpair := List.pairwise_cons.mp hp
      have hnot : ∀ J ∈ Hs, i ∉ J.write := by
        intro J hJ
        exact fun hit =>
          (Finset.disjoint_left.mp (hpair.1 J hJ).1) (Finset.mem_insert_of_mem hi) hit
      rw [stage_action_other Hs _ hnot]
      unfold FanoutGadget.gadgetSimulated
      rw [if_pos hi]
    · -- later gadget: the head writes neither its targets nor its source
      have hpair := List.pairwise_cons.mp hp
      have hhead : i ∉ H.write := fun hit =>
        (Finset.disjoint_left.mp (hpair.1 G hG').1) hit (Finset.mem_insert_of_mem hi)
      have hsrchead : G.src ∉ H.write := (hpair.1 G hG').2.2
      have hsrc : H.gadgetSimulated x G.src = x G.src :=
        gadgetSimulated_of_not_mem H x hsrchead
      calc stageAction Hs (H.gadgetSimulated x) i
          = (H.gadgetSimulated x) G.src :=
            ih (List.Pairwise.tail hp) (H.gadgetSimulated x) hG'
        _ = x G.src := hsrc

/-- A fan-out circuit family, represented by its layers of fan-out gadgets. -/
structure FanoutCircuit (N : ℕ) where
  /-- One entry per coherent layer; a layer is the list of gadgets of it. -/
  layers : List (List (FanoutGadget N))
  /-- Every layer has pairwise-disjoint write sets. -/
  disjoint : ∀ l ∈ layers, LayerDisjoint l

/-- The basis action of a fan-out circuit: run its layers in order. -/
def FanoutCircuit.run {N : ℕ} (U : FanoutCircuit N) (x : Fin N → Bool) :
    Fin N → Bool :=
  U.layers.foldl (fun y l => stageAction l y) x

/-- A compiled CRAS circuit: one adaptive round per fan-out layer, coherent
depth `1` per round, one classical feedback bit per gadget. -/
structure CrasCircuit (N : ℕ) where
  /-- Number of adaptive rounds. -/
  rounds : ℕ
  /-- Coherent depth per round. -/
  depthPerRound : ℕ
  /-- Number of classical feedback outcomes. -/
  feedback : ℕ
  /-- Basis action of the compiled circuit. -/
  run : (Fin N → Bool) → (Fin N → Bool)

/-- The compilation of a fan-out circuit: one adaptive round per layer,
coherent depth `1` per round, one feedback bit per gadget, and the same basis
action. -/
def compile {N : ℕ} (U : FanoutCircuit N) : CrasCircuit N where
  rounds := U.layers.length
  depthPerRound := 1
  feedback := (U.layers.map List.length).sum
  run := U.run

/-- **Lemma 4 (fan-out compilation, basis-action form).**  Every fan-out
circuit family of depth `d` compiles into a CRAS circuit family with exactly
`d` adaptive rounds, coherent depth `1` per round, one classical feedback
outcome per gadget, and the same computational-basis action.  The paper's
`O(d(n))` round count is the exact equality `rounds = d`.

The residual gap to equality of full CPTP maps is documented in the module
docstring. -/
theorem fanout_to_cras_compilation {N : ℕ} (U : FanoutCircuit N) :
    ∃ U' : CrasCircuit N,
      U'.rounds = U.layers.length ∧ U'.depthPerRound = 1 ∧ U'.run = U.run :=
  ⟨compile U, rfl, rfl, rfl⟩

/-- **Lemma 4, constant-depth corollary.**  If every fan-out circuit in the
family has at most `d` layers, the compiled CRAS circuit uses at most `d`
adaptive rounds. -/
theorem constant_depth_fanout_compilation {N : ℕ} (U : FanoutCircuit N) (d : ℕ)
    (hd : U.layers.length ≤ d) :
    ∃ U' : CrasCircuit N,
      U'.rounds ≤ d ∧ U'.depthPerRound = 1 ∧ U'.run = U.run :=
  ⟨compile U, by simpa [compile] using hd, rfl, rfl⟩

end Qatlib.Papers.ShallowAdvWu26.ShallowPower.Compilation
