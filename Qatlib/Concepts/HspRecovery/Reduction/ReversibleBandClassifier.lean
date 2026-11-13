/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSplice
import Qatlib.Concepts.NumericalWord.MixedWordError.FixedGateSynthesisDefs
import Qatlib.Concepts.WalkSearch.MultiBandFilter.MultiBandFilterConsumers
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.LocalQFTReadout
import Mathlib.Tactic

/-!
# Reversible classification of rational bands

This module builds Boolean directed acyclic graphs that test membership of decoded register
values in a finite union of closed rational intervals. It compiles those graphs to reversible
reflection-gate words, with exact basis-state and coherent sign actions, using the circuit
framework of [BarencoEtAl1995].

`bandLocalQFTCircuit` surrounds the sign word by an embedded approximate Fourier transform and
its adjoint. Resource results count oracle queries, elementary gates, and the stored
endpoint-comparison count.

## Main statements

* `value_bandProgram`: the Boolean program computes band membership.
* `bandWord_basis`: reversible classification restores the work register and toggles the output
  bit.
* `bandSignWord_coherent`: the sign word acts diagonally on embedded superpositions.
* `bandLocalQFTCircuit_resources`: zero queries and an exact gate-count formula.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.WalkSearch.MultiBandFilter
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.HhlAlgorithms.UniformHHL
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation Qatlib.Concepts.CircuitImpl.ReflectionCompile
open Qatlib.Concepts.MatrixAccess.RitzPipeline

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open Matrix
open scoped Classical BigOperators

/-- A Boolean directed acyclic graph on `m` input bits, equipped with a selected output and a
stored comparison count. -/
structure BoolDAG (m : ℕ) where
  nodes : ℕ
  graph : BooleanDAG m nodes
  out : Fin (m + nodes)
  comparisons : ℕ

namespace BoolDAG

/-- The Boolean value at the selected output of the graph on input `x`. -/
def value {m : ℕ} (g : BoolDAG m) (x : Reg m) : Bool :=
  booleanDAGValue g.graph x g.out

/-- The Boolean graph with no internal nodes whose output is input bit `i` and whose comparison
count is zero. -/
def input {m : ℕ} (i : Fin m) : BoolDAG m where
  nodes := 0
  graph := .nil
  out := i
  comparisons := 0

/-- An input graph evaluates to its selected input bit. -/
@[simp] theorem value_input {m : ℕ} (i : Fin m) (x : Reg m) :
    (input i).value x = x i := rfl

/-- The graph obtained by appending one Boolean node, selecting it as output, and retaining the
comparison count. -/
def extend {m : ℕ} (g : BoolDAG m) (node : BooleanNode (m + g.nodes)) : BoolDAG m where
  nodes := g.nodes + 1
  graph := g.graph.snoc node
  out := Fin.last _
  comparisons := g.comparisons

/-- An extended graph evaluates to the new node applied to the values of the preceding graph. -/
@[simp] theorem value_extend {m : ℕ} (g : BoolDAG m)
    (node : BooleanNode (m + g.nodes)) (x : Reg m) :
    (g.extend node).value x = booleanNodeValue node (booleanDAGValue g.graph x) := by
  simp [value, extend, booleanDAGValue]

/-- Appending a Boolean node preserves the values of all preceding graph positions. -/
@[simp] theorem value_extend_prefix {m : ℕ} (g : BoolDAG m)
    (node : BooleanNode (m + g.nodes)) (x : Reg m) (i : Fin (m + g.nodes)) :
    booleanDAGValue (g.extend node).graph x (Fin.castSucc i) = booleanDAGValue g.graph x i := by
  simp [extend, booleanDAGValue]

/-- A one-node graph returning the constant Boolean `b`, with zero comparisons. -/
def const {m : ℕ} (b : Bool) : BoolDAG m where
  nodes := 1
  graph := .snoc .nil (.constant b)
  out := Fin.last _
  comparisons := 0

/-- A constant graph evaluates to its defining Boolean. -/
@[simp] theorem value_const {m : ℕ} (b : Bool) (x : Reg m) :
    (const (m := m) b).value x = b := by
  simp [value, const, booleanDAGValue, booleanNodeValue]

/-- The graph formed by appending the negation of the selected output. -/
def neg {m : ℕ} (g : BoolDAG m) : BoolDAG m := g.extend (.neg g.out)

/-- Negating a graph negates its Boolean value. -/
@[simp] theorem value_neg {m : ℕ} (g : BoolDAG m) (x : Reg m) :
    g.neg.value x = !(g.value x) := by
  simp only [neg, value_extend, booleanNodeValue]
  rfl

/-- Evaluation of a Boolean graph preserves each original input bit at its corresponding graph
position. -/
private theorem graph_input {m k : ℕ} (g : BooleanDAG m k) (x : Reg m) (i : Fin m) :
    booleanDAGValue g x (Fin.castLE (by omega) i) = x i := by
  induction g with
  | nil => rfl
  | @snoc k g node ih =>
      change booleanDAGValue (g.snoc node) x
        (Fin.castSucc (Fin.castLE (Nat.le_add_right m k) i)) = x i
      simpa only [booleanDAGValue, Fin.lastCases_castSucc] using! ih

/-- The graph formed by splicing `h` after `g` on the same inputs, selecting the output of `h`,
and adding their comparison counts. -/
def append {m : ℕ} (g h : BoolDAG m) : BoolDAG m where
  nodes := g.nodes + h.nodes
  graph := booleanDAGSplice g.graph (fun i => Fin.castLE (by omega) i) h.graph
  out := booleanSpliceSource (fun i => Fin.castLE (by omega) i) h.out
  comparisons := g.comparisons + h.comparisons

/-- The selected output of the appended graph has the value of the second graph on the same
input. -/
@[simp] theorem value_append {m : ℕ} (g h : BoolDAG m) (x : Reg m) :
    (g.append h).value x = h.value x := by
  simp only [append, value]
  rw [boolean_dag_splice_value]
  congr 1
  funext i
  exact graph_input g.graph x i

/-- Evaluating the appended graph at its selected output yields the second graph's value. -/
theorem value_append_out {m : ℕ} (g h : BoolDAG m) (x : Reg m) :
    booleanDAGValue (g.append h).graph x (g.append h).out = h.value x :=
  value_append g h x

/-- The appended graph preserves the first graph's output value at the embedded output position. -/
theorem value_append_left {m : ℕ} (g h : BoolDAG m) (x : Reg m) :
    booleanDAGValue (g.append h).graph x
      (Fin.castLE (by dsimp [append]; omega) g.out) = g.value x :=
  boolean_dag_splice_prefix g.graph _ h.graph x g.out

/-- The Boolean graph computing the conjunction of the outputs of two graphs on the same inputs. -/
def and {m : ℕ} (g h : BoolDAG m) : BoolDAG m :=
  let gh := g.append h
  let left : Fin (m + gh.nodes) := Fin.castLE (by dsimp [gh, append]; omega) g.out
  gh.extend (.conj left gh.out)

/-- The conjunction graph evaluates to the Boolean conjunction of its component values. -/
@[simp] theorem value_and {m : ℕ} (g h : BoolDAG m) (x : Reg m) :
    (g.and h).value x = (g.value x && h.value x) := by
  simp only [and, value_extend, booleanNodeValue, value_append_left, value_append_out]

/-- The Boolean graph computing the exclusive disjunction of the outputs of two graphs on the
same inputs. -/
def xor {m : ℕ} (g h : BoolDAG m) : BoolDAG m :=
  let gh := g.append h
  let left : Fin (m + gh.nodes) := Fin.castLE (by dsimp [gh, append]; omega) g.out
  gh.extend (.xor left gh.out)

/-- The exclusive-disjunction graph evaluates to the exclusive disjunction of its component
values. -/
@[simp] theorem value_xor {m : ℕ} (g h : BoolDAG m) (x : Reg m) :
    (g.xor h).value x = (g.value x ^^ h.value x) := by
  simp only [xor, value_extend, booleanNodeValue, value_append_left, value_append_out]

/-- The Boolean disjunction graph constructed by negation and conjunction using De Morgan's
identity. -/
def or {m : ℕ} (g h : BoolDAG m) : BoolDAG m := (g.neg.and h.neg).neg

/-- The disjunction graph evaluates to the Boolean disjunction of its component values. -/
@[simp] theorem value_or {m : ℕ} (g h : BoolDAG m) (x : Reg m) :
    (g.or h).value x = (g.value x || h.value x) := by
  simp only [or, value_neg, value_and]
  cases g.value x <;> cases h.value x <;> decide

/-- The graph testing whether input bit `i` agrees with the corresponding bit of `target`. -/
def literal {m : ℕ} (target : Reg m) (i : Fin m) : BoolDAG m :=
  if target i then input i else (input i).neg

/-- A literal graph evaluates to the Boolean equality test for the selected input and target
bits. -/
@[simp] theorem value_literal {m : ℕ} (target : Reg m) (i : Fin m) (x : Reg m) :
    (literal target i).value x = (x i == target i) := by
  cases h : target i <;> simp [literal, h]

/-- The conjunction of the target-matching literals at the listed input positions, with value
true for an empty list. -/
def eqConstAux {m : ℕ} (target : Reg m) : List (Fin m) → BoolDAG m
  | [] => const true
  | i :: is => (literal target i).and (eqConstAux target is)

/-- The partial equality graph evaluates to the test that all listed positions agree with the
target. -/
@[simp] theorem value_eqConstAux {m : ℕ} (target : Reg m) (is : List (Fin m)) (x : Reg m) :
    (eqConstAux target is).value x = is.all (fun i => x i == target i) := by
  induction is with
  | nil => simp [eqConstAux]
  | cons i is ih => simp only [eqConstAux, value_and, value_literal, ih, List.all_cons]

/-- The Boolean graph comparing the entire input register with a fixed target register. -/
def eqConst {m : ℕ} (target : Reg m) : BoolDAG m :=
  eqConstAux target (List.finRange m)

/-- The full equality graph evaluates to `decide (x = target)`. -/
@[simp] theorem value_eqConst {m : ℕ} (target : Reg m) (x : Reg m) :
    (eqConst target).value x = decide (x = target) := by
  by_cases h : x = target
  · subst x
    simp [eqConst, List.all_eq_true]
  · have hj : ∃ j, x j ≠ target j := by
      by_contra! hall
      exact h (funext hall)
    obtain ⟨j, hj⟩ := hj
    rw [eqConst, value_eqConstAux,
      List.all_eq_false.mpr ⟨j, List.mem_finRange j, by simp [hj]⟩]
    exact (decide_eq_false h).symm

/-- The disjunction of a list of Boolean graphs, with value false for an empty list. -/
def orList {m : ℕ} : List (BoolDAG m) → BoolDAG m
  | [] => const false
  | g :: gs => g.or (orList gs)

/-- The disjunction graph evaluates to the test that at least one graph in the list has value
true. -/
@[simp] theorem value_orList {m : ℕ} (gs : List (BoolDAG m)) (x : Reg m) :
    (orList gs).value x = gs.any (fun g => g.value x) := by
  induction gs with
  | nil => simp [orList]
  | cons g gs ih => simp [orList, ih]

/-- The truth-table disjunctive normal form graph for `f`, formed from equality tests at its
satisfying inputs and assigned comparison count one. -/
def dnf {m : ℕ} (f : Reg m → Bool) : BoolDAG m :=
  { orList ((((List.finRange (2 ^ m)).map (bitVecEquiv m).symm).filter f).map eqConst) with
    comparisons := 1 }

/-- The disjunctive normal form graph computes the Boolean function used to construct it. -/
@[simp] theorem value_dnf {m : ℕ} (f : Reg m → Bool) (x : Reg m) :
    (dnf f).value x = f x := by
  change (orList _).value x = f x
  rw [value_orList, Bool.eq_iff_iff, List.any_eq_true]
  constructor
  · rintro ⟨g, hg, hgx⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    have hfa := (List.mem_filter.mp ha).2
    have hxa : x = a := of_decide_eq_true (by simpa only [value_eqConst] using! hgx)
    simpa [hxa] using! hfa
  · intro hfx
    refine ⟨eqConst x, ?_, by simp⟩
    exact List.mem_map.mpr ⟨x, List.mem_filter.mpr
      ⟨List.mem_map.mpr ⟨bitVecEquiv m x, List.mem_finRange _, by simp⟩, hfx⟩, rfl⟩

/-- Appending a Boolean node preserves the stored comparison count. -/
@[simp] theorem comparisons_extend {m : ℕ} (g : BoolDAG m)
    (node : BooleanNode (m + g.nodes)) : (g.extend node).comparisons = g.comparisons := rfl

/-- A constant graph has comparison count zero. -/
@[simp] theorem comparisons_const {m : ℕ} (b : Bool) :
    (const (m := m) b).comparisons = 0 := rfl

/-- Appending two graphs adds their stored comparison counts. -/
@[simp] theorem comparisons_append {m : ℕ} (g h : BoolDAG m) :
    (g.append h).comparisons = g.comparisons + h.comparisons := rfl

/-- The conjunction construction adds the comparison counts of its component graphs. -/
@[simp] theorem comparisons_and {m : ℕ} (g h : BoolDAG m) :
    (g.and h).comparisons = g.comparisons + h.comparisons := by
  simp [and]

/-- The disjunction construction adds the comparison counts of its component graphs. -/
@[simp] theorem comparisons_or {m : ℕ} (g h : BoolDAG m) :
    (g.or h).comparisons = g.comparisons + h.comparisons := by
  simp [or, neg]

/-- Every truth-table disjunctive normal form graph has stored comparison count one. -/
@[simp] theorem comparisons_dnf {m : ℕ} (f : Reg m → Bool) :
    (dnf f).comparisons = 1 := rfl

end BoolDAG

/-- The rational decoding `y.val / M` when `2 * y.val ≤ M`, and `y.val / M - 1` otherwise. -/
def decodedRat (M : ℕ) (y : Fin M) : ℚ :=
  if 2 * y.val ≤ M then (y.val : ℚ) / (M : ℚ) else (y.val : ℚ) / (M : ℚ) - 1

/-- Casting the rational decoding to the reals gives `uniformHHLDecode`. -/
@[simp] theorem decodedRat_cast (M : ℕ) (y : Fin M) :
    (decodedRat M y : ℝ) = uniformHHLDecode M y := by
  simp only [decodedRat, uniformHHLDecode]
  split_ifs <;> norm_num

/-- The condition that the rational number `x` belongs to one of the closed intervals listed in
`bands`. -/
def rationalBandContains (bands : List (ℚ × ℚ)) (x : ℚ) : Prop :=
  ∃ b ∈ bands, b.1 ≤ x ∧ x ≤ b.2

/-- The Boolean test for membership in at least one of the listed closed rational intervals. -/
def rationalBandBool (bands : List (ℚ × ℚ)) (x : ℚ) : Bool :=
  bands.any (fun b => decide (b.1 ≤ x ∧ x ≤ b.2))

/-- The Boolean band test equals the decision procedure for `rationalBandContains`. -/
@[simp] theorem rationalBandBool_eq (bands : List (ℚ × ℚ)) (x : ℚ) :
    rationalBandBool bands x = decide (rationalBandContains bands x) := by
  rw [rationalBandBool, Bool.eq_iff_iff, List.any_eq_true]
  simp only [decide_eq_true_eq]
  rfl

/-- Membership of a rationally decoded label in the rational bands is equivalent to membership
of its real decoding in the same bands. -/
theorem rationalBandContains_iff (M : ℕ) (bands : List (ℚ × ℚ)) (y : Fin M) :
    rationalBandContains bands (decodedRat M y) ↔ bandContains bands (uniformHHLDecode M y) := by
  constructor
  · rintro ⟨b, hb, hl, hu⟩
    have hl' : (b.1 : ℝ) ≤ (decodedRat M y : ℝ) := Rat.cast_le.mpr hl
    have hu' : (decodedRat M y : ℝ) ≤ (b.2 : ℝ) := Rat.cast_le.mpr hu
    exact ⟨b, hb, by simpa only [decodedRat_cast] using! hl',
      by simpa only [decodedRat_cast] using! hu'⟩
  · rintro ⟨b, hb, hl, hu⟩
    have hl' : (b.1 : ℝ) ≤ (decodedRat M y : ℝ) := by
      simpa only [decodedRat_cast] using! hl
    have hu' : (decodedRat M y : ℝ) ≤ (b.2 : ℝ) := by
      simpa only [decodedRat_cast] using! hu
    exact ⟨b, hb, Rat.cast_le.mp hl', Rat.cast_le.mp hu'⟩

/-- The Boolean band-membership test applied to the rational decoding of an `n`-bit register. -/
def bandBool (n : ℕ) (bands : List (ℚ × ℚ)) (x : Reg n) : Bool :=
  rationalBandBool bands (decodedRat (2 ^ n) (bitVecEquiv n x))

/-- The register band test equals the decision procedure for membership of its encoded label in
`bandLabels`. -/
@[simp] theorem bandBool_eq_label (n : ℕ) (bands : List (ℚ × ℚ)) (x : Reg n) :
    bandBool n bands x = decide (bitVecEquiv n x ∈ bandLabels (2 ^ n) bands) := by
  simp [bandBool, bandLabels, rationalBandContains_iff]

/-- The Boolean graph for the union of the rational bands, using two endpoint tests per band and
disjoining their conjunctions. -/
def bandProgram (n : ℕ) : List (ℚ × ℚ) → BoolDAG n
  | [] => .const false
  | b :: bs =>
      let q := fun x : Reg n => decodedRat (2 ^ n) (bitVecEquiv n x)
      let lower := BoolDAG.dnf (fun x => decide (b.1 ≤ q x))
      let upper := BoolDAG.dnf (fun x => decide (q x ≤ b.2))
      (lower.and upper).or (bandProgram n bs)

/-- The band program evaluates to the Boolean band-membership test on every input register. -/
@[simp] theorem value_bandProgram (n : ℕ) (bands : List (ℚ × ℚ)) (x : Reg n) :
    (bandProgram n bands).value x = bandBool n bands x := by
  induction bands with
  | nil => simp [bandProgram, bandBool, rationalBandBool]
  | cons b bs ih => simp [bandProgram, bandBool, rationalBandBool, ih]

/-- The band program has stored comparison count exactly twice the number of bands. -/
@[simp] theorem comparisons_bandProgram (n : ℕ) (bands : List (ℚ × ℚ)) :
    (bandProgram n bands).comparisons = 2 * bands.length := by
  induction bands with
  | nil => rfl
  | cons b bs ih =>
      simp only [bandProgram, BoolDAG.comparisons_or, BoolDAG.comparisons_and,
        BoolDAG.comparisons_dnf, ih, List.length_cons]
      omega

/-- The reversible reflection-gate word obtained by compiling the band program with one output
wire. -/
noncomputable def bandWord (n : ℕ) (bands : List (ℚ × ℚ)) :
    List (ReflectionGate (n + (bandProgram n bands).nodes + 1)) :=
  booleanDAGSteps (bandProgram n bands).graph (fun _ : Fin 1 => (bandProgram n bands).out)

/-- The compiled computation stage maps an initialized basis state to the graph's computed
history, and the selected graph output equals the band test. -/
theorem band_compute_history (n : ℕ) (bands : List (ℚ × ℚ)) (x : Reg n) (y : Reg 1) :
    Run (1 : Matrix (Reg (n + (bandProgram n bands).nodes + 1))
        (Reg (n + (bandProgram n bands).nodes + 1)) ℂ)
      (reflectionCompile (booleanDAGCompute (bandProgram n bands).graph 1))
      (Ket (booleanDAGInput n (bandProgram n bands).nodes 1 x y)) =
      Ket (booleanDAGComputed (bandProgram n bands).graph 1 x y) ∧
    (bandProgram n bands).value x = bandBool n bands x := by
  exact ⟨boolean_dag_compute_basis _ _ _ _, value_bandProgram n bands x⟩

/-- On a basis state with initialized work bits, the band word preserves the input, restores the
work bits, and XORs the band test into the output bit. -/
theorem bandWord_basis (n : ℕ) (bands : List (ℚ × ℚ)) (x : Reg n) (y : Reg 1) :
    Run (1 : Matrix (Reg (n + (bandProgram n bands).nodes + 1))
        (Reg (n + (bandProgram n bands).nodes + 1)) ℂ)
      (reflectionCompile (bandWord n bands))
      (Ket (booleanDAGInput n (bandProgram n bands).nodes 1 x y)) =
      Ket (booleanDAGInput n (bandProgram n bands).nodes 1 x
        (fun j => y j ^^ bandBool n bands x)) := by
  have hout : booleanDAGOutput (bandProgram n bands).graph
      (fun _ : Fin 1 => (bandProgram n bands).out) x y =
      (fun j => y j ^^ bandBool n bands x) := by
    funext j
    simp only [booleanDAGOutput]
    exact congrArg (fun b => y j ^^ b) (value_bandProgram n bands x)
  rw [bandWord, boolean_dag_basis, hout]

/-- Applying the band word twice returns every basis state with initialized work bits to itself. -/
theorem bandWord_involutive (n : ℕ) (bands : List (ℚ × ℚ)) (x : Reg n) (y : Reg 1) :
    Run (1 : Matrix (Reg (n + (bandProgram n bands).nodes + 1))
        (Reg (n + (bandProgram n bands).nodes + 1)) ℂ)
      (reflectionCompile (bandWord n bands ++ bandWord n bands))
      (Ket (booleanDAGInput n (bandProgram n bands).nodes 1 x y)) =
      Ket (booleanDAGInput n (bandProgram n bands).nodes 1 x y) := by
  rw [reflectionCompile_append, run_append, bandWord_basis, bandWord_basis]
  congr 2
  funext j
  cases y j <;> cases bandBool n bands x <;> simp

/-- The band word is legal, has length at most `30 * (bandProgram n bands).nodes + 1`, and
compiles with zero queries and gate count equal to its length. Its graph has comparison
count `2 * bands.length`. -/
theorem bandWord_resources (n : ℕ) (bands : List (ℚ × ℚ)) :
    reflectionLegal (bandWord n bands) ∧
    (bandWord n bands).length ≤ 30 * (bandProgram n bands).nodes + 1 ∧
    QueryCount (reflectionCompile (bandWord n bands)) = 0 ∧
    GateCount (reflectionCompile (bandWord n bands)) = (bandWord n bands).length ∧
    (bandProgram n bands).comparisons = 2 * bands.length := by
  obtain ⟨hl, hn, hq, hg⟩ := boolean_dag_resources (bandProgram n bands).graph
    (fun _ : Fin 1 => (bandProgram n bands).out)
  exact ⟨hl, hn, hq, hg, comparisons_bandProgram n bands⟩

/-- The final wire of the register, used as the single band-classification output bit. -/
def bandOutputWire (n : ℕ) (bands : List (ℚ × ℚ)) :
    Fin (n + (bandProgram n bands).nodes + 1) :=
  ⟨n + (bandProgram n bands).nodes, by omega⟩

/-- The word that computes the band test, applies Pauli Z to its output wire, and repeats the
band word to uncompute. -/
noncomputable def bandSignWord (n : ℕ) (bands : List (ℚ × ℚ)) :
    List (ReflectionGate (n + (bandProgram n bands).nodes + 1)) :=
  bandWord n bands ++
    [.inl (bandOutputWire n bands, PauliZ)] ++ bandWord n bands

/-- The amplitude 1 for registers whose encoded labels lie in the bands and -1 for all other
registers. -/
noncomputable def bandSignAmplitude (n : ℕ) (bands : List (ℚ × ℚ)) (x : Reg n) : ℂ :=
  if bitVecEquiv n x ∈ bandLabels (2 ^ n) bands then 1 else -1

/-- The register sign amplitude equals the corresponding diagonal entry of `bandSign`,
independently of the auxiliary coordinate `p`. -/
@[simp] theorem bandSignAmplitude_eq_bandSign {I : Type} [Fintype I] [DecidableEq I]
    (n : ℕ) (bands : List (ℚ × ℚ)) (x : Reg n) (p : Bool × I) :
    bandSignAmplitude n bands x =
      bandSign (I := I) (2 ^ n) (bandLabels (2 ^ n) bands)
        (bitVecEquiv n x, p) (bitVecEquiv n x, p) := by
  simp [bandSignAmplitude, bandSign]

/-- The sign amplitude is 1 when the Boolean band test is true and -1 otherwise. -/
@[simp] theorem bandSignAmplitude_eq_bandBool (n : ℕ) (bands : List (ℚ × ℚ)) (x : Reg n) :
    bandSignAmplitude n bands x = if bandBool n bands x then 1 else -1 := by
  by_cases h : bitVecEquiv n x ∈ bandLabels (2 ^ n) bands <;>
    simp [bandSignAmplitude, h]

/-- Pauli Z on the band output wire multiplies a basis ket by -1 when that bit is true and by 1
otherwise. -/
theorem run_bandOutputZ (n : ℕ) (bands : List (ℚ × ℚ))
    (z : Reg (n + (bandProgram n bands).nodes + 1)) :
    Run (1 : Matrix (Reg (n + (bandProgram n bands).nodes + 1))
        (Reg (n + (bandProgram n bands).nodes + 1)) ℂ)
      (reflectionCompile [.inl (bandOutputWire n bands, PauliZ)]) (Ket z) =
      (if z (bandOutputWire n bands) then (-1 : ℂ) else 1) • Ket z := by
  change ApplyGate (wireGate _ (bandOutputWire n bands) PauliZ) (Ket z) = _
  rw [applyGate_wireGate_ket]
  cases hz : z (bandOutputWire n bands) <;>
    simp [PauliZ] <;> rw [← hz, Function.update_eq_self]

/-- With initialized work bits and output bit true, the band sign word multiplies a basis ket by
`bandSignAmplitude` and restores all its bits. -/
theorem bandSignWord_basis (n : ℕ) (bands : List (ℚ × ℚ)) (x : Reg n) :
    Run (1 : Matrix (Reg (n + (bandProgram n bands).nodes + 1))
        (Reg (n + (bandProgram n bands).nodes + 1)) ℂ)
      (reflectionCompile (bandSignWord n bands))
      (Ket (booleanDAGInput n (bandProgram n bands).nodes 1 x (fun _ => true))) =
      bandSignAmplitude n bands x •
        Ket (booleanDAGInput n (bandProgram n bands).nodes 1 x (fun _ => true)) := by
  rw [bandSignWord, reflectionCompile_append, reflectionCompile_append,
    run_append, run_append, bandWord_basis, run_bandOutputZ]
  have hw : (booleanDAGInput n (bandProgram n bands).nodes 1 x
      (fun _ : Fin 1 => (true ^^ bandBool n bands x))) (bandOutputWire n bands) =
      (true ^^ bandBool n bands x) := by
    simp [bandOutputWire, booleanDAGInput]
  rw [hw, run_reflectionCompile_smul, bandWord_basis, bandSignAmplitude_eq_bandBool]
  cases bandBool n bands x <;> simp

/-- The linear embedding of an input state obtained by adjoining `k` initialized work bits and
one output bit set to true. -/
noncomputable def bandSignEmbed (n k : ℕ) (ψ : QState (Reg n)) :
    QState (Reg (n + k + 1)) :=
  ∑ x, ψ x • Ket (booleanDAGInput n k 1 x (fun _ => true))

/-- On an embedded superposition, the band sign word multiplies each input amplitude by its band
sign while restoring the work and output bits. -/
theorem bandSignWord_coherent (n : ℕ) (bands : List (ℚ × ℚ)) (ψ : QState (Reg n)) :
    Run (1 : Matrix (Reg (n + (bandProgram n bands).nodes + 1))
        (Reg (n + (bandProgram n bands).nodes + 1)) ℂ)
      (reflectionCompile (bandSignWord n bands))
      (bandSignEmbed n (bandProgram n bands).nodes ψ) =
      ∑ x, (bandSignAmplitude n bands x * ψ x) •
        Ket (booleanDAGInput n (bandProgram n bands).nodes 1 x (fun _ => true)) := by
  simp only [bandSignEmbed, run_reflectionCompile_sum, run_reflectionCompile_smul,
    bandSignWord_basis, smul_smul]
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_comm]

/-- The band sign word is legal, has length `2 * (bandWord n bands).length + 1`, and compiles
with zero queries and gate count equal to its length. -/
theorem bandSignWord_resources (n : ℕ) (bands : List (ℚ × ℚ)) :
    reflectionLegal (bandSignWord n bands) ∧
    (bandSignWord n bands).length = 2 * (bandWord n bands).length + 1 ∧
    QueryCount (reflectionCompile (bandSignWord n bands)) = 0 ∧
    GateCount (reflectionCompile (bandSignWord n bands)) = (bandSignWord n bands).length := by
  have hz : reflectionLegal ([.inl (bandOutputWire n bands, PauliZ)] :
      List (ReflectionGate (n + (bandProgram n bands).nodes + 1))) := by
    intro g hg
    simp only [List.mem_singleton] at hg
    subst g
    exact pauliZ_unitary
  refine ⟨?_, ?_, queryCount_reflectionCompile _, gateCount_reflectionCompile _⟩
  · rw [bandSignWord, reflectionLegal_append, reflectionLegal_append]
    exact ⟨⟨(bandWord_resources n bands).1, hz⟩, (bandWord_resources n bands).1⟩
  · simp only [bandSignWord, List.length_append, List.length_singleton]
    omega

open Qatlib.Concepts.NumericalWord.MixedWordError

/-- The query count of a concatenated circuit is the sum of the query counts of its two parts. -/
private theorem query_count_append {I : Type} [Fintype I] [DecidableEq I]
    (C D : Circuit I) : QueryCount (C ++ D) = QueryCount C + QueryCount D := by
  induction C with
  | nil => simp [QueryCount]
  | cons s C ih =>
      cases s <;> simp only [List.cons_append, QueryCount, ih]
      all_goals omega

/-- The gate count of a concatenated circuit is the sum of the gate counts of its two parts. -/
private theorem gate_count_append {I : Type} [Fintype I] [DecidableEq I]
    (C D : Circuit I) : GateCount (C ++ D) = GateCount C + GateCount D := by
  induction C with
  | nil => simp [GateCount]
  | cons s C ih =>
      cases s <;> simp only [List.cons_append, GateCount, ih]
      all_goals omega

/-- The approximate local Fourier-transform word on `n` wires lifted to a register with `k` work
wires and one output wire. -/
noncomputable def embeddedApproxLocalQFT (n b k : ℕ) : List (LocalQFTGate (n + k + 1)) :=
  liftWordTo (by omega) (approxLocalQFT n b)

/-- The adjoint approximate local Fourier-transform word lifted to a register with `k` work
wires and one output wire. -/
noncomputable def embeddedApproxLocalQFTAdjoint (n b k : ℕ) :
    List (LocalQFTGate (n + k + 1)) :=
  liftWordTo (by omega) (localProgramAdjoint (approxLocalQFT n b))

/-- Lifting a local gate word to more wires commutes with taking its program adjoint. -/
@[simp] theorem liftWordTo_localProgramAdjoint {n n' : ℕ} (h : n ≤ n')
    (gs : List (LocalQFTGate n)) :
    liftWordTo h (localProgramAdjoint gs) = localProgramAdjoint (liftWordTo h gs) := by
  simp only [liftWordTo, localProgramAdjoint, List.map_reverse, List.map_map]
  congr 1
  apply List.map_congr_left
  intro g _
  cases g <;> rfl

/-- The embedded adjoint Fourier word is the program adjoint of the embedded Fourier word. -/
@[simp] theorem embeddedApproxLocalQFTAdjoint_eq (n b k : ℕ) :
    embeddedApproxLocalQFTAdjoint n b k =
      localProgramAdjoint (embeddedApproxLocalQFT n b k) :=
  liftWordTo_localProgramAdjoint _ _

/-- Embedding the approximate Fourier word preserves its length. -/
@[simp] theorem embeddedApproxLocalQFT_length (n b k : ℕ) :
    (embeddedApproxLocalQFT n b k).length = (approxLocalQFT n b).length := by
  simp [embeddedApproxLocalQFT, liftWordTo]

/-- The embedded adjoint Fourier word has the same length as the original approximate Fourier
word. -/
@[simp] theorem embeddedApproxLocalQFTAdjoint_length (n b k : ℕ) :
    (embeddedApproxLocalQFTAdjoint n b k).length = (approxLocalQFT n b).length := by
  simp [embeddedApproxLocalQFTAdjoint, liftWordTo, localProgramAdjoint]

/-- The circuit that applies the embedded approximate Fourier transform, then the band sign
word, then the embedded adjoint Fourier transform. -/
noncomputable def bandLocalQFTCircuit (n : ℕ) (bands : List (ℚ × ℚ)) (b : ℕ) :
    Circuit (Reg (n + (bandProgram n bands).nodes + 1)) :=
  localProgramCircuit (embeddedApproxLocalQFT n b (bandProgram n bands).nodes) ++
    reflectionCompile (bandSignWord n bands) ++
    localProgramCircuit (embeddedApproxLocalQFTAdjoint n b (bandProgram n bands).nodes)

/-- Running the band Fourier circuit equals the nested execution of the forward Fourier word,
band sign word, and adjoint Fourier word, in that order. -/
theorem bandLocalQFTCircuit_run (n : ℕ) (bands : List (ℚ × ℚ)) (b : ℕ)
    (ψ : QState (Reg (n + (bandProgram n bands).nodes + 1))) :
    Run (1 : Matrix (Reg (n + (bandProgram n bands).nodes + 1))
        (Reg (n + (bandProgram n bands).nodes + 1)) ℂ)
      (bandLocalQFTCircuit n bands b) ψ =
      Run (1 : Matrix (Reg (n + (bandProgram n bands).nodes + 1))
          (Reg (n + (bandProgram n bands).nodes + 1)) ℂ)
        (localProgramCircuit (embeddedApproxLocalQFTAdjoint n b (bandProgram n bands).nodes))
        (Run (1 : Matrix (Reg (n + (bandProgram n bands).nodes + 1))
            (Reg (n + (bandProgram n bands).nodes + 1)) ℂ)
          (reflectionCompile (bandSignWord n bands))
          (Run (1 : Matrix (Reg (n + (bandProgram n bands).nodes + 1))
              (Reg (n + (bandProgram n bands).nodes + 1)) ℂ)
            (localProgramCircuit (embeddedApproxLocalQFT n b (bandProgram n bands).nodes)) ψ)) := by
  rw [bandLocalQFTCircuit, run_append, run_append]

/-- The band Fourier circuit uses zero queries and has gate count `2 * (approxLocalQFT n
b).length + (bandSignWord n bands).length`. -/
theorem bandLocalQFTCircuit_resources (n : ℕ) (bands : List (ℚ × ℚ)) (b : ℕ) :
    QueryCount (bandLocalQFTCircuit n bands b) = 0 ∧
    GateCount (bandLocalQFTCircuit n bands b) =
      2 * (approxLocalQFT n b).length + (bandSignWord n bands).length := by
  obtain ⟨-, -, -, -, -, qf, gf, -, -⟩ := localDyadicProgram_run_adjoint_cost
    (n + (bandProgram n bands).nodes + 1)
    (embeddedApproxLocalQFT n b (bandProgram n bands).nodes)
    (0 : QState (Reg (n + (bandProgram n bands).nodes + 1)))
  obtain ⟨-, -, -, -, -, qa, ga, -, -⟩ := localDyadicProgram_run_adjoint_cost
    (n + (bandProgram n bands).nodes + 1)
    (embeddedApproxLocalQFTAdjoint n b (bandProgram n bands).nodes)
    (0 : QState (Reg (n + (bandProgram n bands).nodes + 1)))
  constructor
  · rw [bandLocalQFTCircuit, query_count_append, query_count_append,
      qf, queryCount_reflectionCompile, qa]
  · rw [bandLocalQFTCircuit, gate_count_append, gate_count_append,
      gf, gateCount_reflectionCompile, ga, embeddedApproxLocalQFT_length,
      embeddedApproxLocalQFTAdjoint_length]
    omega

/-- The band Fourier circuit's gate count is at most twice the approximate Fourier-word length
plus `2 * (30 * (bandProgram n bands).nodes + 1) + 1`. -/
theorem bandLocalQFTCircuit_gate_bound (n : ℕ) (bands : List (ℚ × ℚ)) (b : ℕ) :
    GateCount (bandLocalQFTCircuit n bands b) ≤
      2 * (approxLocalQFT n b).length + 2 * (30 * (bandProgram n bands).nodes + 1) + 1 := by
  rw [(bandLocalQFTCircuit_resources n bands b).2,
    (bandSignWord_resources n bands).2.1]
  have h := (bandWord_resources n bands).2.1
  omega

/-- The band classifier has the stated Boolean semantics, reversible basis action, comparison
count, and circuit resource bounds. Its sign word acts coherently by the prescribed signs,
and the Fourier circuit uses the embedded program adjoint with the stated exact counts. -/
theorem frontier1 :
    (∀ (n : ℕ) (bands : List (ℚ × ℚ)) (x : Reg n) (y : Reg 1),
      (bandProgram n bands).value x = decide (bitVecEquiv n x ∈ bandLabels (2 ^ n) bands) ∧
      Run (1 : Matrix (Reg (n + (bandProgram n bands).nodes + 1))
          (Reg (n + (bandProgram n bands).nodes + 1)) ℂ)
        (reflectionCompile (bandWord n bands))
        (Ket (booleanDAGInput n (bandProgram n bands).nodes 1 x y)) =
        Ket (booleanDAGInput n (bandProgram n bands).nodes 1 x
          (fun j => y j ^^ bandBool n bands x)) ∧
      reflectionLegal (bandWord n bands) ∧
      (bandWord n bands).length ≤ 30 * (bandProgram n bands).nodes + 1 ∧
      QueryCount (reflectionCompile (bandWord n bands)) = 0 ∧
      GateCount (reflectionCompile (bandWord n bands)) = (bandWord n bands).length ∧
      (bandProgram n bands).comparisons = 2 * bands.length) ∧
    (∀ (n : ℕ) (bands : List (ℚ × ℚ)) (x : Reg n),
      Run (1 : Matrix (Reg (n + (bandProgram n bands).nodes + 1))
          (Reg (n + (bandProgram n bands).nodes + 1)) ℂ)
        (reflectionCompile (bandSignWord n bands))
        (Ket (booleanDAGInput n (bandProgram n bands).nodes 1 x (fun _ => true))) =
        bandSignAmplitude n bands x •
          Ket (booleanDAGInput n (bandProgram n bands).nodes 1 x (fun _ => true))) ∧
    (∀ (n : ℕ) (bands : List (ℚ × ℚ)) (ψ : QState (Reg n)),
      Run (1 : Matrix (Reg (n + (bandProgram n bands).nodes + 1))
          (Reg (n + (bandProgram n bands).nodes + 1)) ℂ)
        (reflectionCompile (bandSignWord n bands))
        (bandSignEmbed n (bandProgram n bands).nodes ψ) =
        ∑ x, (bandSignAmplitude n bands x * ψ x) •
          Ket (booleanDAGInput n (bandProgram n bands).nodes 1 x (fun _ => true))) ∧
    (∀ (n : ℕ) (bands : List (ℚ × ℚ)) (b : ℕ),
      embeddedApproxLocalQFTAdjoint n b (bandProgram n bands).nodes =
        localProgramAdjoint (embeddedApproxLocalQFT n b (bandProgram n bands).nodes) ∧
      QueryCount (bandLocalQFTCircuit n bands b) = 0 ∧
      GateCount (bandLocalQFTCircuit n bands b) =
        2 * (approxLocalQFT n b).length + (bandSignWord n bands).length) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n bands x y
    exact ⟨by simp, bandWord_basis n bands x y, bandWord_resources n bands⟩
  · exact bandSignWord_basis
  · exact bandSignWord_coherent
  · intro n bands b
    exact ⟨embeddedApproxLocalQFTAdjoint_eq n b (bandProgram n bands).nodes,
      bandLocalQFTCircuit_resources n bands b⟩

end Qatlib.Concepts.HspRecovery.ReductionCore
