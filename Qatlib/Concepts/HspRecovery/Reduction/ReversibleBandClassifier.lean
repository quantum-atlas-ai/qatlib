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
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

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

structure BoolDAG (m : ℕ) where
  nodes : ℕ
  graph : BooleanDAG m nodes
  out : Fin (m + nodes)
  comparisons : ℕ

namespace BoolDAG

def value {m : ℕ} (g : BoolDAG m) (x : Reg m) : Bool :=
  booleanDAGValue g.graph x g.out

def input {m : ℕ} (i : Fin m) : BoolDAG m where
  nodes := 0
  graph := .nil
  out := i
  comparisons := 0

@[simp] theorem value_input {m : ℕ} (i : Fin m) (x : Reg m) :
    (input i).value x = x i := rfl

def extend {m : ℕ} (g : BoolDAG m) (node : BooleanNode (m + g.nodes)) : BoolDAG m where
  nodes := g.nodes + 1
  graph := g.graph.snoc node
  out := Fin.last _
  comparisons := g.comparisons

@[simp] theorem value_extend {m : ℕ} (g : BoolDAG m)
    (node : BooleanNode (m + g.nodes)) (x : Reg m) :
    (g.extend node).value x = booleanNodeValue node (booleanDAGValue g.graph x) := by
  simp [value, extend, booleanDAGValue]

@[simp] theorem value_extend_prefix {m : ℕ} (g : BoolDAG m)
    (node : BooleanNode (m + g.nodes)) (x : Reg m) (i : Fin (m + g.nodes)) :
    booleanDAGValue (g.extend node).graph x (Fin.castSucc i) = booleanDAGValue g.graph x i := by
  simp [extend, booleanDAGValue]

def const {m : ℕ} (b : Bool) : BoolDAG m where
  nodes := 1
  graph := .snoc .nil (.constant b)
  out := Fin.last _
  comparisons := 0

@[simp] theorem value_const {m : ℕ} (b : Bool) (x : Reg m) :
    (const (m := m) b).value x = b := by
  simp [value, const, booleanDAGValue, booleanNodeValue]

def neg {m : ℕ} (g : BoolDAG m) : BoolDAG m := g.extend (.neg g.out)

@[simp] theorem value_neg {m : ℕ} (g : BoolDAG m) (x : Reg m) :
    g.neg.value x = !(g.value x) := by
  simp only [neg, value_extend, booleanNodeValue]
  rfl

private theorem graph_input {m k : ℕ} (g : BooleanDAG m k) (x : Reg m) (i : Fin m) :
    booleanDAGValue g x (Fin.castLE (by omega) i) = x i := by
  induction g with
  | nil => rfl
  | @snoc k g node ih =>
      change booleanDAGValue (g.snoc node) x
        (Fin.castSucc (Fin.castLE (Nat.le_add_right m k) i)) = x i
      simpa only [booleanDAGValue, Fin.lastCases_castSucc] using! ih

def append {m : ℕ} (g h : BoolDAG m) : BoolDAG m where
  nodes := g.nodes + h.nodes
  graph := booleanDAGSplice g.graph (fun i => Fin.castLE (by omega) i) h.graph
  out := booleanSpliceSource (fun i => Fin.castLE (by omega) i) h.out
  comparisons := g.comparisons + h.comparisons

@[simp] theorem value_append {m : ℕ} (g h : BoolDAG m) (x : Reg m) :
    (g.append h).value x = h.value x := by
  simp only [append, value]
  rw [boolean_dag_splice_value]
  congr 1
  funext i
  exact graph_input g.graph x i

theorem value_append_out {m : ℕ} (g h : BoolDAG m) (x : Reg m) :
    booleanDAGValue (g.append h).graph x (g.append h).out = h.value x :=
  value_append g h x

theorem value_append_left {m : ℕ} (g h : BoolDAG m) (x : Reg m) :
    booleanDAGValue (g.append h).graph x
      (Fin.castLE (by dsimp [append]; omega) g.out) = g.value x :=
  boolean_dag_splice_prefix g.graph _ h.graph x g.out

def and {m : ℕ} (g h : BoolDAG m) : BoolDAG m :=
  let gh := g.append h
  let left : Fin (m + gh.nodes) := Fin.castLE (by dsimp [gh, append]; omega) g.out
  gh.extend (.conj left gh.out)

@[simp] theorem value_and {m : ℕ} (g h : BoolDAG m) (x : Reg m) :
    (g.and h).value x = (g.value x && h.value x) := by
  simp only [and, value_extend, booleanNodeValue, value_append_left, value_append_out]

def xor {m : ℕ} (g h : BoolDAG m) : BoolDAG m :=
  let gh := g.append h
  let left : Fin (m + gh.nodes) := Fin.castLE (by dsimp [gh, append]; omega) g.out
  gh.extend (.xor left gh.out)

@[simp] theorem value_xor {m : ℕ} (g h : BoolDAG m) (x : Reg m) :
    (g.xor h).value x = (g.value x ^^ h.value x) := by
  simp only [xor, value_extend, booleanNodeValue, value_append_left, value_append_out]

def or {m : ℕ} (g h : BoolDAG m) : BoolDAG m := (g.neg.and h.neg).neg

@[simp] theorem value_or {m : ℕ} (g h : BoolDAG m) (x : Reg m) :
    (g.or h).value x = (g.value x || h.value x) := by
  simp only [or, value_neg, value_and]
  cases g.value x <;> cases h.value x <;> decide

def literal {m : ℕ} (target : Reg m) (i : Fin m) : BoolDAG m :=
  if target i then input i else (input i).neg

@[simp] theorem value_literal {m : ℕ} (target : Reg m) (i : Fin m) (x : Reg m) :
    (literal target i).value x = (x i == target i) := by
  cases h : target i <;> simp [literal, h]

def eqConstAux {m : ℕ} (target : Reg m) : List (Fin m) → BoolDAG m
  | [] => const true
  | i :: is => (literal target i).and (eqConstAux target is)

@[simp] theorem value_eqConstAux {m : ℕ} (target : Reg m) (is : List (Fin m)) (x : Reg m) :
    (eqConstAux target is).value x = is.all (fun i => x i == target i) := by
  induction is with
  | nil => simp [eqConstAux]
  | cons i is ih => simp only [eqConstAux, value_and, value_literal, ih, List.all_cons]

def eqConst {m : ℕ} (target : Reg m) : BoolDAG m :=
  eqConstAux target (List.finRange m)

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

def orList {m : ℕ} : List (BoolDAG m) → BoolDAG m
  | [] => const false
  | g :: gs => g.or (orList gs)

@[simp] theorem value_orList {m : ℕ} (gs : List (BoolDAG m)) (x : Reg m) :
    (orList gs).value x = gs.any (fun g => g.value x) := by
  induction gs with
  | nil => simp [orList]
  | cons g gs ih => simp [orList, ih]

def dnf {m : ℕ} (f : Reg m → Bool) : BoolDAG m :=
  { orList ((((List.finRange (2 ^ m)).map (bitVecEquiv m).symm).filter f).map eqConst) with
    comparisons := 1 }

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

@[simp] theorem comparisons_extend {m : ℕ} (g : BoolDAG m)
    (node : BooleanNode (m + g.nodes)) : (g.extend node).comparisons = g.comparisons := rfl

@[simp] theorem comparisons_const {m : ℕ} (b : Bool) :
    (const (m := m) b).comparisons = 0 := rfl

@[simp] theorem comparisons_append {m : ℕ} (g h : BoolDAG m) :
    (g.append h).comparisons = g.comparisons + h.comparisons := rfl

@[simp] theorem comparisons_and {m : ℕ} (g h : BoolDAG m) :
    (g.and h).comparisons = g.comparisons + h.comparisons := by
  simp [and]

@[simp] theorem comparisons_or {m : ℕ} (g h : BoolDAG m) :
    (g.or h).comparisons = g.comparisons + h.comparisons := by
  simp [or, neg]

@[simp] theorem comparisons_dnf {m : ℕ} (f : Reg m → Bool) :
    (dnf f).comparisons = 1 := rfl

end BoolDAG

def decodedRat (M : ℕ) (y : Fin M) : ℚ :=
  if 2 * y.val ≤ M then (y.val : ℚ) / (M : ℚ) else (y.val : ℚ) / (M : ℚ) - 1

@[simp] theorem decodedRat_cast (M : ℕ) (y : Fin M) :
    (decodedRat M y : ℝ) = uniformHHLDecode M y := by
  simp only [decodedRat, uniformHHLDecode]
  split_ifs <;> norm_num

def rationalBandContains (bands : List (ℚ × ℚ)) (x : ℚ) : Prop :=
  ∃ b ∈ bands, b.1 ≤ x ∧ x ≤ b.2

def rationalBandBool (bands : List (ℚ × ℚ)) (x : ℚ) : Bool :=
  bands.any (fun b => decide (b.1 ≤ x ∧ x ≤ b.2))

@[simp] theorem rationalBandBool_eq (bands : List (ℚ × ℚ)) (x : ℚ) :
    rationalBandBool bands x = decide (rationalBandContains bands x) := by
  rw [rationalBandBool, Bool.eq_iff_iff, List.any_eq_true]
  simp only [decide_eq_true_eq]
  rfl

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

def bandBool (n : ℕ) (bands : List (ℚ × ℚ)) (x : Reg n) : Bool :=
  rationalBandBool bands (decodedRat (2 ^ n) (bitVecEquiv n x))

@[simp] theorem bandBool_eq_label (n : ℕ) (bands : List (ℚ × ℚ)) (x : Reg n) :
    bandBool n bands x = decide (bitVecEquiv n x ∈ bandLabels (2 ^ n) bands) := by
  simp [bandBool, bandLabels, rationalBandContains_iff]

def bandProgram (n : ℕ) : List (ℚ × ℚ) → BoolDAG n
  | [] => .const false
  | b :: bs =>
      let q := fun x : Reg n => decodedRat (2 ^ n) (bitVecEquiv n x)
      let lower := BoolDAG.dnf (fun x => decide (b.1 ≤ q x))
      let upper := BoolDAG.dnf (fun x => decide (q x ≤ b.2))
      (lower.and upper).or (bandProgram n bs)

@[simp] theorem value_bandProgram (n : ℕ) (bands : List (ℚ × ℚ)) (x : Reg n) :
    (bandProgram n bands).value x = bandBool n bands x := by
  induction bands with
  | nil => simp [bandProgram, bandBool, rationalBandBool]
  | cons b bs ih => simp [bandProgram, bandBool, rationalBandBool, ih]

@[simp] theorem comparisons_bandProgram (n : ℕ) (bands : List (ℚ × ℚ)) :
    (bandProgram n bands).comparisons = 2 * bands.length := by
  induction bands with
  | nil => rfl
  | cons b bs ih =>
      simp only [bandProgram, BoolDAG.comparisons_or, BoolDAG.comparisons_and,
        BoolDAG.comparisons_dnf, ih, List.length_cons]
      omega

noncomputable def bandWord (n : ℕ) (bands : List (ℚ × ℚ)) :
    List (ReflectionGate (n + (bandProgram n bands).nodes + 1)) :=
  booleanDAGSteps (bandProgram n bands).graph (fun _ : Fin 1 => (bandProgram n bands).out)

theorem band_compute_history (n : ℕ) (bands : List (ℚ × ℚ)) (x : Reg n) (y : Reg 1) :
    Run (1 : Matrix (Reg (n + (bandProgram n bands).nodes + 1))
        (Reg (n + (bandProgram n bands).nodes + 1)) ℂ)
      (reflectionCompile (booleanDAGCompute (bandProgram n bands).graph 1))
      (Ket (booleanDAGInput n (bandProgram n bands).nodes 1 x y)) =
      Ket (booleanDAGComputed (bandProgram n bands).graph 1 x y) ∧
    (bandProgram n bands).value x = bandBool n bands x := by
  exact ⟨boolean_dag_compute_basis _ _ _ _, value_bandProgram n bands x⟩

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

theorem bandWord_resources (n : ℕ) (bands : List (ℚ × ℚ)) :
    reflectionLegal (bandWord n bands) ∧
    (bandWord n bands).length ≤ 30 * (bandProgram n bands).nodes + 1 ∧
    QueryCount (reflectionCompile (bandWord n bands)) = 0 ∧
    GateCount (reflectionCompile (bandWord n bands)) = (bandWord n bands).length ∧
    (bandProgram n bands).comparisons = 2 * bands.length := by
  obtain ⟨hl, hn, hq, hg⟩ := boolean_dag_resources (bandProgram n bands).graph
    (fun _ : Fin 1 => (bandProgram n bands).out)
  exact ⟨hl, hn, hq, hg, comparisons_bandProgram n bands⟩

def bandOutputWire (n : ℕ) (bands : List (ℚ × ℚ)) :
    Fin (n + (bandProgram n bands).nodes + 1) :=
  ⟨n + (bandProgram n bands).nodes, by omega⟩

noncomputable def bandSignWord (n : ℕ) (bands : List (ℚ × ℚ)) :
    List (ReflectionGate (n + (bandProgram n bands).nodes + 1)) :=
  bandWord n bands ++
    [.inl (bandOutputWire n bands, PauliZ)] ++ bandWord n bands

noncomputable def bandSignAmplitude (n : ℕ) (bands : List (ℚ × ℚ)) (x : Reg n) : ℂ :=
  if bitVecEquiv n x ∈ bandLabels (2 ^ n) bands then 1 else -1

@[simp] theorem bandSignAmplitude_eq_bandSign {I : Type} [Fintype I] [DecidableEq I]
    (n : ℕ) (bands : List (ℚ × ℚ)) (x : Reg n) (p : Bool × I) :
    bandSignAmplitude n bands x =
      bandSign (I := I) (2 ^ n) (bandLabels (2 ^ n) bands)
        (bitVecEquiv n x, p) (bitVecEquiv n x, p) := by
  simp [bandSignAmplitude, bandSign]

@[simp] theorem bandSignAmplitude_eq_bandBool (n : ℕ) (bands : List (ℚ × ℚ)) (x : Reg n) :
    bandSignAmplitude n bands x = if bandBool n bands x then 1 else -1 := by
  by_cases h : bitVecEquiv n x ∈ bandLabels (2 ^ n) bands <;>
    simp [bandSignAmplitude, h]

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

noncomputable def bandSignEmbed (n k : ℕ) (ψ : QState (Reg n)) :
    QState (Reg (n + k + 1)) :=
  ∑ x, ψ x • Ket (booleanDAGInput n k 1 x (fun _ => true))

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

private theorem query_count_append {I : Type} [Fintype I] [DecidableEq I]
    (C D : Circuit I) : QueryCount (C ++ D) = QueryCount C + QueryCount D := by
  induction C with
  | nil => simp [QueryCount]
  | cons s C ih =>
      cases s <;> simp only [List.cons_append, QueryCount, ih]
      all_goals omega

private theorem gate_count_append {I : Type} [Fintype I] [DecidableEq I]
    (C D : Circuit I) : GateCount (C ++ D) = GateCount C + GateCount D := by
  induction C with
  | nil => simp [GateCount]
  | cons s C ih =>
      cases s <;> simp only [List.cons_append, GateCount, ih]
      all_goals omega

noncomputable def embeddedApproxLocalQFT (n b k : ℕ) : List (LocalQFTGate (n + k + 1)) :=
  liftWordTo (by omega) (approxLocalQFT n b)

noncomputable def embeddedApproxLocalQFTAdjoint (n b k : ℕ) :
    List (LocalQFTGate (n + k + 1)) :=
  liftWordTo (by omega) (localProgramAdjoint (approxLocalQFT n b))

@[simp] theorem liftWordTo_localProgramAdjoint {n n' : ℕ} (h : n ≤ n')
    (gs : List (LocalQFTGate n)) :
    liftWordTo h (localProgramAdjoint gs) = localProgramAdjoint (liftWordTo h gs) := by
  simp only [liftWordTo, localProgramAdjoint, List.map_reverse, List.map_map]
  congr 1
  apply List.map_congr_left
  intro g _
  cases g <;> rfl

@[simp] theorem embeddedApproxLocalQFTAdjoint_eq (n b k : ℕ) :
    embeddedApproxLocalQFTAdjoint n b k =
      localProgramAdjoint (embeddedApproxLocalQFT n b k) :=
  liftWordTo_localProgramAdjoint _ _

@[simp] theorem embeddedApproxLocalQFT_length (n b k : ℕ) :
    (embeddedApproxLocalQFT n b k).length = (approxLocalQFT n b).length := by
  simp [embeddedApproxLocalQFT, liftWordTo]

@[simp] theorem embeddedApproxLocalQFTAdjoint_length (n b k : ℕ) :
    (embeddedApproxLocalQFTAdjoint n b k).length = (approxLocalQFT n b).length := by
  simp [embeddedApproxLocalQFTAdjoint, liftWordTo, localProgramAdjoint]

noncomputable def bandLocalQFTCircuit (n : ℕ) (bands : List (ℚ × ℚ)) (b : ℕ) :
    Circuit (Reg (n + (bandProgram n bands).nodes + 1)) :=
  localProgramCircuit (embeddedApproxLocalQFT n b (bandProgram n bands).nodes) ++
    reflectionCompile (bandSignWord n bands) ++
    localProgramCircuit (embeddedApproxLocalQFTAdjoint n b (bandProgram n bands).nodes)

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

theorem bandLocalQFTCircuit_gate_bound (n : ℕ) (bands : List (ℚ × ℚ)) (b : ℕ) :
    GateCount (bandLocalQFTCircuit n bands b) ≤
      2 * (approxLocalQFT n b).length + 2 * (30 * (bandProgram n bands).nodes + 1) + 1 := by
  rw [(bandLocalQFTCircuit_resources n bands b).2,
    (bandSignWord_resources n bands).2.1]
  have h := (bandWord_resources n bands).2.1
  omega

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
