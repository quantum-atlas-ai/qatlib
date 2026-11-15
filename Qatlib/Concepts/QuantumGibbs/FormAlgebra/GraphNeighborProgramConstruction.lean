/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.GraphSpectralConstructionDefs
public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.GraphCheegerConstruction
public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.GraphExplicitNeighborConstruction
public import Qatlib.Foundations.PureStateMath.Qubit
public import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
public import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
public import Qatlib.Concepts.WalkSearch.TwoLevelLower
public import Qatlib.Concepts.WalkSearch.Spectral.SzegedySpectral
public import Qatlib.Concepts.WalkSearch.CountedWalk.CountedSzegedyAccess
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Nat.Bitwise

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AmplitudeCore.InvFreePhase Qatlib.Concepts.WalkSearch.TwoLevelLower Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.BlockEncoding.StateBlockEncoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false

/-- A finite sum splits into the value at a chosen member and the sum over the remaining
elements. -/
private theorem Finset.sum_eq_add_sum_diff_singleton_of_mem {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    {s : Finset α} {i : α} {f : α → β} (h : i ∈ s) :
    ∑ x ∈ s, f x = f i + ∑ x ∈ s \ {i}, f x := by
  rw [Finset.sdiff_singleton_eq_erase, ← Finset.add_sum_erase _ _ h]
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Qatlib.Concepts.GraphEnergy.ZeroEnergy
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.WalkSearch.CountedWalk
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.WalkSearch.Spectral

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra

open Qatlib
open scoped BigOperators Matrix
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def neighbourRow (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (x : V) : List V :=
  (Finset.univ.filter (fun y => G.Adj x y)).toList.take d

/-- Every vertex listed in `neighbourRow` is adjacent to the row's source vertex. -/
lemma neighbourRow_of_mem {d : ℕ} {x y : V} (hy : y ∈ neighbourRow G d x) : G.Adj x y := by
  have h1 : y ∈ (Finset.univ.filter (fun z => G.Adj x z) : Finset V) :=
    Finset.mem_toList.mp (List.mem_of_mem_take hy)
  exact (Finset.mem_filter.mp h1).2

/-- The neighbor row has length at most its requested bound. -/
lemma neighbourRow_card_le (d : ℕ) (x : V) : (neighbourRow G d x).length ≤ d := by
  unfold neighbourRow
  exact List.length_take_le _ _

structure VertexCodec (V : Type) [Fintype V] (a : ℕ) where

  enc : V → Reg a

  dec : Reg a → V

  dec_enc : ∀ x, dec (enc x) = x

/-- A vertex codec's encoding function is injective. -/
lemma VertexCodec.enc_injective {a : ℕ} (c : VertexCodec V a) : Function.Injective c.enc := by
  intro x y h
  have h1 := c.dec_enc x
  have h2 := c.dec_enc y
  rw [h] at h1
  exact h1.symm.trans h2

/-- A vertex codec of width `a` bounds the vertex count by two to the power `a`. -/
lemma codec_card_le {a : ℕ} (c : VertexCodec V a) : (Fintype.card V : ℕ) ≤ 2 ^ a := by
  have hinj : Function.Injective c.enc := c.enc_injective
  have hcard := Fintype.card_le_of_injective c.enc hinj
  simpa [Fintype.card_fun, Fintype.card_bool] using! hcard

/-- A codec for at least two vertices has positive width. -/
lemma codec_pos_width {a : ℕ} (c : VertexCodec V a) (hne : 2 ≤ Fintype.card V) : 0 < a := by
  by_contra hz
  have ha : a = 0 := Nat.eq_zero_of_not_pos hz
  have hcard := codec_card_le c
  rw [ha, pow_zero] at hcard
  omega

def EffectiveNeighborAccess (n d : ℕ) (hdn : d ≤ n)
    (adj : Fin n → Fin n → Bool) (M : Fin n → Bool) : Prop :=
  ∃ (a w gateRow gateCheck spaceBits : ℕ) (enc : Fin n → Reg a)
      (rowWord checkWord : List FiniteGateCode),
    Function.Injective enc ∧
      0 < a ∧ 2 * a ≤ w ∧ a + 1 ≤ w ∧
      finiteWordLegal w rowWord = true ∧
      finiteWordLegal w checkWord = true ∧
      (∀ x : Fin n, ∀ k : ℕ, (hk : k < d) →
        finiteWordRun w rowWord
            (Qatlib.Foundations.PureStateMath.Ket (regPadLocal w (a + a)
              (regCatLocal (enc x) (enc ⟨k, Nat.lt_of_lt_of_le hk hdn⟩)))) =
          some (Qatlib.Foundations.PureStateMath.Ket (regPadLocal w (a + a)
            (regCatLocal (enc x) (enc (graphNeighborOfLocal n adj x k)))))) ∧
      (∀ x : Fin n,
        finiteWordRun w checkWord
            (Qatlib.Foundations.PureStateMath.Ket (regPadLocal w (a + 1) (regCatLocal (enc x) (fun _ => false)))) =
          some (Qatlib.Foundations.PureStateMath.Ket (regPadLocal w (a + 1) (regCatLocal (enc x) (fun _ => M x))))) ∧
      rowWord.length ≤ gateRow ∧
      checkWord.length ≤ gateCheck ∧
      w ≤ spaceBits ∧
      (∃ x y : Fin n, M x ≠ M y)

/-- Effective neighbor access requires positive address width and workspace of at least twice
that width, hence nonzero workspace. -/
theorem effective_access_excludes_zero_workspace {n d : ℕ} (hdn : d ≤ n)
    (adj : Fin n → Fin n → Bool) (M : Fin n → Bool)
    (h : EffectiveNeighborAccess n d hdn adj M) :
    ∃ (a w : ℕ), 0 < a ∧ 2 * a ≤ w ∧ w ≠ 0 := by
  rcases h with ⟨a, w, gateRow, gateCheck, spaceBits, enc, rowWord, checkWord,
    henc, ha, hw2, hw1, hlegrow, hlegcheck, hrow, hcheck, hgr, hgc, hsp, hM⟩
  refine ⟨a, w, ha, hw2, ?_⟩
  omega

/-- With zero workspace, padding maps all input registers to the same register. -/
theorem zero_workspace_collapses (a w : ℕ) (r : Reg a) (hw : w = 0) (r' : Reg a) :
    regPadLocal w a r = regPadLocal w a r' := by
  subst hw
  funext i
  exact False.elim (Fin.elim0 i)

/-- Effective neighbor access requires positive address width and enough workspace for two
address records. -/
theorem effective_access_requires_two_records {n d : ℕ} (hdn : d ≤ n)
    (adj : Fin n → Fin n → Bool) (M : Fin n → Bool)
    (h : EffectiveNeighborAccess n d hdn adj M) :
    ∃ (a w : ℕ), 0 < a ∧ 2 * a ≤ w := by
  rcases h with ⟨a, w, gateRow, gateCheck, spaceBits, enc, rowWord, checkWord,
    henc, ha, hw2, hw1, hlegrow, hlegcheck, hrow, hcheck, hgr, hgc, hsp, hM⟩
  exact ⟨a, w, ha, hw2⟩

def toffoliCode (n : ℕ) (a b t : Fin n) : List FiniteGateCode :=
  [.h t, .cx b t, .tdg t, .cx a t, .t t, .cx b t, .tdg t, .cx a t, .t b, .t t,
   .h t, .cx a b, .t a, .tdg b, .cx a b]

/-- The finite Hadamard code denotes the corresponding single-wire reflection gate matrix. -/
lemma finiteCodeMatrix_h (n : ℕ) (w : Fin n) :
    finiteCodeMatrix n (.h w) = reflectionGateMatrix (Sum.inl (w, Hadamard)) := by
  rw [finiteCodeMatrix, dite_eq_left w.isLt]
  rfl

/-- The finite T code denotes the corresponding single-wire reflection gate matrix. -/
lemma finiteCodeMatrix_t (n : ℕ) (w : Fin n) :
    finiteCodeMatrix n (.t w) = reflectionGateMatrix (Sum.inl (w, tGate)) := by
  rw [finiteCodeMatrix, dite_eq_left w.isLt]
  rfl

/-- The finite adjoint T code denotes the corresponding single-wire reflection gate matrix. -/
lemma finiteCodeMatrix_tdg (n : ℕ) (w : Fin n) :
    finiteCodeMatrix n (.tdg w) = reflectionGateMatrix (Sum.inl (w, tGateAdj)) := by
  rw [finiteCodeMatrix, dite_eq_left w.isLt]
  rfl

/-- For distinct control and target wires, the finite controlled-X code denotes the
corresponding reflection gate matrix. -/
lemma finiteCodeMatrix_cx (n : ℕ) (c t : Fin n) (hct : c ≠ t) :
    finiteCodeMatrix n (.cx c t) = reflectionGateMatrix (Sum.inr (c, t)) := by
  have h1 : (↑c : ℕ) < n ∧ (↑t : ℕ) < n ∧ (↑c : ℕ) ≠ ↑t :=
    ⟨c.isLt, t.isLt, fun h => hct (Fin.ext h)⟩
  rw [finiteCodeMatrix, dite_eq_left h1]
  rfl

/-- For three distinct wires, the Toffoli code compiles to the circuit of local Toffoli steps. -/
lemma toffoliCode_circuit (n : ℕ) (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    finiteCodeCircuit n (toffoliCode n a b t) = reflectionCompile (toffoliLocalSteps a b t) := by
  simp only [finiteCodeCircuit, reflectionCompile, toffoliCode, toffoliLocalSteps, List.map,
    List.map_cons, List.cons.injEq]
  constructor
  · exact congrArg Step.gate (finiteCodeMatrix_h n t)
  constructor
  · exact congrArg Step.gate (finiteCodeMatrix_cx n b t hbt)
  constructor
  · exact congrArg Step.gate (finiteCodeMatrix_tdg n t)
  constructor
  · exact congrArg Step.gate (finiteCodeMatrix_cx n a t hat)
  constructor
  · exact congrArg Step.gate (finiteCodeMatrix_t n t)
  constructor
  · exact congrArg Step.gate (finiteCodeMatrix_cx n b t hbt)
  constructor
  · exact congrArg Step.gate (finiteCodeMatrix_tdg n t)
  constructor
  · exact congrArg Step.gate (finiteCodeMatrix_cx n a t hat)
  constructor
  · exact congrArg Step.gate (finiteCodeMatrix_t n b)
  constructor
  · exact congrArg Step.gate (finiteCodeMatrix_t n t)
  constructor
  · exact congrArg Step.gate (finiteCodeMatrix_h n t)
  constructor
  · exact congrArg Step.gate (finiteCodeMatrix_cx n a b hab)
  constructor
  · exact congrArg Step.gate (finiteCodeMatrix_t n a)
  constructor
  · exact congrArg Step.gate (finiteCodeMatrix_tdg n b)
  · exact ⟨congrArg Step.gate (finiteCodeMatrix_cx n a b hab), trivial⟩

/-- The Toffoli code is legal when its three wires are distinct. -/
lemma toffoliCode_legal (n : ℕ) (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    finiteWordLegal n (toffoliCode n a b t) = true := by
  have hab' : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Fin.ext h)
  have hat' : (a : ℕ) ≠ (t : ℕ) := fun h => hat (Fin.ext h)
  have hbt' : (b : ℕ) ≠ (t : ℕ) := fun h => hbt (Fin.ext h)
  simp [finiteWordLegal, finiteCodeLegal, toffoliCode, hab', hat', hbt']

/-- On a basis state, the Toffoli code flips the target exactly when both distinct control wires
are true. -/
theorem toffoliCode_run (n : ℕ) (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (x : Reg n) :
    finiteWordRun n (toffoliCode n a b t) (Qatlib.Foundations.PureStateMath.Ket x)
      = some (Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ (x a && x b)))) := by
  have hleg : finiteWordLegal n (toffoliCode n a b t) = true :=
    toffoliCode_legal n a b t hab hat hbt
  unfold finiteWordRun
  rw [hleg, ite_eq_left rfl]
  congr 1
  rw [toffoliCode_circuit n a b t hab hat hbt]
  exact (local_toffoli_fifteen_exact n a b t hab hat hbt).2.2 x

/-- The Toffoli code contains exactly fifteen gates. -/
theorem toffoliCode_length (n : ℕ) (a b t : Fin n) : (toffoliCode n a b t).length = 15 := rfl

abbrev ToffoliSpec (n : ℕ) := Fin n × Fin n × Fin n

def toffoliProgram (n : ℕ) : List (ToffoliSpec n) → List FiniteGateCode
  | [] => []
  | s :: specs => toffoliCode n s.1 s.2.1 s.2.2 ++ toffoliProgram n specs

def applyToffoliSpec {n : ℕ} (x : Reg n) (s : ToffoliSpec n) : Reg n :=
  Function.update x s.2.2 (x s.2.2 ^^ (x s.1 && x s.2.1))

def applyToffoliProgram {n : ℕ} (specs : List (ToffoliSpec n)) (x : Reg n) : Reg n :=
  specs.foldl (fun acc s => applyToffoliSpec acc s) x

/-- A compiled Toffoli program contains fifteen gates per specification. -/
theorem toffoliProgram_length (n : ℕ) (specs : List (ToffoliSpec n)) :
    (toffoliProgram n specs).length = 15 * specs.length := by
  induction specs with
  | nil => rfl
  | cons s specs ih =>
      simp only [toffoliProgram, List.length_append, List.length_cons, toffoliCode_length, ih]
      ring

/-- Running a legal concatenation of finite gate words executes the first circuit and then the
second. -/
lemma finiteWordRun_append (n : ℕ) (gs hs : List FiniteGateCode) (ψ : QState (Reg n))
    (hgs : finiteWordLegal n (gs ++ hs) = true) :
    finiteWordRun n (gs ++ hs) ψ
      = some (Run (1 : Matrix (Reg n) (Reg n) ℂ) (finiteCodeCircuit n hs)
          (Run (1 : Matrix (Reg n) (Reg n) ℂ) (finiteCodeCircuit n gs) ψ)) := by
  unfold finiteWordRun
  rw [hgs, ite_eq_left rfl]
  congr 1
  simp only [finiteCodeCircuit, List.map_append, run_append]

/-- Concatenating two legal finite gate words yields a legal word. -/
lemma finiteWordLegal_append (n : ℕ) (gs hs : List FiniteGateCode)
    (h1 : finiteWordLegal n gs = true) (h2 : finiteWordLegal n hs = true) :
    finiteWordLegal n (gs ++ hs) = true := by
  unfold finiteWordLegal at *
  simp [List.all_append, h1, h2]

/-- A Toffoli program is legal if every specification uses three distinct wires. -/
theorem toffoliProgram_legal (n : ℕ) (specs : List (ToffoliSpec n))
    (h : ∀ (a b t), (a, b, t) ∈ specs → a ≠ b ∧ a ≠ t ∧ b ≠ t) :
    finiteWordLegal n (toffoliProgram n specs) = true := by
  induction specs with
  | nil => simp [toffoliProgram, finiteWordLegal]
  | cons s specs ih =>
      obtain ⟨a, b, t⟩ := s
      have hst : a ≠ b ∧ a ≠ t ∧ b ≠ t := h a b t (by simp)
      have hrest : ∀ (a' b' t'), (a', b', t') ∈ specs → a' ≠ b' ∧ a' ≠ t' ∧ b' ≠ t' :=
        fun a' b' t' hs' => h a' b' t' (by simp [hs'])
      have ihrest := ih hrest
      simp only [toffoliProgram]
      exact finiteWordLegal_append n _ _
        (toffoliCode_legal n a b t hst.1 hst.2.1 hst.2.2) ihrest

/-- A legal Toffoli program maps each basis state to the basis state given by
`applyToffoliProgram`. -/
theorem toffoliProgram_run (n : ℕ) (specs : List (ToffoliSpec n)) (x : Reg n)
    (h : ∀ (a b t), (a, b, t) ∈ specs → a ≠ b ∧ a ≠ t ∧ b ≠ t) :
    finiteWordRun n (toffoliProgram n specs) (Qatlib.Foundations.PureStateMath.Ket x)
      = some (Qatlib.Foundations.PureStateMath.Ket (applyToffoliProgram specs x)) := by
  induction specs generalizing x with
  | nil =>
      simp [toffoliProgram, applyToffoliProgram, finiteWordRun, finiteCodeCircuit, run_nil,
        finiteWordLegal]
  | cons s specs ih =>
      obtain ⟨a, b, t⟩ := s
      have hst : a ≠ b ∧ a ≠ t ∧ b ≠ t := h a b t (by simp)
      have hrest : ∀ (a' b' t'), (a', b', t') ∈ specs → a' ≠ b' ∧ a' ≠ t' ∧ b' ≠ t' :=
        fun a' b' t' hs' => h a' b' t' (by simp [hs'])
      have hleg : finiteWordLegal n (toffoliProgram n specs) = true :=
        toffoliProgram_legal n specs hrest
      have hcode : Run (1 : Matrix (Reg n) (Reg n) ℂ) (finiteCodeCircuit n (toffoliCode n a b t))
          (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (applyToffoliSpec x (a, b, t)) := by
        rw [toffoliCode_circuit n a b t hst.1 hst.2.1 hst.2.2]
        exact (local_toffoli_fifteen_exact n a b t hst.1 hst.2.1 hst.2.2).2.2 x
      simp only [toffoliProgram]
      rw [finiteWordRun_append n _ _ _
        (finiteWordLegal_append n _ _ (toffoliCode_legal n a b t hst.1 hst.2.1 hst.2.2) hleg)]
      rw [hcode]
      have hih := ih (applyToffoliSpec x (a, b, t)) hrest
      have hrest_run : Run (1 : Matrix (Reg n) (Reg n) ℂ)
          (finiteCodeCircuit n (toffoliProgram n specs)) (Qatlib.Foundations.PureStateMath.Ket (applyToffoliSpec x (a, b, t)))
          = Qatlib.Foundations.PureStateMath.Ket (applyToffoliProgram specs (applyToffoliSpec x (a, b, t))) := by
        rw [finiteWordRun, hleg, ite_eq_left rfl] at hih
        exact Option.some.inj hih
      rw [hrest_run]
      simp [applyToffoliProgram, List.foldl_cons]

inductive CodeBlock (n : ℕ) where
  | x (w : Fin n)
  | cx (c t : Fin n)
  | toffoli (a b t : Fin n)
  deriving Repr

def blockWord {n : ℕ} : CodeBlock n → List FiniteGateCode
  | .x w => [.x w]
  | .cx c t => [.cx c t]
  | .toffoli a b t => toffoliCode n a b t

def blockAct {n : ℕ} : CodeBlock n → Reg n → Reg n
  | .x w, x => Function.update x w (!x w)
  | .cx c t, x => Function.update x t (x t ^^ x c)
  | .toffoli a b t, x => Function.update x t (x t ^^ (x a && x b))

def BlockLegal {n : ℕ} : CodeBlock n → Prop
  | .x _ => True
  | .cx c t => (c : ℕ) ≠ (t : ℕ)
  | .toffoli a b t => (a : ℕ) ≠ (b : ℕ) ∧ (a : ℕ) ≠ (t : ℕ) ∧ (b : ℕ) ≠ (t : ℕ)

/-- The finite X code denotes the corresponding single-wire Pauli X matrix. -/
lemma finiteCodeMatrix_x (n : ℕ) (w : Fin n) :
    finiteCodeMatrix n (.x w) = reflectionGateMatrix (Sum.inl (w, PauliX)) := by
  rw [finiteCodeMatrix, dite_eq_left w.isLt]
  rfl

/-- A single-wire Pauli X gate flips that wire in a computational basis state. -/
lemma applyGate_wireGate_pauliX_ket (n : ℕ) (w : Fin n) (x : Reg n) :
    ApplyGate (wireGate n w PauliX) (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (Function.update x w (!x w)) := by
  rw [applyGate_wireGate_ket]
  by_cases h : x w = false
  · rw [h]
    simp [PauliX, permMatrix, Matrix.of_apply]
  · have h' : x w = true := Bool.eq_true_of_not_eq_false h
    rw [h']
    simp [PauliX, permMatrix, Matrix.of_apply]

/-- The word compiled from a legal code block is legal. -/
lemma blockWord_legal {n : ℕ} (b : CodeBlock n) (h : BlockLegal b) :
    finiteWordLegal n (blockWord b) = true := by
  cases b with
  | x w => simp [blockWord, finiteWordLegal, finiteCodeLegal, w.isLt]
  | cx c t =>
      have hne : (c : ℕ) ≠ (t : ℕ) := h
      simp [blockWord, finiteWordLegal, finiteCodeLegal, c.isLt, t.isLt, hne]
  | toffoli a b t =>
      have hab : a ≠ b := fun e => h.1 (congrArg Fin.val e)
      have hat : a ≠ t := fun e => h.2.1 (congrArg Fin.val e)
      have hbt : b ≠ t := fun e => h.2.2 (congrArg Fin.val e)
      simp only [blockWord]
      exact toffoliCode_legal n a b t hab hat hbt

/-- Running the word of a legal block on a basis state implements `blockAct`. -/
theorem blockWord_run {n : ℕ} (b : CodeBlock n) (x : Reg n) (h : BlockLegal b) :
    finiteWordRun n (blockWord b) (Qatlib.Foundations.PureStateMath.Ket x) = some (Qatlib.Foundations.PureStateMath.Ket (blockAct b x)) := by
  cases b with
  | x w =>
      have hleg : finiteWordLegal n (blockWord (.x w)) = true := blockWord_legal _ trivial
      unfold finiteWordRun
      rw [hleg, ite_eq_left rfl]
      congr 1
      simp only [blockWord, blockAct, finiteCodeCircuit, List.map_cons, List.map_nil]
      rw [run_gate, run_nil, finiteCodeMatrix_x n w]
      exact applyGate_wireGate_pauliX_ket n w x
  | cx c t =>
      have hleg : finiteWordLegal n (blockWord (.cx c t)) = true := blockWord_legal _ h
      unfold finiteWordRun
      rw [hleg, ite_eq_left rfl]
      congr 1
      simp only [blockWord, blockAct, finiteCodeCircuit, List.map_cons, List.map_nil]
      rw [run_gate, run_nil]
      have hct : c ≠ t := fun e => h (congrArg Fin.val e)
      rw [finiteCodeMatrix, dite_eq_left ⟨c.isLt, t.isLt, fun h' => hct (Fin.ext h')⟩]
      exact applyGate_cnotGate_ket n c t hct x
  | toffoli a b t =>
      have hleg : finiteWordLegal n (blockWord (.toffoli a b t)) = true := blockWord_legal _ h
      unfold finiteWordRun
      rw [hleg, ite_eq_left rfl]
      congr 1
      simp only [blockWord, blockAct]
      have hab : a ≠ b := fun e => h.1 (congrArg Fin.val e)
      have hat : a ≠ t := fun e => h.2.1 (congrArg Fin.val e)
      have hbt : b ≠ t := fun e => h.2.2 (congrArg Fin.val e)
      rw [toffoliCode_circuit n a b t hab hat hbt]
      exact (local_toffoli_fifteen_exact n a b t hab hat hbt).2.2 x

/-- Compiling concatenated finite gate words concatenates their compiled circuits. -/
lemma finiteCodeCircuit_append (n : ℕ) (gs hs : List FiniteGateCode) :
    finiteCodeCircuit n (gs ++ hs) = finiteCodeCircuit n gs ++ finiteCodeCircuit n hs := by
  simp [finiteCodeCircuit, List.map_append]

def blocksAct {n : ℕ} : List (CodeBlock n) → Reg n → Reg n
  | [], x => x
  | b :: bs, x => blocksAct bs (blockAct b x)

/-- Flattening the words of legal blocks gives a legal finite gate word. -/
lemma blocks_legal {n : ℕ} (bs : List (CodeBlock n)) (h : ∀ b ∈ bs, BlockLegal b) :
    finiteWordLegal n (bs.flatMap blockWord) = true := by
  induction bs with
  | nil => simp [finiteWordLegal]
  | cons b bs ih =>
      have hb : BlockLegal b := h b (by simp)
      have hrest : ∀ b' ∈ bs, BlockLegal b' := fun b' hb' => h b' (by simp [hb'])
      simp only [List.flatMap_cons]
      exact finiteWordLegal_append n _ _ (blockWord_legal b hb) (ih hrest)

/-- Running a list of legal blocks on a basis state implements `blocksAct`. -/
theorem blocks_run {n : ℕ} (bs : List (CodeBlock n)) (h : ∀ b ∈ bs, BlockLegal b) (x : Reg n) :
    finiteWordRun n (bs.flatMap blockWord) (Qatlib.Foundations.PureStateMath.Ket x) = some (Qatlib.Foundations.PureStateMath.Ket (blocksAct bs x)) := by
  induction bs generalizing x with
  | nil =>
      simp [blocksAct, finiteWordRun, finiteWordLegal, finiteCodeCircuit]
  | cons b bs ih =>
      have hb : BlockLegal b := h b (by simp)
      have hrest : ∀ b' ∈ bs, BlockLegal b' := fun b' hb' => h b' (by simp [hb'])
      have hleg : finiteWordLegal n (List.flatMap blockWord (b :: bs)) = true :=
        blocks_legal (b :: bs) (fun b' hb' => h b' hb')
      unfold finiteWordRun
      rw [hleg, ite_eq_left rfl]
      congr 1
      simp only [List.flatMap_cons]
      rw [finiteCodeCircuit_append, run_append]
      have hfirst : Run (1 : Matrix (Reg n) (Reg n) ℂ) (finiteCodeCircuit n (blockWord b)) (Qatlib.Foundations.PureStateMath.Ket x)
          = Qatlib.Foundations.PureStateMath.Ket (blockAct b x) := by
        have hrun := blockWord_run b x hb
        rw [finiteWordRun, ite_eq_left (blockWord_legal b hb)] at hrun
        exact Option.some.inj hrun
      rw [hfirst]
      have hih := ih hrest (blockAct b x)
      rw [finiteWordRun, ite_eq_left (blocks_legal bs hrest)] at hih
      have hrest_run : Run (1 : Matrix (Reg n) (Reg n) ℂ)
          (finiteCodeCircuit n (List.flatMap blockWord bs)) (Qatlib.Foundations.PureStateMath.Ket (blockAct b x))
          = Qatlib.Foundations.PureStateMath.Ket (blocksAct bs (blockAct b x)) := Option.some.inj hih
      rw [hrest_run]
      rfl

def binaryEnc (a : ℕ) (x : Fin (2 ^ a)) : Reg a := fun i => x.val.testBit i.val

/-- Binary encoding is injective for positive bit width. -/
lemma binaryEnc_injective {a : ℕ} (ha : 0 < a) : Function.Injective (binaryEnc a) := by
  intro x y hxy
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < a
  · exact congrFun hxy ⟨i, hi⟩
  · have hp : 2 ^ a ≤ 2 ^ i := Nat.pow_le_pow_of_le (by decide) (by omega)
    have hx : x.val < 2 ^ i := lt_of_lt_of_le x.isLt hp
    have hy : y.val < 2 ^ i := lt_of_lt_of_le y.isLt hp
    rw [Nat.testBit_eq_false_of_lt hx, Nat.testBit_eq_false_of_lt hy]

/-- The top bit of a positive-width binary vertex is true exactly when the vertex lies in the
upper half. -/
lemma testBit_top_iff {a : ℕ} (ha : 0 < a) (x : Fin (2 ^ a)) :
    x.val.testBit (a - 1) = decide (bipartiteHalf a ≤ x.val) := by
  by_cases h : bipartiteHalf a ≤ x.val
  · have hp : 2 ^ a = 2 ^ (a - 1 + 1) := by congr 1; omega
    have h2 : x.val < 2 ^ (a - 1 + 1) := by rw [← hp]; exact x.isLt
    have htb : x.val.testBit (a - 1) = true :=
      Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h h2
    simp [h, htb]
  · have h2 : x.val < 2 ^ (a - 1) := by
      simpa [bipartiteHalf] using! h
    have htb : x.val.testBit (a - 1) = false := Nat.testBit_lt_two_pow h2
    simp [h, htb]

def bipartiteNeighbor {a : ℕ} (ha : 0 < a) (x : Fin (2 ^ a)) (k : Fin (2 ^ (a - 1))) :
    Fin (2 ^ a) :=
  if h : x.val < bipartiteHalf a then
    ⟨k.val + bipartiteHalf a, by
      have hk : k.val < 2 ^ (a - 1) := k.isLt
      have h4 : 2 ^ (a - 1) + 2 ^ (a - 1) = 2 ^ a := by
        have h5 : 2 ^ (a - 1) + 2 ^ (a - 1) = 2 ^ (a - 1) * 2 := by rw [Nat.mul_two]
        have h6 : 2 ^ (a - 1) * 2 = 2 ^ a := by
          have h7 : 2 ^ a = 2 ^ (a - 1 + 1) := by congr 1; omega
          rw [h7, Nat.pow_succ]
        rw [h5, h6]
      have h3 : k.val + 2 ^ (a - 1) < 2 ^ (a - 1) + 2 ^ (a - 1) := Nat.add_lt_add_right hk _
      rw [h4] at h3
      exact h3⟩
  else
    ⟨k.val, by
      have hk : k.val < 2 ^ (a - 1) := k.isLt
      have hp : 2 ^ (a - 1) ≤ 2 ^ a := Nat.pow_le_pow_of_le (by decide) (by omega)
      exact lt_of_lt_of_le hk hp⟩

/-- The top bit of a bipartite neighbor is the negation of the source vertex's top bit. -/
lemma bipartiteNeighbor_top {a : ℕ} (ha : 0 < a) (x : Fin (2 ^ a))
    (k : Fin (2 ^ (a - 1))) :
    (bipartiteNeighbor ha x k).val.testBit (a - 1) = !(x.val.testBit (a - 1)) := by
  by_cases hx : x.val < bipartiteHalf a
  · rw [bipartiteNeighbor, dite_eq_left hx]
    simp only [bipartiteHalf]
    have hk2 : k.val < 2 ^ (a - 1) := k.isLt
    have htop : k.val.testBit (a - 1) = false := Nat.testBit_lt_two_pow hk2
    rw [show k.val + 2 ^ (a - 1) = 2 ^ (a - 1) + k.val by omega]
    rw [Nat.testBit_two_pow_add_eq k.val (a - 1), htop]
    rw [testBit_top_iff ha x]
    simp [hx]
  · rw [bipartiteNeighbor, dite_eq_right hx]
    have hk2 : k.val < 2 ^ (a - 1) := k.isLt
    have htop : k.val.testBit (a - 1) = false := Nat.testBit_lt_two_pow hk2
    rw [htop]
    have hle : bipartiteHalf a ≤ x.val := le_of_not_gt hx
    rw [testBit_top_iff ha x]
    simp [hle]

/-- The lower bits of a bipartite neighbor are the corresponding bits of its neighbor index. -/
lemma bipartiteNeighbor_low {a : ℕ} (ha : 0 < a) (x : Fin (2 ^ a))
    (k : Fin (2 ^ (a - 1))) (i : Fin a) (hi : i.val < a - 1) :
    (bipartiteNeighbor ha x k).val.testBit i.val = k.val.testBit i.val := by
  by_cases hx : x.val < bipartiteHalf a
  · rw [bipartiteNeighbor, dite_eq_left hx]
    simp only [bipartiteHalf]
    have h1 : (2 ^ (a - 1) + k.val).testBit i.val = k.val.testBit i.val :=
      Nat.testBit_two_pow_add_gt (by omega) k.val
    rw [show k.val + 2 ^ (a - 1) = 2 ^ (a - 1) + k.val by omega, h1]
  · rw [bipartiteNeighbor, dite_eq_right hx]

section RecordLayout

variable {w a b : ℕ}

/-- Padding a register to its own width leaves it unchanged. -/
lemma regPad_self (w : ℕ) (r : Reg w) : regPadLocal w w r = r := by
  funext i
  unfold regPadLocal
  rw [dite_eq_left i.isLt]

/-- Below the original width, a padded register agrees with the original register. -/
lemma regPad_lt (w a : ℕ) (r : Reg a) {i : Fin w} (hi : i.val < a) :
    regPadLocal w a r i = r ⟨i.val, hi⟩ := by
  unfold regPadLocal
  rw [dite_eq_left hi]

/-- At or above the original width, a padded register is false. -/
lemma regPad_ge (w a : ℕ) (r : Reg a) {i : Fin w} (hi : a ≤ i.val) :
    regPadLocal w a r i = false := by
  unfold regPadLocal
  rw [dite_eq_right (by omega)]

/-- In the first segment, register concatenation reads the first register. -/
lemma regCat_apply_lt {r : Reg a} {s : Reg b} {i : Fin (a + b)} (hi : i.val < a) :
    regCatLocal r s i = r ⟨i.val, hi⟩ := by
  calc
    regCatLocal r s i = regCatLocal r s (Fin.castAdd b ⟨i.val, hi⟩) := by
      congr 1
    _ = (finSumFinEquiv.symm (Fin.castAdd b ⟨i.val, hi⟩)).elim r s := rfl
    _ = (Sum.inl ⟨i.val, hi⟩).elim r s := by
      rw [finSumFinEquiv_symm_apply_castAdd]
    _ = r ⟨i.val, hi⟩ := rfl

/-- In the second segment, register concatenation reads the second register at the shifted
index. -/
lemma regCat_apply_ge {r : Reg a} {s : Reg b} {i : Fin (a + b)} (hi : a ≤ i.val) :
    regCatLocal r s i = s ⟨i.val - a, by omega⟩ := by
  calc
    regCatLocal r s i = regCatLocal r s (Fin.natAdd a ⟨i.val - a, by omega⟩) := by
      congr 1
      apply Fin.ext
      rw [Fin.natAdd_mk]
      have heq : a + (i.val - a) = i.val := by rw [Nat.add_comm, Nat.sub_add_cancel hi]
      exact heq.symm
    _ = (finSumFinEquiv.symm (Fin.natAdd a ⟨i.val - a, by omega⟩)).elim r s := rfl
    _ = (Sum.inr ⟨i.val - a, by omega⟩).elim r s := by
      rw [finSumFinEquiv_symm_apply_natAdd]
    _ = s ⟨i.val - a, by omega⟩ := rfl

/-- A second-segment concatenation entry equals the second register entry at any index with the
required shifted value. -/
lemma regCat_apply_ge' {r : Reg a} {s : Reg b} {i : Fin (a + b)} {j : Fin b}
    (hj : j.val = i.val - a) (hi : a ≤ i.val) :
    regCatLocal r s i = s j := by
  calc
    regCatLocal r s i = regCatLocal r s (Fin.natAdd a ⟨i.val - a, by omega⟩) := by
      congr 1
      apply Fin.ext
      rw [Fin.natAdd_mk]
      have heq : a + (i.val - a) = i.val := by rw [Nat.add_comm, Nat.sub_add_cancel hi]
      exact heq.symm
    _ = (finSumFinEquiv.symm (Fin.natAdd a ⟨i.val - a, by omega⟩)).elim r s := rfl
    _ = (Sum.inr ⟨i.val - a, by omega⟩).elim r s := by
      rw [finSumFinEquiv_symm_apply_natAdd]
    _ = s ⟨i.val - a, by omega⟩ := rfl
    _ = s j := by
      congr 1
      apply Fin.ext
      exact hj.symm

/-- The first segment of concatenated binary encodings reads the bits of the first vertex. -/
lemma regCat_binaryEnc_lt (a : ℕ) (x y : Fin (2 ^ a)) {i : Fin (a + a)} (hi : i.val < a) :
    regCatLocal (binaryEnc a x) (binaryEnc a y) i = x.val.testBit i.val := by
  rw [regCat_apply_lt hi]
  rfl

/-- The second segment of concatenated binary encodings reads the shifted bits of the second
vertex. -/
lemma regCat_binaryEnc_ge (a : ℕ) (x y : Fin (2 ^ a)) {i : Fin (a + a)} (hi : a ≤ i.val) :
    regCatLocal (binaryEnc a x) (binaryEnc a y) i = y.val.testBit (i.val - a) := by
  rw [regCat_apply_ge hi]
  rfl

/-- Updating the same register wire twice keeps only the second update when the new values
differ. -/
lemma update_update_ne (f : Reg w) (t : Fin w) (v v' : Bool) (h : v' ≠ v) :
    Function.update (Function.update f t v) t v' = Function.update f t v' := by
  funext i
  by_cases hit : i = t
  · subst hit
    rw [Function.update_self, Function.update_self]
  · simp only [Function.update_of_ne hit]

/-- A controlled-X block followed by X on its target replaces the target by the negated XOR of
target and control. -/
lemma blocksAct_cx_x (n : ℕ) (c t : Fin n) (r : Reg n) :
    blocksAct [.cx c t, .x t] r = Function.update r t (! (r t ^^ r c)) := by
  have hstep : Function.update r t (r t ^^ r c) t = (r t ^^ r c) :=
    Function.update_self t (r t ^^ r c) r
  have hne : (!(r t ^^ r c) : Bool) ≠ (r t ^^ r c) := by
    cases hx : (r t ^^ r c) <;> simp
  simp only [blocksAct, blockAct]
  rw [hstep, update_update_ne r t (r t ^^ r c) (! (r t ^^ r c)) hne]

end RecordLayout

section BipartiteProgram

variable {a : ℕ}

def bipartiteMarked (a : ℕ) (x : Fin (2 ^ a)) : Bool := x.val.testBit 0

def rowAddrWire (a : ℕ) (ha : 0 < a) : Fin (a + a) := ⟨a - 1, by omega⟩

def rowDataWire (a : ℕ) (ha : 0 < a) : Fin (a + a) := ⟨a + (a - 1), by omega⟩

def checkFlagWire (a : ℕ) (ha : 0 < a) : Fin (a + a) := ⟨a, by omega⟩

/-- The row address wire has index one less than `a`. -/
lemma rowAddrWire_val (a : ℕ) (ha : 0 < a) : (rowAddrWire a ha).val = a - 1 := rfl

/-- The row data wire has index `a` plus one less than `a`. -/
lemma rowDataWire_val (a : ℕ) (ha : 0 < a) : (rowDataWire a ha).val = a + (a - 1) := rfl

/-- The check flag wire has index `a`. -/
lemma checkFlagWire_val (a : ℕ) (ha : 0 < a) : (checkFlagWire a ha).val = a := rfl

/-- Concatenated binary encodings consist of the first vertex's bits followed by the second
vertex's bits. -/
lemma regCat_binaryEnc_layout (a : ℕ) (x y : Fin (2 ^ a)) (i : Fin (a + a)) :
    regCatLocal (binaryEnc a x) (binaryEnc a y) i
      = if i.val < a then x.val.testBit i.val else y.val.testBit (i.val - a) := by
  by_cases hi : i.val < a
  · rw [regCat_binaryEnc_lt (a := a) (x := x) (y := y) (hi := hi), ite_eq_left hi]
  · have hge : a ≤ i.val := by omega
    rw [regCat_binaryEnc_ge (a := a) (x := x) (y := y) (hi := hge), ite_eq_right hi]

/-- The padded check layout contains the vertex bits, the flag bit, and then false bits. -/
lemma regPad_checkLayout (a : ℕ) (ha : 0 < a) (x : Fin (2 ^ a)) (s : Reg 1)
    (i : Fin (a + a)) :
    regPadLocal (a + a) (a + 1) (regCatLocal (binaryEnc a x) s) i
      = if i.val < a then x.val.testBit i.val
        else if i.val = a then s ⟨0, by omega⟩
        else false := by
  unfold regPadLocal
  by_cases hlt : i.val < a + 1
  · rw [dite_eq_left hlt]
    by_cases h1 : i.val < a
    · rw [regCat_apply_lt (i := ⟨i.val, hlt⟩) (hi := h1), ite_eq_left h1]
      rfl
    · have hge : a ≤ i.val := by omega
      by_cases h2 : i.val = a
      · have hge' := regCat_apply_ge' (r := binaryEnc a x) (s := s) (i := ⟨i.val, hlt⟩)
          (j := ⟨0, by decide⟩) (hj := by omega) (hi := hge)
        rw [hge']
        rw [ite_eq_right h1, ite_eq_left h2]
      · exfalso
        omega
  · rw [dite_eq_right hlt]
    rw [ite_eq_right (by omega : ¬ (i.val < a)), ite_eq_right (by omega : ¬ (i.val = a))]

/-- The row address wire reads the top bit of the first encoded vertex. -/
lemma regCat_binaryEnc_addrTop (a : ℕ) (ha : 0 < a) (x y : Fin (2 ^ a)) :
    regCatLocal (binaryEnc a x) (binaryEnc a y) (rowAddrWire a ha) = x.val.testBit (a - 1) := by
  rw [regCat_binaryEnc_layout, rowAddrWire_val]
  rw [ite_eq_left (by omega)]

/-- The row data wire reads the top bit of the second encoded vertex. -/
lemma regCat_binaryEnc_dataTop (a : ℕ) (ha : 0 < a) (x y : Fin (2 ^ a)) :
    regCatLocal (binaryEnc a x) (binaryEnc a y) (rowDataWire a ha) = y.val.testBit (a - 1) := by
  rw [regCat_binaryEnc_layout, rowDataWire_val]
  rw [ite_eq_right (by omega)]
  rw [Nat.add_sub_cancel_left]

def bipartiteRowBlocks (a : ℕ) (ha : 0 < a) : List (CodeBlock (a + a)) :=
  [.cx (rowAddrWire a ha) (rowDataWire a ha), .x (rowDataWire a ha)]

/-- Every block in the bipartite row program is legal. -/
lemma bipartiteRowBlocks_legal (a : ℕ) (ha : 0 < a) :
    ∀ b ∈ bipartiteRowBlocks a ha, BlockLegal b := by
  intro b hb
  rw [bipartiteRowBlocks] at hb
  rcases List.mem_cons.mp hb with h | h
  · subst h
    show (a - 1 : ℕ) ≠ a + (a - 1)
    omega
  · have h' : b = CodeBlock.x (rowDataWire a ha) := List.mem_singleton.mp h
    subst h'
    trivial

/-- The bipartite row blocks replace the top data bit by the negated XOR of the top data and
address bits. -/
lemma bipartiteRowBlocks_act (a : ℕ) (ha : 0 < a) (r : Reg (a + a)) :
    blocksAct (bipartiteRowBlocks a ha) r
      = Function.update r (rowDataWire a ha)
          (! (r (rowDataWire a ha) ^^ r (rowAddrWire a ha))) := by
  rw [bipartiteRowBlocks]
  exact blocksAct_cx_x (a + a) (rowAddrWire a ha) (rowDataWire a ha) r

/-- The bipartite row word preserves the encoded source and replaces a valid encoded index with
its encoded neighbor. -/
theorem bipartiteRow_run (a : ℕ) (ha : 0 < a) (x : Fin (2 ^ a)) (k : Fin (2 ^ a))
    (hk : k.val < 2 ^ (a - 1)) :
    finiteWordRun (a + a) ((bipartiteRowBlocks a ha).flatMap blockWord)
        (Qatlib.Foundations.PureStateMath.Ket (regPadLocal (a + a) (a + a) (regCatLocal (binaryEnc a x) (binaryEnc a k))))
      = some (Qatlib.Foundations.PureStateMath.Ket (regPadLocal (a + a) (a + a)
          (regCatLocal (binaryEnc a x) (binaryEnc a (bipartiteNeighbor ha x ⟨k.val, hk⟩))))) := by
  have hleg := blocks_run (bipartiteRowBlocks a ha) (bipartiteRowBlocks_legal a ha)
    (regCatLocal (binaryEnc a x) (binaryEnc a k))
  have hrt : regCatLocal (binaryEnc a x) (binaryEnc a k) (rowDataWire a ha) = false := by
    rw [regCat_binaryEnc_dataTop a ha x k]
    exact Nat.testBit_lt_two_pow hk
  have hrc : regCatLocal (binaryEnc a x) (binaryEnc a k) (rowAddrWire a ha)
      = x.val.testBit (a - 1) := regCat_binaryEnc_addrTop a ha x k
  have hout : regCatLocal (binaryEnc a x) (binaryEnc a (bipartiteNeighbor ha x ⟨k.val, hk⟩))
      = Function.update (regCatLocal (binaryEnc a x) (binaryEnc a k)) (rowDataWire a ha)
          (! (x.val.testBit (a - 1))) := by
    funext i
    rw [Function.update_apply]
    by_cases hit : i = rowDataWire a ha
    · subst hit
      rw [ite_eq_left rfl]
      rw [regCat_binaryEnc_dataTop a ha x (bipartiteNeighbor ha x ⟨k.val, hk⟩)]
      exact bipartiteNeighbor_top ha x ⟨k.val, hk⟩
    · rw [ite_eq_right hit]
      have hne : i.val ≠ (rowDataWire a ha).val := fun h => hit (Fin.ext h)
      by_cases hia : i.val < a
      · rw [regCat_binaryEnc_lt (a := a) (x := x)
          (y := bipartiteNeighbor ha x ⟨k.val, hk⟩) (hi := hia),
          regCat_binaryEnc_lt (a := a) (x := x) (y := k) (hi := hia)]
      · have hge : a ≤ i.val := by omega
        have hlt : i.val - a < a - 1 := by
          rw [rowDataWire_val] at hne
          omega
        rw [regCat_binaryEnc_ge (a := a) (x := x)
            (y := bipartiteNeighbor ha x ⟨k.val, hk⟩) (hi := hge),
          regCat_binaryEnc_ge (a := a) (x := x) (y := k) (hi := hge)]
        exact bipartiteNeighbor_low ha x ⟨k.val, hk⟩ ⟨i.val - a, by omega⟩ (by omega)
  simp only [regPad_self]
  rw [hleg, hout, bipartiteRowBlocks_act, hrt, hrc]
  simp only [Bool.false_xor]

def bipartiteCheckBlocks (a : ℕ) (ha : 0 < a) : List (CodeBlock (a + a)) :=
  [.cx ⟨0, by omega⟩ (checkFlagWire a ha)]

/-- Every block in the bipartite checking program is legal. -/
lemma bipartiteCheckBlocks_legal (a : ℕ) (ha : 0 < a) :
    ∀ b ∈ bipartiteCheckBlocks a ha, BlockLegal b := by
  intro b hb
  rw [bipartiteCheckBlocks] at hb
  have h' : b = CodeBlock.cx ⟨0, by omega⟩ (checkFlagWire a ha) := by
    rcases List.mem_cons.mp hb with h | h
    · exact h
    · simp at h
  subst h'
  show (0 : ℕ) ≠ a
  omega

/-- The bipartite checking blocks XOR wire zero into the check flag. -/
lemma bipartiteCheckBlocks_act (a : ℕ) (ha : 0 < a) (r : Reg (a + a)) :
    blocksAct (bipartiteCheckBlocks a ha) r
      = Function.update r (checkFlagWire a ha)
          (r (checkFlagWire a ha) ^^ r ⟨0, by omega⟩) := by
  rw [bipartiteCheckBlocks, blocksAct, blockAct]
  rfl

/-- Starting with a false flag, the bipartite checking word computes `bipartiteMarked` while
preserving the source register. -/
theorem bipartiteCheck_run (a : ℕ) (ha : 0 < a) (x : Fin (2 ^ a)) :
    finiteWordRun (a + a) ((bipartiteCheckBlocks a ha).flatMap blockWord)
        (Qatlib.Foundations.PureStateMath.Ket (regPadLocal (a + a) (a + 1) (regCatLocal (binaryEnc a x) (fun _ => false))))
      = some (Qatlib.Foundations.PureStateMath.Ket (regPadLocal (a + a) (a + 1)
          (regCatLocal (binaryEnc a x) (fun _ => bipartiteMarked a x)))) := by
  have hleg := blocks_run (bipartiteCheckBlocks a ha) (bipartiteCheckBlocks_legal a ha)
    (regPadLocal (a + a) (a + 1) (regCatLocal (binaryEnc a x) (fun _ => false)))
  have hflagIn : regPadLocal (a + a) (a + 1) (regCatLocal (binaryEnc a x) (fun _ => false))
      (checkFlagWire a ha) = false := by
    rw [regPad_checkLayout a ha x (fun _ => false) (checkFlagWire a ha), checkFlagWire_val]
    rw [ite_eq_right (by omega), ite_eq_left rfl]
  have hlowIn : regPadLocal (a + a) (a + 1) (regCatLocal (binaryEnc a x) (fun _ => false))
      ⟨0, by omega⟩ = x.val.testBit 0 := by
    rw [regPad_checkLayout a ha x (fun _ => false) ⟨0, by omega⟩]
    rw [show (⟨0, by omega⟩ : Fin (a + a)).val = 0 by rfl]
    rw [ite_eq_left (by omega)]
  have hout : regPadLocal (a + a) (a + 1) (regCatLocal (binaryEnc a x) (fun _ => bipartiteMarked a x))
      = Function.update (regPadLocal (a + a) (a + 1) (regCatLocal (binaryEnc a x) (fun _ => false)))
          (checkFlagWire a ha) (bipartiteMarked a x) := by
    funext i
    rw [Function.update_apply]
    by_cases hit : i = checkFlagWire a ha
    · subst hit
      rw [ite_eq_left rfl]
      rw [regPad_checkLayout a ha x (fun _ => bipartiteMarked a x) (checkFlagWire a ha),
        checkFlagWire_val]
      rw [ite_eq_right (by omega), ite_eq_left rfl]
    · rw [ite_eq_right hit]
      by_cases h1 : i.val < a
      · rw [regPad_checkLayout a ha x (fun _ => bipartiteMarked a x) i,
            regPad_checkLayout a ha x (fun _ => false) i]
        rw [ite_eq_left h1, ite_eq_left h1]
      · by_cases h2 : i.val = a
        · have hcontra : i = checkFlagWire a ha := by
            apply Fin.ext
            rw [checkFlagWire_val]
            exact h2
          exact (hit hcontra).elim
        · rw [regPad_checkLayout a ha x (fun _ => bipartiteMarked a x) i,
              regPad_checkLayout a ha x (fun _ => false) i]
          rw [ite_eq_right h1, ite_eq_right h1, ite_eq_right h2, ite_eq_right h2]
  rw [hleg, hout, bipartiteCheckBlocks_act, hflagIn, hlowIn]
  simp only [Bool.false_xor, bipartiteMarked]

/-- The bipartite row word contains exactly two gates. -/
lemma bipartiteRowWord_length (a : ℕ) (ha : 0 < a) :
    ((bipartiteRowBlocks a ha).flatMap blockWord).length = 2 := by
  rw [bipartiteRowBlocks]
  simp [blockWord]

/-- The bipartite checking word contains exactly one gate. -/
lemma bipartiteCheckWord_length (a : ℕ) (ha : 0 < a) :
    ((bipartiteCheckBlocks a ha).flatMap blockWord).length = 1 := by
  rw [bipartiteCheckBlocks]
  simp [blockWord]

def EffectiveNeighborProgram (n d : ℕ) (hdn : d ≤ n)
    (adj : Fin n → Fin n → Bool) (M : Fin n → Bool)
    (nbr : Fin n → Fin d → Fin n) : Prop :=
  ∃ (a w gateRow gateCheck spaceBits : ℕ) (enc : Fin n → Reg a)
      (rowWord checkWord : List FiniteGateCode),
    Function.Injective enc ∧
      0 < a ∧ 2 * a ≤ w ∧ a + 1 ≤ w ∧
      finiteWordLegal w rowWord = true ∧
      finiteWordLegal w checkWord = true ∧
      (∀ x : Fin n, ∀ k : Fin d,
        finiteWordRun w rowWord
            (Qatlib.Foundations.PureStateMath.Ket (regPadLocal w (a + a) (regCatLocal (enc x) (enc (Fin.castLE hdn k))))) =
          some (Qatlib.Foundations.PureStateMath.Ket (regPadLocal w (a + a) (regCatLocal (enc x) (enc (nbr x k)))))) ∧
      (∀ x : Fin n,
        finiteWordRun w checkWord
            (Qatlib.Foundations.PureStateMath.Ket (regPadLocal w (a + 1) (regCatLocal (enc x) (fun _ => false)))) =
          some (Qatlib.Foundations.PureStateMath.Ket (regPadLocal w (a + 1) (regCatLocal (enc x) (fun _ => M x))))) ∧
      (∀ x : Fin n, ∀ k : Fin d, adj x (nbr x k) = true) ∧
      (∀ x : Fin n, ∀ k : Fin d, nbr x k ≠ x) ∧
      (∀ x : Fin n, Function.Injective (nbr x)) ∧
      (∀ x y : Fin n, adj x y = true → ∃ k : Fin d, nbr x k = y) ∧
      rowWord.length ≤ gateRow ∧
      checkWord.length ≤ gateCheck ∧
      w ≤ spaceBits ∧
      (∃ x y : Fin n, M x ≠ M y)

/-- A vertex in the lower half has a false top bit. -/
lemma testBit_top_zero (a : ℕ) (ha : 0 < a) (x : Fin (2 ^ a)) (hx : x.val < bipartiteHalf a) :
    x.val.testBit (a - 1) = false := by
  have hnotle : ¬ (bipartiteHalf a ≤ x.val) := fun h => absurd hx (Nat.not_lt_of_ge h)
  have h1 := testBit_top_iff ha x
  rw [decide_eq_false_iff_not.mpr hnotle] at h1
  exact h1

/-- A vertex in the upper half has a true top bit. -/
lemma testBit_top_one (a : ℕ) (ha : 0 < a) (x : Fin (2 ^ a)) (hx : bipartiteHalf a ≤ x.val) :
    x.val.testBit (a - 1) = true := by
  have h1 := testBit_top_iff ha x
  rw [decide_eq_true_eq.mpr hx] at h1
  exact h1

/-- Every vertex produced by `bipartiteNeighbor` satisfies the Boolean bipartite adjacency test. -/
lemma bipartiteAdj_neighbor (a : ℕ) (ha : 0 < a) (x : Fin (2 ^ a))
    (k : Fin (2 ^ (a - 1))) :
    bipartiteAdj a x (bipartiteNeighbor ha x k) = true := by
  have hnb : (bipartiteNeighbor ha x k).val.testBit (a - 1)
      = !(x.val.testBit (a - 1)) := bipartiteNeighbor_top ha x k
  by_cases hx : x.val < bipartiteHalf a
  · have hxbit : x.val.testBit (a - 1) = false := testBit_top_zero a ha x hx
    have hnbit : (bipartiteNeighbor ha x k).val.testBit (a - 1) = true := by
      have h1 := hnb
      rw [hxbit] at h1
      exact h1
    have h1 := testBit_top_iff ha (bipartiteNeighbor ha x k)
    rw [hnbit] at h1
    have hnge : bipartiteHalf a ≤ (bipartiteNeighbor ha x k).val :=
      decide_eq_true_eq.mp h1.symm
    have hnlt : ¬ ((bipartiteNeighbor ha x k).val < bipartiteHalf a) :=
      fun h => absurd h (Nat.not_lt_of_ge hnge)
    simp [bipartiteAdj, hx, hnlt]
  · have hge : bipartiteHalf a ≤ x.val := Nat.le_of_not_gt hx
    have hxbit : x.val.testBit (a - 1) = true := testBit_top_one a ha x hge
    have hnbit : (bipartiteNeighbor ha x k).val.testBit (a - 1) = false := by
      have h1 := hnb
      rw [hxbit] at h1
      exact h1
    have h1 := testBit_top_iff ha (bipartiteNeighbor ha x k)
    rw [hnbit] at h1
    have hnge : ¬ (bipartiteHalf a ≤ (bipartiteNeighbor ha x k).val) :=
      decide_eq_false_iff_not.mp h1.symm
    have hnlt : (bipartiteNeighbor ha x k).val < bipartiteHalf a :=
      Nat.lt_of_not_ge hnge
    simp [bipartiteAdj, hx, hnlt]

/-- For a lower-half source, a bipartite neighbor is the neighbor index plus the half size. -/
lemma bipartiteNeighbor_lower (a : ℕ) (ha : 0 < a) (x : Fin (2 ^ a))
    (k : Fin (2 ^ (a - 1))) (hx : x.val < bipartiteHalf a) :
    (bipartiteNeighbor ha x k).val = k.val + bipartiteHalf a := by
  rw [bipartiteNeighbor, dite_eq_left hx]

/-- For an upper-half source, a bipartite neighbor is the neighbor index itself. -/
lemma bipartiteNeighbor_upper (a : ℕ) (ha : 0 < a) (x : Fin (2 ^ a))
    (k : Fin (2 ^ (a - 1))) (hx : ¬ (x.val < bipartiteHalf a)) :
    (bipartiteNeighbor ha x k).val = k.val := by
  rw [bipartiteNeighbor, dite_eq_right hx]

/-- Every vertex satisfying the bipartite adjacency test is produced by a neighbor index. -/
lemma bipartiteNeighbor_exhaustive (a : ℕ) (ha : 0 < a) (x y : Fin (2 ^ a))
    (hadj : bipartiteAdj a x y = true) :
    ∃ k : Fin (2 ^ (a - 1)), bipartiteNeighbor ha x k = y := by
  have hhalf : bipartiteHalf a + bipartiteHalf a = 2 ^ a := by
    unfold bipartiteHalf
    have h5 : 2 ^ (a - 1) + 2 ^ (a - 1) = 2 ^ (a - 1) * 2 := by rw [Nat.mul_two]
    have h6 : 2 ^ (a - 1) * 2 = 2 ^ a := by
      have h7 : 2 ^ a = 2 ^ (a - 1 + 1) := by congr 1; omega
      rw [h7, Nat.pow_succ]
    rw [h5, h6]
  have hne : ¬ (x.val < bipartiteHalf a ↔ y.val < bipartiteHalf a) := by
    have h := decide_eq_true_eq.mp (by simpa [bipartiteAdj] using! hadj)
    exact h
  by_cases hx : x.val < bipartiteHalf a
  · have hy : bipartiteHalf a ≤ y.val := by
      by_contra hy'
      exact hne (Iff.intro (fun _ => Nat.lt_of_not_ge hy') (fun _ => hx))
    have hy' : y.val < 2 ^ a := y.isLt
    have hy'' : y.val < bipartiteHalf a + bipartiteHalf a := by
      rw [hhalf]
      exact hy'
    have hbound : y.val - bipartiteHalf a < 2 ^ (a - 1) := by
      have : y.val - bipartiteHalf a < bipartiteHalf a := by omega
      simpa [bipartiteHalf] using! this
    obtain ⟨k, hk⟩ : ∃ k : Fin (2 ^ (a - 1)), k.val = y.val - bipartiteHalf a :=
      ⟨⟨y.val - bipartiteHalf a, hbound⟩, rfl⟩
    refine ⟨k, ?_⟩
    have hv : (bipartiteNeighbor ha x k).val = y.val := by
      rw [bipartiteNeighbor_lower a ha x k hx]
      omega
    exact Fin.ext hv
  · have hy : y.val < bipartiteHalf a := by
      by_contra hy'
      exact hne (Iff.intro (fun h => (hx h).elim) (fun h => (hy' h).elim))
    have hbound : y.val < 2 ^ (a - 1) := by simpa [bipartiteHalf] using! hy
    obtain ⟨k, hk⟩ : ∃ k : Fin (2 ^ (a - 1)), k.val = y.val :=
      ⟨⟨y.val, hbound⟩, rfl⟩
    refine ⟨k, ?_⟩
    have hv : (bipartiteNeighbor ha x k).val = y.val := by
      rw [bipartiteNeighbor_upper a ha x k hx, hk]
    exact Fin.ext hv

/-- For positive width, the bipartite family admits an effective neighbor program. -/
theorem bipartite_effectiveNeighborProgram (a : ℕ) (ha : 0 < a) :
    EffectiveNeighborProgram (2 ^ a) (2 ^ (a - 1))
      (Nat.pow_le_pow_of_le (by decide) (by omega))
      (bipartiteAdj a) (bipartiteMarked a) (bipartiteNeighbor ha) := by
  have hdn : 2 ^ (a - 1) ≤ 2 ^ a := Nat.pow_le_pow_of_le (by decide) (by omega)
  have hrowlegal : finiteWordLegal (a + a) ((bipartiteRowBlocks a ha).flatMap blockWord) = true :=
    blocks_legal (bipartiteRowBlocks a ha) (bipartiteRowBlocks_legal a ha)
  have hchecklegal : finiteWordLegal (a + a) ((bipartiteCheckBlocks a ha).flatMap blockWord) = true :=
    blocks_legal (bipartiteCheckBlocks a ha) (bipartiteCheckBlocks_legal a ha)
  refine ⟨a, a + a, 2, 1, a + a, binaryEnc a,
    (bipartiteRowBlocks a ha).flatMap blockWord, (bipartiteCheckBlocks a ha).flatMap blockWord, ?_⟩
  refine ⟨binaryEnc_injective ha, ha, ?_, ?_, hrowlegal, hchecklegal, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro x k
    have hklt : (Fin.castLE hdn k).val < 2 ^ (a - 1) := k.isLt
    have hrun := bipartiteRow_run a ha x (Fin.castLE hdn k) hklt
    convert! hrun using 1
  · intro x
    have hrun := bipartiteCheck_run a ha x
    convert! hrun using 1
  · intro x k
    exact bipartiteAdj_neighbor a ha x k
  · intro x k hEq
    have h1 := bipartiteNeighbor_top ha x k
    have h2 := bipartiteNeighbor_top ha x k
    rw [hEq] at h2
    have hcontra : x.val.testBit (a - 1) ≠ !(x.val.testBit (a - 1)) := by
      intro h
      cases hx : x.val.testBit (a - 1) <;> simp [hx] at h
    exact hcontra h2
  · intro x k1 k2 hEq
    have hv := congrArg Fin.val hEq
    by_cases hx : x.val < bipartiteHalf a
    · have hv1 := bipartiteNeighbor_lower a ha x k1 hx
      have hv2 := bipartiteNeighbor_lower a ha x k2 hx
      rw [hv1, hv2] at hv
      omega
    · have hv1 := bipartiteNeighbor_upper a ha x k1 hx
      have hv2 := bipartiteNeighbor_upper a ha x k2 hx
      rw [hv1, hv2] at hv
      exact Fin.ext hv
  · intro x y hadj
    exact bipartiteNeighbor_exhaustive a ha x y hadj
  · rw [bipartiteRowWord_length a ha]
  · rw [bipartiteCheckWord_length a ha]
  · omega
  · have hlt1 : 1 < 2 ^ a := Nat.one_lt_two_pow (n := a) (by omega)
    refine ⟨⟨0, by positivity⟩, ⟨1, hlt1⟩, ?_⟩
    simp [bipartiteMarked]

end BipartiteProgram

section CoherentRowProgram

variable {a : ℕ}

def binSplitFn (j : ℕ) : Bool × Fin (2 ^ j) → Fin (2 ^ (j + 1))
  | ⟨false, k⟩ => ⟨k.val, by omega⟩
  | ⟨true, k⟩ => ⟨k.val + 2 ^ j, by
      have h4 : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [Nat.pow_succ]; ring
      omega⟩

/-- The binary splitting function adds the half-size offset exactly when its Boolean input is
true. -/
lemma binSplitFn_val (j : ℕ) (k : Fin (2 ^ j)) (b : Bool) :
    (binSplitFn j ⟨b, k⟩).val = k.val + (if b then 2 ^ j else 0) := by
  rcases b with _ | _ <;> simp [binSplitFn]

def binSplitEquiv (j : ℕ) : Bool × Fin (2 ^ j) ≃ Fin (2 ^ (j + 1)) :=
  Equiv.ofBijective (binSplitFn j) (by
    constructor
    · intro p q hp
      rcases p with ⟨b, k⟩
      rcases q with ⟨b', k'⟩
      have hpv := congrArg Fin.val hp
      rcases b with _ | _ <;> rcases b' with _ | _
      · simp only [binSplitFn] at hpv
        have hkk : k = k' := Fin.ext (by omega)
        subst hkk
        rfl
      · simp only [binSplitFn] at hpv
        have hk' : k'.val < 2 ^ j := k'.isLt
        omega
      · simp only [binSplitFn] at hpv
        have hk : k.val < 2 ^ j := k.isLt
        omega
      · simp only [binSplitFn] at hpv
        have hkk : k = k' := Fin.ext (by omega)
        subst hkk
        rfl
    · intro y
      by_cases hy : y.val < 2 ^ j
      · refine ⟨⟨false, ⟨y.val, hy⟩⟩, ?_⟩
        simp only [binSplitFn]
      · refine ⟨⟨true, ⟨y.val - 2 ^ j, by omega⟩⟩, ?_⟩
        simp only [binSplitFn]
        refine Fin.ext ?_
        simp only []
        exact Nat.sub_add_cancel (by omega))

/-- The binary splitting equivalence agrees with `binSplitFn` on every input. -/
lemma binSplitEquiv_apply (j : ℕ) (p : Bool × Fin (2 ^ j)) :
    binSplitEquiv j p = binSplitFn j p := rfl

/-- A sum over binary indices of successor width splits into sums over the lower and upper
halves. -/
lemma sum_binSplit {M : Type*} [AddCommMonoid M] (j : ℕ) (f : Fin (2 ^ (j + 1)) → M) :
    (∑ y : Fin (2 ^ (j + 1)), f y)
      = (∑ k : Fin (2 ^ j), f ⟨k.val, by omega⟩)
        + (∑ k : Fin (2 ^ j), f ⟨k.val + 2 ^ j, by omega⟩) := by
  have h := Fintype.sum_equiv (binSplitEquiv j).symm f
      (fun p : Bool × Fin (2 ^ j) => f (binSplitEquiv j p)) (fun _ => by simp)
  rw [h, Fintype.sum_prod_type]
  have hbool : (∑ b : Bool, (∑ k : Fin (2 ^ j), f (binSplitEquiv j ⟨b, k⟩)))
      = (∑ k : Fin (2 ^ j), f (binSplitEquiv j ⟨false, k⟩))
        + (∑ k : Fin (2 ^ j), f (binSplitEquiv j ⟨true, k⟩)) := by
    rw [Fintype.univ_bool, Finset.sum_insert (by simp), Finset.sum_singleton]
    simp only [add_comm]
  rw [hbool]
  simp only [binSplitEquiv_apply, binSplitFn]

/-- The bits of a split binary index are its lower index bits followed by the splitting Boolean. -/
lemma testBit_binSplit (j : ℕ) (k : Fin (2 ^ j)) (b : Bool) (i : ℕ) (hi : i ≤ j) :
    (binSplitFn j ⟨b, k⟩).val.testBit i
      = if i < j then k.val.testBit i else b := by
  rw [binSplitFn_val]
  by_cases hb : b = true
  · rw [ite_eq_left hb]
    have hk : k.val < 2 ^ j := k.isLt
    rw [show k.val + 2 ^ j = 2 ^ j * 1 + k.val by rw [Nat.mul_one, Nat.add_comm]]
    rw [Nat.testBit_two_pow_mul_add 1 hk i]
    rcases Nat.lt_or_ge i j with h | h
    · simp [h]
    · have hj : i = j := by omega
      subst hj
      simp [hb]
  · rw [ite_eq_right hb]
    have hk : k.val < 2 ^ j := k.isLt
    rcases Nat.lt_or_ge i j with h | h
    · simp [h]
    · have hj : i = j := by omega
      subst hj
      rw [Nat.add_zero, Nat.testBit_lt_two_pow hk]
      have hb' : b = false := Bool.eq_false_of_not_eq_true hb
      simp [hb']

def rowIndexRec (a : ℕ) (x : Fin (2 ^ a)) (j : ℕ) (k : Fin (2 ^ j)) : Reg (a + a) :=
  fun i => if i.val < a then x.val.testBit i.val
           else if i.val - a < j then k.val.testBit (i.val - a)
           else false

/-- Extending a recursive row index by one bit updates the next index wire to that bit. -/
lemma rowIndexRec_succ (a j : ℕ) (hj : j < a) (x : Fin (2 ^ a)) (k : Fin (2 ^ j))
    (b : Bool) :
    rowIndexRec a x (j + 1) (binSplitFn j ⟨b, k⟩)
      = Function.update (rowIndexRec a x j k) ⟨a + j, by omega⟩ b := by
  funext i
  by_cases hi : i.val < a
  · have hne : i ≠ ⟨a + j, by omega⟩ := by
      intro h
      have hh := congrArg Fin.val h
      simp only [] at hh
      omega
    have hadr : rowIndexRec a x j k i = x.val.testBit i.val := by
      simp [rowIndexRec, hi]
    rw [show rowIndexRec a x (j + 1) (binSplitFn j ⟨b, k⟩) i
        = x.val.testBit i.val by simp [rowIndexRec, hi]]
    simp only [Function.update_of_ne hne]
    rw [hadr]
  · by_cases hj' : i.val - a < j
    · have hne : i ≠ ⟨a + j, by omega⟩ := by
        intro h
        have hh := congrArg Fin.val h
        simp only [] at hh
        omega
      have hrec : rowIndexRec a x j k i = k.val.testBit (i.val - a) := by
        simp [rowIndexRec, hi, hj']
      have hrec' : rowIndexRec a x (j + 1) (binSplitFn j ⟨b, k⟩) i
          = k.val.testBit (i.val - a) := by
        have htest := testBit_binSplit j k b (i.val - a) (by omega)
        simp only [rowIndexRec, ite_eq_right hi]
        rw [ite_eq_left (by omega : i.val - a < j + 1), htest, ite_eq_left hj']
      rw [hrec']
      simp only [Function.update_of_ne hne]
      rw [hrec]
    · by_cases heq : i.val - a = j
      · have hi' : i = ⟨a + j, by omega⟩ := by
          apply Fin.ext
          simp only []
          omega
        rw [hi']
        simp only [Function.update_self]
        have htest := testBit_binSplit j k b (a + j - a) (by omega)
        simp only [rowIndexRec, ite_eq_right (by omega : ¬ (a + j < a)),
          ite_eq_left (by omega : a + j - a < j + 1)]
        rw [htest]
        have hadj : a + j - a = j := by omega
        rw [hadj, ite_eq_right (by omega : ¬ (j < j))]
      · have hnot : ¬ (i.val - a < j + 1) := by omega
        have hne : i ≠ ⟨a + j, by omega⟩ := by
          intro h
          have hh := congrArg Fin.val h
          simp only [] at hh
          omega
        have hrec : rowIndexRec a x j k i = false := by
          simp [rowIndexRec, hi, hj']
        have hrec' : rowIndexRec a x (j + 1) (binSplitFn j ⟨b, k⟩) i = false := by
          simp only [rowIndexRec, ite_eq_right hi, ite_eq_right hnot]
        rw [hrec']
        simp only [Function.update_of_ne hne]
        rw [hrec]

/-- At recursion depth zero, the row index register is the padded binary encoding of the source. -/
lemma rowIndexRec_zero (a : ℕ) (x : Fin (2 ^ a)) (k : Fin (2 ^ 0)) :
    rowIndexRec a x 0 k = regPadLocal (a + a) a (binaryEnc a x) := by
  funext i
  by_cases hi : i.val < a
  · simp [rowIndexRec, hi, regPadLocal, binaryEnc]
  · have h0 : ¬ (i.val - a < 0) := by omega
    simp [rowIndexRec, hi, h0, regPadLocal]

/-- The next unused index wire of a recursive row index register is false. -/
lemma rowIndexRec_indexWire_false (a j : ℕ) (hj : j < a) (x : Fin (2 ^ a))
    (k : Fin (2 ^ j)) :
    rowIndexRec a x j k ⟨a + j, by omega⟩ = false := by
  simp only [rowIndexRec]
  rw [ite_eq_right (by omega : ¬ (a + j < a)), ite_eq_right (by omega : ¬ (a + j - a < j))]

/-- Updating an already false wire to false leaves the register unchanged. -/
lemma update_eq_self_of_false {n : ℕ} (r : Reg n) (w : Fin n) (hw : r w = false) :
    Function.update r w false = r := by
  funext k
  by_cases h : k = w
  · subst h
    simp [hw]
  · simp [Function.update_of_ne h]

variable {I : Type*} [Fintype I]

/-- Gate application preserves addition of states. -/
lemma applyGate_add' (U : Matrix I I ℂ) (ψ φ : QState I) :
    ApplyGate U (ψ + φ) = ApplyGate U ψ + ApplyGate U φ := by
  funext y
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Pi.add_apply]
  have h : (∑ x : I, U y x * (ψ x + φ x)) = ∑ x : I, (U y x * ψ x + U y x * φ x) := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [h, Finset.sum_add_distrib]

/-- Gate application commutes with complex scalar multiplication. -/
lemma applyGate_smul' (U : Matrix I I ℂ) (c : ℂ) (ψ : QState I) :
    ApplyGate U (c • ψ) = c • ApplyGate U ψ := by
  funext y
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  have h : (∑ x : I, U y x * (c * ψ x)) = ∑ x : I, c * (U y x * ψ x) := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [h, ← Finset.mul_sum]

/-- Gate application commutes with finite sums of states. -/
lemma applyGate_sum' {ι : Type*} (U : Matrix I I ℂ) (s : Finset ι) (ψ : ι → QState I) :
    ApplyGate U (∑ k ∈ s, ψ k) = ∑ k ∈ s, ApplyGate U (ψ k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ApplyGate]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [applyGate_add', ih]

def indexSuperposition (a : ℕ) (x : Fin (2 ^ a)) (j : ℕ) : QState (Reg (a + a)) :=
  ∑ k : Fin (2 ^ j), ((Real.sqrt 2 : ℂ)⁻¹) ^ j • Qatlib.Foundations.PureStateMath.Ket (rowIndexRec a x j k)

/-- Applying Hadamard to the next index wire advances `indexSuperposition` by one step. -/
lemma hadamardIndexStep (a j : ℕ) (hj : j < a) (x : Fin (2 ^ a)) :
    ApplyGate (wireGate (a + a) ⟨a + j, by omega⟩ Hadamard) (indexSuperposition a x j)
      = indexSuperposition a x (j + 1) := by
  classical
  rw [show indexSuperposition a x j
        = ∑ k ∈ (Finset.univ : Finset (Fin (2 ^ j))),
            ((Real.sqrt 2 : ℂ)⁻¹) ^ j • Qatlib.Foundations.PureStateMath.Ket (rowIndexRec a x j k) from rfl,
    applyGate_sum']
  have hpow : ((Real.sqrt 2 : ℂ)⁻¹) ^ (j + 1)
      = ((Real.sqrt 2 : ℂ)⁻¹) ^ j * ((Real.sqrt 2 : ℂ)⁻¹) := pow_succ _ _
  have hper : ∀ k : Fin (2 ^ j),
      ApplyGate (wireGate (a + a) ⟨a + j, by omega⟩ Hadamard)
          (((Real.sqrt 2 : ℂ)⁻¹) ^ j • Qatlib.Foundations.PureStateMath.Ket (rowIndexRec a x j k))
        = ((Real.sqrt 2 : ℂ)⁻¹) ^ (j + 1) • Qatlib.Foundations.PureStateMath.Ket (rowIndexRec a x j k)
          + ((Real.sqrt 2 : ℂ)⁻¹) ^ (j + 1)
            • Qatlib.Foundations.PureStateMath.Ket (rowIndexRec a x (j + 1) (binSplitFn j ⟨true, k⟩)) := by
    intro k
    have hrw : rowIndexRec a x j k ⟨a + j, by omega⟩ = false :=
      rowIndexRec_indexWire_false a j hj x k
    rw [applyGate_smul', applyGate_wireGate_ket, hrw]
    simp only [hadamard_apply_false]
    rw [update_eq_self_of_false _ _ hrw]
    rw [← rowIndexRec_succ a j hj x k true]
    rw [hpow, mul_smul, mul_smul]
    simp only [smul_add]
  rw [Finset.sum_congr rfl (fun k _ => hper k), Finset.sum_add_distrib]
  have hrec0 : ∀ k : Fin (2 ^ j),
      rowIndexRec a x (j + 1) (binSplitFn j ⟨false, k⟩) = rowIndexRec a x j k := by
    intro k
    have h := rowIndexRec_succ a j hj x k false
    rw [h]
    exact update_eq_self_of_false _ _ (rowIndexRec_indexWire_false a j hj x k)
  have hfirst : (∑ k : Fin (2 ^ j),
        ((Real.sqrt 2 : ℂ)⁻¹) ^ (j + 1) • Qatlib.Foundations.PureStateMath.Ket (rowIndexRec a x j k))
      = ∑ k : Fin (2 ^ j), ((Real.sqrt 2 : ℂ)⁻¹) ^ (j + 1)
        • Qatlib.Foundations.PureStateMath.Ket (rowIndexRec a x (j + 1) (binSplitFn j ⟨false, k⟩)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [show Qatlib.Foundations.PureStateMath.Ket (rowIndexRec a x j k)
        = Qatlib.Foundations.PureStateMath.Ket (rowIndexRec a x (j + 1) (binSplitFn j ⟨false, k⟩)) by rw [hrec0 k]]
  rw [hfirst]
  rw [show indexSuperposition a x (j + 1)
      = ∑ k ∈ (Finset.univ : Finset (Fin (2 ^ (j + 1)))),
          ((Real.sqrt 2 : ℂ)⁻¹) ^ (j + 1) • Qatlib.Foundations.PureStateMath.Ket (rowIndexRec a x (j + 1) k) from rfl]
  have hsplit := sum_binSplit (M := QState (Reg (a + a))) j
      (fun k' => ((Real.sqrt 2 : ℂ)⁻¹) ^ (j + 1) • Qatlib.Foundations.PureStateMath.Ket (rowIndexRec a x (j + 1) k'))
  rw [hsplit]
  simp only [binSplitFn]

def hadamardIndexWires (a : ℕ) (j : ℕ) : List FiniteGateCode :=
  (List.range j).map (fun t : ℕ => .h (a + t))

def coherentRowWord (a : ℕ) : List FiniteGateCode :=
  hadamardIndexWires a (a - 1) ++ [.x (a + (a - 1)), .cx (a - 1) (a + (a - 1))]

/-- The successor Hadamard index word appends Hadamard on the next index wire. -/
lemma hadamardIndexWires_succ (a j : ℕ) :
    hadamardIndexWires a (j + 1) = hadamardIndexWires a j ++ [.h (a + j)] := by
  simp only [hadamardIndexWires, List.range_succ, List.map_append, List.map_cons,
    List.map_nil]

/-- The Hadamard index word is legal when the number of index wires does not exceed the address
width. -/
lemma hadamardIndexWires_legal {a : ℕ} (j : ℕ) (hj : j ≤ a) :
    finiteWordLegal (a + a) (hadamardIndexWires a j) = true := by
  induction j with
  | zero => simp [hadamardIndexWires, finiteWordLegal]
  | succ j ih =>
      have hj' : j < a := by omega
      rw [hadamardIndexWires_succ]
      refine finiteWordLegal_append (a + a) _ _ (ih (by omega)) ?_
      simp only [finiteWordLegal, List.all_cons, List.all_nil, Bool.and_eq_true,
        and_true, finiteCodeLegal, decide_eq_true_eq]
      omega

/-- The coherent row word is legal for positive address width. -/
lemma coherentRowWord_legal {a : ℕ} (ha : 0 < a) :
    finiteWordLegal (a + a) (coherentRowWord a) = true := by
  rw [show coherentRowWord a
      = hadamardIndexWires a (a - 1) ++ [.x (a + (a - 1)), .cx (a - 1) (a + (a - 1))]
      from rfl]
  refine finiteWordLegal_append (a + a) _ _ (hadamardIndexWires_legal (a - 1) (by omega)) ?_
  simp only [finiteWordLegal, List.all_cons, List.all_nil, Bool.and_eq_true,
    and_true, finiteCodeLegal, decide_eq_true_eq]
  omega

/-- For positive address width, the coherent row word has length one more than the width. -/
lemma coherentRowWord_length {a : ℕ} (ha : 0 < a) :
    (coherentRowWord a).length = a + 1 := by
  simp only [coherentRowWord, hadamardIndexWires, List.length_append, List.length_map,
    List.length_range, List.length_cons, List.length_nil]
  omega

/-- Running a compiled word with one appended gate applies that gate after running the original
word. -/
lemma run_finiteCodeCircuit_append (W : ℕ) (gs : List FiniteGateCode) (g : FiniteGateCode)
    (ψ : QState (Reg W)) :
    Run (1 : Matrix (Reg W) (Reg W) ℂ) (finiteCodeCircuit W (gs ++ [g])) ψ
      = ApplyGate (finiteCodeMatrix W g) (Run (1) (finiteCodeCircuit W gs) ψ) := by
  rw [show finiteCodeCircuit W (gs ++ [g])
      = finiteCodeCircuit W gs ++ [Step.gate (finiteCodeMatrix W g)] by
        simp only [finiteCodeCircuit, List.map_append, List.map_cons, List.map_nil]]
  rw [run_append]
  simp only [finiteCodeCircuit, run_gate, run_nil]

/-- Running the Hadamard index word prepares the corresponding index superposition from the
initial row register. -/
lemma indexSuperposition_run {a : ℕ} (ha : 0 < a) (x : Fin (2 ^ a)) (j : ℕ) (hj : j ≤ a - 1) :
    Run (1 : Matrix (Reg (a + a)) (Reg (a + a)) ℂ)
      (finiteCodeCircuit (a + a) (hadamardIndexWires a j))
      (Qatlib.Foundations.PureStateMath.Ket (rowIndexRec a x 0 ⟨0, by omega⟩))
      = indexSuperposition a x j := by
  induction j with
  | zero =>
      simp only [hadamardIndexWires, List.range_zero, List.map_nil, finiteCodeCircuit,
        List.map_nil, run_nil, indexSuperposition]
      have hsum : (∑ k : Fin (2 ^ 0), ((Real.sqrt 2 : ℂ)⁻¹) ^ 0
          • Qatlib.Foundations.PureStateMath.Ket (rowIndexRec a x 0 k))
          = Qatlib.Foundations.PureStateMath.Ket (rowIndexRec a x 0 ⟨0, by simp⟩) := by
        show (∑ k : Fin 1, ((Real.sqrt 2 : ℂ)⁻¹) ^ 0 • Qatlib.Foundations.PureStateMath.Ket (rowIndexRec a x 0 k))
            = Qatlib.Foundations.PureStateMath.Ket (rowIndexRec a x 0 ⟨0, by simp⟩)
        rw [Fin.sum_univ_one]
        simp
      rw [hsum]
  | succ j ih =>
      have hjlt : j < a := by omega
      rw [hadamardIndexWires_succ]
      rw [run_finiteCodeCircuit_append, ih (by omega : j ≤ a - 1)]
      have hmat : finiteCodeMatrix (a + a) (.h (a + j))
          = wireGate (a + a) ⟨a + j, by omega⟩ Hadamard := by
        simp only [finiteCodeMatrix, dite_eq_left (by omega : a + j < a + a)]
      rw [hmat]
      exact hadamardIndexStep a j hjlt x

def rowDataRec {a : ℕ} (ha : 0 < a) (x : Fin (2 ^ a)) (k : Fin (2 ^ (a - 1))) (b : Bool) :
    Reg (a + a) :=
  Function.update (rowIndexRec a x (a - 1) k) ⟨a + (a - 1), by omega⟩ b

def rowFinalRec {a : ℕ} (ha : 0 < a) (x : Fin (2 ^ a)) (k : Fin (2 ^ (a - 1))) :
    Reg (a + a) :=
  rowDataRec ha x k (!(x.val.testBit (a - 1)))

/-- After preparing all lower index bits, the top data wire is still false. -/
lemma rowIndexRec_dataWire_false {a : ℕ} (ha : 0 < a) (x : Fin (2 ^ a))
    (k : Fin (2 ^ (a - 1))) :
    rowIndexRec a x (a - 1) k ⟨a + (a - 1), by omega⟩ = false := by
  simp only [rowIndexRec]
  rw [ite_eq_right (by omega : ¬ (a + (a - 1) < a)),
    ite_eq_right (by omega : ¬ (a + (a - 1) - a < a - 1))]

/-- Pauli X on the top data wire changes its value to true in every term of the index
superposition. -/
lemma pauliXIndexStep {a : ℕ} (ha : 0 < a) (x : Fin (2 ^ a)) :
    ApplyGate (wireGate (a + a) ⟨a + (a - 1), by omega⟩ PauliX)
        (indexSuperposition a x (a - 1))
      = ∑ k : Fin (2 ^ (a - 1)), ((Real.sqrt 2 : ℂ)⁻¹) ^ (a - 1)
          • Qatlib.Foundations.PureStateMath.Ket (rowDataRec ha x k true) := by
  classical
  rw [show indexSuperposition a x (a - 1)
      = ∑ k ∈ (Finset.univ : Finset (Fin (2 ^ (a - 1)))),
          ((Real.sqrt 2 : ℂ)⁻¹) ^ (a - 1) • Qatlib.Foundations.PureStateMath.Ket (rowIndexRec a x (a - 1) k) from rfl,
    applyGate_sum']
  have hper : ∀ k : Fin (2 ^ (a - 1)),
      ApplyGate (wireGate (a + a) ⟨a + (a - 1), by omega⟩ PauliX)
          (((Real.sqrt 2 : ℂ)⁻¹) ^ (a - 1) • Qatlib.Foundations.PureStateMath.Ket (rowIndexRec a x (a - 1) k))
        = ((Real.sqrt 2 : ℂ)⁻¹) ^ (a - 1) • Qatlib.Foundations.PureStateMath.Ket (rowDataRec ha x k true) := by
    intro k
    rw [applyGate_smul', applyGate_wireGate_pauliX_ket]
    rw [rowIndexRec_dataWire_false ha x k]
    simp only [Bool.not_false]
    rfl
  rw [Finset.sum_congr rfl (fun k _ => hper k)]

/-- Two successive updates at the same wire reduce to the last update. -/
lemma update_update_same {n : ℕ} (r : Reg n) (w : Fin n) (b c : Bool) :
    Function.update (Function.update r w b) w c = Function.update r w c := by
  funext i
  by_cases h : i = w
  · subst h
    simp [Function.update_self]
  · simp [Function.update_of_ne h]

/-- The Boolean XOR of true with `b` is the negation of `b`. -/
lemma boolXor_true (b : Bool) : true ^^ b = !b := by
  cases b <;> rfl

/-- The final controlled-X gate sets the top data bit to the negation of the source's top bit in
every superposition term. -/
lemma cnotIndexStep {a : ℕ} (ha : 0 < a) (x : Fin (2 ^ a)) :
    ApplyGate (cnotGate (a + a) ⟨a - 1, by omega⟩ ⟨a + (a - 1), by omega⟩)
        (∑ k : Fin (2 ^ (a - 1)), ((Real.sqrt 2 : ℂ)⁻¹) ^ (a - 1)
          • Qatlib.Foundations.PureStateMath.Ket (rowDataRec ha x k true))
      = ∑ k : Fin (2 ^ (a - 1)), ((Real.sqrt 2 : ℂ)⁻¹) ^ (a - 1)
          • Qatlib.Foundations.PureStateMath.Ket (rowDataRec ha x k (!(x.val.testBit (a - 1)))) := by
  classical
  rw [show (∑ k : Fin (2 ^ (a - 1)), ((Real.sqrt 2 : ℂ)⁻¹) ^ (a - 1)
          • Qatlib.Foundations.PureStateMath.Ket (rowDataRec ha x k true))
        = ∑ k ∈ (Finset.univ : Finset (Fin (2 ^ (a - 1)))),
          ((Real.sqrt 2 : ℂ)⁻¹) ^ (a - 1) • Qatlib.Foundations.PureStateMath.Ket (rowDataRec ha x k true) from rfl,
    applyGate_sum']
  have hper : ∀ k : Fin (2 ^ (a - 1)),
      ApplyGate (cnotGate (a + a) ⟨a - 1, by omega⟩ ⟨a + (a - 1), by omega⟩)
          (((Real.sqrt 2 : ℂ)⁻¹) ^ (a - 1) • Qatlib.Foundations.PureStateMath.Ket (rowDataRec ha x k true))
        = ((Real.sqrt 2 : ℂ)⁻¹) ^ (a - 1)
          • Qatlib.Foundations.PureStateMath.Ket (rowDataRec ha x k (!(x.val.testBit (a - 1)))) := by
    intro k
    have hct : (⟨a - 1, by omega⟩ : Fin (a + a)) ≠ ⟨a + (a - 1), by omega⟩ := by
      intro h
      have hh := congrArg Fin.val h
      simp only [] at hh
      omega
    rw [applyGate_smul', applyGate_cnotGate_ket (a + a) _ _ hct]
    have htop : (rowDataRec ha x k true) ⟨a + (a - 1), by omega⟩ = true := by
      rw [rowDataRec, Function.update_self]
    have hctrl : (rowDataRec ha x k true) ⟨a - 1, by omega⟩
        = x.val.testBit (a - 1) := by
      have hne : (⟨a - 1, by omega⟩ : Fin (a + a)) ≠ ⟨a + (a - 1), by omega⟩ := by
        intro h
        have hh := congrArg Fin.val h
        simp only [] at hh
        omega
      rw [rowDataRec, Function.update_of_ne hne]
      simp only [rowIndexRec]
      rw [ite_eq_left (by omega : a - 1 < a)]
    rw [htop, hctrl]
    have hxor : (true ^^ x.val.testBit (a - 1)) = !(x.val.testBit (a - 1)) := by
      cases x.val.testBit (a - 1) <;> simp
    rw [hxor]
    rw [show rowDataRec ha x k true
        = Function.update (rowIndexRec a x (a - 1) k) ⟨a + (a - 1), by omega⟩ true from rfl]
    rw [update_update_same]
    rfl
  rw [Finset.sum_congr rfl (fun k _ => hper k)]

/-- The coherent row word prepares the equally weighted superposition of final row registers. -/
theorem coherentRowWord_run {a : ℕ} (ha : 0 < a) (x : Fin (2 ^ a)) :
    Run (1 : Matrix (Reg (a + a)) (Reg (a + a)) ℂ)
        (finiteCodeCircuit (a + a) (coherentRowWord a))
        (Qatlib.Foundations.PureStateMath.Ket (rowIndexRec a x 0 ⟨0, by simp⟩))
      = ∑ k : Fin (2 ^ (a - 1)), ((Real.sqrt 2 : ℂ)⁻¹) ^ (a - 1)
          • Qatlib.Foundations.PureStateMath.Ket (rowFinalRec ha x k) := by
  rw [show finiteCodeCircuit (a + a) (coherentRowWord a)
      = finiteCodeCircuit (a + a) (hadamardIndexWires a (a - 1))
        ++ [Step.gate (finiteCodeMatrix (a + a) (.x (a + (a - 1)))),
            Step.gate (finiteCodeMatrix (a + a) (.cx (a - 1) (a + (a - 1))))] by
      simp only [coherentRowWord, finiteCodeCircuit, List.map_append, List.map_cons,
        List.map_nil]]
  rw [run_append, run_gate, run_gate, run_nil]
  have hmx : finiteCodeMatrix (a + a) (.x (a + (a - 1)))
      = wireGate (a + a) ⟨a + (a - 1), by omega⟩ PauliX := by
    simp only [finiteCodeMatrix, dite_eq_left (by omega : a + (a - 1) < a + a)]
  have hmcx : finiteCodeMatrix (a + a) (.cx (a - 1) (a + (a - 1)))
      = cnotGate (a + a) ⟨a - 1, by omega⟩ ⟨a + (a - 1), by omega⟩ := by
    simp only [finiteCodeMatrix,
      dite_eq_left (by omega : a - 1 < a + a ∧ a + (a - 1) < a + a ∧ a - 1 ≠ a + (a - 1))]
  rw [hmx, hmcx, indexSuperposition_run ha x (a - 1) (by omega),
    pauliXIndexStep ha x, cnotIndexStep ha x]
  rfl

end CoherentRowProgram

section

variable {a : ℕ}

def nbFin (a : ℕ) (x : Fin (2 ^ a)) : Finset (Fin (2 ^ a)) :=
  Finset.univ.filter (fun j => bipartiteAdj a x j)

/-- Membership in `nbFin` is equivalent to a true bipartite adjacency test. -/
lemma nbFin_mem (a : ℕ) (x y : Fin (2 ^ a)) :
    y ∈ nbFin a x ↔ bipartiteAdj a x y = true := by
  rw [nbFin, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- The finite set `nbFin` equals the bipartite graph's neighbor finset. -/
lemma nbFin_eq_neighborFinset (a : ℕ) (x : Fin (2 ^ a)) :
    nbFin a x = (bipartiteGraph a).neighborFinset x := by
  ext y
  rw [nbFin_mem, SimpleGraph.mem_neighborFinset]
  simp [bipartiteGraph]

/-- For positive width, `nbFin` has cardinality two raised to one less than the width. -/
lemma nbFin_card (ha : 0 < a) (x : Fin (2 ^ a)) : (nbFin a x).card = 2 ^ (a - 1) := by
  rw [nbFin_eq_neighborFinset, SimpleGraph.card_neighborFinset_eq_degree]
  have hd := bipartiteGraph_degree a ha x
  rw [Qatlib.Concepts.GraphLaplacian.LaplacianPsd.degree_eq_mathlib] at hd
  have hdeg : (bipartiteGraph a).degree x = 2 ^ (a - 1) := by
    exact_mod_cast hd
  rw [hdeg]

/-- Every bipartite neighbor belongs to `nbFin`. -/
lemma bipartiteNeighbor_mem_nbFin (ha : 0 < a) (x : Fin (2 ^ a)) (k : Fin (2 ^ (a - 1))) :
    bipartiteNeighbor ha x k ∈ nbFin a x := by
  rw [nbFin_mem, bipartiteAdj, decide_eq_true_eq]
  by_cases hx : x.val < bipartiteHalf a
  · rw [bipartiteNeighbor, dite_eq_left hx]
    have hne : ¬ (k.val + bipartiteHalf a < bipartiteHalf a) := by omega
    simp [hx, hne]
  · rw [bipartiteNeighbor, dite_eq_right hx]
    have hlt : k.val < bipartiteHalf a := by
      have hk2 : k.val < 2 ^ (a - 1) := k.isLt
      rw [bipartiteHalf]
      exact hk2
    simp [hx, hlt]

/-- For a fixed source of positive width, `bipartiteNeighbor` is injective in its index. -/
lemma bipartiteNeighbor_injective (ha : 0 < a) (x : Fin (2 ^ a)) :
    Function.Injective (bipartiteNeighbor ha x) := by
  intro k1 k2 h
  apply Fin.ext
  have hv := congrArg Fin.val h
  by_cases hx : x.val < bipartiteHalf a
  · simp only [bipartiteNeighbor, dite_eq_left hx] at hv
    omega
  · simp only [bipartiteNeighbor, dite_eq_right hx] at hv
    omega

/-- Every member of `nbFin` has a bipartite neighbor index. -/
lemma bipartiteNeighbor_surjective (ha : 0 < a) (x : Fin (2 ^ a))
    (y : Fin (2 ^ a)) (hy : y ∈ nbFin a x) :
    ∃ k : Fin (2 ^ (a - 1)), bipartiteNeighbor ha x k = y := by
  have hhalf : 2 ^ (a - 1) + 2 ^ (a - 1) = 2 ^ a := by
    have h1 : 2 ^ (a - 1) + 2 ^ (a - 1) = 2 ^ (a - 1) * 2 := by rw [Nat.mul_two]
    have h2 : 2 ^ (a - 1) * 2 = 2 ^ (a - 1 + 1) := by rw [Nat.pow_succ]
    rw [h1, h2, show a - 1 + 1 = a from by omega]
  have hbhalf : bipartiteHalf a = 2 ^ (a - 1) := rfl
  have hAdj : (bipartiteGraph a).Adj x y := by
    rw [nbFin_mem] at hy
    exact hy
  have hiff := bipartiteAdj_iff' a x y
  by_cases hx : x.val < bipartiteHalf a
  · have hyne : ¬ (y.val < bipartiteHalf a) := by
      rcases hiff.mp hAdj with h | h
      · exact h.2
      · exact (h.1 hx).elim
    refine ⟨⟨y.val - bipartiteHalf a, ?_⟩, ?_⟩
    · have hyv : y.val < 2 ^ a := y.isLt
      omega
    · rw [bipartiteNeighbor, dite_eq_left hx]
      apply Fin.ext
      exact Nat.sub_add_cancel (le_of_not_gt hyne)
  · have hylt : y.val < bipartiteHalf a := by
      rcases hiff.mp hAdj with h | h
      · exact (hx h.1).elim
      · exact h.2
    refine ⟨⟨y.val, ?_⟩, ?_⟩
    · have hyv : y.val < 2 ^ a := y.isLt
      omega
    · rw [bipartiteNeighbor, dite_eq_right hx]

/-- Summing over valid indices into a finset's list equals summing over the finset. -/
lemma sum_toList_getD_eq {ι : Type} {M : Type} [Fintype ι] [AddCommMonoid M]
    (s : Finset ι) (dflt : ι) (f : ι → M) :
    (∑ k : Fin s.toList.length, f (s.toList.getD k dflt)) = ∑ v ∈ s, f v := by
  have hnd : s.toList.Nodup := Finset.nodup_toList s
  have hget : ∀ (i j : Fin s.toList.length), i < j → s.toList.get i ≠ s.toList.get j := by
    have hp : s.toList.Pairwise (· ≠ ·) := List.nodup_iff_pairwise_ne.mpr hnd
    exact List.pairwise_iff_get.mp hp
  have hinj : ∀ (i j : Fin s.toList.length), s.toList.get i = s.toList.get j → i = j := by
    intro i j h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd h (hget i j hlt)
    · exact absurd h.symm (hget j i hgt)
  refine Finset.sum_bij (s := (Finset.univ : Finset (Fin s.toList.length))) (t := s)
    (fun k _ => s.toList.get k) ?_ ?_ ?_ ?_
  · intro k _
    exact Finset.mem_toList.mp (List.get_mem _ _)
  · intro k1 _ k2 _ h
    exact hinj k1 k2 h
  · intro v hv
    have hmem : v ∈ s.toList := Finset.mem_toList.mpr hv
    obtain ⟨n, hn⟩ := List.get_of_mem hmem
    exact ⟨n, Finset.mem_univ n, hn⟩
  · intro k _
    have hgd : s.toList.getD k dflt = s.toList.get k := by
      rw [List.getD_eq_getElem s.toList dflt k.isLt, List.get_eq_getElem]
    rw [hgd]

/-- Summing over bipartite neighbor indices equals summing over `nbFin`. -/
lemma sum_bipartiteNeighbor_eq_nbFin {M : Type} [AddCommMonoid M]
    (ha : 0 < a) (x : Fin (2 ^ a)) (f : Fin (2 ^ a) → M) :
    (∑ k : Fin (2 ^ (a - 1)), f (bipartiteNeighbor ha x k)) = ∑ y ∈ nbFin a x, f y := by
  refine Finset.sum_bij (s := (Finset.univ : Finset (Fin (2 ^ (a - 1))))) (t := nbFin a x)
    (fun k _ => bipartiteNeighbor ha x k) ?_ ?_ ?_ ?_
  · intro k _
    exact bipartiteNeighbor_mem_nbFin ha x k
  · intro k1 _ k2 _ h
    exact bipartiteNeighbor_injective ha x h
  · intro b hb
    obtain ⟨k, hk⟩ := bipartiteNeighbor_surjective ha x b hb
    exact ⟨k, Finset.mem_univ k, hk⟩
  · intro k _
    rfl

/-- The Boolean bipartite adjacency test is symmetric. -/
lemma bipartiteAdj_symm (a : ℕ) (x y : Fin (2 ^ a)) :
    bipartiteAdj a x y = bipartiteAdj a y x := by
  unfold bipartiteAdj
  by_cases h : (x.val < bipartiteHalf a) ≠ (y.val < bipartiteHalf a)
  · have h' : (y.val < bipartiteHalf a) ≠ (x.val < bipartiteHalf a) :=
      fun hh => h hh.symm
    simp [h, h']
  · have h' : ¬ ((y.val < bipartiteHalf a) ≠ (x.val < bipartiteHalf a)) :=
      fun hh => h hh.symm
    simp [h, h']

/-- Every natural number is bounded by a power of two with positive exponent. -/
lemma exists_le_two_pow (N : ℕ) : ∃ a : ℕ, 1 ≤ a ∧ N ≤ 2 ^ a := by
  induction N with
  | zero => exact ⟨1, by omega⟩
  | succ N ih =>
      obtain ⟨a, ha1, ha⟩ := ih
      refine ⟨a + 1, by omega, ?_⟩
      have h2 : 2 ^ (a + 1) = 2 ^ a * 2 := Nat.pow_succ _ _
      have hpos : 1 ≤ 2 ^ a := by
        have hle : 2 ^ 0 ≤ 2 ^ a := Nat.pow_le_pow_of_le (by decide) (Nat.zero_le a)
        simpa using! hle
      omega

/-- Describes each final row register bit using the source bits, neighbor index bits, and
complemented source top bit. -/
lemma rowFinalRec_apply (ha : 0 < a) (x : Fin (2 ^ a)) (k : Fin (2 ^ (a - 1)))
    (i : Fin (a + a)) :
    rowFinalRec ha x k i
      = if i.val < a then x.val.testBit i.val
        else if i.val - a < a - 1 then k.val.testBit (i.val - a)
        else !(x.val.testBit (a - 1)) := by
  rw [rowFinalRec, rowDataRec, Function.update]
  by_cases h : i.val = a + (a - 1)
  · have hiw : i = (⟨a + (a - 1), by omega⟩ : Fin (a + a)) := Fin.ext h
    rw [dite_eq_left hiw]
    have hnlt : ¬ (i.val < a) := by omega
    have hnlt2 : ¬ (i.val - a < a - 1) := by omega
    simp [hnlt, hnlt2]
  · have hiw : i ≠ (⟨a + (a - 1), by omega⟩ : Fin (a + a)) := by
      intro hh
      have hval := congrArg Fin.val hh
      have hmk : (⟨a + (a - 1), by omega⟩ : Fin (a + a)).val = a + (a - 1) := rfl
      omega
    rw [dite_eq_right hiw]
    by_cases hi : i.val < a
    · simp [rowIndexRec, hi]
    · by_cases hd : i.val - a < a - 1
      · simp [rowIndexRec, hi, hd]
      · exfalso
        have hi_lt : i.val < a + a := i.isLt
        omega

/-- Describes the bits of concatenated source and neighbor encodings using the source bits,
index bits, and complemented source top bit. -/
lemma regCat_neighbor_apply (ha : 0 < a) (x : Fin (2 ^ a)) (k : Fin (2 ^ (a - 1)))
    (i : Fin (a + a)) :
    regCatLocal (binaryEnc a x) (binaryEnc a (bipartiteNeighbor ha x k)) i
      = if i.val < a then x.val.testBit i.val
        else if i.val - a < a - 1 then k.val.testBit (i.val - a)
        else !(x.val.testBit (a - 1)) := by
  rw [regCat_binaryEnc_layout]
  by_cases hi : i.val < a
  · simp [hi]
  · by_cases hd : i.val - a < a - 1
    · rw [bipartiteNeighbor_low ha x k ⟨i.val - a, by omega⟩ hd]
      simp [hi, hd]
    · have hsub : i.val - a = a - 1 := by omega
      rw [hsub]
      have hnlt : ¬ (i.val < a) := by omega
      have hlt2 : ¬ (a - 1 < a - 1) := by omega
      simp only [hnlt, hlt2, ite_false]
      exact bipartiteNeighbor_top ha x k

/-- The final row register is the concatenation of the encoded source and its encoded neighbor. -/
lemma rowFinalRec_regCat (ha : 0 < a) (x : Fin (2 ^ a)) (k : Fin (2 ^ (a - 1))) :
    rowFinalRec ha x k = regCatLocal (binaryEnc a x) (binaryEnc a (bipartiteNeighbor ha x k)) := by
  funext i
  rw [rowFinalRec_apply, regCat_neighbor_apply]

/-- The square root of a natural power of two is the corresponding power of the square root of
two. -/
lemma sqrt_two_pow' (n : ℕ) : Real.sqrt ((2 : ℝ) ^ n) = (Real.sqrt 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 2 := pow_succ _ _
      have h2 : (Real.sqrt 2 : ℝ) ^ (n + 1) = (Real.sqrt 2 : ℝ) ^ n * Real.sqrt 2 :=
        pow_succ _ _
      rw [h1, Real.sqrt_mul (by positivity) _]
      rw [ih, h2]

/-- The square root of the bipartite degree equals the corresponding power of the square root of
two. -/
lemma sqrt_two_pow (a : ℕ) :
    Real.sqrt ((2 ^ (a - 1) : ℕ) : ℝ) = (Real.sqrt 2) ^ (a - 1) := by
  have hcast : ((2 ^ (a - 1) : ℕ) : ℝ) = (2 : ℝ) ^ (a - 1) := by
    exact_mod_cast (Nat.cast_pow 2 (a - 1)).symm
  rw [hcast, sqrt_two_pow']

/-- Casting a real natural power to complex numbers commutes with exponentiation. -/
lemma ofReal_pow (n : ℕ) (x : ℝ) : (↑(x ^ n) : ℂ) = (↑x : ℂ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      rw [Complex.ofReal_mul, ih]

/-- The coherent row amplitude equals the reciprocal square root of the bipartite degree. -/
lemma amplitude_eq (a : ℕ) :
    ((Real.sqrt 2 : ℂ)⁻¹) ^ (a - 1)
      = ((Real.sqrt ((2 ^ (a - 1) : ℕ) : ℝ))⁻¹ : ℂ) := by
  have hre : (Real.sqrt ((2 ^ (a - 1) : ℕ) : ℝ) : ℂ)
      = (Real.sqrt 2 : ℂ) ^ (a - 1) := by
    have hcast : ((2 ^ (a - 1) : ℕ) : ℝ) = (2 : ℝ) ^ (a - 1) := by
      exact_mod_cast (Nat.cast_pow 2 (a - 1)).symm
    rw [hcast, sqrt_two_pow', ofReal_pow]
  rw [inv_pow, ← hre]

/-- For positive width, the nonlazy bipartite kernel is a transition matrix. -/
theorem bipartite_nonLazyKernel_isTransition (a : ℕ) (ha : 0 < a) :
    IsTransitionMatrix (regularKernel (bipartiteGraph a) ((2 ^ (a - 1) : ℕ) : ℝ)) := by
  have hdpos : 0 < ((2 ^ (a - 1) : ℕ) : ℝ) := by
    have h1 : (1 : ℕ) ≤ 2 ^ (a - 1) := Nat.one_le_two_pow
    have h2 : (0 : ℕ) < 2 ^ (a - 1) := Nat.lt_of_lt_of_le (by decide) h1
    exact_mod_cast h2
  refine ⟨?_, ?_⟩
  · intro x y
    exact regularKernel_nonneg (bipartiteGraph a) hdpos x y
  · intro x
    exact regularKernel_sum (bipartiteGraph a) (bipartiteGraph_isDegreeRegular a ha) hdpos x

/-- A bipartite Szegedy isometry column has reciprocal-square-root degree amplitude at neighbors
and zero elsewhere in its source row. -/
theorem szegedyIsometry_bipartite_apply (a : ℕ) (ha : 0 < a) (x y : Fin (2 ^ a)) :
    (SzegedyIsometry (regularKernel (bipartiteGraph a) ((2 ^ (a - 1) : ℕ) : ℝ)) *ᵥ Qatlib.Foundations.PureStateMath.Ket x) (x, y)
      = (if y ∈ nbFin a x then ((Real.sqrt ((2 ^ (a - 1) : ℕ) : ℝ))⁻¹ : ℂ) else 0) := by
  rw [mulVec_ket_column, szegedyIsometry_apply_pair, ite_eq_left rfl]
  by_cases hy : y ∈ nbFin a x
  · rw [ite_eq_left hy]
    have hadj : (bipartiteGraph a).Adj x y := by
      simpa [bipartiteGraph] using! (nbFin_mem a x y).mp hy
    rw [regularKernel, ite_eq_left hadj, Real.sqrt_inv, Complex.ofReal_inv]
  · rw [ite_eq_right hy]
    have hnot : ¬ (bipartiteGraph a).Adj x y := by
      simp only [bipartiteGraph]
      intro hcon
      exact hy ((nbFin_mem a x y).mpr hcon)
    rw [regularKernel, ite_eq_right hnot]
    simp

/-- A bipartite Szegedy isometry column is the normalized superposition of source-neighbor basis
pairs. -/
theorem szegedyIsometry_bipartite_column (a : ℕ) (ha : 0 < a) (x : Fin (2 ^ a)) :
    SzegedyIsometry (regularKernel (bipartiteGraph a) ((2 ^ (a - 1) : ℕ) : ℝ)) *ᵥ Qatlib.Foundations.PureStateMath.Ket x
      = ∑ y ∈ nbFin a x, ((Real.sqrt ((2 ^ (a - 1) : ℕ) : ℝ))⁻¹ : ℂ) • Qatlib.Foundations.PureStateMath.Ket (x, y) := by
  funext p
  obtain ⟨x', y⟩ := p
  rw [Finset.sum_apply]
  by_cases hx : x' = x
  · rw [hx]
    by_cases hy : y ∈ nbFin a x
    · have hcol := szegedyIsometry_bipartite_apply a ha x y
      rw [ite_eq_left hy] at hcol
      rw [hcol]
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hy]
      simp [Qatlib.Foundations.PureStateMath.Ket]
    · have hcol := szegedyIsometry_bipartite_apply a ha x y
      rw [ite_eq_right hy] at hcol
      rw [hcol]
      symm
      rw [Finset.sum_eq_zero]
      intro c hc
      simp only [Qatlib.Foundations.PureStateMath.Ket, Pi.smul_apply, smul_eq_mul, mul_ite,
          mul_one, mul_zero]
      by_cases h : (x, y) = (x, c)
      · have hcy : y = c := (Prod.ext_iff.mp h).2
        exact False.elim (hy (hcy ▸ hc))
      · simp [h]
  · rw [mulVec_ket_column, szegedyIsometry_apply_pair, ite_eq_right hx]
    symm
    rw [Finset.sum_eq_zero]
    intro c hc
    simp only [Qatlib.Foundations.PureStateMath.Ket, Pi.smul_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero]
    by_cases h : (x', y) = (x, c)
    · exact False.elim (hx (Prod.ext_iff.mp h).1)
    · simp [h]

/-- The prepared bipartite row state equals the sum of encoded source-neighbor pairs with
reciprocal-square-root degree amplitudes. -/
theorem bipartite_rowState_is_isometryColumn (a : ℕ) (ha : 0 < a) (x : Fin (2 ^ a)) :
    (∑ k : Fin (2 ^ (a - 1)), ((Real.sqrt 2 : ℂ)⁻¹) ^ (a - 1) • Qatlib.Foundations.PureStateMath.Ket (rowFinalRec ha x k))
      = ∑ k : Fin (2 ^ (a - 1)), ((Real.sqrt ((2 ^ (a - 1) : ℕ) : ℝ))⁻¹ : ℂ)
          • Qatlib.Foundations.PureStateMath.Ket (regCatLocal (binaryEnc a x) (binaryEnc a (bipartiteNeighbor ha x k))) := by
  apply Finset.sum_congr rfl
  intro k _
  rw [rowFinalRec_regCat, amplitude_eq]

/-- Records the bipartite setup and check word lengths and four queries and four gates per
repeated counted Szegedy word. -/
theorem bipartite_setup_update_check_ledger (a : ℕ) (ha : 0 < a) (m : ℕ) :
    (coherentRowWord a).length = a + 1 ∧
    ((bipartiteCheckBlocks a ha).flatMap blockWord).length = 1 ∧
    adjointQueryCount (List.replicate m (countedSzegedyWord (0 : Fin (2 ^ a)))).flatten = 4 * m ∧
    adjointGateCount (List.replicate m (countedSzegedyWord (0 : Fin (2 ^ a)))).flatten = 4 * m := by
  have hcount : ∀ m : ℕ,
      adjointQueryCount (List.replicate m (countedSzegedyWord (0 : Fin (2 ^ a)))).flatten = 4 * m ∧
      adjointGateCount (List.replicate m (countedSzegedyWord (0 : Fin (2 ^ a)))).flatten = 4 * m := by
    intro m
    induction m with
    | zero =>
        simp only [List.replicate_zero, List.flatten_nil]
        constructor <;> rfl
    | succ m ih =>
        have hbase := counted_szegedy_actual_word_and_counts (0 : Fin (2 ^ a))
        simp only [List.replicate_succ, List.flatten_cons]
        rw [adjointQueryCount_append, ih.1, hbase.2.1]
        rw [adjointGateCount_append, ih.2, hbase.2.2]
        omega
  exact ⟨coherentRowWord_length ha, bipartiteCheckWord_length a ha, (hcount m).1, (hcount m).2⟩

end

section PairFamilyMNRS

variable {N : ℕ}

def pairDegree (N : ℕ) : ℝ := ((2 * (N - 2) : ℕ) : ℝ)

def pairMarked (hN : 3 ≤ N) : PairVertex N :=
  pairAtTotal (by omega) (⟨0, by omega⟩) (⟨1, by omega⟩)

/-- For `N` at least three, the nonlazy pair graph kernel is a transition matrix. -/
theorem pairGraph_nonLazyKernel_isTransition (hN : 3 ≤ N) :
    IsTransitionMatrix (regularKernel (pairGraph N) (pairDegree N)) := by
  have hdpos : 0 < pairDegree N := by
    have hpos : 0 < (2 * (N - 2) : ℕ) := by omega
    unfold pairDegree
    exact_mod_cast hpos
  refine ⟨?_, ?_⟩
  · intro x y
    exact regularKernel_nonneg (pairGraph N) hdpos x y
  · intro x
    exact regularKernel_sum (pairGraph N) (pairGraph_isDegreeRegular N) hdpos x

/-- A pair graph Szegedy isometry column has reciprocal-square-root degree amplitude at
neighbors and zero elsewhere in its source row. -/
theorem szegedyIsometry_pairGraph_apply (hN : 3 ≤ N) (x y : PairVertex N) :
    (SzegedyIsometry (regularKernel (pairGraph N) (pairDegree N)) *ᵥ Qatlib.Foundations.PureStateMath.Ket x) (x, y)
      = (if y ∈ pairNeighbours N x then ((Real.sqrt (pairDegree N))⁻¹ : ℂ) else 0) := by
  rw [mulVec_ket_column, szegedyIsometry_apply_pair, ite_eq_left rfl]
  by_cases hy : y ∈ pairNeighbours N x
  · rw [ite_eq_left hy]
    have hadj : (pairGraph N).Adj x y := by
      have h1 : (x.1 ∩ y.1).card = 1 := by simpa [pairNeighbours, pairGraph] using! hy
      exact h1
    rw [regularKernel, ite_eq_left hadj, Real.sqrt_inv, Complex.ofReal_inv]
  · rw [ite_eq_right hy]
    have hnot : ¬ (pairGraph N).Adj x y := by
      intro hcon
      have h1 : y ∈ pairNeighbours N x := by
        simpa [pairNeighbours, pairGraph] using! hcon
      exact hy h1
    rw [regularKernel, ite_eq_right hnot]
    simp

/-- A pair graph Szegedy isometry column is the normalized superposition of source-neighbor
basis pairs. -/
theorem szegedyIsometry_pairGraph_column (hN : 3 ≤ N) (x : PairVertex N) :
    SzegedyIsometry (regularKernel (pairGraph N) (pairDegree N)) *ᵥ Qatlib.Foundations.PureStateMath.Ket x
      = ∑ y ∈ pairNeighbours N x, ((Real.sqrt (pairDegree N))⁻¹ : ℂ) • Qatlib.Foundations.PureStateMath.Ket (x, y) := by
  funext p
  obtain ⟨x', y⟩ := p
  rw [Finset.sum_apply]
  by_cases hx : x' = x
  · rw [hx]
    by_cases hy : y ∈ pairNeighbours N x
    · have hcol := szegedyIsometry_pairGraph_apply hN x y
      rw [ite_eq_left hy] at hcol
      rw [hcol]
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hy]
      simp [Qatlib.Foundations.PureStateMath.Ket]
    · have hcol := szegedyIsometry_pairGraph_apply hN x y
      rw [ite_eq_right hy] at hcol
      rw [hcol]
      symm
      rw [Finset.sum_eq_zero]
      intro c hc
      simp only [Qatlib.Foundations.PureStateMath.Ket, Pi.smul_apply, smul_eq_mul, mul_ite,
          mul_one, mul_zero]
      by_cases h : (x, y) = (x, c)
      · have hcy : y = c := (Prod.ext_iff.mp h).2
        exact False.elim (hy (hcy ▸ hc))
      · simp [h]
  · rw [mulVec_ket_column, szegedyIsometry_apply_pair, ite_eq_right hx]
    symm
    rw [Finset.sum_eq_zero]
    intro c hc
    simp only [Qatlib.Foundations.PureStateMath.Ket, Pi.smul_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero]
    by_cases h : (x', y) = (x, c)
    · exact False.elim (hx (Prod.ext_iff.mp h).1)
    · simp [h]

/-- Repeating the counted pair Szegedy word uses four queries and four gates per repetition. -/
theorem pair_setup_update_check_ledger (hN : 3 ≤ N) (m : ℕ) :
    adjointQueryCount (List.replicate m (countedSzegedyWord (pairMarked hN))).flatten = 4 * m ∧
    adjointGateCount (List.replicate m (countedSzegedyWord (pairMarked hN))).flatten = 4 * m := by
  have hcount : ∀ m : ℕ,
      adjointQueryCount (List.replicate m (countedSzegedyWord (pairMarked hN))).flatten = 4 * m ∧
      adjointGateCount (List.replicate m (countedSzegedyWord (pairMarked hN))).flatten = 4 * m := by
    intro m
    induction m with
    | zero =>
        simp only [List.replicate_zero, List.flatten_nil]
        constructor <;> rfl
    | succ m ih =>
        have hbase := counted_szegedy_actual_word_and_counts (pairMarked hN)
        simp only [List.replicate_succ, List.flatten_cons]
        rw [adjointQueryCount_append, ih.1, hbase.2.1]
        rw [adjointGateCount_append, ih.2, hbase.2.2]
        omega
  exact hcount m

/-- Establishes the pair graph degree, complete injective neighbor enumeration without
self-loops, gap parameter bound, transition property, and Szegedy column amplitudes. -/
theorem explicit_neighbor_family_consumers (hN : 3 ≤ N) :
    (∀ S : PairVertex N, Qatlib.Concepts.GraphEnergy.ZeroEnergy.degree (pairGraph N) S = pairDegree N) ∧
    (∀ S : PairVertex N, (pairNeighbours N S).card = pairDegree N) ∧
    (∀ S : PairVertex N, Function.Injective (pairRowOracle S)) ∧
    (∀ S z : PairVertex N, z ∈ pairNeighbours N S →
        ∃ p : PairRowIndex S, pairRowOracle S p = z) ∧
    (∀ (S : PairVertex N) (p : PairRowIndex S), pairRowOracle S p ≠ S) ∧
    (1 / 4 : ℝ) ≤ (N : ℝ) / (4 * ((N : ℝ) - 2)) ∧
    IsTransitionMatrix (regularKernel (pairGraph N) (pairDegree N)) ∧
    (∀ x y : PairVertex N,
      (SzegedyIsometry (regularKernel (pairGraph N) (pairDegree N)) *ᵥ Qatlib.Foundations.PureStateMath.Ket x) (x, y)
        = (if y ∈ pairNeighbours N x then ((Real.sqrt (pairDegree N))⁻¹ : ℂ) else 0)) := by
  have hfam := pair_family_neighbour_program hN
  have htrans := pairGraph_nonLazyKernel_isTransition hN
  have happ := szegedyIsometry_pairGraph_apply hN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S
    exact hfam.1 S
  · intro S
    exact hfam.2.1 S
  · intro S
    exact hfam.2.2.1 S
  · intro S z hz
    exact hfam.2.2.2.1 S z hz
  · intro S p
    exact pairRowOracle_ne S p
  · exact hfam.2.2.2.2.1
  · exact htrans
  · intro x y
    exact happ x y

end PairFamilyMNRS
end Qatlib.Concepts.QuantumGibbs.FormAlgebra
