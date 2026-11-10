/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
open Qatlib.Foundations.BornMetrics.EventProbability
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Matrix
set_option maxHeartbeats 1000000

inductive FiniteGateCode where
  | h : ℕ → FiniteGateCode
  | x : ℕ → FiniteGateCode
  | t : ℕ → FiniteGateCode
  | tdg : ℕ → FiniteGateCode
  | cx : ℕ → ℕ → FiniteGateCode
  deriving DecidableEq, Repr

def finiteCodeLegal (n : ℕ) : FiniteGateCode → Bool
  | .h w | .x w | .t w | .tdg w => decide (w < n)
  | .cx c t => decide (c < n ∧ t < n ∧ c ≠ t)

def finiteCodeAdjoint : FiniteGateCode → FiniteGateCode
  | .t w => .tdg w
  | .tdg w => .t w
  | g => g

def finiteWordAdjoint (gs : List FiniteGateCode) : List FiniteGateCode :=
  gs.reverse.map finiteCodeAdjoint

noncomputable def finiteCodeMatrix (n : ℕ) : FiniteGateCode → Matrix (Reg n) (Reg n) ℂ
  | .h w => if h : w < n then wireGate n ⟨w, h⟩ Hadamard else 1
  | .x w => if h : w < n then wireGate n ⟨w, h⟩ PauliX else 1
  | .t w => if h : w < n then wireGate n ⟨w, h⟩ tGate else 1
  | .tdg w => if h : w < n then wireGate n ⟨w, h⟩ tGateAdj else 1
  | .cx c t => if h : c < n ∧ t < n ∧ c ≠ t then cnotGate n ⟨c, h.1⟩ ⟨t, h.2.1⟩ else 1

noncomputable def finiteCodeCircuit (n : ℕ) (gs : List FiniteGateCode) : Circuit (Reg n) :=
  gs.map (fun g => Step.gate (finiteCodeMatrix n g))

def finiteWordLegal (n : ℕ) (gs : List FiniteGateCode) : Bool := gs.all (finiteCodeLegal n)

noncomputable def finiteWordRun (n : ℕ) (gs : List FiniteGateCode) (ψ : QState (Reg n)) :
    Option (QState (Reg n)) :=
  if finiteWordLegal n gs then some (Run (1 : Matrix (Reg n) (Reg n) ℂ) (finiteCodeCircuit n gs) ψ)
  else none

theorem finiteCodeMatrix_unitary (n : ℕ) (g : FiniteGateCode) (hg : finiteCodeLegal n g = true) :
    finiteCodeMatrix n g ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  cases g with
  | h w =>
    have hw : w < n := by simpa [finiteCodeLegal] using hg
    simpa [finiteCodeMatrix, hw] using wireGate_unitary n ⟨w, hw⟩ Hadamard hadamard_unitary
  | x w =>
    have hw : w < n := by simpa [finiteCodeLegal] using hg
    simpa [finiteCodeMatrix, hw] using wireGate_unitary n ⟨w, hw⟩ PauliX pauliX_unitary
  | t w =>
    have hw : w < n := by simpa [finiteCodeLegal] using hg
    simpa [finiteCodeMatrix, hw] using wireGate_unitary n ⟨w, hw⟩ tGate tGate_mem_unitary
  | tdg w =>
    have hw : w < n := by simpa [finiteCodeLegal] using hg
    simpa [finiteCodeMatrix, hw] using wireGate_unitary n ⟨w, hw⟩ tGateAdj tGateAdj_mem_unitary
  | cx c t =>
    have hw : c < n ∧ t < n ∧ c ≠ t := by simpa [finiteCodeLegal] using hg
    have hct : (⟨c, hw.1⟩ : Fin n) ≠ ⟨t, hw.2.1⟩ := fun hh => hw.2.2 (congrArg Fin.val hh)
    simpa [finiteCodeMatrix, hw] using cnotGate_unitary n ⟨c, hw.1⟩ ⟨t, hw.2.1⟩ hct

theorem finiteCodeCircuit_counts (n : ℕ) (gs : List FiniteGateCode) :
    QueryCount (finiteCodeCircuit n gs) = 0 ∧ GateCount (finiteCodeCircuit n gs) = gs.length := by
  induction gs with
  | nil => simp [finiteCodeCircuit]
  | cons g gs ih => simpa [finiteCodeCircuit, List.length_cons] using ih

theorem finite_gate_description_rejection_unitarity_and_counts (n : ℕ) (gs : List FiniteGateCode) :
    (∀ ψ : QState (Reg n), finiteWordLegal n gs = false → finiteWordRun n gs ψ = none) ∧
    (finiteWordLegal n gs = true → IsUnitaryCircuit (finiteCodeCircuit n gs) ∧
      QueryCount (finiteCodeCircuit n gs) = 0 ∧ GateCount (finiteCodeCircuit n gs) = gs.length) := by
  refine ⟨fun ψ hh => by simp [finiteWordRun, hh], fun hh => ⟨?_, finiteCodeCircuit_counts n gs⟩⟩
  intro U hU
  obtain ⟨g, hg, he⟩ := List.mem_map.mp hU
  injection he with he
  subst U
  exact finiteCodeMatrix_unitary n g ((List.all_eq_true.mp hh) g hg)

private theorem rz_conjTranspose_neg (θ : ℝ) : (Rz θ)ᴴ = Rz (-θ) := by
  rw [Rz, Matrix.diagonal_conjTranspose, Rz]
  congr 1
  funext b
  cases b
  · simp
  · change star (Complex.exp ((θ : ℂ) * Complex.I)) = Complex.exp ((-θ : ℝ) * Complex.I)
    rw [RCLike.star_def, ← Complex.exp_conj]
    simp

theorem finiteCodeAdjoint_spec (n : ℕ) (g : FiniteGateCode) (hg : finiteCodeLegal n g = true) :
    finiteCodeLegal n (finiteCodeAdjoint g) = true ∧
    finiteCodeMatrix n (finiteCodeAdjoint g) = (finiteCodeMatrix n g)ᴴ := by
  cases g with
  | h w =>
    have hw : w < n := by simpa [finiteCodeLegal] using hg
    simp [finiteCodeAdjoint, finiteCodeLegal, finiteCodeMatrix, hw,
      wireGate_conjTranspose, hadamard_conjTranspose]
  | x w =>
    have hw : w < n := by simpa [finiteCodeLegal] using hg
    have hx : PauliXᴴ = PauliX := by
      exact permMatrix_conjTranspose (fun b : Bool => by cases b <;> rfl)
    simp [finiteCodeAdjoint, finiteCodeLegal, finiteCodeMatrix, hw, wireGate_conjTranspose, hx]
  | t w =>
    have hw : w < n := by simpa [finiteCodeLegal] using hg
    simp [finiteCodeAdjoint, finiteCodeLegal, finiteCodeMatrix, hw, wireGate_conjTranspose,
      tGate, tGateAdj, rz_conjTranspose_neg]
  | tdg w =>
    have hw : w < n := by simpa [finiteCodeLegal] using hg
    simp [finiteCodeAdjoint, finiteCodeLegal, finiteCodeMatrix, hw, wireGate_conjTranspose,
      tGate, tGateAdj, rz_conjTranspose_neg]
  | cx c t =>
    have hw : c < n ∧ t < n ∧ c ≠ t := by simpa [finiteCodeLegal] using hg
    have hct : (⟨c, hw.1⟩ : Fin n) ≠ ⟨t, hw.2.1⟩ := fun hh => hw.2.2 (congrArg Fin.val hh)
    simp [finiteCodeAdjoint, finiteCodeLegal, finiteCodeMatrix, hw, cnotGate,
      permMatrix_conjTranspose (cnotUpdate_involutive n ⟨c, hw.1⟩ ⟨t, hw.2.1⟩ hct)]

private theorem finite_inverse_run (n : ℕ) (gs : List FiniteGateCode)
    (hg : finiteWordLegal n gs = true) (ψ : QState (Reg n)) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (finiteCodeCircuit n (finiteWordAdjoint gs))
      (Run (1 : Matrix (Reg n) (Reg n) ℂ) (finiteCodeCircuit n gs) ψ) = ψ := by
  induction gs generalizing ψ with
  | nil => simp [finiteWordAdjoint, finiteCodeCircuit]
  | cons g gs ih =>
    have hh : finiteCodeLegal n g = true ∧ finiteWordLegal n gs = true := by
      simpa [finiteWordLegal] using hg
    have he := (finiteCodeAdjoint_spec n g hh.1).2
    have hu := Matrix.mem_unitaryGroup_iff'.mp (finiteCodeMatrix_unitary n g hh.1)
    simp only [finiteWordAdjoint, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, finiteCodeCircuit, run_append, run_gate, Run]
    rw [show (gs.reverse.map finiteCodeAdjoint).map (fun g => Step.gate (finiteCodeMatrix n g)) =
      finiteCodeCircuit n (finiteWordAdjoint gs) from rfl]
    change ApplyGate (finiteCodeMatrix n (finiteCodeAdjoint g))
      (Run 1 (finiteCodeCircuit n (finiteWordAdjoint gs))
        (Run 1 (finiteCodeCircuit n gs) (ApplyGate (finiteCodeMatrix n g) ψ))) = ψ
    rw [ih hh.2, he, ← applyGate_mul]
    have hu' : (finiteCodeMatrix n g)ᴴ * finiteCodeMatrix n g = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using hu
    rw [hu', applyGate_one]

theorem finite_gate_word_paid_adjoint_semantics (n : ℕ) (gs : List FiniteGateCode)
    (ψ : QState (Reg n)) (hg : finiteWordLegal n gs = true) :
    finiteWordLegal n (finiteWordAdjoint gs) = true ∧
    (finiteWordAdjoint gs).length = gs.length ∧
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (finiteCodeCircuit n (gs ++ finiteWordAdjoint gs)) ψ = ψ ∧
    GateCount (finiteCodeCircuit n (gs ++ finiteWordAdjoint gs)) = 2 * gs.length := by
  refine ⟨?_, by simp [finiteWordAdjoint], ?_, ?_⟩
  · apply List.all_eq_true.mpr
    intro g hmem
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmem
    exact (finiteCodeAdjoint_spec n a ((List.all_eq_true.mp hg) a (List.mem_reverse.mp ha))).1
  · rw [finiteCodeCircuit, List.map_append, run_append]
    exact finite_inverse_run n gs hg ψ
  · rw [(finiteCodeCircuit_counts n _).2]
    simp [finiteWordAdjoint, two_mul]
end Qatlib.Concepts.GateVocabulary.FiniteGateDescription
