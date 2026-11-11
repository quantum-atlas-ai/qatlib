/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Foundations.BornMetrics.EventProbability

/-!
# Finite gate words for initialization and parity

This module connects legal finite gate words to normalized output states and Born acceptance
probabilities. It gives an explicit CNOT word that computes classical parity into a clean extra
wire while preserving the input bits, using the standard circuit semantics of
[NielsenChuang2010].

## Main statements

* `finite_gate_initialized_run_born_acceptance`: legal words on initialized basis inputs produce
  normalized states and acceptance probabilities in `[0, 1]`.
* `finite_gate_parity_actual_clean_output_and_basic_cost`: the parity word uses `n` gates and
  zero queries, with exact output and deterministic parity readout.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.UniformBqp.FiniteGateWord
open Matrix
open scoped Classical
set_option maxHeartbeats 1000000

/-- Extends the `n` input bits `x` by `m` false ancillary bits. -/
def finiteInitializedBasis (n m : ℕ) (x : Reg n) : Reg (n + m) :=
  fun i => if h : i.val < n then x ⟨i.val, h⟩ else false

/-- The list of CNOT gates from each of the first `n` wires to the extra wire numbered `n`. -/
def finiteParityWord (n : ℕ) : List FiniteGateCode :=
  List.ofFn (fun i : Fin n => FiniteGateCode.cx i.val n)

/-- The Boolean XOR of all `n` input bits, starting from false. -/
def finiteParityValue (n : ℕ) (x : Reg n) : Bool := (List.ofFn x).foldl (· ^^ ·) false

/-- Running a legal finite gate word on the input basis state with false ancillas gives a
normalized state whose probability of observing true on wire `j` lies between zero and one. -/
theorem finite_gate_initialized_run_born_acceptance (n m : ℕ) (x : Reg n)
    (gs : List FiniteGateCode) (j : Fin (n + m)) (hg : finiteWordLegal (n + m) gs = true) :
    let ψ := Run (1 : Matrix (Reg (n + m)) (Reg (n + m)) ℂ)
      (finiteCodeCircuit (n + m) gs) (Ket (finiteInitializedBasis n m x))
    Normalized ψ ∧
    0 ≤ MeasureProb ψ (Finset.univ.filter (fun y : Reg (n + m) => y j = true)) ∧
    MeasureProb ψ (Finset.univ.filter (fun y : Reg (n + m) => y j = true)) ≤ 1 := by
  (try dsimp only)
  have hu := ((finite_gate_description_rejection_unitarity_and_counts (n + m) gs).2 hg).1
  have hn := normalized_run (1 : Matrix (Reg (n + m)) (Reg (n + m)) ℂ)
    (Matrix.unitaryGroup (Reg (n + m)) ℂ).one_mem _ hu (normalized_ket (finiteInitializedBasis n m x))
  exact ⟨hn, measureProb_nonneg _ _, measureProb_le_one hn _⟩

/-- The basis label consisting of the `n` input bits `x` followed by the bit `b`. -/
private def finiteParityState (n : ℕ) (x : Reg n) (b : Bool) : Reg (n + 1) :=
  fun j => if h : j.val < n then x ⟨j.val, h⟩ else b

/-- A CNOT from input wire `i` to the parity wire replaces `b` by `b ^^ x i` while preserving
the input bits. -/
private theorem finiteParity_step (n : ℕ) (x : Reg n) (b : Bool) (i : Fin n) :
    ApplyGate (finiteCodeMatrix (n + 1) (.cx i.val n)) (Ket (finiteParityState n x b)) =
      Ket (finiteParityState n x (b ^^ x i)) := by
  have hc : i.val < n + 1 := by omega
  have ht : n < n + 1 := by omega
  have hne : i.val ≠ n := by omega
  have hct : (⟨i.val, hc⟩ : Fin (n + 1)) ≠ ⟨n, ht⟩ :=
    fun hh => hne (congrArg Fin.val hh)
  rw [finiteCodeMatrix, dif_pos ⟨hc, ht, hne⟩, applyGate_cnotGate_ket _ _ _ hct]
  congr 1
  funext j
  by_cases hj : j = (⟨n, ht⟩ : Fin (n + 1))
  · subst j
    simp [Function.update_self, finiteParityState, i.isLt]
  · have hjn : j.val < n := by
      have hv : j.val ≠ n := fun hh => hj (Fin.ext hh)
      omega
    simp [Function.update_of_ne hj, finiteParityState, hjn]

/-- Running the CNOTs indexed by `is` on `finiteParityState n x b` accumulates the XOR of the
selected input bits into `b`. -/
private theorem finiteParity_list_run (n : ℕ) (x : Reg n) (is : List (Fin n)) (b : Bool) :
    Run (1 : Matrix (Reg (n + 1)) (Reg (n + 1)) ℂ)
      (finiteCodeCircuit (n + 1) (is.map (fun i => FiniteGateCode.cx i.val n)))
      (Ket (finiteParityState n x b)) =
      Ket (finiteParityState n x ((is.map x).foldl (· ^^ ·) b)) := by
  induction is generalizing b with
  | nil => simp [finiteCodeCircuit]
  | cons i is ih =>
    simp only [List.map_cons, finiteCodeCircuit, run_gate, List.foldl_cons]
    rw [finiteParity_step]
    exact ih (b ^^ x i)

/-- The probability of a finite event in basis state `Ket x` is one when `x` belongs to the
event and zero otherwise. -/
private theorem finiteMeasureProb_ket {I : Type*} [Fintype I] [DecidableEq I]
    (x : I) (S : Finset I) : MeasureProb (Ket x) S = if x ∈ S then 1 else 0 := by
  simp only [MeasureProb, bornProb_ket]
  simp

/-- The parity word is legal, uses zero queries and exactly `n` gates, and maps the initialized
input to the basis state containing `x` and its parity. Measuring true on the last wire has
probability one or zero according to that parity. -/
theorem finite_gate_parity_actual_clean_output_and_basic_cost (n : ℕ) (x : Reg n) :
    finiteWordLegal (n + 1) (finiteParityWord n) = true ∧
    QueryCount (finiteCodeCircuit (n + 1) (finiteParityWord n)) = 0 ∧
    GateCount (finiteCodeCircuit (n + 1) (finiteParityWord n)) = n ∧
    Run (1 : Matrix (Reg (n + 1)) (Reg (n + 1)) ℂ)
      (finiteCodeCircuit (n + 1) (finiteParityWord n)) (Ket (finiteInitializedBasis n 1 x)) =
      Ket (fun j : Fin (n + 1) => if h : j.val < n then x ⟨j.val, h⟩ else finiteParityValue n x) ∧
    MeasureProb (Run (1 : Matrix (Reg (n + 1)) (Reg (n + 1)) ℂ)
      (finiteCodeCircuit (n + 1) (finiteParityWord n)) (Ket (finiteInitializedBasis n 1 x)))
      (Finset.univ.filter (fun y : Reg (n + 1) => y (Fin.last n) = true)) =
      if finiteParityValue n x then 1 else 0 := by
  have hl : finiteWordLegal (n + 1) (finiteParityWord n) = true := by
    apply List.all_eq_true.mpr
    intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    simp only [finiteCodeLegal, decide_eq_true_eq]
    have hi := i.isLt
    omega
  have hcounts := (finite_gate_description_rejection_unitarity_and_counts (n + 1)
    (finiteParityWord n)).2 hl
  have hr : Run (1 : Matrix (Reg (n + 1)) (Reg (n + 1)) ℂ)
      (finiteCodeCircuit (n + 1) (finiteParityWord n)) (Ket (finiteInitializedBasis n 1 x)) =
      Ket (finiteParityState n x (finiteParityValue n x)) := by
    have hh := finiteParity_list_run n x (List.ofFn id) false
    simpa only [List.map_ofFn, Function.comp_id, finiteParityWord,
      finiteInitializedBasis, finiteParityState, finiteParityValue] using! hh
  refine ⟨hl, hcounts.2.1, ?_, hr, ?_⟩
  · simpa only [finiteParityWord, List.length_ofFn] using! hcounts.2.2
  · rw [hr, finiteMeasureProb_ket]
    cases finiteParityValue n x <;> simp [finiteParityState]
end Qatlib.Concepts.UniformBqp.FiniteGateWord
