/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.DimConditioning.EventCondition.PaidRetry

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Matrix

variable {R : Type} [Fintype R] {N D : ℕ}

def Transcript (R : Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => R ⊕ (R × Transcript R n)

instance transcriptFintype : (n : ℕ) → Fintype (Transcript R n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 =>
    letI := transcriptFintype n
    inferInstanceAs (Fintype (R ⊕ (R × Transcript R n)))

def accepted : {n : ℕ} → Transcript R n → Bool
  | 0, _ => false
  | _ + 1, .inl _ => true
  | _ + 1, .inr (_, t) => accepted t

structure Leaf (R : Type) (D : ℕ) where
  map : Operator D →ₗ[ℂ] Operator D
  record : List (R × Bool)

def execute (I : Instrument (R × Bool) N D) (P : QuantumChannel D N) :
    {n : ℕ} → Transcript R n → Leaf R D
  | 0, _ => ⟨LinearMap.id, []⟩
  | _ + 1, .inl r => ⟨(I.branch (r, true)).comp P.map, [(r, true)]⟩
  | _ + 1, .inr (r, t) =>
    let tail := execute I P t
    ⟨tail.map.comp ((I.branch (r, false)).comp P.map), (r, false) :: tail.record⟩

theorem execute_cp (I : Instrument (R × Bool) N D) (P : QuantumChannel D N)
    {n : ℕ} (t : Transcript R n) : CompletelyPositive (execute I P t).map := by
  induction n with
  | zero => exact (QuantumChannel.id D).completelyPositive
  | succ n ih =>
    rcases t with r | ⟨r, t⟩
    · exact (I.cp (r, true)).comp P.completelyPositive
    · exact (ih t).comp ((I.cp (r, false)).comp P.completelyPositive)

theorem execute_total (I : Instrument (R × Bool) N D) (P : QuantumChannel D N)
    (n : ℕ) (A : Operator D) :
    trace (∑ t : Transcript R n, (execute I P t).map A) = trace A := by
  induction n generalizing A with
  | zero =>
    change trace (∑ _ : Unit, A) = trace A
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_nsmul]
  | succ n ih =>
    change trace (∑ t : R ⊕ (R × Transcript R n),
      (execute I P (n := n + 1) t).map A) = _
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [execute, LinearMap.comp_apply, trace_add, trace_sum]
    have htail (r : R) :
        (∑ t : Transcript R n, trace ((execute I P t).map (I.branch (r, false) (P.map A)))) =
          trace (I.branch (r, false) (P.map A)) := by
      rw [← trace_sum]
      exact ih _
    simp_rw [htail]
    have h := I.total (P.map A)
    rw [Fintype.sum_prod_type] at h
    simpa only [Fintype.sum_bool, trace_sum, trace_add, Finset.sum_add_distrib,
      add_comm] using h.trans (P.tracePreserving A)

def run (I : Instrument (R × Bool) N D) (P : QuantumChannel D N) (n : ℕ) :
    Instrument (Transcript R n) D D :=
  Instrument.ofBranches (fun t => (execute I P t).map) (execute_cp I P)
    (execute_total I P n)

def stopped (I : Instrument (R × Bool) N D) (P : QuantumChannel D N) (n : ℕ) :
    Instrument Bool D D := (run I P n).coarsen accepted

theorem record_length_le (I : Instrument (R × Bool) N D) (P : QuantumChannel D N)
    {n : ℕ} (t : Transcript R n) : (execute I P t).record.length ≤ n := by
  induction n with
  | zero => exact le_refl 0
  | succ n ih =>
    rcases t with r | ⟨r, t⟩
    · simp [execute]
    · exact Nat.succ_le_succ (ih t)

theorem exhausted_length (I : Instrument (R × Bool) N D) (P : QuantumChannel D N)
    {n : ℕ} (t : Transcript R n) (ht : accepted t = false) :
    (execute I P t).record.length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases t with r | ⟨r, t⟩
    · simp [accepted] at ht
    · simpa only [execute, List.length_cons] using congrArg Nat.succ (ih t ht)

theorem record_acceptance (I : Instrument (R × Bool) N D) (P : QuantumChannel D N)
    {n : ℕ} (t : Transcript R n) :
    ((execute I P t).record.map Prod.snd).getLast?.getD false = accepted t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases t with r | ⟨r, t⟩
    · rfl
    · simpa [execute, accepted, List.getLast?_cons] using ih t

structure Prices where
  prepare : ℕ
  measure : ℕ
  decide : ℕ

def charge (prices : Prices) (I : Instrument (R × Bool) N D) (P : QuantumChannel D N)
    {n : ℕ} (t : Transcript R n) : ℕ :=
  ((execute I P t).record.map fun _ => prices.prepare + prices.measure + prices.decide).sum

theorem charge_eq (prices : Prices) (I : Instrument (R × Bool) N D)
    (P : QuantumChannel D N) {n : ℕ} (t : Transcript R n) :
    charge prices I P t = (execute I P t).record.length *
      (prices.prepare + prices.measure + prices.decide) := by
  simp [charge]

theorem charge_le (prices : Prices) (I : Instrument (R × Bool) N D)
    (P : QuantumChannel D N) {n : ℕ} (t : Transcript R n) :
    charge prices I P t ≤ n * (prices.prepare + prices.measure + prices.decide) := by
  rw [charge_eq]
  exact Nat.mul_le_mul_right _ (record_length_le I P t)

end Qatlib.Concepts.DimConditioning.EventCondition.PaidRetry
