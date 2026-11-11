/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitDefs

/-!
# Kraus circuits and sequential instruments

This module relates a circuit performing two successive Kraus measurements to the sequential
composition of the corresponding instruments. It identifies every trace, its outcome record and
resources, and the event mass of any fixed pair of outcomes.

The general theorem `krausCircuit_totalMass` proves trace-mass preservation for well-formed
Kraus circuits with a unitary oracle. These results connect operational branch records with the
channel and instrument formalism of [Wilde2017].

## Main statements

* `twoStep_traces`: explicit traces of two successive Kraus measurements.
* `krausCircuit_totalMass`: preservation of total trace mass.
* `twoStep_mass`: circuit event masses agree with sequential instrument probabilities.

## References

* [Wilde, 2017][Wilde2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.InstrumentSeq.SeqAssoc.KrausSeqCircuitBridge
open Matrix

/-- Increment the gate count of a mixed branch trace by one. -/
private def updGate {d : ℕ} (t : Qatlib.Concepts.AdversaryBounds.AdvDuality.MixedBranchTrace d) : Qatlib.Concepts.AdversaryBounds.AdvDuality.MixedBranchTrace d :=
  {t with gates := t.gates + 1}

/-- Increment the query count of a mixed branch trace by one. -/
private def updQuery {d : ℕ} (t : Qatlib.Concepts.AdversaryBounds.AdvDuality.MixedBranchTrace d) : Qatlib.Concepts.AdversaryBounds.AdvDuality.MixedBranchTrace d :=
  {t with queries := t.queries + 1}

/-- Add two gates and one measurement to a mixed branch trace and prepend the outcome record
`(s, a)`. -/
private def updInst (s : ℕ) (a : ℕ) {d : ℕ} (t : Qatlib.Concepts.AdversaryBounds.AdvDuality.MixedBranchTrace d) : Qatlib.Concepts.AdversaryBounds.AdvDuality.MixedBranchTrace d :=
  {t with gates := t.gates + 2, measurements := t.measurements + 1, outcomes := (s, a) :: t.outcomes}

/-- Prepending a gate conjugates the input before evaluating the remaining circuit and
increments every resulting trace's gate count. -/
private theorem traces_step_gate {d s : ℕ} (O G : Qatlib.Foundations.PureStateMath.Operator d) (P : Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuit d s)
    (ρ : Qatlib.Foundations.PureStateMath.Operator d) :
    Qatlib.Concepts.AdversaryBounds.AdvDuality.krausCircuitMixedTraces O (.step (.gate G) P) ρ =
      (Qatlib.Concepts.AdversaryBounds.AdvDuality.krausCircuitMixedTraces O P (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch G ρ)).map updGate := rfl

/-- Prepending an oracle query conjugates the input by the oracle before evaluating the
remaining circuit and increments every resulting trace's query count. -/
private theorem traces_step_query {d s : ℕ} (O : Qatlib.Foundations.PureStateMath.Operator d) (P : Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuit d s)
    (ρ : Qatlib.Foundations.PureStateMath.Operator d) :
    Qatlib.Concepts.AdversaryBounds.AdvDuality.krausCircuitMixedTraces O (.step .query P) ρ =
      (Qatlib.Concepts.AdversaryBounds.AdvDuality.krausCircuitMixedTraces O P (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch O ρ)).map updQuery := rfl

/-- The traces of an instrument node are the flattened outcome continuations on their
Kraus-conjugated inputs, with each outcome and its resource costs recorded. -/
private theorem traces_instrument {d s : ℕ} (O : Qatlib.Foundations.PureStateMath.Operator d) (K : Fin s → Qatlib.Foundations.PureStateMath.Operator d)
    (next : Fin s → Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuit d s) (ρ : Qatlib.Foundations.PureStateMath.Operator d) :
    Qatlib.Concepts.AdversaryBounds.AdvDuality.krausCircuitMixedTraces O (.instrument K next) ρ =
      (List.ofFn fun a : Fin s =>
        (Qatlib.Concepts.AdversaryBounds.AdvDuality.krausCircuitMixedTraces O (next a) (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (K a) ρ)).map (updInst s a)).flatten := by
  simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.krausCircuitMixedTraces]
  rfl

/-- The circuit performing the Kraus measurements `K₁` and `K₂` successively and then accepting. -/
def twoStepCircuit {d s : ℕ} (K₁ K₂ : Fin s → Qatlib.Foundations.PureStateMath.Operator d) : Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuit d s :=
  .instrument K₁ fun _ => .instrument K₂ fun _ => .halt true

/-- The sequential instrument associated with two complete Kraus families, with outcomes indexed
by their ordered pair. -/
noncomputable def seqInstrument {d s : ℕ} (K₁ K₂ : Fin s → Qatlib.Foundations.PureStateMath.Operator d)
    (h₁ : ∑ a, (K₁ a).conjTranspose * K₁ a = 1)
    (h₂ : ∑ b, (K₂ b).conjTranspose * K₂ b = 1) :
    Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument (Fin s × Fin s) d d :=
  (Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.ofKraus K₁ h₁).seq (Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.ofKraus K₂ h₂)

/-- The branch for `(a, b)` applies Kraus conjugation by `K₁ a` and then by `K₂ b`. -/
@[simp] theorem seqInstrument_branch {d s : ℕ} (K₁ K₂ : Fin s → Qatlib.Foundations.PureStateMath.Operator d)
    (h₁ : ∑ a, (K₁ a).conjTranspose * K₁ a = 1)
    (h₂ : ∑ b, (K₂ b).conjTranspose * K₂ b = 1)
    (a b : Fin s) (ρ : Qatlib.Foundations.PureStateMath.Operator d) :
    (Qatlib.Concepts.InstrumentSeq.SeqAssoc.KrausSeqCircuitBridge.seqInstrument K₁ K₂ h₁ h₂).branch (a, b) ρ =
      Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (K₂ b) (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (K₁ a) ρ) := rfl

/-- The two-step circuit has one accepting trace for each outcome pair, with the composed Kraus
branch, zero queries, four gates, two measurements, and the ordered outcome record. -/
theorem twoStep_traces {d s : ℕ} (O : Qatlib.Foundations.PureStateMath.Operator d) (K₁ K₂ : Fin s → Qatlib.Foundations.PureStateMath.Operator d)
    (ρ : Qatlib.Foundations.PureStateMath.Operator d) :
    Qatlib.Concepts.AdversaryBounds.AdvDuality.krausCircuitMixedTraces O (Qatlib.Concepts.InstrumentSeq.SeqAssoc.KrausSeqCircuitBridge.twoStepCircuit K₁ K₂) ρ =
      (List.ofFn fun a : Fin s => (List.ofFn fun b : Fin s =>
        [Qatlib.Concepts.AdversaryBounds.AdvDuality.MixedBranchTrace.mk (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (K₂ b) (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (K₁ a) ρ)) true 0 4 2
          [(s, (a : ℕ)), (s, (b : ℕ))]]).flatten).flatten := by
  simp [Qatlib.Concepts.InstrumentSeq.SeqAssoc.KrausSeqCircuitBridge.twoStepCircuit,
      Qatlib.Concepts.AdversaryBounds.AdvDuality.krausCircuitMixedTraces, Function.comp_def, List.map_singleton]

/-- Mapping traces by a function that preserves their states preserves the sum of their masses. -/
private theorem mass_of_map_state {d : ℕ}
    (f : Qatlib.Concepts.AdversaryBounds.AdvDuality.MixedBranchTrace d → Qatlib.Concepts.AdversaryBounds.AdvDuality.MixedBranchTrace d) (hf : ∀ t, (f t).state = t.state)
    (L : List (Qatlib.Concepts.AdversaryBounds.AdvDuality.MixedBranchTrace d)) :
    ((L.map f).map Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass).sum = (L.map Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass).sum := by
  induction L with
  | nil => rfl
  | cons t L ih =>
      have hm : Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass (f t) = Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass t := by
        unfold Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass
        rw [hf t]
      simp only [List.map_cons, List.sum_cons, ih, hm]

/-- The total mass of a flattened list of trace lists equals the sum of their individual total
masses. -/
private theorem map_flatten_mass {d : ℕ} (l : List (List (Qatlib.Concepts.AdversaryBounds.AdvDuality.MixedBranchTrace d))) :
    List.sum (List.map Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass (List.flatten l)) =
      List.sum (List.map (fun x : List (Qatlib.Concepts.AdversaryBounds.AdvDuality.MixedBranchTrace d) => List.sum (List.map Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass x)) l) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      simp only [List.flatten_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, List.sum_nil, add_zero, ih]

/-- The real trace of Kraus conjugation by `M` equals the real trace of `X * (Mᴴ * M)`. -/
private theorem trace_conjBranch_eq {d : ℕ} (M X : Qatlib.Foundations.PureStateMath.Operator d) :
    (Matrix.trace (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch M X)).re =
      (Matrix.trace (X * (M.conjTranspose * M))).re := by
  calc (Matrix.trace (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch M X)).re
      = (Matrix.trace (M * X * M.conjTranspose)).re := by rw [Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch_apply]
    _ = (Matrix.trace (M.conjTranspose * (M * X))).re := by rw [Matrix.trace_mul_comm]
    _ = (Matrix.trace ((M.conjTranspose * M) * X)).re := by rw [Matrix.mul_assoc]
    _ = (Matrix.trace (X * (M.conjTranspose * M))).re := by rw [Matrix.trace_mul_comm]

/-- Summing the real trace masses of a complete Kraus family recovers the real trace of the
input operator. -/
private theorem sum_trace_conjBranch {d s : ℕ} (K : Fin s → Qatlib.Foundations.PureStateMath.Operator d)
    (hK : ∑ a, (K a).conjTranspose * K a = 1) (X : Qatlib.Foundations.PureStateMath.Operator d) :
    ∑ a, (Matrix.trace (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (K a) X)).re = (Matrix.trace X).re := by
  have hcomp : ∀ a : Fin s, (Matrix.trace (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (K a) X)).re =
      (Matrix.trace (X * ((K a).conjTranspose * K a))).re :=
    fun a => trace_conjBranch_eq (K a) X
  calc ∑ a, (Matrix.trace (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (K a) X)).re
      = ∑ a, (Matrix.trace (X * ((K a).conjTranspose * K a))).re :=
          Finset.sum_congr rfl fun a _ => hcomp a
    _ = (Matrix.trace (X * (∑ a, (K a).conjTranspose * K a))).re := by
          rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.mul_sum]
    _ = (Matrix.trace X).re := by rw [hK, Matrix.mul_one]

/-- For a unitary oracle and a well-formed Kraus circuit, the sum of all mixed-trace masses
equals the real trace of the input operator. -/
theorem krausCircuit_totalMass {d s : ℕ} (O : Qatlib.Foundations.PureStateMath.Operator d)
    (hO : O ∈ Matrix.unitaryGroup (Fin d) ℂ) (P : Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuit d s)
    (hP : Qatlib.Concepts.AdversaryBounds.AdvDuality.krausCircuitWellFormed P) (ρ : Qatlib.Foundations.PureStateMath.Operator d) :
    ((Qatlib.Concepts.AdversaryBounds.AdvDuality.krausCircuitMixedTraces O P ρ).map Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass).sum = (Matrix.trace ρ).re := by
  induction P generalizing ρ with
  | halt b => simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.krausCircuitMixedTraces, Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass]
  | step action P ih =>
      cases action with
      | gate G =>
          rw [traces_step_gate, mass_of_map_state updGate (fun _ => rfl) _]
          exact (ih hP.2 (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch G ρ)).trans
              (by rw [Qatlib.Concepts.AdaptiveCP.BranchTrace.trace_conjBranch_unitary G hP.1])
      | query =>
          rw [traces_step_query, mass_of_map_state updQuery (fun _ => rfl) _]
          exact (ih hP (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch O ρ)).trans
              (by rw [Qatlib.Concepts.AdaptiveCP.BranchTrace.trace_conjBranch_unitary O hO])
  | instrument K next ih =>
      obtain ⟨hK, hnext⟩ := hP
      rw [traces_instrument, map_flatten_mass, List.map_ofFn, List.sum_ofFn]
      show ∑ a : Fin s, ((List.map Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass
          (List.map (updInst s a) (Qatlib.Concepts.AdversaryBounds.AdvDuality.krausCircuitMixedTraces O (next a) (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (K a) ρ)))).sum) =
        (Matrix.trace ρ).re
      refine Eq.trans (Finset.sum_congr rfl fun a _ =>
        mass_of_map_state (updInst s a) (fun _ => rfl) _) ?_
      refine Eq.trans (Finset.sum_congr rfl fun a _ =>
        ih a (hnext a) (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (K a) ρ)) ?_
      exact sum_trace_conjBranch K hK ρ

/-- The event mass of a fixed ordered outcome record in the two-step circuit equals the
corresponding sequential-instrument branch probability. -/
theorem twoStep_mass {d s : ℕ} (O : Qatlib.Foundations.PureStateMath.Operator d) (K₁ K₂ : Fin s → Qatlib.Foundations.PureStateMath.Operator d)
    (h₁ : ∑ a, (K₁ a).conjTranspose * K₁ a = 1)
    (h₂ : ∑ b, (K₂ b).conjTranspose * K₂ b = 1)
    (ρ : Qatlib.Foundations.PureStateMath.Operator d) (a b : Fin s) :
    Qatlib.Concepts.AdversaryBounds.AdvDuality.krausCircuitEventMass O (Qatlib.Concepts.InstrumentSeq.SeqAssoc.KrausSeqCircuitBridge.twoStepCircuit K₁ K₂) ρ
        (fun _ rec => rec = [(s, (a : ℕ)), (s, (b : ℕ))]) =
      Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb (Qatlib.Concepts.InstrumentSeq.SeqAssoc.KrausSeqCircuitBridge.seqInstrument K₁ K₂ h₁ h₂) ρ (a, b) := by
  simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.krausCircuitEventMass, Qatlib.Concepts.InstrumentSeq.SeqAssoc.KrausSeqCircuitBridge.twoStep_traces, List.map_flatten,
    List.map_map, Function.comp_def, List.map_ofFn, List.sum_flatten,
    List.sum_ofFn, List.map_singleton, List.sum_cons, List.sum_nil,
    List.cons.injEq, Prod.mk.injEq, Fin.val_inj, and_true, true_and,
    eq_self_iff_true, true_and]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass,
        Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb, Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch_apply]
    · intro b' _ hb'
      simp [hb']
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  · intro a' _ ha'
    rw [Finset.sum_eq_zero]
    intro b' _
    simp [ha']
  · intro ha
    exact absurd (Finset.mem_univ a) ha

/-- Every trace of the two-step circuit uses zero queries, four gates, and two measurements, and
records an outcome pair with its composed Kraus-conjugated state. -/
theorem twoStep_records {d s : ℕ} (O : Qatlib.Foundations.PureStateMath.Operator d) (K₁ K₂ : Fin s → Qatlib.Foundations.PureStateMath.Operator d)
    (ρ : Qatlib.Foundations.PureStateMath.Operator d) (t : Qatlib.Concepts.AdversaryBounds.AdvDuality.MixedBranchTrace d)
    (ht : t ∈ Qatlib.Concepts.AdversaryBounds.AdvDuality.krausCircuitMixedTraces O (Qatlib.Concepts.InstrumentSeq.SeqAssoc.KrausSeqCircuitBridge.twoStepCircuit K₁ K₂) ρ) :
    t.queries = 0 ∧ t.gates = 4 ∧ t.measurements = 2 ∧
      ∃ a b : Fin s, t.outcomes = [(s, (a : ℕ)), (s, (b : ℕ))] ∧
        t.state = Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (K₂ b) (Qatlib.Concepts.AdaptiveCP.BranchTrace.conjBranch (K₁ a) ρ) := by
  rw [Qatlib.Concepts.InstrumentSeq.SeqAssoc.KrausSeqCircuitBridge.twoStep_traces] at ht
  obtain ⟨la, hla, hta⟩ := List.mem_flatten.mp ht
  obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hla
  obtain ⟨lb, hlb, htb⟩ := List.mem_flatten.mp hta
  obtain ⟨b, rfl⟩ := List.mem_ofFn.mp hlb
  simp only [List.mem_singleton] at htb
  subst htb
  exact ⟨rfl, rfl, rfl, a, b, rfl, rfl⟩

end Qatlib.Concepts.InstrumentSeq.SeqAssoc.KrausSeqCircuitBridge
