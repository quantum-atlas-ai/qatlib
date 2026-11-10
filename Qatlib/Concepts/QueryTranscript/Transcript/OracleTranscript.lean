/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryTranscript.Transcript.OracleTranscriptDefs
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib
open Qatlib

set_option autoImplicit false
namespace Qatlib.Concepts.QueryTranscript.Transcript

private theorem trace_output_count {Query Output : Type} (A : Query → Bool)
    (T : BoolQueryTree Query Output) :
    (runTrace A T).1 = (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run A T).1 ∧
    (runTrace A T).2.length = (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run A T).2 ∧
    ∀ p ∈ (runTrace A T).2, p.2 = A p.1 := by
  induction T with
  | halt y => simp [runTrace, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run]
  | ask q no yes hn hy =>
    cases h : A q <;> simp_all [runTrace,
        Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run, Nat.add_comm]

theorem runTrace_refines_Run :
    ∀ (Query Output : Type) (A : Query → Bool) (T : BoolQueryTree Query Output),
      (runTrace A T).1 = (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run A T).1 ∧
      (runTrace A T).2.length = (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run A T).2 ∧
      (runTrace A T).2.length ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries T ∧
      ∀ p ∈ (runTrace A T).2, p.2 = A p.1 := by
  intro Query Output A T
  obtain ⟨hv,hc,ha⟩ := trace_output_count A T
  exact ⟨hv,hc,hc.trans_le (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.run_queries_le A T),ha⟩

theorem runTrace_readdress {Query Target Output : Type} (f : Query → Target)
    (A : Query → Bool) (B : Target → Bool) (h : ∀ q, B (f q) = A q)
    (T : BoolQueryTree Query Output) :
    runTrace B (readdress f T) =
      ((runTrace A T).1, (runTrace A T).2.map (fun p => (f p.1,p.2))) := by
  induction T with
  | halt y => rfl
  | ask q no yes hn hy =>
    cases ha : A q <;> simp [readdress, runTrace, h, ha, hn, hy]

theorem packedOracle_packAddress {n : ℕ} (S U : Reg n → Bool) (a : Bool × Reg n) :
    packedOracle S U (packAddress a) = pairOracle S U a := by
  simp [packedOracle, packAddress, pairOracle]

private theorem serialized_length {n : ℕ} (xs : List (Reg (n+1) × Bool)) :
    (xs.flatMap (fun p => List.ofFn p.1)).length = (n+1)*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_ofFn, List.length_cons, ih]
    ring

theorem packed_run_preserves_trace_and_serialized_bits :
    ∀ (n : ℕ) (Output : Type) (S U : Reg n → Bool)
      (T : BoolQueryTree (Bool × Reg n) Output),
    (runTrace (packedOracle S U) (readdress packAddress T)).1 =
        (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (pairOracle S U) T).1 ∧
    (runTrace (packedOracle S U) (readdress packAddress T)).2 =
        ((runTrace (pairOracle S U) T).2.map (fun p => (packAddress p.1,p.2))) ∧
    (runTrace (packedOracle S U) (readdress packAddress T)).2.length =
        (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (pairOracle S U) T).2 ∧
    ((runTrace (packedOracle S U) (readdress packAddress T)).2.flatMap
      (fun p => List.ofFn p.1)).length =
        (n+1)*(Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (pairOracle S U) T).2 := by
  intro n Output S U T
  have ht := runTrace_readdress packAddress (pairOracle S U) (packedOracle S U)
    (packedOracle_packAddress S U) T
  have hr := runTrace_refines_Run _ _ (pairOracle S U) T
  constructor
  · rw [ht]
    exact hr.1
  · constructor
    · exact congrArg Prod.snd ht
    · have hc : (runTrace (packedOracle S U) (readdress packAddress T)).2.length =
          (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (pairOracle S U) T).2 := by
        rw [ht, List.length_map]
        exact hr.2.1
      exact ⟨hc, (serialized_length _).trans (congrArg (fun k => (n+1)*k) hc)⟩

theorem runTrace_agrees_on_visited_queries :
    ∀ (Query Output : Type) (A B : Query → Bool) (T : BoolQueryTree Query Output),
      (∀ p ∈ (runTrace A T).2, A p.1 = B p.1) → runTrace B T = runTrace A T := by
  intro Query Output A B T
  induction T with
  | halt y => intro _; rfl
  | ask q no yes hn hy =>
    intro h
    cases ha : A q with
    | false =>
      have hb : B q = false := by
        simpa [runTrace, ha] using (h (q,false) (by simp [runTrace,ha])).symm
      have he := hn (fun p hp => h p (by simp [runTrace,ha,hp]))
      simpa [runTrace,ha,hb] using congrArg (fun r : Output × List (Query × Bool) =>
        (r.1,(q,false)::r.2)) he
    | true =>
      have hb : B q = true := by
        simpa [runTrace, ha] using (h (q,true) (by simp [runTrace,ha])).symm
      have he := hy (fun p hp => h p (by simp [runTrace,ha,hp]))
      simpa [runTrace,ha,hb] using congrArg (fun r : Output × List (Query × Bool) =>
        (r.1,(q,true)::r.2)) he

end Qatlib.Concepts.QueryTranscript.Transcript
