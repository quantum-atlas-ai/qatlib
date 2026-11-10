/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.AlphabetAdversary
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.HspRecovery.RecordExtract

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

noncomputable def alphabetAddressSwap {n a : ℕ} (j i : Fin n) :
    Equiv.Perm ((Fin n × ZMod a) × (Fin n → ZMod a)) :=
  (Equiv.swap j i).prodCongr (Equiv.refl (ZMod a)) |>.prodCongr (Equiv.refl _)

noncomputable def alphabetStoreSwap {n a : ℕ} (i : Fin n) :
    Equiv.Perm ((Fin n × ZMod a) × (Fin n → ZMod a)) where
  toFun p := ((p.1.1, p.2 i), Function.update p.2 i p.1.2)
  invFun p := ((p.1.1, p.2 i), Function.update p.2 i p.1.2)
  left_inv p := by ext k <;> simp [Function.update_idem]
  right_inv p := by ext k <;> simp [Function.update_idem]

noncomputable def alphabetInterrogationRound {n a : ℕ} [NeZero a] (j i : Fin n) :
    Circuit ((Fin n × ZMod a) × (Fin n → ZMod a)) :=
  [Step.gate (permMatrix (alphabetAddressSwap j i)), Step.query,
    Step.gate (permMatrix (alphabetStoreSwap i)), Step.gate (permMatrix (alphabetAddressSwap j i))]

noncomputable def alphabetInterrogationList {n a : ℕ} [NeZero a] (j : Fin n) :
    List (Fin n) → Circuit ((Fin n × ZMod a) × (Fin n → ZMod a))
  | [] => []
  | i :: is => alphabetInterrogationRound j i ++ alphabetInterrogationList j is

theorem alphabetInterrogationList_append {n a : ℕ} [NeZero a] (j : Fin n)
    (xs ys : List (Fin n)) :
    alphabetInterrogationList (a:=a) j (xs ++ ys) =
      alphabetInterrogationList j xs ++ alphabetInterrogationList j ys := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp only [List.cons_append, alphabetInterrogationList, ih, List.append_assoc]

private theorem alphabet_perm_ket {I : Type} [Fintype I] [DecidableEq I]
    (e : Equiv.Perm I) (j : I) : permMatrix e *ᵥ Qatlib.Foundations.PureStateMath.Ket j = Qatlib.Foundations.PureStateMath.Ket (e j) := by
  ext x
  simp [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, permMatrix]

private theorem alphabet_round_unitary {n a : ℕ} [NeZero a] (j i : Fin n) :
    IsUnitaryCircuit (alphabetInterrogationRound (a:=a) j i) := by
  have hA := permMatrix_unitary_of_injective (alphabetAddressSwap (a:=a) j i).injective
  have hS := permMatrix_unitary_of_injective (alphabetStoreSwap (a:=a) i).injective
  simp [alphabetInterrogationRound, hA, hS]

private theorem alphabet_round_run {n a : ℕ} [NeZero a] (j i : Fin n)
    (x s : Fin n → ZMod a) (hi : s i = 0) :
    Run (alphabetOracle x) (alphabetInterrogationRound j i) (Qatlib.Foundations.PureStateMath.Ket ((j, 0), s)) =
      Qatlib.Foundations.PureStateMath.Ket ((j, 0), Function.update s i (x i)) := by
  have ho : alphabetOracle x *ᵥ Qatlib.Foundations.PureStateMath.Ket ((i, 0), s) = Qatlib.Foundations.PureStateMath.Ket ((i, x i), s) := by
    change permMatrix (alphabetShift x) *ᵥ Qatlib.Foundations.PureStateMath.Ket ((i, 0), s) = _
    rw [alphabet_perm_ket]
    simp [alphabetShift]
  simp only [alphabetInterrogationRound, Run, ApplyGate]
  rw [alphabet_perm_ket]
  have hroute : alphabetAddressSwap (a:=a) j i ((j, 0), s) = ((i, 0), s) := by
    simp [alphabetAddressSwap, Equiv.prodCongr, Prod.map]
  rw [hroute]
  rw [ho, alphabet_perm_ket]
  simp only [alphabetStoreSwap, Equiv.coe_fn_mk, hi]
  rw [alphabet_perm_ket]
  simp [alphabetAddressSwap, Equiv.prodCongr, Prod.map]

theorem alphabetInterrogationList_run {n a : ℕ} [NeZero a] (j : Fin n)
    (is : List (Fin n)) (hn : is.Nodup) (x s : Fin n → ZMod a)
    (hz : ∀ i ∈ is, s i = 0) :
    Run (alphabetOracle x) (alphabetInterrogationList j is) (Qatlib.Foundations.PureStateMath.Ket ((j, 0), s)) =
      Qatlib.Foundations.PureStateMath.Ket ((j, 0), fun k => if k ∈ is then x k else s k) := by
  induction is generalizing s with
  | nil => simp [alphabetInterrogationList]
  | cons i is ih =>
    have hnot := (List.nodup_cons.mp hn).1
    rw [alphabetInterrogationList, run_append, alphabet_round_run j i x s (hz i (by simp))]
    rw [ih (List.nodup_cons.mp hn).2 _ (by
      intro k hk
      have hki : k ≠ i := by intro h; subst k; exact hnot hk
      simp [Function.update, hki, hz k (by simp [hk])])]
    apply congrArg (fun s => Qatlib.Foundations.PureStateMath.Ket ((j, 0), s))
    funext k
    by_cases hki : k = i
    · subst k; simp [hnot]
    · simp [hki, Function.update]

theorem alphabetInterrogationList_resources {n a : ℕ} [NeZero a] (j : Fin n) (is : List (Fin n)) :
    IsUnitaryCircuit (alphabetInterrogationList (a:=a) j is) ∧
    QueryCount (alphabetInterrogationList (a:=a) j is) = is.length ∧
    GateCount (alphabetInterrogationList (a:=a) j is) = 3 * is.length := by
  induction is with
  | nil => simp [alphabetInterrogationList]
  | cons i is ih =>
    refine ⟨(isUnitaryCircuit_append _ _).mpr ⟨alphabet_round_unitary j i, ih.1⟩, ?_, ?_⟩
    · simp [alphabetInterrogationList, alphabetInterrogationRound, QueryCount, ih.2.1]
    · simp [alphabetInterrogationList, alphabetInterrogationRound, GateCount, ih.2.2]; omega

theorem alphabet_interrogation_actual_output_and_counts (n a : ℕ) [NeZero a] (hn : 0 < n) :
    ∃ (C : Circuit ((Fin n × ZMod a) × (Fin n → ZMod a)))
      (j : (Fin n × ZMod a) × (Fin n → ZMod a)),
      IsUnitaryCircuit C ∧ QueryCount C = n ∧ GateCount C ≤ 3 * n + 1 ∧
      ∀ x : Fin n → ZMod a, MeasureProb (Run (alphabetOracle x) C (Qatlib.Foundations.PureStateMath.Ket j))
        (Finset.univ.filter (fun p => p.2 = x)) = 1 := by
  let j : Fin n := ⟨0, hn⟩
  let is := (Finset.univ : Finset (Fin n)).toList
  obtain ⟨hC, hq, hg⟩ := alphabetInterrogationList_resources (a:=a) j is
  refine ⟨alphabetInterrogationList j is, ((j, 0), fun _ => 0), hC, ?_, ?_, ?_⟩
  · simpa [is] using hq
  · simp [hg, is]
  · intro x
    rw [alphabetInterrogationList_run j is (Finset.nodup_toList _) x (fun _ => 0) (by simp)]
    have he : (fun k : Fin n => if k ∈ is then x k else (0 : ZMod a)) = x := by
      ext k; simp [is]
    rw [he]
    simp only [MeasureProb, BornProb, Qatlib.Foundations.PureStateMath.Ket]
    rw [Finset.sum_eq_single ((j, 0), x)]
    · simp
    · intro p _ hp; simp [hp]
    · simp

end Qatlib.Concepts.QueryComplexity.DegreeMethod
