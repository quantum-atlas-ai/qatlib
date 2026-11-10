/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel.ReversibleOperationDefs

set_option autoImplicit false

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel

open Qatlib.Foundations.PureStateMath

def lemma6Seq {n : ℕ} (U : Reg n ≃ Reg n) : List (RevStep (CtrlMem n)) :=
  [⟨lamTauABEquiv n, n⟩, ⟨lamTauBAEquiv n, n⟩, ⟨liftU U, 1⟩,
   ⟨lamTauBAEquiv n, n⟩, ⟨lamTauABEquiv n, n⟩]

theorem lemma6_controlled
    {n : ℕ} (U : Reg n ≃ Reg n) (hU0 : U (ZeroStr n) = ZeroStr n)
    (B : RevBasis (CtrlMem n))
    (hAB : B.mem (lamTauABEquiv n)) (hBA : B.mem (lamTauBAEquiv n))
    (hUB : B.mem (liftU U)) :
    seqCost (lemma6Seq U) = 4 * n + 1 ∧
      AllIn B (lemma6Seq U) ∧
      (∀ (a : Bool) (ξ : Reg n),
        runOps (lemma6Seq U) (a, ξ, ZeroStr n) =
          (a, if a then U ξ else ξ, ZeroStr n)) ∧
      lemma6Seq U =
        [⟨lamTauABEquiv n, n⟩, ⟨lamTauBAEquiv n, n⟩] ++
          [⟨liftU U, 1⟩] ++
          [⟨lamTauBAEquiv n, n⟩, ⟨lamTauABEquiv n, n⟩] := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · simp only [lemma6Seq, seqCost, Nat.add_zero]
    omega
  · intro t ht
    simp only [lemma6Seq, List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    exacts [hAB, hBA, hUB, hBA, hAB]
  · intro a ξ
    cases a
    · simp [lemma6Seq, runOps, lamTauAB, lamTauBA, liftU, hU0]
    · simp [lemma6Seq, runOps, lamTauAB, lamTauBA, liftU, bxor_zero_left,
        bxor_self]

end Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel
