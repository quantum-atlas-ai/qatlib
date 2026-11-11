/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel.ReversibleOperationDefs

/-!
# Controlling a reversible operation fixing zero

`lemma6Seq` surrounds one lifted reversible operation by four controlled register-copy blocks.
If the operation fixes the zero string, `lemma6_controlled` proves that this sequence applies it
conditionally, restores the auxiliary register, and has cost `4 * n + 1` in the specified basis.
The development follows [Kitaev1995].

## Main statements

* `lemma6_controlled`: establishes controlled execution, basis membership, and exact cost.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option autoImplicit false

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel

open Qatlib.Foundations.PureStateMath

/-- The five-block sequence of two controlled XOR copies, one lifted use of `U`, and the two
copies in reverse order. -/
def lemma6Seq {n : ℕ} (U : Reg n ≃ Reg n) : List (RevStep (CtrlMem n)) :=
  [⟨lamTauABEquiv n, n⟩, ⟨lamTauBAEquiv n, n⟩, ⟨liftU U, 1⟩,
   ⟨lamTauBAEquiv n, n⟩, ⟨lamTauABEquiv n, n⟩]

/-- If `U` fixes the zero string and the three operation types belong to the basis, `lemma6Seq
U` implements controlled `U` on a zero-initialized auxiliary register at cost `4 * n + 1`.
It also records basis membership and the block decomposition, as in [Kitaev, 1995, Lemma
6][Kitaev1995]. -/
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
