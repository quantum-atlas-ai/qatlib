/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel.ReversibleOperationDefs

set_option autoImplicit false

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel

open Qatlib.Foundations.PureStateMath

def lemma7Seq {k l n w : ℕ} (U : Reg l → Reg n ≃ Reg n)
    (sG : List (RevStep (FunMem k l n w))) : List (RevStep (FunMem k l n w)) :=
  sG ++ ([⟨ctrlFun U, 1⟩] ++ reverseSeq sG)

theorem lemma7_controlled_function
    {k l n w : ℕ} (F : Reg k → Reg l) (U : Reg l → Reg n ≃ Reg n)
    (C : (Reg k × (Reg l × Reg w)) ≃ (Reg k × (Reg l × Reg w)))
    (hIn : ∀ a, (C (a, (ZeroStr l, ZeroStr w))).1 = a)
    (hY : ∀ a, (C (a, (ZeroStr l, ZeroStr w))).2.1 = F a)
    (B : RevBasis (FunMem k l n w))
    (sG : List (RevStep (FunMem k l n w)))
    (hG : ∀ x, runOps sG x = liftFunG C x)
    (hGin : AllIn B sG)
    (hT : B.mem (ctrlFun U))
    (L : ℕ) (hL : seqCost sG = L) :
    seqCost (lemma7Seq U sG) = 2 * L + 1 ∧
      AllIn B (lemma7Seq U sG) ∧
      (∀ (a : Reg k) (ξ : Reg n),
        runOps (lemma7Seq U sG) (a, ξ, ZeroStr l, ZeroStr w) =
          (a, U (F a) ξ, ZeroStr l, ZeroStr w)) ∧
      lemma7Seq U sG = sG ++ ([⟨ctrlFun U, 1⟩] ++ reverseSeq sG) := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · rw [lemma7Seq, seqCost_append, seqCost_append, seqCost_reverseSeq, hL]
    simp only [seqCost, Nat.add_zero]
    omega
  · refine allIn_append B hGin (allIn_append B (allIn_singleton B hT) (allIn_reverseSeq B hGin))
  · intro a ξ

    have h1 : runOps sG (a, ξ, ZeroStr l, ZeroStr w) =
        (a, ξ, F a, (C (a, (ZeroStr l, ZeroStr w))).2.2) := by
      rw [hG]
      simp only [liftFunG_apply]
      rw [hIn a, hY a]

    have h2 : ctrlFun U (a, ξ, F a, (C (a, (ZeroStr l, ZeroStr w))).2.2) =
        (a, U (F a) ξ, F a, (C (a, (ZeroStr l, ZeroStr w))).2.2) := rfl

    have h3 : liftFunG C (a, U (F a) ξ, ZeroStr l, ZeroStr w) =
        (a, U (F a) ξ, F a, (C (a, (ZeroStr l, ZeroStr w))).2.2) := by
      simp only [liftFunG_apply]
      rw [hIn a, hY a]

    have h4 : runOps (reverseSeq sG)
        (a, U (F a) ξ, F a, (C (a, (ZeroStr l, ZeroStr w))).2.2) =
        (a, U (F a) ξ, ZeroStr l, ZeroStr w) := by
      rw [← h3]
      have hrev := runOps_reverseSeq sG (a, U (F a) ξ, ZeroStr l, ZeroStr w)
      rw [hG] at hrev
      exact hrev
    calc runOps (lemma7Seq U sG) (a, ξ, ZeroStr l, ZeroStr w)
        = runOps ([⟨ctrlFun U, 1⟩] ++ reverseSeq sG)
            (runOps sG (a, ξ, ZeroStr l, ZeroStr w)) := by
          rw [lemma7Seq, runOps_append]
      _ = runOps (reverseSeq sG)
            (runOps [⟨ctrlFun U, 1⟩] (runOps sG (a, ξ, ZeroStr l, ZeroStr w))) := by
          rw [runOps_append]
      _ = runOps (reverseSeq sG)
            (a, U (F a) ξ, F a, (C (a, (ZeroStr l, ZeroStr w))).2.2) := by
          rw [h1]; simp [runOps, ctrlFun]
      _ = (a, U (F a) ξ, ZeroStr l, ZeroStr w) := h4

end Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel
