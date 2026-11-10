/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel.ReversibleOperationDefs

set_option autoImplicit false

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel

open Qatlib.Foundations.PureStateMath

theorem lemma1_tau_representable
    {n m w : ℕ} (F : Reg n → Reg m)
    (C : (Reg n × (Reg m × Reg w)) ≃ (Reg n × (Reg m × Reg w)))
    (hIn : ∀ u, (C (u, (ZeroStr m, ZeroStr w))).1 = u)
    (hY : ∀ u, (C (u, (ZeroStr m, ZeroStr w))).2.1 = F u)
    (B : RevBasis (Mem n m w))
    (sG : List (RevStep (Mem n m w)))
    (hG : ∀ x, runOps sG x = liftCore C x)
    (hGin : AllIn B sG)
    (hτ : B.mem (tauCopyEquiv n m w))
    (L : ℕ) (hL : seqCost sG = L) :
    ∃ s : List (RevStep (Mem n m w)),
      seqCost s = 2 * L + m ∧ AllIn B s ∧
        ∀ (u : Reg n) (v : Reg m),
          runOps s (u, v, ZeroStr m, ZeroStr w) =
            (u, bxor v (F u), ZeroStr m, ZeroStr w) := by
  refine ⟨sG ++ ([⟨tauCopyEquiv n m w, m⟩] ++ reverseSeq sG), ?_, ?_, ?_⟩
  · rw [seqCost_append, seqCost_append, seqCost_reverseSeq, hL]
    simp only [seqCost, Nat.add_zero]
    omega
  · exact allIn_append B hGin (allIn_append B (allIn_singleton B hτ) (allIn_reverseSeq B hGin))
  · intro u v

    have h1 : runOps sG (u, v, ZeroStr m, ZeroStr w) =
        (u, v, F u, (C (u, (ZeroStr m, ZeroStr w))).2.2) := by
      rw [hG]
      simp only [liftCore_apply]
      rw [hIn u]
      ext <;> simp [hY u]

    have h2 : tauCopy (u, v, F u, (C (u, (ZeroStr m, ZeroStr w))).2.2) =
        (u, bxor v (F u), F u, (C (u, (ZeroStr m, ZeroStr w))).2.2) := rfl

    have h3 : liftCore C (u, bxor v (F u), ZeroStr m, ZeroStr w) =
        (u, bxor v (F u), F u, (C (u, (ZeroStr m, ZeroStr w))).2.2) := by
      simp only [liftCore_apply]
      rw [hIn u]
      ext <;> simp [hY u]

    have h4 : runOps (reverseSeq sG)
        (u, bxor v (F u), F u, (C (u, (ZeroStr m, ZeroStr w))).2.2) =
        (u, bxor v (F u), ZeroStr m, ZeroStr w) := by
      rw [← h3]
      have hrev := runOps_reverseSeq sG (u, bxor v (F u), ZeroStr m, ZeroStr w)
      rw [hG] at hrev
      exact hrev
    calc runOps (sG ++ ([⟨tauCopyEquiv n m w, m⟩] ++ reverseSeq sG))
          (u, v, ZeroStr m, ZeroStr w)
        = runOps ([⟨tauCopyEquiv n m w, m⟩] ++ reverseSeq sG)
            (runOps sG (u, v, ZeroStr m, ZeroStr w)) := by rw [runOps_append]
      _ = runOps (reverseSeq sG)
            (runOps [⟨tauCopyEquiv n m w, m⟩]
              (runOps sG (u, v, ZeroStr m, ZeroStr w))) := by rw [runOps_append]
      _ = runOps (reverseSeq sG)
            (u, bxor v (F u), F u, (C (u, (ZeroStr m, ZeroStr w))).2.2) := by
            rw [h1]; simp [runOps, tauCopyEquiv_apply, tauCopy]
      _ = (u, bxor v (F u), ZeroStr m, ZeroStr w) := h4

end Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel
