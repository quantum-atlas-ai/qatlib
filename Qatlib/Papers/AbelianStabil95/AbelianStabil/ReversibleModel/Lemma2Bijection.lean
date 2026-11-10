/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel.ReversibleOperationDefs

set_option autoImplicit false

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel

open Qatlib.Foundations.PureStateMath

theorem lemma2_representable
    {n : ℕ} (G : Reg n ≃ Reg n) (L L' : ℕ)
    (B : RevBasis (Reg n × Reg n))
    (sG : List (RevStep (Reg n × Reg n)))
    (hG : ∀ p, runOps sG p = Ftau (fun u => G u) p)
    (hGin : AllIn B sG)
    (hGc : seqCost sG = 2 * L + n)
    (sGi : List (RevStep (Reg n × Reg n)))
    (hGi : ∀ p, runOps sGi p = (bxor p.1 (G.symm p.2), p.2))
    (hGiin : AllIn B sGi)
    (hGic : seqCost sGi = 2 * L' + n)
    (hτXY : B.mem (copyXYEquiv n))
    (hτYX : B.mem (copyYXEquiv n)) :
    ∃ s : List (RevStep (Reg n × Reg n)),
      seqCost s = 2 * L + 2 * L' + 4 * n ∧ AllIn B s ∧
        ∀ x : Reg n, runOps s (x, ZeroStr n) = (G x, ZeroStr n) := by
  refine ⟨sG ++ (sGi ++ [⟨copyYXEquiv n, n⟩, ⟨copyXYEquiv n, n⟩]), ?_, ?_, ?_⟩
  · rw [seqCost_append, seqCost_append, hGc, hGic]
    simp only [seqCost, Nat.add_zero]
    omega
  · refine allIn_append B hGin (allIn_append B hGiin ?_)
    exact allIn_append B (allIn_singleton B hτYX) (allIn_singleton B hτXY)
  · intro x

    have h1 : runOps sG (x, ZeroStr n) = (x, G x) := by
      rw [hG]
      simp [Ftau, bxor_zero_left]

    have h2 : runOps sGi (x, G x) = (ZeroStr n, G x) := by
      rw [hGi]
      simp [bxor_self]
    calc runOps (sG ++ (sGi ++ [⟨copyYXEquiv n, n⟩, ⟨copyXYEquiv n, n⟩]))
          (x, ZeroStr n)
        = runOps (sGi ++ [⟨copyYXEquiv n, n⟩, ⟨copyXYEquiv n, n⟩])
            (runOps sG (x, ZeroStr n)) := by rw [runOps_append]
      _ = runOps [⟨copyYXEquiv n, n⟩, ⟨copyXYEquiv n, n⟩]
            (runOps sGi (runOps sG (x, ZeroStr n))) := by rw [runOps_append]
      _ = runOps [⟨copyYXEquiv n, n⟩, ⟨copyXYEquiv n, n⟩] (ZeroStr n, G x) := by
            rw [h1, h2]
      _ = (G x, ZeroStr n) := by
            rw [runOps_pair]
            simp [copyYX, copyXY, bxor_zero_left, bxor_self]

end Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel
