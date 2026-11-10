/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsExt
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.ECDLPResource17.ResourceDefs

open Qatlib.Concepts.ResourceBounds.AsymBounds
open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs

def qubitCount (n : ℕ) : ℕ := 9 * n + 2 * Nat.clog 2 n + 10

theorem clog_two_le_self {n : ℕ} : Nat.clog 2 n ≤ n := by
  rw [Nat.clog_le_iff_le_pow (by norm_num)]
  exact Nat.le_of_lt Nat.lt_two_pow_self

theorem qubitCount_le_linear (n : ℕ) :
    qubitCount n ≤ 9 * n + 2 * n + 10 := by
  unfold qubitCount
  have h := clog_two_le_self (n := n)
  omega

theorem qubitCount_P256 : qubitCount 256 = 2330 := by
  unfold qubitCount
  have hlog : Nat.clog 2 256 = 8 := by
    rw [show (256 : ℕ) = 2 ^ 8 by norm_num, Nat.clog_pow _ _ (by norm_num)]
  rw [hlog]

noncomputable def pointAddToffoli (n : ℕ) (L : ℝ) : ℝ :=
  224 * (n : ℝ) ^ 2 * L + 2045 * (n : ℝ) ^ 2

noncomputable def shorToffoli (n : ℕ) (L : ℝ) : ℝ :=
  448 * (n : ℝ) ^ 3 * L + 4090 * (n : ℝ) ^ 3

theorem shorToffoli_eq_two_n_mul_pointAddToffoli (n : ℕ) (L : ℝ) :
    (2 * (n : ℝ)) * pointAddToffoli n L = shorToffoli n L := by
  unfold pointAddToffoli shorToffoli
  ring

theorem repeat_basicGates_two_n (pa : Account) (n : ℕ) :
    (Account.repeat pa (2 * n)).basicGates = (2 * n) * pa.basicGates :=
  repeat_basicGates pa (2 * n)

theorem repeat_livePeak_le (a : Account) (k : ℕ) :
    (Account.repeat a k).livePeak ≤ a.livePeak := by
  induction k with
  | zero => simp [Account.repeat, Account.zero]
  | succ k ih =>
      show (Account.seq a (Account.repeat a k)).livePeak ≤ a.livePeak
      rw [seq_livePeak]
      exact max_le le_rfl ih

theorem shor_qubits_reuse (pa : Account) (n : ℕ) :
    (Account.repeat pa (2 * n)).livePeak ≤ pa.livePeak :=
  repeat_livePeak_le pa (2 * n)

theorem shor_depth_repeat (pa : Account) (n : ℕ) :
    (Account.repeat pa (2 * n)).depth = (2 * n) * pa.depth :=
  repeat_depth pa (2 * n)

theorem shor_toffoli_via_repeat (n : ℕ) (pa : Account) (L : ℝ)
    (hpa : (pa.basicGates : ℝ) ≤ pointAddToffoli n L) :
    ((Account.repeat pa (2 * n)).basicGates : ℝ) ≤ shorToffoli n L := by
  rw [repeat_basicGates]
  have hcast :
      (((2 * n) * pa.basicGates : ℕ) : ℝ) = (2 * (n : ℝ)) * (pa.basicGates : ℝ) := by
    push_cast
    ring
  rw [hcast]
  calc
    (2 * (n : ℝ)) * (pa.basicGates : ℝ)
        ≤ (2 * (n : ℝ)) * pointAddToffoli n L := by
          exact mul_le_mul_of_nonneg_left hpa (by positivity)
    _ = shorToffoli n L := shorToffoli_eq_two_n_mul_pointAddToffoli n L

end Qatlib.Papers.ECDLPResource17.ResourceDefs
