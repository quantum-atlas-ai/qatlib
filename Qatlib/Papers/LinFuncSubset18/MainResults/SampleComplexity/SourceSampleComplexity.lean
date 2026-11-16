/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LinFuncSubset18.MainResults.Core.SourceCore
public import Mathlib.Tactic

@[expose] public section


/-! Closed source mathematics; paper algorithm claims retain their separate obligations. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.LinFuncSubset18.MainResults.SampleComplexity
variable {n d : ℕ}

/-- Elementary bound used by the proof of Theorem 1.3 (arXiv:1806.09660v1,
page 4), citing Theorem 3.2 (page 11): at the Theorem 3.2 sample size,
`C(n+d,d) · d² · (log C(n+d,d) + 1) ≤ (n+d)^{3d}` for `2 ≤ d`. -/
lemma choose_d_sq_log_bound (hd : 2 ≤ d) :
    (n + d).choose d * d ^ 2 * (Nat.log 2 ((n + d).choose d) + 1) ≤
      (n + d) ^ (3 * d) := by
  have hchoose : (n + d).choose d ≤ (n + d) ^ d := Nat.choose_le_pow (n + d) d
  have hlog : Nat.log 2 ((n + d).choose d) ≤ (n + d) ^ d :=
    (Nat.log_le_self 2 _).trans hchoose
  have hd2 : d ^ 2 ≤ (n + d) ^ d := by
    have h1 : d ≤ n + d := Nat.le_add_left d n
    have h2 : d ^ 2 ≤ (n + d) ^ 2 := Nat.pow_le_pow_left h1 2
    have h4 : (n + d) ^ 2 ≤ (n + d) ^ d :=
      Nat.pow_le_pow_right (by omega) hd
    exact h2.trans h4
  have hcne : (n + d).choose d ≠ 0 :=
    (Nat.choose_pos (Nat.le_add_left d n)).ne'
  have hlog1 : Nat.log 2 ((n + d).choose d) + 1 ≤ (n + d) ^ d := by
    have hlt : Nat.log 2 ((n + d).choose d) < (n + d).choose d :=
      Nat.log_lt_self 2 hcne
    exact (Nat.succ_le_of_lt hlt).trans hchoose
  calc (n + d).choose d * d ^ 2 * (Nat.log 2 ((n + d).choose d) + 1)
      ≤ (n + d) ^ d * (n + d) ^ d * (n + d) ^ d := by gcongr
    _ = (n + d) ^ (d + d + d) := by rw [← pow_add, ← pow_add]
    _ = (n + d) ^ (3 * d) := by rw [show d + d + d = 3 * d by omega]

end Qatlib.Papers.LinFuncSubset18.MainResults.SampleComplexity
