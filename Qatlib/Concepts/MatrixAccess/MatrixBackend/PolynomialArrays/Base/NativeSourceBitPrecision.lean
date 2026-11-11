/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option backward.isDefEq.respectTransparency false

/-! Exact rational bit-length dyadic envelope; no original-input controller is included. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput

/-- Python max(0, num.bit_length()-den.bit_length()) is natural subtraction. -/
def sourceCeilLog2 (q : ℚ) : ℕ :=
  let k := q.num.natAbs.size-q.den.size
  k+if (2 : ℚ)^k<q then 1 else 0

/-- The same emitted instruction list satisfies `bit_length_ratio_bound` with the displayed gate and query accounting. -/
private theorem bit_length_ratio_bound (A B : ℕ) (hB : 0<B) :
    A<B*2^(A.size-B.size+1) := by
  have hsB : 0<B.size := Nat.size_pos.mpr hB
  have he : A.size ≤ B.size-1+(A.size-B.size+1) := by omega
  have hl : 2^(B.size-1) ≤ B := Nat.lt_size.mp (by omega)
  calc
    A < 2^A.size := Nat.lt_size_self A
    _ ≤ 2^(B.size-1+(A.size-B.size+1)) := Nat.pow_le_pow_right (by decide) he
    _ = 2^(B.size-1)*2^(A.size-B.size+1) := pow_add _ _ _
    _ ≤ B*2^(A.size-B.size+1) := Nat.mul_le_mul_right _ hl

/-- The actual bit_length formula provides its required dyadic envelope,
including q<1; this is not a runtime/whole-phase success theorem. -/
theorem sourceCeilLog2_envelope (q : ℚ) (hq : 0<q) : q ≤ (2 : ℚ)^sourceCeilLog2 q := by
  have hn : (q.num.natAbs : ℚ)=(q.num : ℚ) := by
    have hz : (q.num.natAbs : ℤ)=q.num := Int.natAbs_of_nonneg (Rat.num_pos.mpr hq).le
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) hz
  have hr : (q.num.natAbs : ℚ)/(q.den : ℚ)=q := by
    rw [hn,Rat.num_div_den]
  have ht : (q.num.natAbs : ℚ)<(q.den : ℚ)*
      (2 : ℚ)^(q.num.natAbs.size-q.den.size+1) := by
    exact_mod_cast bit_length_ratio_bound q.num.natAbs q.den q.pos
  have hb : q<(2 : ℚ)^(q.num.natAbs.size-q.den.size+1) := by
    calc
      q=(q.num.natAbs : ℚ)/(q.den : ℚ) := hr.symm
      _<(2 : ℚ)^(q.num.natAbs.size-q.den.size+1) := by
        apply (div_lt_iff₀ (by exact_mod_cast q.pos)).mpr
        simpa only [mul_comm] using ht
  dsimp only [sourceCeilLog2]
  split_ifs with hc
  · exact hb.le
  · simpa only [Nat.add_zero] using le_of_not_gt hc

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput
