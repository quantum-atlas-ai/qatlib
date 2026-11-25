/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdiabHypergph12.SymmetrySector.Filter

@[expose] public section

/-!
# Normalization in the finite diagonal ground-state filter

The finite diagonal filter in the model for Appendix B, Eq. (B2), weights each coordinate by
a power of its eigenvalue. Each squared contribution is nonnegative. The zeroth coordinate
gives a strictly positive term under the stated assumptions, so normalization is defined.
-/

set_option autoImplicit false

open Qatlib.Papers.AdiabHypergph12.SymmetrySector

namespace Qatlib.Papers.AdiabHypergph12.SymmetrySector

/-- The finite diagonal filter has strictly positive normalized ground-coordinate weight
at each step when that coordinate starts nonzero and its eigenvalue is positive. -/
theorem groundWeight_pos {n : ℕ} (lam : Fin (n + 1) → ℝ) (v : Fin (n + 1) → ℝ)
    (h0 : 0 < lam 0) (hv : v 0 ≠ 0) (m : ℕ) :
    0 < groundWeight lam v m := by
  let term (i : Fin (n + 1)) := (lam i) ^ (2 * m) * (v i) ^ 2
  have hterm : 0 < term 0 := mul_pos (pow_pos h0 _) (sq_pos_of_ne_zero hv)
  have hsum : term 0 ≤ ∑ i, term i := by
    apply Finset.single_le_sum (f := term) _ (Finset.mem_univ 0)
    intro i _
    dsimp [term]
    rw [pow_mul]
    positivity
  exact div_pos hterm (hterm.trans_le hsum)

end Qatlib.Papers.AdiabHypergph12.SymmetrySector
