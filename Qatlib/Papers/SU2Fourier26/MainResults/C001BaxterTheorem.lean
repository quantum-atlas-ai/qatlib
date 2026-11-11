/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup.SourceNLFTModel

/-!
# Theorem 1: the `SU(2)`-Baxter theorem (c001)

Fixed source: arXiv:2603.02021v1 (2026-03-02), Theorem 1, p.3.

The theorem states: if `(a, b)` is the NLFT image of `F ∈ ℓ²(ℤ)` and `w` is a
strong Beurling weight, then

* (easy direction) `F ∈ ℓ¹_w` implies `a*, b ∈ A_w`;
* (converse) if `a*` is outer in `𝔻` and `b/a* ∈ A_w`, then `F ∈ ℓ¹_w`.

The easy direction is proved in the paper (§3.1, pp.6–7) from the multilinear
expansion (2.3)–(2.4): writing `b = ∑_n T_{2n+1}(F, …, F)`, the coefficient
estimate (2.5) together with the *weight comparison* `w(k) ≤ ∏_l w(j_l)` for the
alternating index sum `k = ∑_l (-1)^{l-1} j_l` (p.7, lines 385–391) yields
`‖b‖_{A_w} ≤ sinh ‖F‖_{ℓ¹_w}`.

This file formalizes the weight comparison step, which is the part of §3.1 that
turns the multilinear bound into a *weighted* bound.  The full statement of
Theorem 1 (both directions) is recorded below for reference:

```
theorem baxter_theorem_su2 (W : StrongBeurlingWeight) (F : ℤ → ℂ)
    (a b : CircleT → ℂ) (hF : MemL2 F) (himg : IsNLFTImage F a b) :
    (MemL1w W F → MemAW W (starFun a) ∧ MemAW W b) ∧
      (IsOuterInD W (starFun a) → MemAW W (fun x => b x / starFun a x) → MemL1w W F)
```

The remaining gap (not formalized here) is the multilinear expansion of the
infinite ordered product (1.1) and the converse direction (Baxter's trick plus
the `A_w` functional calculus); see the PR work record.
-/

open scoped BigOperators
open MeasureTheory Filter Topology

set_option autoImplicit false

open Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup

namespace Qatlib.Papers.SU2Fourier26.MainResults

noncomputable section

/-- Multiplicativity of a strong Beurling weight under multiplication by `±1`,
using the symmetry condition i (`w(-n) = w(n)`, p.2). -/
theorem weight_sign_mul (W : StrongBeurlingWeight) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (n : ℤ) : W.w (s * n) = W.w n := by
  rcases hs with rfl | rfl
  · simp
  · simp [W.symm n]

/-- The weight comparison of §3.1 of arXiv:2603.02021v1, p.7 (lines 385–391):
for a strong Beurling weight `w`, the weight of the alternating sum
`∑_{i} (-1)^i j_i` is dominated by the product `∏_i w(j_i)`.  This is exactly
the estimate that makes the multilinear expansion (2.3)–(2.5) a bound in the
weighted algebra `A_w`. -/
theorem weight_altSum_bound (W : StrongBeurlingWeight) :
    ∀ (N : ℕ) (J : Fin (N + 1) → ℤ),
      W.w (∑ i : Fin (N + 1), (-1 : ℤ) ^ (i : ℕ) * J i) ≤ ∏ i : Fin (N + 1), W.w (J i) := by
  intro N
  induction N with
  | zero => intro J; simp
  | succ N ih =>
    intro J
    rw [Fin.sum_univ_castSucc, Fin.prod_univ_castSucc]
    have hstep : W.w ((∑ i : Fin (N + 1), (-1 : ℤ) ^ (i : ℕ) * J i.castSucc)
        + (-1 : ℤ) ^ ((N + 1) : ℕ) * J (Fin.last (N + 1))) ≤
        W.w (∑ i : Fin (N + 1), (-1 : ℤ) ^ (i : ℕ) * J i.castSucc) *
          W.w ((-1 : ℤ) ^ ((N + 1) : ℕ) * J (Fin.last (N + 1))) := by
      have := W.submultiplicative (∑ i : Fin (N + 1), (-1 : ℤ) ^ (i : ℕ) * J i.castSucc)
        ((-1 : ℤ) ^ ((N + 1) : ℕ) * J (Fin.last (N + 1)))
      simpa [add_comm] using this
    have hsign : W.w ((-1 : ℤ) ^ ((N + 1) : ℕ) * J (Fin.last (N + 1))) =
        W.w (J (Fin.last (N + 1))) := by
      have hs : ((-1 : ℤ) ^ ((N + 1) : ℕ)) = 1 ∨ ((-1 : ℤ) ^ ((N + 1) : ℕ)) = -1 := by
        by_cases hN : (N + 1) % 2 = 0
        · left; rw [show (N + 1 : ℕ) = 2 * ((N + 1) / 2) by omega]; simp [pow_mul]
        · right; have hh : (N + 1 : ℕ) = 2 * ((N + 1) / 2) + 1 := by omega
          rw [hh, pow_succ, pow_mul]; simp
      exact weight_sign_mul W _ hs _
    rw [hsign] at hstep
    refine le_trans hstep ?_
    have hih := ih (fun i => J i.castSucc)
    have hnn : 0 ≤ W.w (J (Fin.last (N + 1))) := by
      have := W.one_le (J (Fin.last (N + 1))); linarith
    exact mul_le_mul_of_nonneg_right hih hnn

end

end Qatlib.Papers.SU2Fourier26.MainResults
