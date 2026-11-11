/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GenHidShift05.MainResults.MatrixSumCount
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Moments of the matrix-sum solution count (source Lemma 2, Appendix Eqs. 19–45)

Fixed source: A. M. Childs and W. van Dam, *Quantum algorithm for a generalized
hidden shift problem*, arXiv:quant-ph/0507190v1, §3 (Eqs. 16–19) and Appendix
"Number of solutions of the matrix sum problem" (Eqs. 40–53).

The source fixes `M = ⌊N^{1/k}⌋` and studies `η_w^x`, the number of
`b ∈ {0, …, M-1}^k` with `b · x = w mod N`, for uniformly random
`x ∈ (ZMod N)^k` and `w ∈ ZMod N`.  `solCount N M k x w` below is exactly
`η_w^x`, with the box `{0, …, M-1}^k` represented as `Fin k → Fin M` and the
entries read through the canonical representatives.

Formalised here are the exact finite identities the source uses to control
`η`, in the form the paper's Eqs. (19) and (40)–(45) state them:

* `sum_solCount` is Eq. (19)'s normalization `∑_w η_w^x = M^k` for every `x`;
* `sum_solCount_eq_card` is the resulting mean `μ = M^k / N`;
* `sum_sq_solCount_eq_pair_card` is the double count of Eqs. (40)–(43):
  `∑_{x,w} (η_w^x)^2 = ∑_{b,c} #{x : (b - c) · x = 0}`;
* `sum_sq_solCount_eq_gcd` substitutes source Lemma 4 to reach the gcd
  expression of Eq. (45).

The endpoint of the source's Lemma 2 — that `Pr(1 ≤ η ≤ 4)` is bounded below
by an absolute constant for `M = ⌊N^{1/k}⌋`, `k ≥ 3` and `N` large — needs the
variance lower bound, the Alon–Spencer zero-probability bound and the
asymptotic bookkeeping (`o(1)` terms), and is not formalised here.
-/

set_option autoImplicit false
noncomputable section

open Finset

namespace Qatlib.Papers.GenHidShift05.MainResults

variable {k M N : ℕ}

/-- The source "matrix sum" value `b · x` of a box point
`b ∈ {0, …, M-1}^k`, represented as `Fin k → Fin M`. -/
def boxDot (N M k : ℕ) (x : Fin k → ZMod N) (b : Fin k → Fin M) : ZMod N :=
  ∑ i, ((b i).val : ZMod N) * x i

/-- The source quantity `η_w^x` of Lemma 2: the number of box points
`b ∈ {0, …, M-1}^k` with `b · x = w mod N`. -/
def solCount (N M k : ℕ) (x : Fin k → ZMod N) (w : ZMod N) : ℕ :=
  Nat.card {b : Fin k → Fin M // boxDot N M k x b = w}

/-- The fiber of a map counts the indicator of that fiber: the cardinality of
`{a // f a = y}` is the sum of `if f a = y then 1 else 0`. -/
theorem card_fiber_eq_sum_indicator {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β)
    (y : β) :
    Nat.card {a : α // f a = y} = ∑ a : α, (if f a = y then 1 else 0) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]

/-- The pair-fiber count in indicator form: the number of pairs with equal
`f`-value is the double sum of the equality indicator. -/
theorem card_pair_eq_sum_indicator {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β) :
    Nat.card {p : α × α // f p.1 = f p.2}
      = ∑ b : α, ∑ c : α, (if f b = f c then 1 else 0) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    ← Finset.univ_product_univ, Finset.sum_product]

/-- The first-moment normalization of Eq. (16)/(19): for every `x`, the counts
`η_w^x` over all residues `w` add up to the size `M^k` of the box. -/
theorem sum_solCount [NeZero N] (x : Fin k → ZMod N) :
    ∑ w : ZMod N, solCount N M k x w = M ^ k := by
  classical
  have h := Nat.card_congr
    (Equiv.sigmaFiberEquiv (fun b : Fin k → Fin M => boxDot N M k x b)).symm
  rw [Nat.card_sigma] at h
  simp only [solCount]
  rw [← h, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin]

/-- The mean of `η` over uniformly random `x` and `w` is `M^k / N`, Eq. (19):
the sum of all counts is `N^k · M^k`. -/
theorem sum_solCount_eq_card [NeZero N] :
    ∑ x : Fin k → ZMod N, ∑ w : ZMod N, solCount N M k x w = N ^ k * M ^ k := by
  classical
  rw [Finset.sum_congr rfl fun x _ => sum_solCount x, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, ZMod.card, Fintype.card_fin, smul_eq_mul]

/-- The square of the fiber count at `w` is the number of ordered pairs of box
points whose matrix-sum value is `w`, written as a double indicator sum. -/
theorem sq_solCount_eq_sum (x : Fin k → ZMod N) (w : ZMod N) :
    (solCount N M k x w) ^ 2
      = ∑ b : Fin k → Fin M, ∑ c : Fin k → Fin M,
          (if boxDot N M k x b = w then 1 else 0) *
            (if boxDot N M k x c = w then 1 else 0) := by
  classical
  rw [solCount, card_fiber_eq_sum_indicator, pow_two, Finset.sum_mul_sum]

/-- A fixed matrix-sum value: `b · x = c · x` holds exactly when the difference
vector `(b - c)` pairs with `x` to zero.  This is the linear rewriting behind
the off-diagonal term of Eqs. (42)–(43). -/
theorem boxDot_eq_iff_sub :
    ∀ (x : Fin k → ZMod N) (b c : Fin k → Fin M),
      (boxDot N M k x b = boxDot N M k x c)
        ↔ ∑ i, (((b i).val : ZMod N) - ((c i).val : ZMod N)) * x i = 0 := by
  intro x b c
  have hlin : ∑ i, (((b i).val : ZMod N) - ((c i).val : ZMod N)) * x i
      = boxDot N M k x b - boxDot N M k x c := by
    simp only [boxDot]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => sub_mul _ _ _
  constructor
  · intro h
    rw [hlin, h, sub_self]
  · intro h
    rw [hlin] at h
    exact sub_eq_zero.mp h

/-- Eq. (42): over a single `x`, the sum of squared fiber counts is the number
of ordered box pairs with equal matrix-sum value. -/
theorem sum_sq_solCount_eq_card [NeZero N] (x : Fin k → ZMod N) :
    ∑ w : ZMod N, (solCount N M k x w) ^ 2
      = Nat.card {p : (Fin k → Fin M) × (Fin k → Fin M) //
          boxDot N M k x p.1 = boxDot N M k x p.2} := by
  classical
  rw [card_pair_eq_sum_indicator]
  have step : ∑ w : ZMod N, (solCount N M k x w) ^ 2
      = ∑ w : ZMod N, ∑ b : Fin k → Fin M, ∑ c : Fin k → Fin M,
          (if boxDot N M k x b = w then 1 else 0) *
            (if boxDot N M k x c = w then 1 else 0) :=
    Finset.sum_congr rfl fun w _ => sq_solCount_eq_sum x w
  rw [step, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : boxDot N M k x b = boxDot N M k x c
  · rw [if_pos h, Finset.sum_eq_single (boxDot N M k x b)]
    · rw [if_pos rfl, if_pos h.symm, one_mul]
    · intro w _ hw
      rw [if_neg (Ne.symm hw), zero_mul]
    · intro hw
      exact absurd (Finset.mem_univ _) hw
  · rw [if_neg h, Finset.sum_eq_zero]
    intro w _
    by_cases hb : boxDot N M k x b = w
    · rw [if_pos hb, if_neg (fun hc => h (hb.trans hc.symm)), mul_zero]
    · rw [if_neg hb, zero_mul]

/-- The off-diagonal reduction of Eqs. (43)–(45): summed over all `x` and `w`,
the squared solution count is the sum over box pairs `(b, c)` of the number of
`x` with `(b - c) · x = 0`. -/
theorem sum_sq_solCount_eq_pair_card [NeZero N] :
    ∑ x : Fin k → ZMod N, ∑ w : ZMod N, (solCount N M k x w) ^ 2
      = ∑ p : (Fin k → Fin M) × (Fin k → Fin M),
          Nat.card {x : Fin k → ZMod N //
            ∑ i, (((p.1 i).val : ZMod N) - ((p.2 i).val : ZMod N)) * x i = 0} := by
  classical
  have hx : ∀ x : Fin k → ZMod N, ∑ w : ZMod N, (solCount N M k x w) ^ 2
      = ∑ b : Fin k → Fin M, ∑ c : Fin k → Fin M,
          (if boxDot N M k x b = boxDot N M k x c then 1 else 0) := by
    intro x
    rw [sum_sq_solCount_eq_card x, card_pair_eq_sum_indicator]
  have hL : ∑ x : Fin k → ZMod N, ∑ w : ZMod N, (solCount N M k x w) ^ 2
      = ∑ b : Fin k → Fin M, ∑ c : Fin k → Fin M, ∑ x : Fin k → ZMod N,
          (if boxDot N M k x b = boxDot N M k x c then 1 else 0) := by
    rw [Finset.sum_congr rfl fun x _ => hx x, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_comm]
  have hR : (∑ p : (Fin k → Fin M) × (Fin k → Fin M),
        Nat.card {x : Fin k → ZMod N //
          ∑ i, (((p.1 i).val : ZMod N) - ((p.2 i).val : ZMod N)) * x i = 0})
      = ∑ b : Fin k → Fin M, ∑ c : Fin k → Fin M,
          Nat.card {x : Fin k → ZMod N //
            ∑ i, (((b i).val : ZMod N) - ((c i).val : ZMod N)) * x i = 0} := by
    conv_lhs => rw [← Finset.univ_product_univ]
    rw [Finset.sum_product]
  rw [hL, hR]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [card_fiber_eq_sum_indicator]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : boxDot N M k x b = boxDot N M k x c
  · rw [if_pos h, if_pos ((boxDot_eq_iff_sub x b c).mp h)]
  · rw [if_neg h, if_neg (fun hz => h ((boxDot_eq_iff_sub x b c).mpr hz))]

/-- Eqs. (43)–(45) with source Lemma 4 substituted: the total squared solution
count is the sum over box pairs of `N^(k-1) · gcd(b - c, N)`. -/
theorem sum_sq_solCount_eq_gcd [NeZero N] (hk : 0 < k) :
    ∑ x : Fin k → ZMod N, ∑ w : ZMod N, (solCount N M k x w) ^ 2
      = ∑ p : (Fin k → Fin M) × (Fin k → Fin M),
          N ^ (k - 1) * matrixGcd N
            (fun i => ((p.1 i).val : ZMod N) - ((p.2 i).val : ZMod N)) := by
  classical
  rw [sum_sq_solCount_eq_pair_card]
  refine Finset.sum_congr rfl ?_
  intro p _
  exact card_solutions hk (fun i => ((p.1 i).val : ZMod N) - ((p.2 i).val : ZMod N))

end Qatlib.Papers.GenHidShift05.MainResults
