/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamLCUSim12.TaylorBounds.DefectOrder
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Lemma 8 — the printed error bound for the `k = χ` multi-product

Fixed source: Childs and Wiebe, arXiv:1202.5822v1, Lemma 8, Eq. (39):
for `M_{k,k}(λ)` as in Definition 1 with `|C_q| ≤ 2` and
`hλ ≤ 3 log 2 / (4 m k (5/3)^{k-1})`, one has
`‖U(λ) − M_{k,k}(λ)‖ ≤ (2 m (5/3)^{k-1} h λ)^{4k+1}`.

The source proof combines three ingredients: (i) the moment cancellation of
Lemma 4 at `χ = k` (formalized as `multiproduct_order_at`), (ii) the
evolution-side Taylor remainder bound `‖Rem_{4k}(U(λ))‖ < ((4/3) m (5/3)^{k-1}
hλ)^{4k+1}` (from Lemma 9, Eq. (R4kU)), and (iii) the per-word remainder
bound `‖Rem_{4k}(S_k(λ/p)^p)‖ ≤ (2/5!) ((4/3) m (5/3)^{k-1} hλ)^{4k+1}`
(Eq. (Skremainder), folding in the Suzuki time-ratio input `q_{k,ℓ} ≤ 2k/3^k`
and the factorial bound `(4k+1)! ≥ 5!·k^{4k+1}`).

This module takes (ii)+(iii) bundled as the per-node defect bound with
constant `(61/60)·((4/3)·m·(5/3)^{k-1}·h)^{4k+1}` and derives the printed
final bound: the coefficient mass `Σ_q |C_q| ≤ 2(k+1)` gives the intermediate
`2(k+1)(61/60)(4/3)^{4k+1}`, which the geometric decay `(2/3)^{4k+1}`
dominates back to the printed `(2 m (5/3)^{k-1} h λ)^{4k+1}`.

This is a conditional coefficient-combination estimate. The Taylor defect
`hdef` is assumed, rather than derived from a Suzuki product or from the
source small-time regime.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.HamLCUSim12.FullSimulation.Lemma8Bound

open Qatlib.Papers.HamLCUSim12.TaylorBounds
open Qatlib.Papers.HamLCUSim12.TaylorBounds.DefectOrder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The coefficient-mass decay factor of the source's final combination:
`2 (k+1) (61/60) (2/3)^{4k+1} ≤ 1` for all `k ≥ 1` (numerical base case at
`k = 1`, then the ratio `(k+2)/(k+1) · (2/3)^4 ≤ 1`). -/
theorem mass_decay (k : ℕ) (hk : 1 ≤ k) :
    2 * ((k : ℝ) + 1) * (61 / 60 : ℝ) * ((2 : ℝ) / 3) ^ (4 * k + 1) ≤ 1 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k _ ih =>
      push_cast
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      have hsplit : ((2 : ℝ) / 3) ^ (4 * (k + 1) + 1) =
          ((2 : ℝ) / 3) ^ (4 * k + 1) * ((2 : ℝ) / 3) ^ (4 : ℕ) := by
        rw [show 4 * (k + 1) + 1 = (4 * k + 1) + 4 by omega, pow_add]
      have hpos : 0 < 2 * ((k : ℝ) + 1) * (61 / 60 : ℝ) *
          ((2 : ℝ) / 3) ^ (4 * k + 1) := by positivity
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have htwo : ((2 : ℝ) / 3) ^ (4 : ℕ) = 16 / 81 := by norm_num
      have hratio : ((k : ℝ) + 2) / ((k : ℝ) + 1) * ((2 : ℝ) / 3) ^ (4 : ℕ) ≤ 1 := by
        rw [htwo, div_mul_eq_mul_div]
        exact (div_le_one hk1).2 (by linarith)
      have hf : 2 * (((k : ℝ) + 1) + 1) * (61 / 60 : ℝ) * ((2 : ℝ) / 3) ^ (4 * (k + 1) + 1) =
          (2 * ((k : ℝ) + 1) * (61 / 60 : ℝ) * ((2 : ℝ) / 3) ^ (4 * k + 1)) *
            (((k : ℝ) + 2) / ((k : ℝ) + 1) * ((2 : ℝ) / 3) ^ (4 : ℕ)) := by
        rw [hsplit]
        field_simp
        ring
      calc 2 * (((k : ℝ) + 1) + 1) * (61 / 60 : ℝ) * ((2 : ℝ) / 3) ^ (4 * (k + 1) + 1)
          = (2 * ((k : ℝ) + 1) * (61 / 60 : ℝ) * ((2 : ℝ) / 3) ^ (4 * k + 1)) *
              (((k : ℝ) + 2) / ((k : ℝ) + 1) * ((2 : ℝ) / 3) ^ (4 : ℕ)) := hf
        _ ≤ (2 * ((k : ℝ) + 1) * (61 / 60 : ℝ) * ((2 : ℝ) / 3) ^ (4 * k + 1)) * 1 :=
            mul_le_mul_of_nonneg_left hratio hpos.le
        _ ≤ 1 * 1 := by
            exact mul_le_mul_of_nonneg_right ih (by positivity)
        _ = 1 := by ring

/-- Lemma 8, Eq. (39): with the moment system of Lemma 4 at `χ = k`, the
coefficient bound `|C_q| ≤ 2`, and the bundled per-node defect bound at the
constant `(61/60)·((4/3)·m·(5/3)^{k-1}·h)^{4k+1}` (the source's Eqs. (R4kU)
and (Skremainder)), the multi-product defect obeys the printed bound
`(2 m (5/3)^{k-1} h λ)^{4k+1}`. -/
theorem lemma8_multiproduct_bound (k : ℕ) (hk : 1 ≤ k) (m h lam : ℝ)
    (hm : 0 ≤ m) (hh : 0 ≤ h) (hlam : 0 ≤ lam)
    (C : Fin (k + 1) → ℝ) (ℓ : Fin (k + 1) → ℝ)
    (hmom₁ : ∑ q, C q = 1)
    (hmom : ∀ j : ℕ, j < k → (∑ q, C q / ℓ q ^ (2 * k + 2 * j)) = 0)
    (U : ℝ → E) (W : Fin (k + 1) → ℝ → E) (D : ℕ → E)
    (hC : ∀ q, |C q| ≤ 2)
    (hdef : ∀ q : Fin (k + 1),
      ‖W q lam - U lam - ∑ j : Fin k, ((lam ^ (2 * k + 1 + 2 * (j : ℕ)) /
          (ℓ q ^ (2 * k + 2 * (j : ℕ)))) • (D (j : ℕ)))‖ ≤
        (61 / 60) * (((4 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h) ^ (4 * k + 1)) *
          lam ^ (4 * k + 1)) :
    ‖(∑ q, C q • W q lam) - U lam‖ ≤
      (2 * m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam) ^ (4 * k + 1) := by
  have hmass : (∑ q, |C q|) ≤ 2 * ((k : ℝ) + 1) := by
    have hle : ∑ q, |C q| ≤ ∑ q : Fin (k + 1), (2 : ℝ) :=
      Finset.sum_le_sum fun q _ => hC q
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
    push_cast at hle
    linarith
  have hex : (4 * k + 1 : ℕ) = 2 * (k + k) + 1 := by omega
  have hdef' : ∀ q : Fin (k + 1),
      ‖W q lam - U lam - ∑ j : Fin k, ((lam ^ (2 * k + 1 + 2 * (j : ℕ)) /
          (ℓ q ^ (2 * k + 2 * (j : ℕ)))) • (D (j : ℕ)))‖ ≤
      (61 / 60) * (((4 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h) ^ (4 * k + 1)) *
        lam ^ (2 * (k + k) + 1) := by
    intro q
    have hq := hdef q
    nth_rewrite 2 [hex] at hq
    exact hq
  have hB := multiproduct_order_at k k C ℓ hmom₁ hmom U W D
    ((61 / 60) * (((4 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h) ^ (4 * k + 1))) lam hdef'
  have hfivethree : (0 : ℝ) < (5 : ℝ) / 3 := by norm_num
  have hprod1 : 0 ≤ m * ((5 : ℝ) / 3) ^ (k - 1) * h :=
    mul_nonneg (mul_nonneg hm (pow_nonneg hfivethree.le _)) hh
  have hlamnn : 0 ≤ lam ^ (4 * k + 1) := pow_nonneg hlam _
  have hBnn : 0 ≤ ((4 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h) ^ (4 * k + 1) :=
    pow_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hm)
      (pow_nonneg hfivethree.le _)) hh) _
  have hmassnn : 0 ≤ ∑ q, |C q| := Finset.sum_nonneg fun q _ => abs_nonneg _
  have hstep1 : (∑ q, |C q|) *
      ((61 / 60) * (((4 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h) ^ (4 * k + 1))) *
      lam ^ (2 * (k + k) + 1) ≤
      2 * ((k : ℝ) + 1) * (61 / 60 : ℝ) *
      (((4 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h) ^ (4 * k + 1)) *
      lam ^ (2 * (k + k) + 1) := by
    have hlam' : 0 ≤ lam ^ (2 * (k + k) + 1) := pow_nonneg hlam _
    have hnn' : 0 ≤ ((61 / 60 : ℝ)) *
        (((4 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h) ^ (4 * k + 1)) :=
      mul_nonneg (by norm_num) hBnn
    have hm1 : (∑ q, |C q|) *
        ((61 / 60) * (((4 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h) ^ (4 * k + 1))) ≤
        2 * ((k : ℝ) + 1) *
        ((61 / 60) * (((4 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h) ^ (4 * k + 1))) :=
      mul_le_mul_of_nonneg_right hmass hnn'
    calc (∑ q, |C q|) *
          ((61 / 60) * (((4 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h) ^ (4 * k + 1))) *
          lam ^ (2 * (k + k) + 1)
        ≤ (2 * ((k : ℝ) + 1) *
            ((61 / 60) * (((4 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h) ^ (4 * k + 1)))) *
            lam ^ (2 * (k + k) + 1) := mul_le_mul_of_nonneg_right hm1 hlam'
      _ = 2 * ((k : ℝ) + 1) * (61 / 60 : ℝ) *
          (((4 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h) ^ (4 * k + 1)) *
          lam ^ (2 * (k + k) + 1) := by ring
  have hkey : (2 * (m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam)) ^ (4 * k + 1) *
      ((2 : ℝ) / 3) ^ (4 * k + 1) =
      ((4 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h) ^ (4 * k + 1) * lam ^ (4 * k + 1) := by
    have ha : (2 * (m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam)) ^ (4 * k + 1) *
        ((2 : ℝ) / 3) ^ (4 * k + 1) =
        ((2 * (m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam)) * ((2 : ℝ) / 3)) ^ (4 * k + 1) :=
      (mul_pow _ _ _).symm
    have hb : (2 * (m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam)) * ((2 : ℝ) / 3) =
        (4 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam := by ring
    have hc : ((4 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam) ^ (4 * k + 1) =
        ((4 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h) ^ (4 * k + 1) * lam ^ (4 * k + 1) := by
      have hab : ((4 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h) * lam =
          (4 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam := by ring
      nth_rewrite 1 [← hab]
      rw [mul_pow]
    rw [ha, hb, hc]
  have hsplit : (2 * (m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam)) ^ (4 * k + 1) *
      (2 * ((k : ℝ) + 1) * (61 / 60 : ℝ) * ((2 : ℝ) / 3) ^ (4 * k + 1)) =
      2 * ((k : ℝ) + 1) * (61 / 60 : ℝ) *
      (((4 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h) ^ (4 * k + 1)) *
      lam ^ (4 * k + 1) := by
    have hcomm : (2 * (m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam)) ^ (4 * k + 1) *
        (2 * ((k : ℝ) + 1) * (61 / 60 : ℝ) * ((2 : ℝ) / 3) ^ (4 * k + 1)) =
        (2 * ((k : ℝ) + 1) * (61 / 60 : ℝ)) *
        ((2 * (m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam)) ^ (4 * k + 1) *
          ((2 : ℝ) / 3) ^ (4 * k + 1)) := by ring
    rw [hcomm, hkey]
    ring
  have hbase2 : (0 : ℝ) ≤ m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam := mul_nonneg hprod1 hlam
  have hpowpos : 0 ≤ (2 * (m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam)) ^ (4 * k + 1) :=
    pow_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hbase2) _
  have hlam' : 0 ≤ lam ^ (2 * (k + k) + 1) := pow_nonneg hlam _
  have hfin : (2 * (m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam)) ^ (4 * k + 1) *
      (2 * ((k : ℝ) + 1) * (61 / 60 : ℝ) * ((2 : ℝ) / 3) ^ (4 * k + 1)) ≤
      (2 * (m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam)) ^ (4 * k + 1) := by
    calc (2 * (m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam)) ^ (4 * k + 1) *
          (2 * ((k : ℝ) + 1) * (61 / 60 : ℝ) * ((2 : ℝ) / 3) ^ (4 * k + 1))
        ≤ (2 * (m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam)) ^ (4 * k + 1) * 1 :=
            mul_le_mul_of_nonneg_left (mass_decay k hk) hpowpos
      _ = (2 * (m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam)) ^ (4 * k + 1) := by ring
  calc ‖(∑ q, C q • W q lam) - U lam‖
      ≤ (∑ q, |C q|) *
          ((61 / 60) * (((4 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h) ^ (4 * k + 1))) *
          lam ^ (2 * (k + k) + 1) := hB
    _ ≤ 2 * ((k : ℝ) + 1) * (61 / 60 : ℝ) *
          (((4 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h) ^ (4 * k + 1)) *
          lam ^ (2 * (k + k) + 1) := hstep1
    _ = 2 * ((k : ℝ) + 1) * (61 / 60 : ℝ) *
          (((4 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h) ^ (4 * k + 1)) *
          lam ^ (4 * k + 1) := by rw [← hex]
    _ = (2 * (m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam)) ^ (4 * k + 1) *
          (2 * ((k : ℝ) + 1) * (61 / 60 : ℝ) * ((2 : ℝ) / 3) ^ (4 * k + 1)) :=
        hsplit.symm
    _ ≤ (2 * (m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam)) ^ (4 * k + 1) := hfin
    _ = (2 * m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam) ^ (4 * k + 1) := by
        congr 1
        ring

end Qatlib.Papers.HamLCUSim12.FullSimulation.Lemma8Bound
