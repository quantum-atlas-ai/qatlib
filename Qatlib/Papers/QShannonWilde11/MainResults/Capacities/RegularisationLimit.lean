/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QShannonWilde11.MainResults.Model.ChannelCaps
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Cast.Order.Field

@[expose] public section


/-!
# Limits of subadditive regularised information quantities

Paper version: **arXiv:1106.1445v8**, [Wilde2017], Theorem 20.3.1, Eqs. (20.22)–(20.23), fixed
PDF p. 564; also Theorems 23.2.1, 24.3.1 and 25.2.1 (fixed PDF pp. 642, 661, 696).
<https://arxiv.org/abs/1106.1445>

The capacity formulas of Chapters 20–25 regularise a single-letter information quantity:
`(1/k)·f(N^{⊗k})` is shown to converge, so the regularised capacity is a genuine limit rather
than a limsup or an infimum.  The shared interface
`Qatlib.Papers.QShannonWilde11.MainResults.Model.QChanInfo.reg` records the regularised
sequence, and the existing limit lemmas in
`Qatlib.Papers.QShannonWilde11.MainResults.ChannelInfo` and
`Qatlib.Papers.QShannonWilde11.MainResults.Capacities` cover only the *additive* case, where
the sequence is constant.

This file supplies Fekete's subadditivity argument: if `f(N^{⊗(k+l)}) ≤ f(N^{⊗k}) + f(N^{⊗l})`
for all positive `k`, `l` and the regularised sequence is bounded below, then it converges, and
the limit is `sInf {(1/k)·f(N^{⊗k}) | k ≥ 1}`.

Only plain convergence is proved.  No additivity, no operational coding statement and no
identification of the limit with a capacity is derived, and the tensor powers themselves remain
an interface field without a composition law.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QShannonWilde11.MainResults.Capacities

open Qatlib.Papers.QShannonWilde11.MainResults.Model
open Filter
open scoped Topology

noncomputable section

variable (C : QChanInfo)

/-- **Fekete for regularised information quantities** — [Wilde2017], arXiv:1106.1445v8,
Theorems 20.3.1, 23.2.1, 24.3.1 and 25.2.1.  If the information functional is subadditive against the tensor
power and its regularised sequence is bounded below, then `(1/k)·f(N^{⊗k})` converges. -/
theorem exists_tendsto_reg_of_subadditive (f : C.Ch → ℝ) (N : C.Ch)
    (hsub : ∀ k l : ℕ, 1 ≤ k → 1 ≤ l →
      f (C.tensorPow N (k + l)) ≤ f (C.tensorPow N k) + f (C.tensorPow N l))
    (hbound : ∃ b : ℝ, ∀ k : ℕ, 1 ≤ k → b ≤ C.reg f N k) :
    ∃ L : ℝ, Tendsto (fun k => C.reg f N k) atTop (nhds L) := by
  classical
  set a : ℕ → ℝ := fun n => f (C.tensorPow N n) with hadef
  have hreg : ∀ n : ℕ, C.reg f N n = a n / n := by
    intro n
    unfold QChanInfo.reg
    show (1 / (n : ℝ)) * a n = a n / n
    rw [one_div, div_eq_mul_inv, mul_comm]
  have hsub' : ∀ k l : ℕ, 1 ≤ k → 1 ≤ l → a (k + l) ≤ a k + a l := hsub
  have hmul : ∀ (m k : ℕ), 1 ≤ m → 1 ≤ k → a (m * k) ≤ (m : ℝ) * a k := by
    intro m
    induction m with
    | zero => intro k hm _; exact absurd hm (by omega)
    | succ m ih =>
      intro k hm hk
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0
        simp
      · have hmk : 1 ≤ m * k := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
        calc a ((m + 1) * k) = a (m * k + k) := by rw [Nat.succ_mul]
          _ ≤ a (m * k) + a k := hsub' (m * k) k hmk hk
          _ ≤ (m : ℝ) * a k + a k := by
              have := ih k (by omega) hk
              linarith
          _ = ((m + 1 : ℕ) : ℝ) * a k := by push_cast; ring
  set Mk : ℕ → ℝ := fun k => ∑ r ∈ Finset.Ico 1 k, |a r| with hMkdef
  have hMk_nonneg : ∀ k : ℕ, 0 ≤ Mk k :=
    fun k => Finset.sum_nonneg fun r _ => abs_nonneg (a r)
  have hMk_bound : ∀ k r : ℕ, 1 ≤ r → r < k → a r ≤ Mk k := by
    intro k r hr hrk
    have hmem : r ∈ Finset.Ico 1 k := Finset.mem_Ico.mpr ⟨hr, hrk⟩
    calc a r ≤ |a r| := le_abs_self _
      _ ≤ Mk k := Finset.single_le_sum (f := fun r => |a r|) (fun i _ => abs_nonneg (a i)) hmem
  have hfloor : ∀ n k : ℕ, 1 ≤ k → 1 ≤ n → a n ≤ ((n / k : ℕ) : ℝ) * a k + Mk k := by
    intro n k hk hn
    have hdecomp : n = k * (n / k) + n % k := (Nat.div_add_mod n k).symm
    have hmod : n % k < k := Nat.mod_lt _ (by omega)
    rcases Nat.eq_zero_or_pos (n % k) with hr | hr
    · have hnq : n = (n / k) * k := by
        conv_lhs => rw [hdecomp, hr]
        rw [add_zero, mul_comm]
      have hq : 1 ≤ n / k := by
        rcases Nat.eq_zero_or_pos (n / k) with hq0 | hqpos
        · exfalso
          have h0 : n = 0 := by rw [hnq, hq0, zero_mul]
          omega
        · exact hqpos
      conv_lhs => rw [hnq]
      exact (hmul (n / k) k hq hk).trans (le_add_of_nonneg_right (hMk_nonneg k))
    · rcases Nat.eq_zero_or_pos (n / k) with hq | hq
      · have hnr : n = n % k := by
          conv_lhs => rw [hdecomp, hq]
          simp
        have hb := hMk_bound k (n % k) hr hmod
        rw [hq]
        push_cast
        rw [zero_mul, zero_add]
        rw [hnr]
        exact hb
      · have hqk : 1 ≤ (n / k) * k :=
          Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
        have h1 : a n ≤ a ((n / k) * k) + a (n % k) := by
          conv_lhs => rw [hdecomp, mul_comm k (n / k)]
          exact hsub' ((n / k) * k) (n % k) hqk hr
        have h2 : a ((n / k) * k) ≤ ((n / k : ℕ) : ℝ) * a k := hmul (n / k) k hq hk
        have h3 : a (n % k) ≤ Mk k := hMk_bound k (n % k) hr hmod
        linarith
  have hkey : ∀ n k : ℕ, 1 ≤ k → 1 ≤ n →
      a n / n ≤ a k / k + (|a k| + Mk k) / n := by
    intro n k hk hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hdecomp : n = k * (n / k) + n % k := (Nat.div_add_mod n k).symm
    have hmod : n % k < k := Nat.mod_lt _ (by omega)
    have hlt : n < (n / k + 1) * k := by
      calc n = k * (n / k) + n % k := hdecomp
        _ < k * (n / k) + k := Nat.add_lt_add_left hmod _
        _ = (n / k + 1) * k := by rw [Nat.add_mul, one_mul]; ring
    have hcast_le : ((n / k : ℕ) : ℝ) ≤ (n : ℝ) / k := Nat.cast_div_le
    have hcast_lt : (n : ℝ) / k < ((n / k : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hkpos]
      have hc : (n : ℝ) < (((n / k : ℕ) : ℝ) + 1) * (k : ℝ) := by
        exact_mod_cast hlt
      linarith
    have hcast : (n : ℝ) / k - 1 ≤ ((n / k : ℕ) : ℝ) := by linarith
    have hmain : ((n / k : ℕ) : ℝ) * a k ≤ ((n : ℝ) / k) * a k + |a k| := by
      rcases le_or_gt 0 (a k) with hak | hak
      · have h := mul_le_mul_of_nonneg_right hcast_le hak
        linarith [abs_nonneg (a k)]
      · have h := mul_le_mul_of_nonpos_right hcast (le_of_lt hak)
        have habs : |a k| = -a k := abs_of_neg hak
        linarith
    have hcore : ((n / k : ℕ) : ℝ) * a k / n ≤ a k / k + |a k| / n := by
      have hdiv : ((n : ℝ) / k) * a k / n = a k / k := by
        field_simp
      calc ((n / k : ℕ) : ℝ) * a k / n
          ≤ (((n : ℝ) / k) * a k + |a k|) / n := div_le_div_of_nonneg_right hmain hnpos.le
        _ = a k / k + |a k| / n := by rw [add_div, hdiv]
    calc a n / n
        ≤ (((n / k : ℕ) : ℝ) * a k + Mk k) / n :=
          div_le_div_of_nonneg_right (hfloor n k hk hn) hnpos.le
      _ = ((n / k : ℕ) : ℝ) * a k / n + Mk k / n := by rw [add_div]
      _ ≤ (a k / k + |a k| / n) + Mk k / n := by linarith
      _ = a k / k + (|a k| + Mk k) / n := by rw [add_div]; ring
  obtain ⟨b, hb⟩ := hbound
  set S : Set ℝ := {x | ∃ k : ℕ, 1 ≤ k ∧ x = a k / k} with hSdef
  have hSne : S.Nonempty := ⟨a 1 / 1, 1, le_refl 1, by simp⟩
  have hSbdd : BddBelow S := by
    refine ⟨b, ?_⟩
    rintro x ⟨k, hk, rfl⟩
    have hbk := hb k hk
    rw [hreg] at hbk
    exact hbk
  refine ⟨sInf S, ?_⟩
  rw [show (fun k => C.reg f N k) = fun n => a n / n from funext hreg]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlower : ∀ n : ℕ, 1 ≤ n → sInf S ≤ a n / n :=
    fun n hn => csInf_le hSbdd ⟨n, hn, rfl⟩
  obtain ⟨y, hyS, hylt⟩ :=
    exists_lt_of_csInf_lt hSne (show sInf S < sInf S + ε / 2 by linarith)
  obtain ⟨k, hk, rfl⟩ := hyS
  have hlim : Tendsto (fun n : ℕ => a k / k + (|a k| + Mk k) / n) atTop (nhds (a k / k)) := by
    have h0 := tendsto_const_div_atTop_nhds_zero_nat (|a k| + Mk k)
    simpa using tendsto_const_nhds.add h0
  have hev : ∀ᶠ n : ℕ in atTop,
      a k / k + (|a k| + Mk k) / n < a k / k + ε / 2 :=
    (tendsto_order.1 hlim).2 _ (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left N 1) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hlt : a k / k + (|a k| + Mk k) / n < a k / k + ε / 2 := hN n hnN
  have hup : a n / n < a k / k + ε / 2 := (hkey n k hk hn1).trans_lt hlt
  have hlow : sInf S ≤ a n / n := hlower n hn1
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end

end Qatlib.Papers.QShannonWilde11.MainResults.Capacities
