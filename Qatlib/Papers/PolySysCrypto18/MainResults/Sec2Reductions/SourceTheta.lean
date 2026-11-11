/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PolySysCrypto18.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# §2.1 — Representing an integer interval with a Boolean polynomial

Chen–Gao–Yuan, arXiv:1802.03856v2, §2.1, Lemma 2.1 (p.5), equation (2).

`θ_b` encodes the integers `0, 1, …, b` exactly.  We prove:

* `theta_le` — every Boolean evaluation of `θ_b` lies in `{0, …, b}`;
* `binary_repr` — every `n < 2^s` is a sum of Boolean low bits;
* `theta_surjective` — `θ_b : {0,1}^{s+1} → {0,…,b}` is surjective;
* `theta_varCount_eq_sparseness` (in `SourceModel`) — `#B_bit = #θ_b = ⌊log₂ b⌋+1`.

The paper's `F_p = {0,1,…,p-1}` evaluation is the same statement because all
intermediate values are `≤ b < p`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.PolySysCrypto18.MainResults.Sec2Reductions

open Qatlib.Papers.PolySysCrypto18.MainResults

/-- `Σ_{i<s} 2^i = 2^s − 1`. -/
theorem sum_two_pow (s : ℕ) : (∑ i ∈ Finset.range s, 2 ^ i) = 2 ^ s - 1 := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have : 0 < 2 ^ s := by positivity
      omega

/-- The sum over `Fin s` agrees with the sum over `range s`. -/
theorem sum_fin_eq_range (s : ℕ) (g : ℕ → ℕ) :
    (∑ i : Fin s, g (i : ℕ)) = ∑ i ∈ Finset.range s, g i :=
  Fin.sum_univ_eq_sum_range g s

/-- A Boolean word `f : Fin s → Bool` realises `n` on the low `s` bits, for every
`n < 2^s`. -/
theorem binary_repr (s : ℕ) : ∀ n < 2 ^ s, ∃ f : Fin s → Bool,
    (∑ i : Fin s, (f i).toNat * 2 ^ (i : ℕ)) = n := by
  induction s with
  | zero =>
      intro n hn
      have hn0 : n = 0 := by simpa using hn
      subst hn0
      exact ⟨Fin.elim0, by simp⟩
  | succ s ih =>
      intro n hn
      have hq : n / 2 < 2 ^ s := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]
        calc n < 2 ^ (s + 1) := hn
          _ = 2 ^ s * 2 := by rw [pow_succ]
      obtain ⟨f, hf⟩ := ih (n / 2) hq
      refine ⟨Fin.cons (n % 2 == 1) f, ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_succ]
      have htoNat : ((n % 2 == 1) : Bool).toNat = n % 2 := by
        rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]
      rw [htoNat]
      have hpow : (2 : ℕ) ^ ((0 : Fin (s + 1)) : ℕ) = 1 := by simp
      rw [hpow, mul_one]
      have hshift :
          (∑ i : Fin s, (f i).toNat * 2 ^ ((i : ℕ) + 1))
            = 2 * ∑ i : Fin s, (f i).toNat * 2 ^ (i : ℕ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [pow_succ]
        ring
      rw [hshift, hf]
      omega

/-- `θ_b` never leaves `{0, …, b}` when all inputs are Boolean and `b ≥ 1`
(Lemma 2.1, p.5). -/
theorem theta_le {b : ℕ} (hb : 0 < b) (B : Fin (Nat.log2 b + 1) → ℕ)
    (hB : ∀ i, B i = 0 ∨ B i = 1) :
    theta b B ≤ b := by
  have h2s_le : 2 ^ Nat.log2 b ≤ b := by
    simpa [Nat.log2_eq_log_two] using
      (Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp hb))
  have ha : 1 ≤ 2 ^ Nat.log2 b := Nat.one_le_two_pow
  have key : (∑ i : Fin (Nat.log2 b), B i.castSucc * 2 ^ (i : ℕ))
      ≤ 2 ^ Nat.log2 b - 1 := by
    have hbnd : ∀ i : Fin (Nat.log2 b), B i.castSucc * 2 ^ (i : ℕ) ≤ 2 ^ (i : ℕ) := by
      intro i
      rcases hB i.castSucc with h | h
      · rw [h, Nat.zero_mul]; exact Nat.zero_le _
      · rw [h, Nat.one_mul]
    calc (∑ i : Fin (Nat.log2 b), B i.castSucc * 2 ^ (i : ℕ))
        ≤ ∑ i : Fin (Nat.log2 b), 2 ^ (i : ℕ) := Finset.sum_le_sum (fun i _ => hbnd i)
      _ = ∑ i ∈ Finset.range (Nat.log2 b), 2 ^ i :=
            sum_fin_eq_range (Nat.log2 b) (fun i => 2 ^ i)
      _ = 2 ^ Nat.log2 b - 1 := sum_two_pow (Nat.log2 b)
  have hcoef : (b + 1 - 2 ^ Nat.log2 b) * B (Fin.last _) ≤ b + 1 - 2 ^ Nat.log2 b := by
    rcases hB (Fin.last _) with h | h
    · rw [h, Nat.mul_zero]; exact Nat.zero_le _
    · rw [h, Nat.mul_one]
  unfold theta
  calc (∑ i : Fin (Nat.log2 b), B i.castSucc * 2 ^ (i : ℕ))
        + (b + 1 - 2 ^ Nat.log2 b) * B (Fin.last _)
      ≤ (2 ^ Nat.log2 b - 1) + (b + 1 - 2 ^ Nat.log2 b) := add_le_add key hcoef
    _ = b := by omega

/-- Lemma 2.1 (p.5): `θ_b` maps Boolean inputs onto `{0, …, b}`.  (The `F_p`
evaluation is identical since intermediate values stay below `p`.) -/
theorem theta_surjective {b : ℕ} (hb : 0 < b) :
    ∀ n, n ≤ b → ∃ B : Fin (Nat.log2 b + 1) → Bool,
      theta b (fun i => (B i).toNat) = n := by
  intro n hn
  have h2s_le : 2 ^ Nat.log2 b ≤ b := by
    simpa [Nat.log2_eq_log_two] using
      (Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp hb))
  have hb_lt : b < 2 ^ (Nat.log2 b + 1) := by
    have hlog : Nat.log 2 b = Nat.log2 b := Nat.log2_eq_log_two.symm
    have := Nat.lt_pow_of_log_lt (b := 2) (by norm_num) (y := b) (x := Nat.log2 b + 1)
      (by rw [hlog]; exact Nat.lt_succ_self _)
    simpa using this
  by_cases hnc : n < 2 ^ Nat.log2 b
  · obtain ⟨f, hf⟩ := binary_repr (Nat.log2 b) n hnc
    refine ⟨Fin.snoc f false, ?_⟩
    unfold theta
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Bool.toNat_false]
    rw [hf, Nat.mul_zero, Nat.add_zero]
  · push Not at hnc
    have hp : 2 ^ (Nat.log2 b + 1) = 2 ^ Nat.log2 b * 2 := by rw [pow_succ]
    have hcoef_le_n : b + 1 - 2 ^ Nat.log2 b ≤ n := by
      have h1 : b + 1 - 2 ^ Nat.log2 b ≤ 2 ^ Nat.log2 b := by omega
      omega
    have hm_lt : n - (b + 1 - 2 ^ Nat.log2 b) < 2 ^ Nat.log2 b := by
      have hle : n - (b + 1 - 2 ^ Nat.log2 b) ≤ b - (b + 1 - 2 ^ Nat.log2 b) :=
        Nat.sub_le_sub_right hn _
      have hbsub : b - (b + 1 - 2 ^ Nat.log2 b) = 2 ^ Nat.log2 b - 1 := by omega
      omega
    obtain ⟨f, hf⟩ := binary_repr (Nat.log2 b) (n - (b + 1 - 2 ^ Nat.log2 b)) hm_lt
    refine ⟨Fin.snoc f true, ?_⟩
    unfold theta
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Bool.toNat_true]
    rw [hf, Nat.mul_one]
    exact Nat.sub_add_cancel hcoef_le_n

end Qatlib.Papers.PolySysCrypto18.MainResults.Sec2Reductions
