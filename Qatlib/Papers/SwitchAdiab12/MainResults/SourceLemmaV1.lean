/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SwitchAdiab12 — Lemma V.1 (eq. (V.1))

Fixed paper version: arXiv:1204.2318v3 (7 Jul 2012), Elgart--Hagedorn,
"A Note on the Switching Adiabatic Theorem", Appendix V, p. 15.

Lemma V.1 (paper, eq. (V.1)): for all `α ≥ 1`, `k₁, k₂ ≥ 0` and `n ≥ 1`,

```
  k! / (k₁! k₂!) · (k₁+n)^{α(k₁+n)} · k₂^{α k₂}
      ≤ 4^{-(α-1)·min(k₁+n,k₂)} · (k+n)^{α(k+n)},      k = k₁ + k₂.
```

The proof follows the paper's route:

* the binomial theorem gives the `α = 1` estimate (V.2), including the
  factorial count;
* the inequality `x(1-x) ≤ 1/4` gives `(k₁+n)·k₂ ≤ (k+n)²/4`, hence the
  integer-power core estimate (V.4)/(V.5);
* writing `α = 1 + (α-1)` and using `Real.rpow_add_of_nonneg` /
  `Real.rpow_mul` splits the left-hand side into the `α = 1` factor and the
  `α-1` power of the core estimate.

Everything is proved; no `sorry`, no extra axiom.
-/

set_option autoImplicit false
noncomputable section

open scoped Nat

namespace Qatlib.Papers.SwitchAdiab12.MainResults.SourceLemmaV1

open Finset

/-- `4^{-n}` for a natural `n`, in the `rpow` form used by the paper. -/
private lemma four_rpow_neg_nat (n : ℕ) : (4 : ℝ) ^ (-(n : ℝ)) = ((4 : ℝ) ^ n)⁻¹ := by
  rw [Real.rpow_neg_natCast, zpow_neg, zpow_natCast]

/-- **Binomial-theorem step (V.2).**  With `A = k₁+n`, `B = k₂` and `S = A + B`,
the factorial-weighted product of integer powers is bounded by `S^{k+n}`.

This is the paper's estimate (V.2): the term `k₁` of the binomial expansion of
`(A+B)^{k}` is at most the whole sum, and then one multiplies by `A^n ≤ S^n`. -/
private lemma base_int (k₁ k₂ n : ℕ) :
    (Nat.factorial (k₁ + k₂) : ℝ) / ((Nat.factorial k₁ : ℝ) * (Nat.factorial k₂ : ℝ)) *
        ((k₁ + n : ℕ) : ℝ) ^ (k₁ + n) * ((k₂ : ℕ) : ℝ) ^ k₂
      ≤ ((k₁ + k₂ + n : ℕ) : ℝ) ^ (k₁ + k₂ + n) := by
  set A : ℝ := ((k₁ + n : ℕ) : ℝ)
  set B : ℝ := ((k₂ : ℕ) : ℝ)
  set S : ℝ := ((k₁ + k₂ + n : ℕ) : ℝ)
  have hS : S = A + B := by
    simp only [S, A, B]; push_cast; ring
  have hA0 : 0 ≤ A := by simp only [A]; positivity
  have hB0 : 0 ≤ B := by simp only [B]; positivity
  have hnum : (Nat.factorial (k₁ + k₂) : ℝ) / ((Nat.factorial k₁ : ℝ) * (Nat.factorial k₂ : ℝ)) =
      ((k₁ + k₂).choose k₁ : ℝ) := by
    rw [Nat.cast_add_choose (K := ℝ) (a := k₁) (b := k₂)]
  have hterm : ∀ j ∈ Finset.range (k₁ + k₂ + 1),
      0 ≤ A ^ j * B ^ (k₁ + k₂ - j) * ((k₁ + k₂).choose j : ℝ) := by
    intro j _
    have h1 : (0 : ℝ) ≤ A ^ j := pow_nonneg hA0 j
    have h2 : (0 : ℝ) ≤ B ^ (k₁ + k₂ - j) := pow_nonneg hB0 _
    have h3 : (0 : ℝ) ≤ ((k₁ + k₂).choose j : ℝ) := by positivity
    exact mul_nonneg (mul_nonneg h1 h2) h3
  have hmem : k₁ ∈ Finset.range (k₁ + k₂ + 1) := by
    simp only [Finset.mem_range]; omega
  have hsingle := Finset.single_le_sum hterm hmem
  have hsingle' :
      A ^ k₁ * B ^ k₂ * ((k₁ + k₂).choose k₁ : ℝ) ≤ (A + B) ^ (k₁ + k₂) := by
    have hsub : k₁ + k₂ - k₁ = k₂ := Nat.add_sub_cancel_left k₁ k₂
    rw [hsub] at hsingle
    rw [← add_pow] at hsingle
    exact hsingle
  have hAeq : A ^ (k₁ + n) = A ^ k₁ * A ^ n := pow_add A k₁ n
  have hAleS : A ≤ S := by
    rw [hS]; linarith [hB0]
  have hpowle : A ^ n ≤ S ^ n := pow_le_pow_left₀ hA0 hAleS n
  calc
    (Nat.factorial (k₁ + k₂) : ℝ) / ((Nat.factorial k₁ : ℝ) * (Nat.factorial k₂ : ℝ)) *
        ((k₁ + n : ℕ) : ℝ) ^ (k₁ + n) * ((k₂ : ℕ) : ℝ) ^ k₂
        = (A ^ k₁ * B ^ k₂ * ((k₁ + k₂).choose k₁ : ℝ)) * A ^ n := by
          rw [hnum, hAeq]; ring
    _ ≤ (A + B) ^ (k₁ + k₂) * S ^ n :=
          mul_le_mul hsingle' hpowle (pow_nonneg hA0 n)
            (by positivity)
    _ = S ^ (k₁ + k₂ + n) := by
          rw [hS, ← pow_add]

/-- **Integer-power core estimate (V.4)/(V.5).**  For `A = k₁+n`, `B = k₂`,
`S = A + B = k₁+k₂+n`,

```
  A^{k₁+n} · B^{k₂} ≤ 4^{-min(k₁+n,k₂)} · S^{k₁+k₂+n}.
```

The proof uses `(k₁+n)·k₂ ≤ (k+n)²/4` (i.e. `x(1-x) ≤ 1/4`), splitting on
whether `k₂ ≤ k₁+n` (paper's (V.4)) or `k₁+n ≤ k₂` (paper's (V.5)). -/
private lemma core_int (k₁ k₂ n : ℕ) :
    ((k₁ + n : ℕ) : ℝ) ^ (k₁ + n) * ((k₂ : ℕ) : ℝ) ^ k₂ ≤
      (4 : ℝ) ^ (-((min (k₁ + n) k₂ : ℕ) : ℝ)) *
        ((k₁ + k₂ + n : ℕ) : ℝ) ^ (k₁ + k₂ + n) := by
  set A : ℝ := ((k₁ + n : ℕ) : ℝ)
  set B : ℝ := ((k₂ : ℕ) : ℝ)
  set S : ℝ := ((k₁ + k₂ + n : ℕ) : ℝ)
  have hS : S = A + B := by
    simp only [S, A, B]; push_cast; ring
  have hA0 : 0 ≤ A := by simp only [A]; positivity
  have hB0 : 0 ≤ B := by simp only [B]; positivity
  have hAB : A * B ≤ (A + B) ^ 2 / 4 := by
    nlinarith [sq_nonneg (A - B)]
  rcases le_total B A with hBA | hABle
  · -- Case `k₂ ≤ k₁+n`: minimum is `k₂`, paper's (V.4).
    have hkB : k₂ ≤ k₁ + n := by
      have h := hBA
      simp only [A, B] at h
      exact_mod_cast h
    have hmin : min (k₁ + n) k₂ = k₂ := Nat.min_eq_right hkB
    rw [hmin]
    have hsplit : A ^ (k₁ + n) = A ^ k₂ * A ^ (k₁ + n - k₂) := by
      rw [← pow_add]; congr 1; omega
    have h1 : A ^ k₂ * B ^ k₂ ≤ ((A + B) ^ 2 / 4) ^ k₂ := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hAB k₂
    have h2 : A ^ (k₁ + n - k₂) ≤ S ^ (k₁ + n - k₂) := by
      apply pow_le_pow_left₀ hA0
      rw [hS]; linarith [hB0]
    have hmul : ((A + B) ^ 2 / 4) ^ k₂ * S ^ (k₁ + n - k₂) =
        S ^ (k₁ + k₂ + n) * ((4 : ℝ) ^ k₂)⁻¹ := by
      rw [div_pow, ← pow_mul, hS, div_mul_eq_mul_div, ← pow_add, div_eq_mul_inv]
      have hexp : 2 * k₂ + (k₁ + n - k₂) = k₁ + k₂ + n := by omega
      rw [hexp]
    calc A ^ (k₁ + n) * B ^ k₂
        = (A ^ k₂ * B ^ k₂) * A ^ (k₁ + n - k₂) := by rw [hsplit]; ring
      _ ≤ ((A + B) ^ 2 / 4) ^ k₂ * S ^ (k₁ + n - k₂) :=
            mul_le_mul h1 h2 (pow_nonneg hA0 _) (by positivity)
      _ = S ^ (k₁ + k₂ + n) * ((4 : ℝ) ^ k₂)⁻¹ := hmul
      _ = (4 : ℝ) ^ (-(k₂ : ℝ)) * S ^ (k₁ + k₂ + n) := by
            rw [four_rpow_neg_nat]; ring
  · -- Case `k₁+n ≤ k₂`: minimum is `k₁+n`, paper's (V.5).
    have hkn : k₁ + n ≤ k₂ := by
      have h := hABle
      simp only [A, B] at h
      exact_mod_cast h
    have hmin : min (k₁ + n) k₂ = k₁ + n := Nat.min_eq_left hkn
    rw [hmin]
    have hsplit : B ^ k₂ = B ^ (k₁ + n) * B ^ (k₂ - (k₁ + n)) := by
      rw [← pow_add]; congr 1; omega
    have h1 : A ^ (k₁ + n) * B ^ (k₁ + n) ≤ ((A + B) ^ 2 / 4) ^ (k₁ + n) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hAB (k₁ + n)
    have h2 : B ^ (k₂ - (k₁ + n)) ≤ S ^ (k₂ - (k₁ + n)) := by
      apply pow_le_pow_left₀ hB0
      rw [hS]; linarith [hA0]
    have hmul : ((A + B) ^ 2 / 4) ^ (k₁ + n) * S ^ (k₂ - (k₁ + n)) =
        S ^ (k₁ + k₂ + n) * ((4 : ℝ) ^ (k₁ + n))⁻¹ := by
      rw [div_pow, ← pow_mul, hS, div_mul_eq_mul_div, ← pow_add, div_eq_mul_inv]
      have hexp : 2 * (k₁ + n) + (k₂ - (k₁ + n)) = k₁ + k₂ + n := by omega
      rw [hexp]
    calc A ^ (k₁ + n) * B ^ k₂
        = (A ^ (k₁ + n) * B ^ (k₁ + n)) * B ^ (k₂ - (k₁ + n)) := by
            rw [hsplit]; ring
      _ ≤ ((A + B) ^ 2 / 4) ^ (k₁ + n) * S ^ (k₂ - (k₁ + n)) :=
            mul_le_mul h1 h2 (pow_nonneg hB0 _) (by positivity)
      _ = S ^ (k₁ + k₂ + n) * ((4 : ℝ) ^ (k₁ + n))⁻¹ := hmul
      _ = (4 : ℝ) ^ (-((k₁ + n : ℕ) : ℝ)) * S ^ (k₁ + k₂ + n) := by
            rw [four_rpow_neg_nat]; ring

/-- **Lemma V.1** (paper, arXiv:1204.2318v3, Appendix V, p. 15, eq. (V.1)).

For `α ≥ 1`, `k₁, k₂ ≥ 0`, `n ≥ 1`, with `k = k₁ + k₂`,

```
  k! / (k₁! k₂!) · (k₁+n)^{α(k₁+n)} · k₂^{α k₂}
      ≤ 4^{-(α-1)·min(k₁+n,k₂)} · (k+n)^{α(k+n)}.
```

Proof: write `α = 1 + (α-1)`, split both `rpow`s with
`Real.rpow_add_of_nonneg`, bound the `α = 1` factor by `base_int`, and bound
the product of the `(α-1)`-powers by the `(α-1)`-power of `core_int`. -/
theorem lemma_V1 (α : ℝ) (hα : 1 ≤ α) (k₁ k₂ n : ℕ) (hn : 1 ≤ n) :
    (Nat.factorial (k₁ + k₂) : ℝ) / ((Nat.factorial k₁ : ℝ) * (Nat.factorial k₂ : ℝ)) *
        ((k₁ + n : ℕ) : ℝ) ^ (α * ((k₁ + n : ℕ) : ℝ)) *
        ((k₂ : ℕ) : ℝ) ^ (α * ((k₂ : ℕ) : ℝ))
      ≤ (4 : ℝ) ^ (-(α - 1) * ((min (k₁ + n) k₂ : ℕ) : ℝ)) *
        ((k₁ + k₂ + n : ℕ) : ℝ) ^ (α * ((k₁ + k₂ + n : ℕ) : ℝ)) := by
  set A : ℝ := ((k₁ + n : ℕ) : ℝ)
  set B : ℝ := ((k₂ : ℕ) : ℝ)
  set S : ℝ := ((k₁ + k₂ + n : ℕ) : ℝ)
  set m : ℕ := min (k₁ + n) k₂
  have hS : S = A + B := by
    simp only [S, A, B]; push_cast; ring
  have hA0 : 0 ≤ A := by simp only [A]; positivity
  have hB0 : 0 ≤ B := by simp only [B]; positivity
  have hApos : 0 < A := by
    have hn1 : (1 : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hn
    have hk : (0 : ℝ) ≤ ((k₁ : ℕ) : ℝ) := by positivity
    simp only [A]; push_cast; linarith
  have hS0 : 0 ≤ S := by simp only [S]; positivity
  have hα1 : 0 ≤ α - 1 := by linarith
  have hAB0 : 0 ≤ A ^ (k₁ + n) * B ^ k₂ :=
    mul_nonneg (pow_nonneg hA0 _) (pow_nonneg hB0 _)
  -- exponent decompositions
  have e1 : α * ((k₁ + n : ℕ) : ℝ) =
      ((k₁ + n : ℕ) : ℝ) + (α - 1) * ((k₁ + n : ℕ) : ℝ) := by ring
  have e2 : α * ((k₂ : ℕ) : ℝ) =
      ((k₂ : ℕ) : ℝ) + (α - 1) * ((k₂ : ℕ) : ℝ) := by ring
  have e3 : α * ((k₁ + k₂ + n : ℕ) : ℝ) =
      ((k₁ + k₂ + n : ℕ) : ℝ) +
        (α - 1) * ((k₁ + k₂ + n : ℕ) : ℝ) := by ring
  -- split the left-hand side
  have hL1 : A ^ (α * ((k₁ + n : ℕ) : ℝ)) =
      A ^ (k₁ + n) * A ^ ((α - 1) * ((k₁ + n : ℕ) : ℝ)) := by
    rw [e1, Real.rpow_add_of_nonneg hA0 (by positivity)
      (mul_nonneg hα1 (by positivity)), Real.rpow_natCast]
  have hL2 : B ^ (α * ((k₂ : ℕ) : ℝ)) =
      B ^ k₂ * B ^ ((α - 1) * ((k₂ : ℕ) : ℝ)) := by
    rw [e2, Real.rpow_add_of_nonneg hB0 (by positivity)
      (mul_nonneg hα1 (by positivity)), Real.rpow_natCast]
  have hA_split : A ^ ((α - 1) * ((k₁ + n : ℕ) : ℝ)) = (A ^ (k₁ + n)) ^ (α - 1) := by
    rw [mul_comm, Real.rpow_mul hA0, Real.rpow_natCast]
  have hB_split : B ^ ((α - 1) * ((k₂ : ℕ) : ℝ)) = (B ^ k₂) ^ (α - 1) := by
    rw [mul_comm, Real.rpow_mul hB0, Real.rpow_natCast]
  have hfactor : A ^ ((α - 1) * ((k₁ + n : ℕ) : ℝ)) *
        B ^ ((α - 1) * ((k₂ : ℕ) : ℝ)) =
      (A ^ (k₁ + n) * B ^ k₂) ^ (α - 1) := by
    rw [hA_split, hB_split, ← Real.mul_rpow (pow_nonneg hA0 _) (pow_nonneg hB0 _)]
  have hbase' : (Nat.factorial (k₁ + k₂) : ℝ) / ((Nat.factorial k₁ : ℝ) * (Nat.factorial k₂ : ℝ)) *
        A ^ (k₁ + n) * B ^ k₂ ≤ S ^ ((k₁ + k₂ + n : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    simpa only [A, B, S] using base_int k₁ k₂ n
  have hcore' : A ^ (k₁ + n) * B ^ k₂ ≤
      (4 : ℝ) ^ (-(m : ℝ)) * S ^ ((k₁ + k₂ + n : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    simpa only [A, B, S, m] using core_int k₁ k₂ n
  have hcore_pow : (A ^ (k₁ + n) * B ^ k₂) ^ (α - 1) ≤
      ((4 : ℝ) ^ (-(m : ℝ)) * S ^ ((k₁ + k₂ + n : ℕ) : ℝ)) ^ (α - 1) :=
    Real.rpow_le_rpow hAB0 hcore' hα1
  have hRHSpow : ((4 : ℝ) ^ (-(m : ℝ)) * S ^ ((k₁ + k₂ + n : ℕ) : ℝ)) ^ (α - 1) =
      (4 : ℝ) ^ (-(α - 1) * (m : ℝ)) *
        S ^ ((α - 1) * ((k₁ + k₂ + n : ℕ) : ℝ)) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4), ← Real.rpow_mul hS0]
    congr 1
    · rw [neg_mul]; congr 1; ring
    · ring
  have hS_split : S ^ ((k₁ + k₂ + n : ℕ) : ℝ) *
        S ^ ((α - 1) * ((k₁ + k₂ + n : ℕ) : ℝ)) =
      S ^ (α * ((k₁ + k₂ + n : ℕ) : ℝ)) := by
    rw [← Real.rpow_add_of_nonneg hS0 (by positivity)
      (mul_nonneg hα1 (by positivity)), ← e3]
  have hrhs_nonneg : 0 ≤
      (4 : ℝ) ^ (-(α - 1) * (m : ℝ)) *
        S ^ ((α - 1) * ((k₁ + k₂ + n : ℕ) : ℝ)) := by positivity
  calc
    (Nat.factorial (k₁ + k₂) : ℝ) / ((Nat.factorial k₁ : ℝ) * (Nat.factorial k₂ : ℝ)) *
        ((k₁ + n : ℕ) : ℝ) ^ (α * ((k₁ + n : ℕ) : ℝ)) *
        ((k₂ : ℕ) : ℝ) ^ (α * ((k₂ : ℕ) : ℝ))
        = ((Nat.factorial (k₁ + k₂) : ℝ) / ((Nat.factorial k₁ : ℝ) * (Nat.factorial k₂ : ℝ)) *
            A ^ (k₁ + n) * B ^ k₂) *
          (A ^ ((α - 1) * ((k₁ + n : ℕ) : ℝ)) *
            B ^ ((α - 1) * ((k₂ : ℕ) : ℝ))) := by
          rw [hL1, hL2]; ring
    _ = ((Nat.factorial (k₁ + k₂) : ℝ) / ((Nat.factorial k₁ : ℝ) * (Nat.factorial k₂ : ℝ)) *
            A ^ (k₁ + n) * B ^ k₂) *
          (A ^ (k₁ + n) * B ^ k₂) ^ (α - 1) := by
          rw [hfactor]
    _ ≤ S ^ ((k₁ + k₂ + n : ℕ) : ℝ) *
          ((4 : ℝ) ^ (-(m : ℝ)) * S ^ ((k₁ + k₂ + n : ℕ) : ℝ)) ^ (α - 1) :=
          mul_le_mul hbase' hcore_pow (Real.rpow_nonneg hAB0 _) (by positivity)
    _ = (4 : ℝ) ^ (-(α - 1) * (m : ℝ)) *
          (S ^ ((k₁ + k₂ + n : ℕ) : ℝ) *
            S ^ ((α - 1) * ((k₁ + k₂ + n : ℕ) : ℝ))) := by
          rw [hRHSpow]; ring
    _ = (4 : ℝ) ^ (-(α - 1) * (m : ℝ)) *
          S ^ (α * ((k₁ + k₂ + n : ℕ) : ℝ)) := by
          rw [hS_split]
    _ = (4 : ℝ) ^ (-(α - 1) * ((min (k₁ + n) k₂ : ℕ) : ℝ)) *
          ((k₁ + k₂ + n : ℕ) : ℝ) ^ (α * ((k₁ + k₂ + n : ℕ) : ℝ)) := by
          simp only [m, S]

end Qatlib.Papers.SwitchAdiab12.MainResults.SourceLemmaV1
