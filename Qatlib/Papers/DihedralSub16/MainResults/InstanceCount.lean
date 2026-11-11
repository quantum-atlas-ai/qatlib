/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DihedralSub16.MainResults.DihedralHSP
import Qatlib.Papers.DihedralSub16.MainResults.Injectivization
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Qatlib.Papers.DihedralSub16.MainResults

open Finset

noncomputable section

open Classical

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- The set of length-`m` translation tuples `V` for which the injectivized hiding
function `f_V` is injective, i.e. the tuples on which the random-translation
injectivization of arXiv:1608.02005v1, §3.2 succeeds. -/
def goodTranslations (D : Finset A) (m : ℕ) : Finset (Fin m → A) :=
  Finset.univ.filter (fun V => Function.Injective (injectivized D m V))

/-- Successful and failed translation tuples partition all `|A|^m` tuples
(arXiv:1608.02005v1, proof of Corollary 1, p. 14). -/
theorem card_goodTranslations_add_card_badTranslations (D : Finset A) (m : ℕ) :
    (goodTranslations D m).card + (badTranslations D m).card = (Fintype.card A) ^ m := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m → A)))
    (p := fun V => Function.Injective (injectivized D m V))
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h
  simpa [goodTranslations, badTranslations] using h

/-- Numerical core of Corollary 1 (arXiv:1608.02005v1, p. 14): for `n ≥ 2` and
`v ≥ 2^(n-1)`, the winning-tuple lower bound `(63/64) · v^(2n+6)` dominates
`2^(n^2)`.  The exponent gain is `(n-1)(2n+6) - n^2 = n^2 + 4n - 6 ≥ 6`, so
`v^(2n+6) ≥ 2^(n^2+6) = 64 · 2^(n^2)`. -/
theorem singer_count_arith (n v : ℕ) (hn : 2 ≤ n) (hv : 2 ^ (n - 1) ≤ v) :
    (2 : ℝ) ^ (n ^ 2) ≤ (63 / 64) * (v : ℝ) ^ (2 * n + 6) := by
  have hexp : n ^ 2 + 6 ≤ (n - 1) * (2 * n + 6) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hsub : (2 + k - 1) = k + 1 := by omega
    rw [hsub]
    nlinarith
  have h2n : (2 : ℝ) ^ (n ^ 2) * 64 ≤ (v : ℝ) ^ (2 * n + 6) := by
    calc (2 : ℝ) ^ (n ^ 2) * 64 = (2 : ℝ) ^ (n ^ 2 + 6) := by
          rw [pow_add]; norm_num
      _ ≤ (2 : ℝ) ^ ((n - 1) * (2 * n + 6)) := pow_le_pow_right₀ (by norm_num) hexp
      _ = ((2 : ℝ) ^ (n - 1)) ^ (2 * n + 6) := by rw [← pow_mul]
      _ ≤ (v : ℝ) ^ (2 * n + 6) :=
          pow_le_pow_left₀ (by positivity) (by exact_mod_cast hv) _
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (n ^ 2) := by positivity
  nlinarith [h2n]

/-- Corollary 1 of arXiv:1608.02005v1 (p. 14), counting form.  Let `N = 2^n - 1`
with `n ≥ 2` and let `D ⊆ Z_N` be a Singer difference set with parameters
`(|D|, λ) = (2^(n-1) - 1, 2^(n-2) - 1)`.  Then at least `2^(n^2)` of the
`N^(2n+6)` choices of `m = 2n + 6` translations make the injectivized hiding
function injective; by Theorem 4 each such instance is efficiently solvable.

The proof is the paper's probabilistic method: Theorem 3 bounds the number of bad
tuples by `N^2 (N - 2(k - λ))^(2n+6)`, and here `N - 2(k - λ) = 2^(n-1) - 1 ≤ N/2`,
so at most `N^(2n+6) / 64` tuples are bad; the remaining `(63/64) N^(2n+6)` good
tuples number at least `2^(n^2)` by `singer_count_arith`. -/
theorem corollary1_good_instance_count (n : ℕ) (hn : 2 ≤ n) [NeZero (2 ^ n - 1)]
    (D : Finset (ZMod (2 ^ n - 1))) (lam : ℕ) (hD : IsDifferenceSet D lam)
    (hk : D.card = 2 ^ (n - 1) - 1) (hlam : lam = 2 ^ (n - 2) - 1) :
    2 ^ (n ^ 2) ≤ (goodTranslations D (2 * n + 6)).card := by
  classical
  set m : ℕ := 2 * n + 6 with hm
  set v : ℕ := Fintype.card (ZMod (2 ^ n - 1)) with hv
  -- `v = 2^n - 1`
  have hvdef : v = 2 ^ n - 1 := ZMod.card (2 ^ n - 1)
  -- difference-set parameters of the Singer family
  have hdiff : D.card - lam = 2 ^ (n - 2) := by
    have hp : 2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
      rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
    have h1 : 1 ≤ 2 ^ (n - 2) := Nat.one_le_two_pow
    rw [hk, hlam, hp]
    omega
  have hc2 : v - 2 * (D.card - lam) = 2 ^ (n - 1) - 1 := by
    have hp : 2 ^ n = 2 ^ (n - 1) * 2 := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ]
    have h2 : 2 * 2 ^ (n - 2) = 2 ^ (n - 1) := by
      rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]; ring
    rw [hvdef, hdiff, hp, h2]
    have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
    omega
  have hv_ge : 2 ^ (n - 1) ≤ v := by
    rw [hvdef]
    have hp : 2 ^ n = 2 ^ (n - 1) * 2 := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ]
    have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
    omega
  -- Theorem 3 in counting form: at most `v^2 (v - 2(k-λ))^m` bad tuples
  have hbad_nat : (badTranslations D m).card ≤ v ^ 2 * (v - 2 * (D.card - lam)) ^ m := by
    have h := card_badTranslations_le (A := ZMod (2 ^ n - 1)) D lam m hD
    simpa [← hv] using h
  -- bad tuples are at most all tuples
  have hbad_le : (badTranslations D m).card ≤ v ^ m := by
    have h := Finset.card_le_card (Finset.subset_univ (badTranslations D m))
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ← hv] at h
    exact h
  -- good tuples are the complement
  have hsplit := card_goodTranslations_add_card_badTranslations (A := ZMod (2 ^ n - 1)) D m
  rw [← hv] at hsplit
  have hgood_nat : (goodTranslations D m).card = v ^ m - (badTranslations D m).card := by
    omega
  -- `(v : ℝ) = 2^n - 1`
  have hvR : (v : ℝ) = (2 : ℝ) ^ n - 1 := by
    rw [hvdef]
    have h1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
    rw [Nat.cast_sub h1, Nat.cast_pow]
    norm_num
  -- the bad count in real form is at most `v^m / 64`
  have hbadr : ((badTranslations D m).card : ℝ) ≤ (v : ℝ) ^ m * (1 / 64) := by
    have hc_eq : ((v - 2 * (D.card - lam) : ℕ) : ℝ) = ((2 : ℝ) ^ (n - 1) - 1) := by
      rw [hc2]
      have h1 : (1 : ℕ) ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
      rw [Nat.cast_sub h1, Nat.cast_pow]
      norm_num
    have hcast : ((badTranslations D m).card : ℝ)
        ≤ (v : ℝ) ^ 2 * (((v - 2 * (D.card - lam) : ℕ)) : ℝ) ^ m := by
      exact_mod_cast hbad_nat
    -- `2 (2^(n-1) - 1) ≤ v`
    have h2c : 2 * ((2 : ℝ) ^ (n - 1) - 1) ≤ (v : ℝ) := by
      rw [hvR]
      have hp : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by
        conv_lhs => rw [show n = (n - 1) + 1 by omega]
        rw [pow_succ]
      rw [hp]; linarith
    have h2c_nonneg : (0 : ℝ) ≤ 2 * ((2 : ℝ) ^ (n - 1) - 1) := by
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (n - 1) := one_le_pow₀ (by norm_num)
      linarith
    have hcm : ((2 : ℝ) ^ (n - 1) - 1) ^ m ≤ (v : ℝ) ^ m / (2 : ℝ) ^ m := by
      have hpow := pow_le_pow_left₀ h2c_nonneg h2c m
      have hmul : (2 : ℝ) ^ m * ((2 : ℝ) ^ (n - 1) - 1) ^ m ≤ (v : ℝ) ^ m := by
        rwa [mul_pow] at hpow
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ m)]
      calc ((2 : ℝ) ^ (n - 1) - 1) ^ m * (2 : ℝ) ^ m
          = (2 : ℝ) ^ m * ((2 : ℝ) ^ (n - 1) - 1) ^ m := by ring
        _ ≤ (v : ℝ) ^ m := hmul
    -- `v^2 / 2^m ≤ 1/64`
    have hratio : (v : ℝ) ^ 2 / (2 : ℝ) ^ m ≤ 1 / 64 := by
      have hv2le : (v : ℝ) ≤ (2 : ℝ) ^ n := by
        rw [hvR]
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
        linarith
      have hsq : (v : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * n) := by
        have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (v : ℝ)) hv2le 2
        rw [← pow_mul, mul_comm] at h
        exact h
      rw [hm]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (2 * n + 6))]
      calc (v : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * n) := hsq
        _ = (1 / 64) * (2 : ℝ) ^ (2 * n + 6) := by rw [pow_add]; norm_num; ring_nf
    calc ((badTranslations D m).card : ℝ)
        ≤ (v : ℝ) ^ 2 * (((2 : ℝ) ^ (n - 1) - 1)) ^ m := by
          rw [hc_eq] at hcast
          exact hcast
      _ ≤ (v : ℝ) ^ 2 * ((v : ℝ) ^ m / (2 : ℝ) ^ m) :=
          mul_le_mul_of_nonneg_left hcm (by positivity)
      _ = (v : ℝ) ^ m * ((v : ℝ) ^ 2 / (2 : ℝ) ^ m) := by ring
      _ ≤ (v : ℝ) ^ m * (1 / 64) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
  -- good count in real form
  have hgoodr : ((goodTranslations D m).card : ℝ)
      = (v : ℝ) ^ m - ((badTranslations D m).card : ℝ) := by
    rw [hgood_nat, Nat.cast_sub hbad_le, Nat.cast_pow]
  have hgood_lb : (v : ℝ) ^ m * (1 - 1 / 64) ≤ ((goodTranslations D m).card : ℝ) := by
    rw [hgoodr]
    nlinarith [hbadr]
  have harith := singer_count_arith n v hn hv_ge
  have harith' : (2 : ℝ) ^ (n ^ 2) ≤ (63 / 64) * (v : ℝ) ^ m := by
    rw [hm]
    exact harith
  have hfin : (2 : ℝ) ^ (n ^ 2) ≤ ((goodTranslations D m).card : ℝ) := by
    calc (2 : ℝ) ^ (n ^ 2) ≤ (63 / 64) * (v : ℝ) ^ m := harith'
      _ = (v : ℝ) ^ m * (1 - 1 / 64) := by ring
      _ ≤ ((goodTranslations D m).card : ℝ) := hgood_lb
  exact_mod_cast hfin

end

end Qatlib.Papers.DihedralSub16.MainResults
