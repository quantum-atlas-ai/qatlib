/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.CycleModel
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Cast.Field

@[expose] public section


/-! # Corrected colored-cycle enumeration at the verified small dimensions

Fixed source: Aaronson--Arkhipov, arXiv:1011.3245v1, Proposition 55 (p. 72):
for every integer `c ≥ 1`, `E_{σ ∈ S_n}[c^{cyc(σ)}] = binom(n + c - 1, c - 1)`,
where `cyc(σ)` counts every cycle of `σ` including its fixed points.  The
historical model counted only nontrivial cycles and is refuted by
`Qatlib.Papers.LinearOptics10.StockmeyerSrc.CycleModel.legacyRefuted`.

The corrected `allCycles` count gives the exact source identity at `n = 1` and
`n = 2` for every positive integer `c`. The enumeration for arbitrary `n`
and the extension to noninteger `c` remain open here.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.ColoredCycleCount
open Qatlib.Foundations.ProbabilityCore.Concentration.CycleCount

/-- Every permutation of `Fin 2` is either the identity or the unique
transposition `swap 0 1`. -/
theorem perm_fin_two_cases (sigma : Equiv.Perm (Fin 2)) :
    sigma = 1 ∨ sigma = Equiv.swap 0 1 := by
  decide +revert

/-- The full cycle count of the unique transposition on `Fin 2` is one. -/
theorem allCycles_swap_fin_two : allCycles (Equiv.swap (0 : Fin 2) 1) = 1 := by
  unfold allCycles
  rw [Equiv.Perm.IsCycle.cycleType (Equiv.Perm.isCycle_swap (by decide)),
    Equiv.Perm.support_swap (by decide)]
  simp

/-- Summing over `Perm (Fin 2)` splits into the identity and the swap contributions. -/
theorem sum_perm_fin_two {M : Type*} [AddCommMonoid M] (g : Equiv.Perm (Fin 2) → M) :
    ∑ sigma : Equiv.Perm (Fin 2), g sigma = g 1 + g (Equiv.swap 0 1) := by
  have hsw : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by
    decide
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by
    ext sigma
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact perm_fin_two_cases sigma
  rw [huniv, Finset.sum_insert (by simpa using hsw), Finset.sum_singleton]

/-- Proposition 55 at `n = 1`: the single permutation of `Fin 1` has exactly one
cycle, so the mean of `c^{cyc(σ)}` is `c = binom(c, c - 1)`. -/
theorem prop55_one (c : ℕ) (hc : 1 ≤ c) :
    (∑ sigma : Equiv.Perm (Fin 1), (c : ℝ) ^ allCycles sigma) / (Nat.factorial 1 : ℝ) =
      ((1 + c - 1).choose (c - 1) : ℝ) := by
  have hs (sigma : Equiv.Perm (Fin 1)) : allCycles sigma = 1 := by
    rw [singletonPerm sigma, identityCount]
  simp only [hs, Nat.factorial_one, Nat.cast_one, div_one, pow_one, Finset.sum_const]
  rw [show (Finset.univ.card : ℕ) = 1 by simp, one_smul]
  have h1 : (1 + c - 1 : ℕ) = c := by omega
  have h2 : (c.choose (c - 1) : ℕ) = c := by
    have e : c = c - 1 + 1 := (Nat.sub_add_cancel hc).symm
    rw [e, show c - 1 + 1 - 1 = c - 1 by omega, Nat.choose_succ_self_right]
  rw [h1, h2]

/-- Proposition 55 at `n = 2`: the identity has two cycles and the transposition
has one, so the mean of `c^{cyc(σ)}` is `(c² + c) / 2 = binom(c + 1, c - 1)`. -/
theorem prop55_two (c : ℕ) (hc : 1 ≤ c) :
    (∑ sigma : Equiv.Perm (Fin 2), (c : ℝ) ^ allCycles sigma) / (Nat.factorial 2 : ℝ) =
      ((2 + c - 1).choose (c - 1) : ℝ) := by
  rw [sum_perm_fin_two, identityCount, allCycles_swap_fin_two, pow_one]
  rw [show (Nat.factorial 2 : ℝ) = 2 by norm_num]
  have hch : (c + 1).choose (c - 1) = (c + 1).choose 2 := by
    rw [← Nat.choose_symm (n := c + 1) (k := c - 1) (by omega),
      show c + 1 - (c - 1) = 2 by omega]
  rw [show (2 + c - 1 : ℕ) = c + 1 by omega, hch, Nat.choose_two_right, Nat.cast_div (by
      rcases Nat.even_or_odd' c with ⟨k, hk | hk⟩
      · rw [hk, show 2 * k + 1 - 1 = 2 * k by omega]
        exact ⟨k * (2 * k + 1), by ring⟩
      · rw [hk, show 2 * k + 1 + 1 - 1 = 2 * k + 1 by omega,
          show 2 * k + 1 + 1 = 2 * k + 2 by omega]
        exact ⟨(k + 1) * (2 * k + 1), by ring⟩) (by norm_num),
    Nat.cast_mul]
  push_cast
  ring

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.ColoredCycleCount
