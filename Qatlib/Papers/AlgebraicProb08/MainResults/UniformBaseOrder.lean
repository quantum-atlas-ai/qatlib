/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.OrderRecovery.RandomBaseFactor
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Data.Nat.PrimeFin
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Papers.AlgebraicProb08.MainResults

open Qatlib
open Qatlib.Concepts.PeriodSampling.OrderRecovery
open scoped Classical

noncomputable def algGoodBase (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) : Prop :=
  Even (orderOf a) ∧ ((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N) ≠ -1

noncomputable def algGoodBaseProbability (N : ℕ) [NeZero N] : ℝ :=
  ((Finset.univ.filter (fun a : (ZMod N)ˣ => algGoodBase N a)).card : ℝ) /
    (Fintype.card (ZMod N)ˣ : ℝ)

theorem alg08_one_lt_of_primeFactors_card (N : ℕ) (hk : 2 ≤ N.primeFactors.card) :
    1 < N := by
  have hne : N.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  exact Nat.nonempty_primeFactors.mp hne

theorem alg08_good_base_event_iff_checked_program (N : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (hN : 1 < N) (hodd : Odd N) :
    algGoodBase N a ↔ randomBaseGood N a :=
  (random_base_exact_order_factor_characterization N a hN hodd).symm

theorem alg08_lemma2_refined (N : ℕ) [NeZero N] (hodd : Odd N)
    (hk : 2 ≤ N.primeFactors.card) :
    1 - (2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ)) ≤ algGoodBaseProbability N := by
  have hN : 1 < N := alg08_one_lt_of_primeFactors_card N hk
  have hfilter : (Finset.univ.filter (fun a : (ZMod N)ˣ => algGoodBase N a)) =
      Finset.univ.filter (fun a : (ZMod N)ˣ => randomBaseGood N a) := by
    refine Finset.filter_congr ?_
    intro a _
    exact alg08_good_base_event_iff_checked_program N a hN hodd
  rw [algGoodBaseProbability, hfilter, div_eq_inv_mul]
  exact random_base_crt_success_bound N hN hodd hk

theorem alg08_lemma2_probability (N : ℕ) [NeZero N] (hodd : Odd N)
    (hk : 2 ≤ N.primeFactors.card) :
    (1 / 2 : ℝ) ≤ algGoodBaseProbability N := by
  have hbound := alg08_lemma2_refined N hodd hk
  have hcard : 1 ≤ N.primeFactors.card := by omega
  have hsub : (1 : ℤ) ≤ ((N.primeFactors.card - 1 : ℕ) : ℤ) := by
    have h : 1 ≤ N.primeFactors.card - 1 := by omega
    exact_mod_cast h
  have hle : -(N.primeFactors.card - 1 : ℤ) ≤ -(1 : ℤ) := by omega
  have hpow : (2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ)) ≤ (2 : ℝ) ^ (-(1 : ℤ)) :=
    zpow_le_zpow_right₀ (by norm_num) hle
  have hone : (2 : ℝ) ^ (-(1 : ℤ)) = 1 / 2 := by norm_num
  have hx : (2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ)) ≤ 1 / 2 := hpow.trans hone.le
  linarith

end Qatlib.Papers.AlgebraicProb08.MainResults
