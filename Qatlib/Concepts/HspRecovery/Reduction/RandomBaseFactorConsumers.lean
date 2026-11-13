/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.OrderRecovery.RandomBaseFactor

/-!
# Repetition bounds for random-base factoring

This module turns a success bound for one uniformly sampled base into a bound for independent
repetitions. It applies the random-base estimate from the order-finding reduction of [Shor1997]
to odd moduli with at least two distinct prime factors.

## Main statements

* `uniform_fresh_success_bound`: one-trial failure bounded by `q` gives repeated success at
  least `1 - q ^ R`.
* `random_base_verified_fresh_failure_consumer`: the repeated random-base estimate together with
  soundness of every returned order-based factor.

## References

* [Shor, 1997][Shor1997]
-/

open Qatlib.Concepts.PeriodSampling.OrderRecovery

set_option autoImplicit false

noncomputable section
namespace Qatlib.Concepts.HspRecovery.ReductionCore
open scoped Classical BigOperators

set_option backward.isDefEq.respectTransparency false in

/-- If a predicate holds with probability at least `1 - q` under the uniform law on a nonempty
finite type, it holds in at least one of `R` independent uniform samples with probability at
least `1 - q ^ R`. -/
private theorem uniform_fresh_success_bound {A : Type*} [Fintype A] [Nonempty A]
    (P : A → Prop) (R : ℕ) (q : ℝ)
    (hP : 1 - q ≤ (Fintype.card A : ℝ)⁻¹ *
      ((Finset.univ.filter P).card : ℝ)) :
    1 - q ^ R ≤ (Fintype.card (Fin R → A) : ℝ)⁻¹ *
      ((Finset.univ.filter (fun ω : Fin R → A => ∃ j, P (ω j))).card : ℝ) := by
  let good := Finset.univ.filter P
  let bad := Finset.univ.filter (fun a : A => ¬ P a)
  let goodRecords := Finset.univ.filter (fun ω : Fin R → A => ∃ j, P (ω j))
  let badRecords := Finset.univ.filter (fun ω : Fin R → A => ∀ j, ¬ P (ω j))
  have hpartition : good.card + bad.card = Fintype.card A :=
    Finset.card_filter_add_card_filter_not _
  have hrecords : goodRecords.card + badRecords.card = Fintype.card (Fin R → A) := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin R → A))) (fun ω => ∃ j, P (ω j))
    simpa only [not_exists, Finset.card_univ, goodRecords, badRecords] using! h
  have hbadRecords : badRecords.card = bad.card ^ R := by
    let e : {ω : Fin R → A // ∀ j, ¬ P (ω j)} ≃
        (Fin R → {a : A // ¬ P a}) :=
      Equiv.subtypePiEquivPi (p := fun (_ : Fin R) (a : A) => ¬ P a)
    have h := Fintype.card_congr e
    simpa only [Fintype.card_subtype, Fintype.card_pi_const, bad, badRecords] using! h
  have hA : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  have hpart : (good.card : ℝ) + (bad.card : ℝ) = (Fintype.card A : ℝ) := by
    exact_mod_cast hpartition
  have hbad : (bad.card : ℝ) / (Fintype.card A : ℝ) ≤ q := by
    rw [div_le_iff₀ hA]
    change 1 - q ≤ (Fintype.card A : ℝ)⁻¹ * (good.card : ℝ) at hP
    rw [← div_eq_inv_mul, le_div_iff₀ hA] at hP
    nlinarith
  have hp : ((bad.card : ℝ) / (Fintype.card A : ℝ)) ^ R ≤ q ^ R := by
    gcongr
  have hrec : (goodRecords.card : ℝ) + (bad.card : ℝ) ^ R =
      (Fintype.card A : ℝ) ^ R := by
    rw [hbadRecords, Fintype.card_pi_const] at hrecords
    exact_mod_cast hrecords
  change 1 - q ^ R ≤ (Fintype.card (Fin R → A) : ℝ)⁻¹ * (goodRecords.card : ℝ)
  rw [Fintype.card_pi_const, Nat.cast_pow, ← div_eq_inv_mul, le_div_iff₀ (pow_pos hA R)]
  have hpow : (bad.card : ℝ) ^ R ≤ q ^ R * (Fintype.card A : ℝ) ^ R := by
    rw [div_pow, div_le_iff₀ (pow_pos hA R)] at hp
    exact hp
  nlinarith

/-- For odd `N > 1` with `k ≥ 2` distinct prime factors, `R` independent uniform units include a
good base with probability at least `1 - (2 ^ (-(k - 1))) ^ R`. Every factor returned from a
unit's exact order is a proper divisor of `N`, in the factoring reduction of [Shor1997]. -/
theorem random_base_verified_fresh_failure_consumer :
    ∀ (N R : ℕ) [NeZero N], 1 < N → Odd N → 2 ≤ N.primeFactors.card →
      ((Fintype.card (Fin R → (ZMod N)ˣ) : ℝ)⁻¹ *
        ((Finset.univ.filter (fun ω : Fin R → (ZMod N)ˣ =>
          ∃ j : Fin R, randomBaseGood N (ω j))).card : ℝ)) ≥
          1 - ((2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ))) ^ R ∧
      (∀ (a : (ZMod N)ˣ) (d : ℕ),
        orderFactor N a (orderOf a) = some d → 1 < d ∧ d < N ∧ d ∣ N) := by
  intro N R _ hN hodd hk
  refine ⟨?_, fun a d h => orderFactor_sound N a (orderOf a) d h⟩
  exact uniform_fresh_success_bound (randomBaseGood N) R
    ((2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ)))
    (random_base_crt_success_bound N hN hodd hk)

end Qatlib.Concepts.HspRecovery.ReductionCore
