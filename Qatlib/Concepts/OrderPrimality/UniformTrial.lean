/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Foundations.OrderPrimality.GeneratorCount
import Mathlib.Probability.Distributions.Uniform

/-!
# Uniform nonidentity unit trials

For a prime modulus `N ≥ 3`, `sample` chooses uniformly among the nonidentity units. Counting
the units of order `N - 1` gives the exact success probability `φ(N - 1) / (N - 2)`, a finite
trial relevant to the order finding primality test of [DonisVelaGarciaEscartin2017].

## Main statements

* `candidates_good_card`: counts candidates with full multiplicative order.
* `sample_success_mass` and `successProb_eq`: compute the success probability.
* `successProb_pos`: proves that the success probability is positive.

## References

* [Donis-Vela and Garcia-Escartin, 2017][DonisVelaGarciaEscartin2017]
-/

set_option autoImplicit false
noncomputable section
open scoped Finset ENNReal
namespace Qatlib.Concepts.OrderPrimality.UniformTrial
open Qatlib.Foundations.OrderPrimality.GeneratorCount

/-- The finite set of units modulo `N` other than the identity. -/
def candidates (N : ℕ) [NeZero N] : Finset (ZMod N)ˣ := Finset.univ.erase 1

/-- For prime `N ≥ 3`, there are `N - 2` nonidentity units modulo `N`. -/
theorem candidates_card {N : ℕ} [NeZero N] (hp : N.Prime) (hN : 3 ≤ N) :
    (candidates N).card = N-2 := by
  unfold candidates
  rw [Finset.card_erase_of_mem (Finset.mem_univ 1),Finset.card_univ,
    ZMod.card_units_eq_totient,Nat.totient_prime hp]
  omega

/-- For prime `N ≥ 3`, the set of nonidentity units modulo `N` is nonempty. -/
theorem candidates_nonempty {N : ℕ} [NeZero N] (hp : N.Prime) (hN : 3 ≤ N) :
    (candidates N).Nonempty := by
  apply Finset.card_pos.mp
  rw [candidates_card hp hN]
  omega

/-- For prime `N ≥ 3`, exactly `Nat.totient (N - 1)` nonidentity units have order `N - 1`. -/
theorem candidates_good_card {N : ℕ} [NeZero N] (hp : N.Prime) (hN : 3 ≤ N) :
    ((candidates N).filter (fun a => orderOf a=N-1)).card = Nat.totient (N-1) := by
  have hs : (candidates N).filter (fun a => orderOf a=N-1) =
      Finset.univ.filter (fun a : (ZMod N)ˣ => orderOf a=N-1) := by
    ext a
    simp only [Finset.mem_filter,candidates,Finset.mem_erase,Finset.mem_univ,
      and_true,true_and]
    constructor
    · exact And.right
    · intro ho
      refine ⟨?_,ho⟩
      intro ha
      subst a
      simp only [orderOf_one] at ho
      omega
  rw [hs]
  exact card_order_pred_eq_totient hp

/-- The uniform probability mass function on the nonidentity units modulo a prime `N ≥ 3`. -/
def sample {N : ℕ} [NeZero N] (hp : N.Prime) (hN : 3 ≤ N) : PMF (ZMod N)ˣ :=
  PMF.uniformOfFinset (candidates N) (candidates_nonempty hp hN)

/-- For the uniform nonidentity unit trial at prime `N ≥ 3`, the mass of elements with order `N
- 1` is `φ(N - 1) / (N - 2)`. This is the finite candidate trial associated with
[DonisVelaGarciaEscartin2017]. -/
theorem sample_success_mass {N : ℕ} [NeZero N] (hp : N.Prime) (hN : 3 ≤ N) :
    (sample hp hN).toOuterMeasure {a | orderOf a=N-1} =
      (Nat.totient (N-1) : ℝ≥0∞)/(N-2 : ℕ) := by
  rw [sample,PMF.toOuterMeasure_uniformOfFinset'_apply]
  simp only [Set.mem_setOf_eq]
  rw [candidates_good_card hp hN,candidates_card hp hN]

/-- The real probability that a uniformly sampled nonidentity unit has order `N - 1`. -/
def successProb {N : ℕ} [NeZero N] (hp : N.Prime) (hN : 3 ≤ N) : ℝ :=
  ((sample hp hN).toOuterMeasure {a | orderOf a=N-1}).toReal

/-- For prime `N ≥ 3`, the real success probability of the nonidentity unit trial is `φ(N - 1) /
(N - 2)`; see [DonisVelaGarciaEscartin2017]. -/
theorem successProb_eq {N : ℕ} [NeZero N] (hp : N.Prime) (hN : 3 ≤ N) :
    successProb hp hN = (Nat.totient (N-1) : ℝ)/(N-2 : ℕ) := by
  simp only [successProb,sample_success_mass,ENNReal.toReal_div,ENNReal.toReal_natCast]

/-- For prime `N ≥ 3`, the nonidentity unit trial has strictly positive success probability. -/
theorem successProb_pos {N : ℕ} [NeZero N] (hp : N.Prime) (hN : 3 ≤ N) :
    0 < successProb hp hN := by
  rw [successProb_eq]
  apply div_pos
  · exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < N-1)
  · exact_mod_cast (by omega : 0 < N-2)

/-- For prime `N ≥ 3`, the fraction `φ(N - 1) / (N - 1)` is at most the success probability of
sampling only nonidentity units. -/
theorem all_units_fraction_le {N : ℕ} [NeZero N] (hp : N.Prime) (hN : 3 ≤ N) :
    (Nat.totient (N-1) : ℝ)/(N-1 : ℕ) ≤ successProb hp hN := by
  rw [successProb_eq]
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by exact_mod_cast (by omega : 0<N-2))
  exact_mod_cast (by omega : N-2 ≤ N-1)

end Qatlib.Concepts.OrderPrimality.UniformTrial
