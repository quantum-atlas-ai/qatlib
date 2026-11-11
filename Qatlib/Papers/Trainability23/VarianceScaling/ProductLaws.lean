/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Tactic.Ring

/-!
# Product laws for finite kernel sums

This module factors coordinatewise sums over pairs of Boolean strings and applies the
factorization to a product-distribution kernel self-term. It also proves the subset-sum identity
used to bound weighted correlation mass. See [RudolphEtAl2024].

## Main statements

* `sum_pi_prod_factor`: a double sum of coordinatewise products factors into coordinate sums.
* `mmdQQ_factor`: the product-model kernel self-term factors over coordinates.
* `sum_powerset_pow_factor`: the subset expansion of `(c + d)^n`.

## References

* [Rudolph et al., 2024][RudolphEtAl2024]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.Trainability23.VarianceScaling

open scoped BigOperators

/-- A double sum over Boolean strings of a coordinatewise product factors into the product of
the two-bit sums at each coordinate. -/
theorem sum_pi_prod_factor {n : ℕ} (f : (i : Fin n) → Bool → Bool → ℝ) :
    (∑ x : Fin n → Bool, ∑ y : Fin n → Bool, ∏ i, f i (x i) (y i))
      = ∏ i, (∑ a : Bool, ∑ b : Bool, f i a b) := by
  have hpi : Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset Bool)) = Finset.univ := by
    ext x
    simp [Fintype.mem_piFinset]
  rw [Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Bool))
    (fun i a => ∑ b : Bool, f i a b), hpi]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Bool))
    (fun i b => f i (x i) b), hpi]

/-- The kernel self-term for a product of finite Boolean distributions and a product kernel
factors into its coordinatewise self-terms. -/
theorem mmdQQ_factor {n : ℕ} (q : Fin n → FinDist Bool) (K : Fin n → Bool → Bool → ℝ) :
    (∑ x : Fin n → Bool, ∑ y : Fin n → Bool,
        (∏ i, (q i).prob (x i)) * (∏ i, (q i).prob (y i)) * (∏ i, K i (x i) (y i)))
      = ∏ i, (∑ a : Bool, ∑ b : Bool, (q i).prob a * (q i).prob b * K i a b) := by
  rw [← sum_pi_prod_factor (fun i a b => (q i).prob a * (q i).prob b * K i a b)]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

/-- Summing `c^(n - A.card) * d^A.card` over all subsets of `Fin n` gives `(c + d)^n`. -/
theorem sum_powerset_pow_factor (n : ℕ) (c d : ℝ) :
    (∑ A ∈ (Finset.univ : Finset (Fin n)).powerset, c ^ (n - A.card) * d ^ A.card)
      = (c + d) ^ n := by
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  have hinner : ∀ j : ℕ,
      (∑ A ∈ Finset.powersetCard j (Finset.univ : Finset (Fin n)),
          c ^ (n - A.card) * d ^ A.card)
        = (n.choose j : ℝ) * (c ^ (n - j) * d ^ j) := by
    intro j
    have h := Finset.sum_powersetCard j (Finset.univ : Finset (Fin n))
      (fun m => c ^ (n - m) * d ^ m)
    rw [hcard] at h
    simpa [nsmul_eq_mul] using h
  rw [Finset.sum_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_congr rfl fun j _ => hinner j, add_comm c d, add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end Qatlib.Papers.Trainability23.VarianceScaling
