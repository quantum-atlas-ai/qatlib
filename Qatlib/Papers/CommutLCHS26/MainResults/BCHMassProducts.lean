/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHPerturbation
import Mathlib.Algebra.Order.Antidiag.Pi

/-!
# Products of commutator mass series

This module groups products of nonnegative summable sequences by total degree using
`degreeEquiv`. The specialized profile `massProfile` records products of odd commutator mass
terms with a fixed total index.

Under `OddControl`, these profiles sum to powers of `commutatorMass` and bound the Dyson
remainder for repeated symmetric steps with Hermitian generators. This supplies the mass product
estimates used in [AftabAnTrivisa2026].

## Main statements

* `degree_hasSum`: groups a product series by total degree.
* `massProfile_hasSum`: sums the mass profile to a power of the commutator mass.
* `remainder_profile_bound`: bounds the Dyson remainder by the total profile with repetition and
  factorial denominators.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHMassProducts

open Matrix
open scoped BigOperators Classical Matrix.Norms.L2Operator NNReal ENNReal
open BCHControlled BCHCommMass BCHPerturbation
open Qatlib.Concepts.TrotterFormula.GeneralOrder

/-- For a summable nonnegative real sequence, the sum of products over p tuples equals the pth
power of its sum. -/
theorem tuple_hasSum (f : ℕ → ℝ) (hf : Summable f) (hpos : ∀ n, 0 ≤ f n) (p : ℕ) :
    HasSum (fun v : Fin p → ℕ => ∏ i, f (v i)) ((∑' n, f n) ^ p) := by
  induction p with
  | zero =>
    have h := hasSum_unique (fun v : Fin 0 → ℕ => ∏ i, f (v i))
    simpa only [Fin.prod_univ_zero, pow_zero] using! h
  | succ p ih =>
    have hprod := hf.mul_of_nonneg ih.summable hpos (fun v => Finset.prod_nonneg fun i _ => hpos _)
    have h := hf.hasSum.mul ih hprod
    have he : HasSum (fun v : ℕ × (Fin p → ℕ) =>
        ∏ i : Fin (p + 1), f ((Fin.cons v.1 v.2 : Fin (p + 1) → ℕ) i))
        ((∑' n, f n) ^ (p + 1)) := by
      simpa only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, pow_succ'] using! h
    exact (Fin.consEquiv (fun _ : Fin (p + 1) => ℕ)).hasSum_iff.mp he

/-- The equivalence between tuples of natural numbers grouped by total degree and all tuples of
natural numbers. -/
def degreeEquiv (p : ℕ) : (Σ n : ℕ, ↥(Finset.finAntidiagonal p n)) ≃ (Fin p → ℕ) where
  toFun v := v.2.1
  invFun v := ⟨∑ i, v i, ⟨v, Finset.mem_finAntidiagonal.mpr rfl⟩⟩
  left_inv := by
    rintro ⟨n, ⟨v, hv⟩⟩
    have hn : ∑ i, v i = n := Finset.mem_finAntidiagonal.mp hv
    subst n
    rfl
  right_inv _ := rfl

/-- Grouping products of a summable nonnegative sequence by total degree gives a series summing
to the pth power of its sum. -/
theorem degree_hasSum (f : ℕ → ℝ) (hf : Summable f) (hpos : ∀ n, 0 ≤ f n) (p : ℕ) :
    HasSum (fun n => ∑ v ∈ Finset.finAntidiagonal p n, ∏ i, f (v i)) ((∑' n, f n) ^ p) := by
  have hs := (degreeEquiv p).hasSum_iff.mpr (tuple_hasSum f hf hpos p)
  apply hs.sigma
  intro n
  change HasSum (fun v : ↥(Finset.finAntidiagonal p n) => ∏ i, f (v.1 i)) _
  have he : (∑ v : ↥(Finset.finAntidiagonal p n), ∏ i, f (v.1 i)) =
      ∑ v ∈ Finset.finAntidiagonal p n, ∏ i, f (v i) :=
    Finset.sum_coe_sort (Finset.finAntidiagonal p n) (fun v : Fin p → ℕ => ∏ i, f (v i))
  rw [← he]
  exact hasSum_fintype _

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The sum of products of `p` commutator mass terms with total index `n`. -/
def massProfile (xs : List (Matrix I I ℂ)) (t : ℝ) (p n : ℕ) : ℝ :=
  ∑ v ∈ Finset.finAntidiagonal p n, ∏ i, massTerm xs t (v i)

omit [DecidableEq I] in

/-- A tuple of total index `n` contributes the factor `|t|^(2*n + 3*p)` times the product of the
corresponding commutator bounds divided by squared degrees. -/
theorem tuple_mass_degree (xs : List (Matrix I I ℂ)) (t : ℝ) (p n : ℕ)
    (v : Fin p → ℕ) (hv : v ∈ Finset.finAntidiagonal p n) :
    (∏ i, massTerm xs t (v i)) = |t| ^ (2 * n + 3 * p) *
      ∏ i, (pfCommAlphaSelf xs (2 * v i + 3) / ((2 * v i + 3 : ℕ) : ℝ) ^ 2) := by
  have he : ∑ i, (2 * v i + 3) = 2 * n + 3 * p := by
    have hsum : ∑ i, v i = n := Finset.mem_finAntidiagonal.mp hv
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  calc
    _ = ∏ i, (|t| ^ (2 * v i + 3) *
        (pfCommAlphaSelf xs (2 * v i + 3) / ((2 * v i + 3 : ℕ) : ℝ) ^ 2)) := by
      apply Finset.prod_congr rfl
      intro i _
      unfold massTerm
      ring
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, he]

/-- Under `OddControl` and within its radius, the mass profile sums to the pth power of the
commutator mass. -/
theorem massProfile_hasSum (xs : List (Matrix I I ℂ)) (r : ℝ≥0) (J : ℕ)
    (hc : OddControl xs r J) (t : ℝ) (ht : |t| ≤ r) (p : ℕ) :
    HasSum (massProfile xs t p) (commutatorMass xs t ^ p) :=
  degree_hasSum _ (massTerm_summable xs r J hc t ht) (massTerm_nonneg xs t) p

/-- For Hermitian generators under `OddControl`, positive repetition count and positive
remainder order, the Dyson remainder norm is bounded by the total mass profile divided by
the repetition count to power `2*p` and by `p!`. -/
theorem remainder_profile_bound (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (r : ℝ≥0) (J : ℕ) (hc : OddControl xs r J)
    (q : ℕ) (hq : 0 < q) (t : ℝ) (ht : |t| ≤ r) (p : ℕ) (hp : 0 < p) :
    ‖PerturbationDyson.remainder (t • ((-Complex.I) • xs.sum)) (perturbation xs q t) p 1‖ ≤
      (∑' n, massProfile xs t p n) / ((q : ℝ) ^ (2 * p) * (p.factorial : ℝ)) := by
  have h := (repetition_expansion xs hxs r J hc q hq t ht p hp).2
  rw [(massProfile_hasSum xs r J hc t ht p).tsum_eq]
  convert! h using 1
  rw [div_pow, div_div, ← pow_mul]

end Qatlib.Papers.CommutLCHS26.MainResults.BCHMassProducts
