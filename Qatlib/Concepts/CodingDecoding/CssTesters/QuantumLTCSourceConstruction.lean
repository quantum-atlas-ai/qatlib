/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.CodingDecoding.CssTesters.QuantumLTCSourceConstructionDefs
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.CodingDecoding.CssTesters

open Matrix

/-- The fixed parameter one eighth satisfies the stated lower and upper coefficient bounds. -/
theorem fixed_coefficient_bounds :
    (1 / 4 : ℝ) ≤ fixedGammaLower (1 / 8) ∧
    fixedMiddleUpper (1 / 8) < 8 ∧
    (2 : ℝ) ≤ (2 * (1 - (1 / 8 : ℝ))) ^ 2 ∧
    fixedAdjacentUpper (1 / 8) < 8 := by
  norm_num [fixedGammaLower, fixedMiddleUpper, fixedAdjacentUpper]

/-- The fixed rate ratio is at least one thirty-second. -/
theorem fixed_rate_ratio :
    (1 / 32 : ℝ) ≤ fixedGammaLower (1 / 8) / fixedMiddleUpper (1 / 8) := by
  norm_num [fixedGammaLower, fixedMiddleUpper]

/-- The fixed soundness dimension ratio is at least one quarter. -/
theorem fixed_soundness_dimension_ratio :
    (1 / 4 : ℝ) ≤ (2 * (1 - (1 / 8 : ℝ))) ^ 2 / fixedAdjacentUpper (1 / 8) := by
  norm_num [fixedAdjacentUpper]

/-- The fixed starting exponent satisfies all three stated exponent budgets. -/
theorem fixed_exponent_budgets :
    2 ^ 14 + 12 + 68 + 6 * (fixedStartingExponent + 4) < 2 ^ 18 ∧
    2 ^ 14 + 54 + 68 + 24 * (fixedStartingExponent + 4) < 2 ^ 20 ∧
    4 + 68 + 3 * (fixedStartingExponent + 4) < 2 ^ 17 := by
  norm_num [fixedStartingExponent]

/-- For four positive numbers bounded below by `m`, the stated ratio of elementary symmetric
sums is at least one third of `m`. -/
theorem elementary_ratio_lower (a b c d m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hma : m ≤ a) (hmb : m ≤ b) (hmc : m ≤ c) (hmd : m ≤ d) :
    m / 3 ≤ (a*b*c + a*b*d + a*c*d + b*c*d) /
      (2 * (a*b + a*c + a*d + b*c + b*d + c*d)) := by
  have hden : 0 < 2 * (a*b + a*c + a*d + b*c + b*d + c*d) := by positivity
  apply (le_div_iff₀ hden).mpr
  have h1 := mul_le_mul_of_nonneg_left (add_le_add hmc hmd) (mul_pos ha hb).le
  have h2 := mul_le_mul_of_nonneg_left (add_le_add hmb hmd) (mul_pos ha hc).le
  have h3 := mul_le_mul_of_nonneg_left (add_le_add hmb hmc) (mul_pos ha hd).le
  have h4 := mul_le_mul_of_nonneg_left (add_le_add hma hmd) (mul_pos hb hc).le
  have h5 := mul_le_mul_of_nonneg_left (add_le_add hma hmc) (mul_pos hb hd).le
  have h6 := mul_le_mul_of_nonneg_left (add_le_add hma hmb) (mul_pos hc hd).le
  nlinarith only [h1, h2, h3, h4, h5, h6]

/-- The edge boundary composed with the boundary of each cyclically glued square is zero. -/
theorem edgeBoundary_mul_squareBoundary {V E Q : Type*} [Fintype E]
    [DecidableEq V] [DecidableEq E] (start finish : E → V) (edges : Q → Fin 4 → E)
    (hglue : ∀ q j, finish (edges q j) = start (edges q (j + 1))) :
    edgeBoundary start finish * squareBoundary edges = 0 := by
  ext v q
  change (edgeBoundary start finish *ᵥ
    (Pi.single (edges q 0) 1 + Pi.single (edges q 1) 1 +
      Pi.single (edges q 2) 1 + Pi.single (edges q 3) 1)) v = 0
  simp only [Matrix.mulVec_add, Matrix.mulVec_single_one,
    Pi.add_apply, Matrix.col_apply, edgeBoundary]
  rw [hglue q 0, hglue q 1, hglue q 2, hglue q 3]
  let a : Fin 4 → ZMod 2 := fun j => if start (edges q j) = v then 1 else 0
  change (a 0 + a 1) + (a 1 + a 2) + (a 2 + a 3) + (a 3 + a 0) = 0
  have htwo (x : ZMod 2) : x + x = 0 := CharTwo.add_self_eq_zero x
  linear_combination htwo (a 0) + htwo (a 1) + htwo (a 2) + htwo (a 3)

/-- A nonzero polynomial of degree below `k` has the stated minimum number of nonzero
evaluations on a finite set. -/
theorem evaluationWeight_lower {F : Type*} [Field F] (S : Finset F)
    (p : Polynomial F) (hp : p ≠ 0) (k : ℕ) (hk : p.natDegree < k) :
    S.card + 1 - k ≤ evaluationWeight S p := by
  classical
  have hzero : (S.filter fun x => p.eval x = 0).card ≤ p.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro x hx
    exact (Polynomial.mem_roots hp).mpr ((Finset.mem_filter.mp hx).2)
  have hpartition := Finset.card_filter_add_card_filter_not (s := S) (fun x => p.eval x = 0)
  simp only [evaluationWeight, ne_eq] at *
  omega

/-- Multiplying the elementary symmetric dimension expression by the product of the side sizes
gives the cubical cell count. -/
theorem dimension_formula_integral (t j : ℕ) (n : Fin t → ℕ)
    (m : Fin t → Fin 2 → ℕ) (hj : j ≤ t) (hn : ∀ i, 0 < n i) :
    (Finset.univ.prod fun i : Fin t => (n i : ℝ)) *
      elementarySymR t (sIB n m) j = (cubicalCellCount t j n m : ℝ) := by
  classical
  unfold elementarySymR cubicalCellCount
  rw [ite_eq_left hj, Finset.mul_sum]
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_prod, Nat.cast_add]
  apply Finset.sum_congr rfl
  intro s _
  have hden : (∏ i ∈ s, (n i : ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact_mod_cast (Nat.ne_of_gt (hn i))
  simp only [sIB, muIB, ← add_div, Finset.prod_div_distrib]
  rw [← Finset.prod_mul_prod_compl s (fun i : Fin t => (n i : ℝ))]
  field_simp

end Qatlib.Concepts.CodingDecoding.CssTesters
