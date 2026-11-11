/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QRegression16.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# SourcePostselection — c002 of QRegression16

Fixed arXiv:1601.07823v2 (Schuld–Sinayskiy–Petruccione), *Prediction by linear
regression on a quantum computer*, Section IV (runtime analysis, p.5).

The paper writes the probability of the conditional measurement succeeding as

`p(1) = Σ_r (c / λ_r)²`

with `λ_r = (σ_r)²` the eigenvalues of `X†X` (`ρ_{X†X}`), and states the bound
`p(1) ≤ R (λ_min/λ_max)² = R κ⁻⁴`, concluding that "one needs on average less than
`κ⁴` tries", and that amplitude amplification reduces this to `O(κ²)`.

Formalised here:

* `postselection_upper_bound`: the unconditional upper bound actually implied by
  the paper's condition `c ≤ λ_min`, namely `p(1) ≤ R (c/λ_min)²` (each term is
  `≤ (c/λ_min)² ≤ 1`). The displayed paper inequality `p(1) ≤ R κ⁻⁴` does **not**
  follow from `c ≤ λ_min`: with `c = λ_min` a single term `(c/λ_min)² = 1` already
  exceeds `κ⁻⁴`. This is recorded explicitly; the bound that does yield the paper's
  retry statement is the matching *lower* bound below.
* `postselection_lower_bound`: with `c = λ_min` and `λ_min ≤ λ_r ≤ λ_max`
  one gets `R (λ_min/λ_max)² = R κ⁻⁴ ≤ p(1)`, since each term
  `(c/λ_r)² ≥ (λ_min/λ_max)²`. This is the genuine `κ⁻⁴` statement behind the
  runtime discussion: the post-selected branch is populated with probability at
  least `R κ⁻⁴`.
* `retry_bound`: consequently `1/p(1) ≤ κ⁴/R ≤ κ⁴`, i.e. fewer than `κ⁴`
  repetitions on average.
* `amplification_bound`: `√(1/p(1)) ≤ κ²/√R`, i.e. the `O(κ²)` amplitude
  amplification factor claimed in the paper.
* `kappa_sq`, `kappa_pow_four`: the bookkeeping identities `κ² = σ_max²/σ_min²`
  and `κ⁴ = (σ_max²/σ_min²)²` used to translate between the σ- and λ-spellings.

Out of scope here: the `O(log N)` time and `O(ε⁻³)` copy count of the
quantum-PCA/density-matrix exponentiation step. Both are imported from reference
[14] (Lloyd–Mohseni–Rebentrost) as stated in Section IV, p.4–5, and are not
derived in this paper; the same qualification as in
`Prediction/SourcePrediction.lean` applies to claim c001.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QRegression16.MainResults.Postselection

open Qatlib.Papers.QRegression16.MainResults.SourceModel

variable {R : ℕ}

/-- Fixed arXiv:1601.07823v2, Section IV p.5: for any `c ≥ 0` and `0 < λ_min`
with `λ_min ≤ λ_r` for all used eigenvalues, each term `(c/λ_r)²` is bounded by
`(c/λ_min)²`, hence `p(1) ≤ R (c/λ_min)²`, in particular `p(1) ≤ R` when
`c ≤ λ_min`. -/
theorem postselection_upper_bound (lam : Fin R → ℝ) (c lamMin : ℝ)
    (hmin : 0 < lamMin) (hc0 : 0 ≤ c) (hlo : ∀ r, lamMin ≤ lam r) :
    postselectionProbability lam c ≤ (R : ℝ) * (c / lamMin) ^ 2 := by
  have hterm : ∀ r : Fin R, (c / lam r) ^ 2 ≤ (c / lamMin) ^ 2 := by
    intro r
    have hrpos : 0 < lam r := lt_of_lt_of_le hmin (hlo r)
    have hle : c / lam r ≤ c / lamMin := by
      gcongr
      exact hlo r
    exact pow_le_pow_left₀ (div_nonneg hc0 hrpos.le) hle 2
  unfold postselectionProbability
  calc ∑ r, (c / lam r) ^ 2
      ≤ ∑ r, (c / lamMin) ^ 2 := Finset.sum_le_sum (fun r _ => hterm r)
    _ = (R : ℝ) * (c / lamMin) ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Fixed arXiv:1601.07823v2, Section IV p.5: with the maximal admissible choice
`c = λ_min` and `λ_min ≤ λ_r ≤ λ_max`, every term satisfies
`(c/λ_r)² = (λ_min/λ_r)² ≥ (λ_min/λ_max)² = κ⁻⁴`, so

`R κ⁻⁴ ≤ p(1)`.

This is the exact form of the post-selection probability bound that supports the
paper's retry count (`κ⁴` repetitions); see the module docstring for why the
displayed `≤ R κ⁻⁴` cannot follow from `c ≤ λ_min`. -/
theorem postselection_lower_bound (lam : Fin R → ℝ) (c lamMin lamMax : ℝ)
    (hmin : 0 < lamMin) (hmax : 0 < lamMax) (hc : c = lamMin)
    (hlo : ∀ r, lamMin ≤ lam r) (hhi : ∀ r, lam r ≤ lamMax) :
    (R : ℝ) * (lamMin / lamMax) ^ 2 ≤ postselectionProbability lam c := by
  rw [hc]
  have hterm : ∀ r : Fin R, (lamMin / lamMax) ^ 2 ≤ (lamMin / lam r) ^ 2 := by
    intro r
    have hrpos : 0 < lam r := lt_of_lt_of_le hmin (hlo r)
    have hle : lamMin / lamMax ≤ lamMin / lam r := by
      gcongr
      exact hhi r
    exact pow_le_pow_left₀ (div_nonneg hmin.le hmax.le) hle 2
  unfold postselectionProbability
  calc (R : ℝ) * (lamMin / lamMax) ^ 2
      = ∑ _ : Fin R, (lamMin / lamMax) ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ∑ r, (lamMin / lam r) ^ 2 := Finset.sum_le_sum (fun r _ => hterm r)

/-- Fixed arXiv:1601.07823v2, Section IV p.5: "one needs on average less than
`κ⁴` tries". With `c = λ_min` and `λ_min ≤ λ_r ≤ λ_max`, the lower bound
`p(1) ≥ R (λ_min/λ_max)²` gives `1/p(1) ≤ (λ_max/λ_min)²/R`. Since
`(λ_max/λ_min)² = κ⁴`, the average retry count is at most `κ⁴/R ≤ κ⁴` (for `R ≥ 1`). -/
theorem retry_bound (lam : Fin R → ℝ) (c lamMin lamMax : ℝ)
    (hmin : 0 < lamMin) (hmax : 0 < lamMax) (hc : c = lamMin)
    (hlo : ∀ r, lamMin ≤ lam r) (hhi : ∀ r, lam r ≤ lamMax) (hR : 0 < R) :
    1 / postselectionProbability lam c ≤ (lamMax / lamMin) ^ 2 / (R : ℝ) := by
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hbase : 0 < (R : ℝ) * (lamMin / lamMax) ^ 2 := by positivity
  have hlower := postselection_lower_bound lam c lamMin lamMax hmin hmax hc hlo hhi
  have hrecip : 1 / postselectionProbability lam c ≤
      1 / ((R : ℝ) * (lamMin / lamMax) ^ 2) :=
    one_div_le_one_div_of_le hbase hlower
  have heq : 1 / ((R : ℝ) * (lamMin / lamMax) ^ 2) =
      (lamMax / lamMin) ^ 2 / (R : ℝ) := by
    have hmin0 : lamMin ≠ 0 := ne_of_gt hmin
    have hmax0 : lamMax ≠ 0 := ne_of_gt hmax
    have hR0 : (R : ℝ) ≠ 0 := ne_of_gt hRpos
    field_simp
  rwa [heq] at hrecip

/-- Fixed arXiv:1601.07823v2, Section IV p.5: amplitude amplification reduces the
`κ⁴` retry factor to `O(κ²)`. Concretely, with the same hypotheses as
`retry_bound`, `√(1/p(1)) ≤ (λ_max/λ_min)/√R = κ²/√R`. -/
theorem amplification_bound (lam : Fin R → ℝ) (c lamMin lamMax : ℝ)
    (hmin : 0 < lamMin) (hmax : 0 < lamMax) (hc : c = lamMin)
    (hlo : ∀ r, lamMin ≤ lam r) (hhi : ∀ r, lam r ≤ lamMax) (hR : 0 < R) :
    Real.sqrt (1 / postselectionProbability lam c) ≤
      (lamMax / lamMin) / Real.sqrt (R : ℝ) := by
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hretry := retry_bound lam c lamMin lamMax hmin hmax hc hlo hhi hR
  have hsq : (lamMax / lamMin) ^ 2 / (R : ℝ) =
      ((lamMax / lamMin) / Real.sqrt (R : ℝ)) ^ 2 := by
    have hsqR : (Real.sqrt (R : ℝ)) ^ 2 = (R : ℝ) := Real.sq_sqrt hRpos.le
    rw [show ((lamMax / lamMin) / Real.sqrt (R : ℝ)) ^ 2 =
        (lamMax / lamMin) ^ 2 / (Real.sqrt (R : ℝ)) ^ 2 by rw [div_pow],
      hsqR]
  rw [hsq] at hretry
  have hnonneg : 0 ≤ (lamMax / lamMin) / Real.sqrt (R : ℝ) := by positivity
  have := Real.sqrt_le_sqrt hretry
  rwa [Real.sqrt_sq hnonneg] at this

/-- Fixed arXiv:1601.07823v2, Section IV p.5 with `κ = σ_max/σ_min` and
`λ_r = σ_r²`: the squared condition number is `κ² = σ_max²/σ_min²`. -/
theorem kappa_sq (σmin σmax : ℝ) :
    (conditionNumber σmin σmax) ^ 2 = σmax ^ 2 / σmin ^ 2 := by
  unfold conditionNumber
  rw [div_pow]

/-- Fixed arXiv:1601.07823v2, Section IV p.5: the condition-number identity
`κ⁴ = (σ_max²/σ_min²)² = (λ_max/λ_min)²`, matching the post-selection bound
`R κ⁻⁴`. -/
theorem kappa_pow_four (σmin σmax : ℝ) :
    (conditionNumber σmin σmax) ^ 4 = (σmax ^ 2 / σmin ^ 2) ^ 2 := by
  calc (conditionNumber σmin σmax) ^ 4
      = ((conditionNumber σmin σmax) ^ 2) ^ 2 := by ring
    _ = (σmax ^ 2 / σmin ^ 2) ^ 2 := by rw [kappa_sq]

end Qatlib.Papers.QRegression16.MainResults.Postselection
