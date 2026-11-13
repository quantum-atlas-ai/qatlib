/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.FlagProjection.Born

/-!
# Coherent probability amplitudes and pair marginals

`coherent` encodes real weights by square-root complex amplitudes. `pairCoherent` extends this
construction to a two-register state with amplitudes `sqrt (pi i) * sqrt (P j i)`.

For nonnegative weights and a column-stochastic transition matrix, the module proves the pair's
first-register marginal and flagged mass formulas; normalized source weights also give a unit
state. These calculations formalize the pair-state construction in [PaparoEtAl2014].

## Main statements

* `coherent_unit`: probability weights give a unit coherent vector.
* `pair_marginal`: the first-register Born marginal is `pi`.
* `pair_conditional`: the first-register flagged conditional formula is the restricted source
  weight divided by its flagged sum.

## References

* [Paparo et al., 2014][PaparoEtAl2014]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.MatrixGeometry.FlagProjection
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The complex Euclidean vector whose coordinate at `x` is the real square root of `pi x`. -/
def coherent (pi : X → ℝ) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun x => (Real.sqrt (pi x) : ℂ))

omit [Fintype X] [DecidableEq X] in

/-- For nonnegative source weights, the squared amplitude of the coherent vector at `x` equals
`pi x`. -/
theorem coherent_born (pi : X → ℝ) (hn : ∀ x, 0 ≤ pi x) (x : X) :
    ‖(coherent pi).ofLp x‖^2 = pi x := by
  simp [coherent, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hn x)]

omit [DecidableEq X] in

/-- Nonnegative source weights summing to one give a coherent vector with self inner product
one. -/
theorem coherent_unit (pi : X → ℝ) (hn : ∀ x, 0 ≤ pi x) (hs : ∑ x, pi x = 1) :
    inner ℂ (coherent pi) (coherent pi) = 1 := by
  have hnorm : ‖coherent pi‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp_rw [coherent_born pi hn]
    exact hs
  rw [inner_self_eq_norm_sq_to_K]
  simpa only [map_pow, map_one] using congrArg (algebraMap ℝ ℂ) hnorm

omit [Fintype X] [DecidableEq X] in

/-- For nonnegative source weights, the flagged mass of the coherent vector is the sum of those
weights on the flag set. -/
theorem coherent_mass (pi : X → ℝ) (hn : ∀ x, 0 ≤ pi x) (S : Finset X) :
    mass S (coherent pi) = ∑ x ∈ S, pi x := by
  simp [mass, coherent_born pi hn]

/-- The two-register vector with amplitude `sqrt (pi i) * sqrt (P j i)` at coordinate `(i, j)`. -/
def pairCoherent (pi : X → ℝ) (P : X → X → ℝ) : EuclideanSpace ℂ (X × X) :=
  WithLp.toLp 2 (fun ij => (Real.sqrt (pi ij.1) : ℂ) * (Real.sqrt (P ij.2 ij.1) : ℂ))

omit [Fintype X] [DecidableEq X] in

/-- For nonnegative source and transition weights, the squared pair-state amplitude at `(i, j)`
is `pi i * P j i`. -/
theorem pair_born (pi : X → ℝ) (P : X → X → ℝ)
    (hn : ∀ x, 0 ≤ pi x) (hP : ∀ j i, 0 ≤ P j i) (i j : X) :
    ‖(pairCoherent pi P).ofLp (i,j)‖^2 = pi i * P j i := by
  simp [pairCoherent, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hn i), Real.sq_sqrt (hP j i)]

omit [DecidableEq X] in

/-- For nonnegative weights and transition columns summing to one, the pair state's
first-register Born marginal equals `pi`, as in the Equation (9) construction of
[PaparoEtAl2014]. -/
theorem pair_marginal (pi : X → ℝ) (P : X → X → ℝ)
    (hn : ∀ x, 0 ≤ pi x) (hP : ∀ j i, 0 ≤ P j i) (hsP : ∀ i, ∑ j, P j i = 1) (i : X) :
    (∑ j, ‖(pairCoherent pi P).ofLp (i,j)‖^2) = pi i := by
  simp_rw [pair_born pi P hn hP]
  rw [← Finset.mul_sum, hsP i, mul_one]

omit [DecidableEq X] in

/-- Nonnegative source weights summing to one and nonnegative transition columns summing to one
give a pair vector with self inner product one. -/
theorem pair_unit (pi : X → ℝ) (P : X → X → ℝ)
    (hn : ∀ x, 0 ≤ pi x) (hs : ∑ x, pi x = 1)
    (hP : ∀ j i, 0 ≤ P j i) (hsP : ∀ i, ∑ j, P j i = 1) :
    inner ℂ (pairCoherent pi P) (pairCoherent pi P) = 1 := by
  have hnorm : ‖pairCoherent pi P‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    simp_rw [pair_marginal pi P hn hP hsP]
    exact hs
  rw [inner_self_eq_norm_sq_to_K]
  simpa only [map_pow, map_one] using congrArg (algebraMap ℝ ℂ) hnorm

/-- The set of pair coordinates whose first component belongs to `S`, with unrestricted second
component. -/
def pairFlags (S : Finset X) : Finset (X × X) := S ×ˢ Finset.univ

omit [DecidableEq X] in

/-- For nonnegative source weights and a column-stochastic transition matrix, the pair state's
first-register flagged mass is the sum of `pi` on the flags. This gives the nonuniform
flagged input mass used in [PaparoEtAl2014]. -/
theorem pair_mass (pi : X → ℝ) (P : X → X → ℝ)
    (hn : ∀ x, 0 ≤ pi x) (hP : ∀ j i, 0 ≤ P j i) (hsP : ∀ i, ∑ j, P j i = 1)
    (S : Finset X) : mass (pairFlags S) (pairCoherent pi P) = ∑ i ∈ S, pi i := by
  simp only [mass, pairFlags, Finset.sum_product]
  simp_rw [pair_marginal pi P hn hP hsP]

/-- For nonnegative source weights and column-stochastic transitions, summing the flagged
conditional Born function over the second register gives `pi i` divided by the flagged
weight sum on flagged indices, and zero elsewhere. -/
theorem pair_conditional (pi : X → ℝ) (P : X → X → ℝ)
    (hn : ∀ x, 0 ≤ pi x) (hP : ∀ j i, 0 ≤ P j i) (hsP : ∀ i, ∑ j, P j i = 1)
    (S : Finset X) (i : X) :
    (∑ j, conditionalBorn (pairFlags S) (pairCoherent pi P) (i,j)) =
      if i ∈ S then pi i / (∑ x ∈ S, pi x) else 0 := by
  simp only [conditionalBorn, pairFlags, Finset.mem_product, Finset.mem_univ, and_true]
  by_cases hi : i ∈ S
  · simp only [hi, if_true]
    rw [← Finset.sum_div, pair_marginal pi P hn hP hsP, ← pair_mass pi P hn hP hsP S]
    rfl
  · simp [hi]
end Qatlib.Foundations.MatrixGeometry.FlagProjection
