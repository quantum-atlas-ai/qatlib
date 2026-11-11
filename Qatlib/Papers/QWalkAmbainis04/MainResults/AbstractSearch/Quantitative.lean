/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Qatlib.Papers.QWalkAmbainis04.MainResults.AbstractSearch.EigenEngine

/-!
# Quantitative bounds for abstract quantum search

`SpecIdx`, `phase`, and `goodVec` encode a distinguished zero phase and conjugate phase pairs
with real coefficients. The condition `cotEq` expresses orthogonality to the auxiliary vector
`wPrime`.

Trigonometric identities convert this condition into an exact equation for the search phase and
explicit upper and lower bounds for its square, under the stated phase separation hypotheses.
This development supports the analysis in [AmbainisKempeRivosh2004].

## Main statements

* `alpha_exact_eq`: rewrite the cotangent equation in terms of cosine differences.
* `alpha_sq_upper`: bound the squared search phase from above.
* `alpha_sq_lower`: bound the squared search phase from below under stronger separation.

## References

* [Ambainis et al., 2004][AmbainisKempeRivosh2004]
-/

set_option warningAsError false

open Matrix
open scoped BigOperators ComplexOrder

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalkAmbainis04.MainResults.AbstractSearch.Quantitative

open Eigen

/-- The spectral index type consisting of one distinguished index and a signed pair for each
element of `Fin m`. -/
abbrev SpecIdx (m : ℕ) := Option (Fin m × Bool)

/-- The spectral phase function assigning zero to the distinguished index and `θ j` and `-θ j`
to each paired index. -/
def phase {m : ℕ} (θ : Fin m → ℝ) : SpecIdx m → ℝ
  | none => 0
  | some (j, true) => θ j
  | some (j, false) => -θ j

/-- The complex vector with coefficient `a0` at the distinguished index and the real coefficient
`a j` at both indices of each pair. -/
def goodVec {m : ℕ} (a0 : ℝ) (a : Fin m → ℝ) : SpecIdx m → ℂ
  | none => (a0 : ℂ)
  | some (j, _) => (a j : ℂ)

/-- The squared norm of `goodVec a0 a` is `a0 ^ 2 + 2 * ∑ j, (a j) ^ 2`. -/
lemma normSq_goodVec {m : ℕ} (a0 : ℝ) (a : Fin m → ℝ) :
    normSq (goodVec a0 a) = a0 ^ 2 + 2 * ∑ j, (a j) ^ 2 := by
  have hsq : ∀ z : ℝ, ‖((z : ℂ))‖ ^ 2 = z ^ 2 := by
    intro z
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [normSq, goodVec]
  rw [Fintype.sum_option]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, hsq]
  have h2 : (∑ j : Fin m, ((a j) ^ 2 + (a j) ^ 2)) = 2 * ∑ j, (a j) ^ 2 := by
    rw [Finset.sum_add_distrib, ← two_mul, Finset.mul_sum]
  rw [h2]

/-- The vector `goodVec a0 a` has inner product one with itself when its coefficients satisfy
the stated normalization. -/
lemma inner_goodVec {m : ℕ} (a0 : ℝ) (a : Fin m → ℝ)
    (h : a0 ^ 2 + 2 * ∑ j, (a j) ^ 2 = 1) :
    inner (goodVec a0 a) (goodVec a0 a) = 1 := by
  rw [Eigen.inner_self_cast, normSq_goodVec, h, Complex.ofReal_one]

/-- The weighted cotangent equation in `α` obtained from the zero phase and the paired phases
`±θ j`. -/
def cotEq {m : ℕ} (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ) : Prop :=
  a0 ^ 2 * Real.cot (α / 2) +
    ∑ j : Fin m, (a j) ^ 2 *
      (Real.cot ((α - θ j) / 2) + Real.cot ((α + θ j) / 2)) = 0

/-- The inner product of `goodVec` with `wPrime` is the complex embedding of the weighted
cotangent expression. -/
lemma inner_goodVec_wPrime {m : ℕ} (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ)
    (α : ℝ) :
    inner (goodVec a0 a) (wPrime (phase θ) (goodVec a0 a) α)
      = ((a0 ^ 2 * Real.cot (α / 2) +
          ∑ j : Fin m, (a j) ^ 2 *
            (Real.cot ((α - θ j) / 2) + Real.cot ((α + θ j) / 2)) : ℝ) : ℂ) := by
  rw [Eigen.inner_wPrime_cast]
  congr 1
  have hsq : ∀ z : ℝ, ‖((z : ℂ))‖ ^ 2 = z ^ 2 := by
    intro z
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [goodVec, phase]
  rw [Fintype.sum_option]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, hsq, sub_neg_eq_add]
  have h0 : (α - 0) / 2 = α / 2 := by ring
  have key : (∑ x : Fin m,
        ((a x) ^ 2 * ((α - θ x) / 2).cot + (a x) ^ 2 * ((α + θ x) / 2).cot))
      = ∑ j : Fin m, (a j) ^ 2 *
          (((α - θ j) / 2).cot + ((α + θ j) / 2).cot) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h0, key]

/-- The cotangent equation implies orthogonality of `goodVec` and the corresponding auxiliary
vector `wPrime`. -/
lemma orth_goodVec_of_cotEq {m : ℕ} (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ)
    {α : ℝ} (h : cotEq θ a0 a α) :
    inner (goodVec a0 a) (wPrime (phase θ) (goodVec a0 a) α) = 0 := by
  rw [inner_goodVec_wPrime]
  rw [cotEq] at h
  rw [h, Complex.ofReal_zero]

/-- Division by a fixed real number distributes over a finite sum. -/
lemma sum_div_finset {ι : Type*} (s : Finset ι) (f : ι → ℝ) (c : ℝ) :
    (∑ i ∈ s, f i) / c = ∑ i ∈ s, f i / c := by
  rw [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]

/-- For angles with nonzero sine, the sum of their cotangents equals `sin (x + y) / (sin x * sin
y)`. -/
lemma cot_add_eq (x y : ℝ) (hx : Real.sin x ≠ 0) (hy : Real.sin y ≠ 0) :
    Real.cot x + Real.cot y = Real.sin (x + y) / (Real.sin x * Real.sin y) := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  field_simp [hx, hy]
  rw [Real.sin_add]
  ring

/-- The cotangents of the paired half angles sum to `2 * sin α / (cos θ - cos α)` under the
stated nonvanishing conditions. -/
lemma cot_pair_eq {α θ : ℝ}
    (h1 : Real.sin ((α - θ) / 2) ≠ 0) (h2 : Real.sin ((α + θ) / 2) ≠ 0)
    (_hcos : Real.cos θ ≠ Real.cos α) :
    Real.cot ((α - θ) / 2) + Real.cot ((α + θ) / 2)
      = 2 * Real.sin α / (Real.cos θ - Real.cos α) := by
  have hx : ((α - θ) / 2) + ((α + θ) / 2) = α := by ring
  rw [cot_add_eq _ _ h1 h2, hx]
  have hprod : Real.cos θ - Real.cos α
      = 2 * (Real.sin ((α + θ) / 2) * Real.sin ((α - θ) / 2)) := by
    have h := Real.cos_sub_cos θ α
    have hneg : Real.sin ((θ - α) / 2) = -Real.sin ((α - θ) / 2) := by
      have : (θ - α) / 2 = -((α - θ) / 2) := by ring
      rw [this, Real.sin_neg]
    rw [h, hneg]
    ring
  rw [hprod]
  have hne : Real.sin ((α + θ) / 2) * Real.sin ((α - θ) / 2) ≠ 0 :=
    mul_ne_zero h2 h1
  field_simp [hne]

/-- The quotient `cot (α / 2) / sin α` equals `1 / (1 - cos α)` when the half-angle sine and
cosine are nonzero. -/
lemma cot_half_div_sin {α : ℝ} (h : Real.sin (α / 2) ≠ 0) (hc : Real.cos (α / 2) ≠ 0) :
    Real.cot (α / 2) / Real.sin α = 1 / (1 - Real.cos α) := by
  have h1 : (1 : ℝ) - Real.cos α = 2 * Real.sin (α / 2) ^ 2 := by
    have hcos := Real.cos_two_mul (α / 2)
    have hsq := Real.sin_sq_add_cos_sq (α / 2)
    rw [show (2 : ℝ) * (α / 2) = α by ring] at hcos
    nlinarith
  have hsα : Real.sin α = 2 * Real.sin (α / 2) * Real.cos (α / 2) := by
    simpa only [show (2 : ℝ) * (α / 2) = α by ring] using Real.sin_two_mul (α / 2)
  have hs : Real.sin α ≠ 0 := by
    rw [hsα]
    exact mul_ne_zero (mul_ne_zero (by norm_num) h) hc
  rw [Real.cot_eq_cos_div_sin, hsα, h1]
  field_simp [h, hc]

/-- For a positive search phase below all phases in `(0, π)`, `cotEq` yields the exact identity
relating `a0 ^ 2 / (1 - cos α)` to the weighted cosine denominators. See
[AmbainisKempeRivosh2004]. -/
theorem alpha_exact_eq {m : ℕ} (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ)
    {α : ℝ} (hm : 0 < m) (hθpos : ∀ j, 0 < θ j) (hθπ : ∀ j, θ j < Real.pi)
    (hαpos : 0 < α) (hαθ : ∀ j, α < θ j) (hcot : cotEq θ a0 a α) :
    a0 ^ 2 / (1 - Real.cos α)
      = ∑ j : Fin m, 2 * (a j) ^ 2 / (Real.cos α - Real.cos (θ j)) := by
  have hpi := Real.pi_pos
  have hαπ : α < Real.pi := lt_trans (hαθ ⟨0, hm⟩) (hθπ ⟨0, hm⟩)
  have hsinα : Real.sin α ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hαpos hαπ).ne'
  have hsinhalf : Real.sin (α / 2) ≠ 0 := by
    apply (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have hcoshalf : Real.cos (α / 2) ≠ 0 := by
    have h := Real.cos_pos_of_mem_Ioo (x := α / 2) ⟨by linarith, by linarith⟩
    exact h.ne'

  have hpair : ∀ j : Fin m,
      Real.cot ((α - θ j) / 2) + Real.cot ((α + θ j) / 2)
        = 2 * Real.sin α / (Real.cos (θ j) - Real.cos α) := by
    intro j
    have h1 : Real.sin ((α - θ j) / 2) ≠ 0 := by
      apply (Real.sin_neg_of_neg_of_neg_pi_lt (x := (α - θ j) / 2)
        (by have := hαθ j; linarith) (by
        have := hθπ j; linarith)).ne
    have h2 : Real.sin ((α + θ j) / 2) ≠ 0 := by
      apply (Real.sin_pos_of_pos_of_lt_pi (x := (α + θ j) / 2)
        (by have := hθpos j; linarith) (by
        have := hθπ j; linarith)).ne'
    have hcos : Real.cos (θ j) ≠ Real.cos α := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := α) (y := θ j)
        (le_of_lt hαpos) (le_of_lt (hθπ j)) (hαθ j)
      exact ne_of_lt this
    exact cot_pair_eq h1 h2 hcos
  have hdenpos : ∀ j : Fin m, 0 < Real.cos α - Real.cos (θ j) := by
    intro j
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := α) (y := θ j)
      (le_of_lt hαpos) (le_of_lt (hθπ j)) (hαθ j)
    linarith
  have hcot' : a0 ^ 2 * Real.cot (α / 2) +
      ∑ j : Fin m, (a j) ^ 2 *
        (2 * Real.sin α / (Real.cos (θ j) - Real.cos α)) = 0 := by
    rw [cotEq] at hcot
    rw [← hcot]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [(hpair j).symm]

  have hdiv : a0 ^ 2 * (Real.cot (α / 2) / Real.sin α) +
      ∑ j : Fin m, (a j) ^ 2 * (2 / (Real.cos (θ j) - Real.cos α)) = 0 := by
    have h := congrArg (fun x => x / Real.sin α) hcot'
    simp only [add_div, zero_div] at h
    rw [sum_div_finset] at h
    rw [← h]
    have hterm : (∑ j : Fin m, (a j) ^ 2 * (2 / (Real.cos (θ j) - Real.cos α)))
        = ∑ j : Fin m,
            ((a j) ^ 2 * (2 * Real.sin α / (Real.cos (θ j) - Real.cos α))) /
              Real.sin α := by
      apply Finset.sum_congr rfl
      intro j _
      have hd : Real.cos (θ j) - Real.cos α ≠ 0 := by
        have := hdenpos j; linarith
      field_simp [hsinα, hd]
    have hfirst : a0 ^ 2 * (Real.cot (α / 2) / Real.sin α)
        = a0 ^ 2 * Real.cot (α / 2) / Real.sin α := by ring
    rw [hfirst, hterm]
  rw [cot_half_div_sin hsinhalf hcoshalf] at hdiv
  have hsum : (∑ j : Fin m, (a j) ^ 2 * (2 / (Real.cos (θ j) - Real.cos α)))
      = - ∑ j : Fin m, 2 * (a j) ^ 2 / (Real.cos α - Real.cos (θ j)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hd : Real.cos (θ j) - Real.cos α ≠ 0 := by
      have := hdenpos j; linarith
    have hd' : Real.cos α - Real.cos (θ j) ≠ 0 := by
      have := hdenpos j; linarith
    field_simp [hd, hd']
    ring
  rw [hsum] at hdiv
  have h1 : a0 ^ 2 * (1 / (1 - Real.cos α)) = a0 ^ 2 / (1 - Real.cos α) := by ring
  rw [h1] at hdiv
  linarith

/-- For `0 ≤ x ≤ π`, the quantity `1 - cos x` is at least `2 * x ^ 2 / π ^ 2`. -/
lemma two_div_pi_sq_mul_sq_le_one_sub_cos (x : ℝ) (h0 : 0 ≤ x) (hπ : x ≤ Real.pi) :
    2 * x ^ 2 / Real.pi ^ 2 ≤ 1 - Real.cos x := by
  have hx2 : 0 ≤ x / 2 := by linarith
  have hx2π : x / 2 ≤ Real.pi / 2 := by linarith
  have hjordan : 2 / Real.pi * (x / 2) ≤ Real.sin (x / 2) :=
    Real.mul_le_sin hx2 hx2π
  have hsin_nonneg : 0 ≤ Real.sin (x / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx2 (by linarith)
  have hsq : (2 / Real.pi * (x / 2)) ^ 2 ≤ Real.sin (x / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hjordan 2
  have hone : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
    have hcos := Real.cos_two_mul (x / 2)
    have hsq' := Real.sin_sq_add_cos_sq (x / 2)
    rw [show (2 : ℝ) * (x / 2) = x by ring] at hcos
    nlinarith
  have hsqr : (x / Real.pi) ^ 2 ≤ Real.sin (x / 2) ^ 2 := by
    have hp : (2 / Real.pi * (x / 2)) = x / Real.pi := by ring
    rwa [hp] at hsq
  rw [hone]
  have hkey : 2 * x ^ 2 / Real.pi ^ 2 = 2 * (x / Real.pi) ^ 2 := by ring
  rw [hkey]
  nlinarith [hsqr]

/-- For every real `x`, the quantity `1 - cos x` is at most `x ^ 2 / 2`. -/
lemma one_sub_cos_le_half_sq (x : ℝ) :
    1 - Real.cos x ≤ x ^ 2 / 2 := by
  have h := Real.one_sub_sq_div_two_le_cos (x := x)
  linarith

/-- For `0 < θ < π`, half of `1 - cos θ` is at most `cos (θ / 2) - cos θ`. -/
lemma half_one_sub_cos_le_cos_half_sub_cos (θ : ℝ) (h0 : 0 < θ) (hπ : θ < Real.pi) :
    (1 - Real.cos θ) / 2 ≤ Real.cos (θ / 2) - Real.cos θ := by
  have h2 : Real.cos (2 * (θ / 2)) = Real.cos θ := by rw [show 2 * (θ / 2) = θ by ring]
  have hcos : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    rw [← h2, Real.cos_two_mul]
  have hc0 : 0 ≤ Real.cos (θ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hc1 : Real.cos (θ / 2) ≤ 1 := Real.cos_le_one _
  have key : Real.cos (θ / 2) - Real.cos θ - (1 - Real.cos θ) / 2
      = Real.cos (θ / 2) * (1 - Real.cos (θ / 2)) := by
    rw [hcos]; ring
  nlinarith

/-- Under the cotangent equation and the stated positivity and separation hypotheses, `α ^ 2` is
at most `π ^ 2 * a0 ^ 2 / (4 * ∑ j, (a j) ^ 2 / (1 - cos (θ j)))`. See
[AmbainisKempeRivosh2004]. -/
theorem alpha_sq_upper {m : ℕ} (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ)
    {α : ℝ} (hm : 0 < m) (ha0 : a0 ≠ 0)
    (hθpos : ∀ j, 0 < θ j) (hθπ : ∀ j, θ j < Real.pi)
    (hαpos : 0 < α) (hαθ : ∀ j, α < θ j) (hcot : cotEq θ a0 a α) :
    α ^ 2 ≤ Real.pi ^ 2 * a0 ^ 2 /
      (4 * ∑ j : Fin m, (a j) ^ 2 / (1 - Real.cos (θ j))) := by
  have hαπ : α < Real.pi := lt_trans (hαθ ⟨0, hm⟩) (hθπ ⟨0, hm⟩)
  have hexact := alpha_exact_eq θ a0 a hm hθpos hθπ hαpos hαθ hcot
  have hdenpos : ∀ j : Fin m, 0 < Real.cos α - Real.cos (θ j) := by
    intro j
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := α) (y := θ j)
      (le_of_lt hαpos) (le_of_lt (hθπ j)) (hαθ j)
    linarith
  have hLpos : 0 < a0 ^ 2 / (1 - Real.cos α) := by
    have hc : Real.cos α < 1 := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := α)
        (le_refl 0) (le_of_lt hαπ) hαpos
      simpa using this
    exact div_pos (by positivity) (by linarith)
  have hexists : ∃ j : Fin m, a j ≠ 0 := by
    by_contra h
    have hnull : ∀ j : Fin m, a j = 0 := fun j => by
      by_contra hj
      exact h ⟨j, hj⟩
    have hzero : (∑ j : Fin m, 2 * (a j) ^ 2 / (Real.cos α - Real.cos (θ j))) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hnull j]; ring
    rw [hzero] at hexact
    exact (ne_of_gt hLpos) hexact
  obtain ⟨j0, hj0⟩ := hexists
  have hSpos : 0 < ∑ j : Fin m, (a j) ^ 2 / (1 - Real.cos (θ j)) := by
    apply Finset.sum_pos'
    · intro j _
      have hc : Real.cos (θ j) < 1 := by
        have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := θ j)
          (le_refl 0) (le_of_lt (hθπ j)) (hθpos j)
        simpa using this
      exact div_nonneg (by positivity) (by linarith)
    · exact ⟨j0, Finset.mem_univ _, div_pos (by positivity) (by
        have hc : Real.cos (θ j0) < 1 := by
          have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := θ j0)
            (le_refl 0) (le_of_lt (hθπ j0)) (hθpos j0)
          simpa using this
        linarith)⟩
  have hterm_le : ∀ j : Fin m,
      2 * (a j) ^ 2 / (1 - Real.cos (θ j))
        ≤ 2 * (a j) ^ 2 / (Real.cos α - Real.cos (θ j)) := by
    intro j
    have h1 : Real.cos α - Real.cos (θ j) ≤ 1 - Real.cos (θ j) := by
      have hc : Real.cos α < 1 := by
        have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := α)
          (le_refl 0) (le_of_lt hαπ) hαpos
        simpa using this
      linarith
    have hpos := hdenpos j
    have hpos2 : 0 < 1 - Real.cos (θ j) := by
      have hc : Real.cos (θ j) < 1 := by
        have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := θ j)
          (le_refl 0) (le_of_lt (hθπ j)) (hθpos j)
        simpa using this
      linarith
    exact div_le_div_of_nonneg_left (by positivity) hpos h1
  have hbound : (∑ j : Fin m, 2 * (a j) ^ 2 / (1 - Real.cos (θ j)))
      ≤ a0 ^ 2 / (1 - Real.cos α) := by
    rw [hexact]
    exact Finset.sum_le_sum fun j _ => hterm_le j

  have hT2 : (∑ j : Fin m, 2 * (a j) ^ 2 / (1 - Real.cos (θ j)))
      = 2 * ∑ j : Fin m, (a j) ^ 2 / (1 - Real.cos (θ j)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hdenα : 0 < 1 - Real.cos α := by
    have hc : Real.cos α < 1 := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := α)
        (le_refl 0) (le_of_lt hαπ) hαpos
      simpa using this
    linarith
  have h2S : 2 * (∑ j : Fin m, (a j) ^ 2 / (1 - Real.cos (θ j)))
      ≤ a0 ^ 2 / (1 - Real.cos α) := by
    rw [← hT2]; exact hbound
  have hmul : 2 * (∑ j : Fin m, (a j) ^ 2 / (1 - Real.cos (θ j))) * (1 - Real.cos α)
      ≤ a0 ^ 2 := (le_div_iff₀ hdenα).mp h2S
  have hupper : 1 - Real.cos α ≤ a0 ^ 2 /
      (2 * ∑ j : Fin m, (a j) ^ 2 / (1 - Real.cos (θ j))) := by
    rw [le_div_iff₀ (by linarith [hSpos] :
      (0:ℝ) < 2 * ∑ j : Fin m, (a j) ^ 2 / (1 - Real.cos (θ j)))]
    nlinarith [hmul]
  have hlower : 2 * α ^ 2 / Real.pi ^ 2 ≤ 1 - Real.cos α :=
    two_div_pi_sq_mul_sq_le_one_sub_cos α (le_of_lt hαpos) (le_of_lt hαπ)
  have hchain : 2 * α ^ 2 / Real.pi ^ 2 ≤ a0 ^ 2 /
      (2 * ∑ j : Fin m, (a j) ^ 2 / (1 - Real.cos (θ j))) :=
    le_trans hlower hupper
  have key : (2 * α ^ 2) * (2 * (∑ j : Fin m, (a j) ^ 2 / (1 - Real.cos (θ j))))
      ≤ a0 ^ 2 * Real.pi ^ 2 := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < Real.pi ^ 2)
      (by linarith [hSpos] : (0:ℝ) < 2 * ∑ j : Fin m, (a j) ^ 2 / (1 - Real.cos (θ j)))]
      at hchain
    linarith [hchain]
  rw [le_div_iff₀ (by linarith [hSpos] :
    (0:ℝ) < 4 * ∑ j : Fin m, (a j) ^ 2 / (1 - Real.cos (θ j)))]
  nlinarith [key]

/-- When `α` is positive and less than every `θ j / 2`, the cotangent equation gives the lower
bound `a0 ^ 2 / (2 * ∑ j, (a j) ^ 2 / (1 - cos (θ j))) ≤ α ^ 2`, provided `a0 ≠ 0` and `0 <
θ j < π`. See [AmbainisKempeRivosh2004]. -/
theorem alpha_sq_lower {m : ℕ} (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ)
    {α : ℝ} (hm : 0 < m) (ha0 : a0 ≠ 0)
    (hθpos : ∀ j, 0 < θ j) (hθπ : ∀ j, θ j < Real.pi)
    (hαpos : 0 < α) (hαhalf : ∀ j, α < θ j / 2) (hcot : cotEq θ a0 a α) :
    a0 ^ 2 / (2 * ∑ j : Fin m, (a j) ^ 2 / (1 - Real.cos (θ j))) ≤ α ^ 2 := by
  have hαθ : ∀ j, α < θ j := fun j => lt_trans (hαhalf j) (by linarith [hθpos j])
  have hαπ : α < Real.pi := lt_trans (hαθ ⟨0, hm⟩) (hθπ ⟨0, hm⟩)
  have hexact := alpha_exact_eq θ a0 a hm hθpos hθπ hαpos hαθ hcot

  have hterm_le : ∀ j : Fin m,
      2 * (a j) ^ 2 / (Real.cos α - Real.cos (θ j))
        ≤ 4 * (a j) ^ 2 / (1 - Real.cos (θ j)) := by
    intro j
    have hpair := half_one_sub_cos_le_cos_half_sub_cos (θ j) (hθpos j) (hθπ j)
    have hcos : Real.cos (θ j / 2) ≤ Real.cos α := by
      have hlt := Real.cos_lt_cos_of_nonneg_of_le_pi (x := α) (y := θ j / 2)
        (le_of_lt hαpos) (by linarith [hθπ j]) (hαhalf j)
      exact le_of_lt hlt
    have hden : (1 - Real.cos (θ j)) / 2 ≤ Real.cos α - Real.cos (θ j) := by linarith
    have hdenpos : 0 < (1 - Real.cos (θ j)) / 2 := by
      have hc : Real.cos (θ j) < 1 := by
        have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := θ j)
          (le_refl 0) (le_of_lt (hθπ j)) (hθpos j)
        simpa using this
      linarith
    have hpos : 0 < Real.cos α - Real.cos (θ j) := lt_of_lt_of_le hdenpos hden
    rw [div_le_div_iff₀ hpos (by linarith)]
    nlinarith [sq_nonneg (a j)]
  have hbound : a0 ^ 2 / (1 - Real.cos α)
      ≤ ∑ j : Fin m, 4 * (a j) ^ 2 / (1 - Real.cos (θ j)) := by
    rw [hexact]; exact Finset.sum_le_sum fun j _ => hterm_le j
  have hSnonneg : 0 ≤ ∑ j : Fin m, (a j) ^ 2 / (1 - Real.cos (θ j)) := by
    apply Finset.sum_nonneg
    intro j _
    have hc : Real.cos (θ j) < 1 := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := θ j)
        (le_refl 0) (le_of_lt (hθπ j)) (hθpos j)
      simpa using this
    exact div_nonneg (by positivity) (by linarith)
  have hL : 0 < a0 ^ 2 / (1 - Real.cos α) := by
    have hc : Real.cos α < 1 := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := α)
        (le_refl 0) (le_of_lt hαπ) hαpos
      simpa using this
    exact div_pos (by positivity) (by linarith)
  have h4 : (∑ j : Fin m, 4 * (a j) ^ 2 / (1 - Real.cos (θ j)))
      = 4 * ∑ j : Fin m, (a j) ^ 2 / (1 - Real.cos (θ j)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hSpos : 0 < ∑ j : Fin m, (a j) ^ 2 / (1 - Real.cos (θ j)) := by
    rcases eq_or_lt_of_le hSnonneg with h0 | hpos
    · exfalso
      have hz : (∑ j : Fin m, 4 * (a j) ^ 2 / (1 - Real.cos (θ j))) = 0 := by
        rw [h4, ← h0]
        ring
      rw [hz] at hbound
      linarith [hL]
    · exact hpos

  have hhalf : a0 ^ 2 / (1 - Real.cos α) ≤ 4 * ∑ j : Fin m, (a j) ^ 2 / (1 - Real.cos (θ j)) := by
    refine le_trans hbound ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    exact le_of_eq (by ring :
      4 * (a j) ^ 2 / (1 - Real.cos (θ j)) = 4 * ((a j) ^ 2 / (1 - Real.cos (θ j))))
  have hone : 1 - Real.cos α ≤ α ^ 2 / 2 := one_sub_cos_le_half_sq α
  have hdenα : 0 < 1 - Real.cos α := by
    have hc : Real.cos α < 1 := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := α)
        (le_refl 0) (le_of_lt hαπ) hαpos
      simpa using this
    linarith
  rw [div_le_iff₀ hdenα] at hhalf
  have hmul := mul_le_mul_of_nonneg_left hone (by linarith [hSpos] :
    0 ≤ 4 * ∑ j : Fin m, (a j) ^ 2 / (1 - Real.cos (θ j)))
  have hfin : a0 ^ 2 ≤ 4 * (∑ j : Fin m, (a j) ^ 2 / (1 - Real.cos (θ j))) * (α ^ 2 / 2) :=
    le_trans hhalf hmul
  rw [div_le_iff₀ (by linarith [hSpos] :
    (0:ℝ) < 2 * ∑ j : Fin m, (a j) ^ 2 / (1 - Real.cos (θ j)))]
  nlinarith [hfin]

end Qatlib.Papers.QWalkAmbainis04.MainResults.AbstractSearch.Quantitative
