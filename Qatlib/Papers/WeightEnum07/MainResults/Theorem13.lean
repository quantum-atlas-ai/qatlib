/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.WeightEnum07.MainResults.Proposition1
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Basic

/-!
# Exact weight enumerators from lattice rounding

This module defines bivariate weight enumerators, the parameter records `ICQParams` and
`ICQCode`, and a probabilistic output interface. Integer-lattice rounding recovers exact weight
counts and hence the enumerator whenever every approximation error is less than half the known
weight spacing; auxiliary estimates bound the parameter `delta`.

This development forms part of the formalization of [GeraciVanBussel2007].

## Main statements

* `weightEnumerator`: The bivariate polynomial whose coefficient at `X 0 ^ (n - i) * X 1 ^ i` is
  the weight count `A i`, summed over `0 ≤ i ≤ n`.
* `theorem13_exact_weight_enumerator`: For an `ICQCode` with weights divisible by positive `g`,
  errors strictly below `g / 2` suffice to recover its exact weight enumerator by lattice
  rounding.

## References

* [Geraci and Van Bussel, 2007][GeraciVanBussel2007]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WeightEnum07.MainResults

open scoped BigOperators ENNReal

/-- The bivariate polynomial whose coefficient at `X 0 ^ (n - i) * X 1 ^ i` is the weight count
`A i`, summed over `0 ≤ i ≤ n`. -/
def weightEnumerator (n : ℕ) (A : ℕ → ℕ) : MvPolynomial (Fin 2) ℤ :=
  ∑ i ∈ Finset.range (n + 1),
    (A i : MvPolynomial (Fin 2) ℤ) * MvPolynomial.X 0 ^ (n - i) * MvPolynomial.X 1 ^ i

/-- The number of nonzero coordinates of a length-`n` word. -/
def hammingWeightOf {F : Type*} [Zero F] {n : ℕ} (w : Fin n → F) : ℕ :=
  Nat.card {i : Fin n // w i ≠ 0}

/-- The Hamming weight of a length-`n` word is at most `n`. -/
lemma hammingWeightOf_le {F : Type*} [Zero F] {n : ℕ} (w : Fin n → F) :
    hammingWeightOf w ≤ n := by
  have h := Nat.card_le_card_of_injective
    (f := (Subtype.val : {i : Fin n // w i ≠ 0} → Fin n)) Subtype.val_injective
  have hfin : Nat.card (Fin n) = n := by simp
  rw [hfin] at h
  exact h

/-- The enumerator formed from weight multiplicities equals the sum of the corresponding
monomial over every word. -/
lemma weightEnumerator_eq_sum_words
    {F : Type*} [Zero F] [DecidableEq F] {n : ℕ} (words : Finset (Fin n → F)) :
    weightEnumerator n (fun i => (words.filter (fun w => hammingWeightOf w = i)).card) =
      ∑ w ∈ words,
        (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ) ^ (n - hammingWeightOf w) *
          MvPolynomial.X 1 ^ hammingWeightOf w := by
  classical
  rw [weightEnumerator]
  rw [← Finset.sum_fiberwise_of_maps_to' (s := words) (t := Finset.range (n + 1))
    (g := fun w => hammingWeightOf w)
    (f := fun i => (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ) ^ (n - i) *
      MvPolynomial.X 1 ^ i)
    (fun w _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hammingWeightOf_le w)))]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/-- Sum at most the given number of base-`q` remainders by repeated natural division. -/
def digitSumAux (q : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, x => x % q + digitSumAux q fuel (x / q)

/-- The fuel-based digit sum obtained by applying `digitSumAux` with fuel `x + 1`. -/
def digitSum (q x : ℕ) : ℕ := digitSumAux q (x + 1) x

/-- The minimum of `digitSum q (j * n)` over natural indices `1 ≤ j ≤ B`. -/
def thetaNum (q n B : ℕ) (hB : 1 ≤ B) : ℕ :=
  ((Finset.Icc 1 B).image (fun j => digitSum q (j * n))).min'
    (Finset.image_nonempty.mpr (Finset.nonempty_Icc.mpr hB))

/-- The real-valued minimum digit sum `thetaNum q n B hB` divided by `q - 1`. -/
def thetaOf (q n B : ℕ) (hB : 1 ≤ B) : ℝ :=
  (thetaNum q n B hB : ℝ) / ((q : ℝ) - 1)

/-- Parameters `q`, `k`, `n`, `s`, and `ε` with `q ≥ 2`, positive dimension and length, and `0 ≤
ε < 1`. -/
structure ICQParams where

  q : ℕ

  k : ℕ

  n : ℕ

  s : ℕ

  ε : ℝ

  hq : 2 ≤ q

  hk : 0 < k

  hn : 0 < n

  hε : 0 ≤ ε

  hε1 : ε < 1

/-- The reciprocal error expression `1 / (2 * (((q ^ k - 1) ^ 2) * ε - 2))` associated with the
code parameters. -/
def delta (p : ICQParams) : ℝ :=
  (2 * (((p.q : ℝ) ^ p.k - 1) ^ 2 * p.ε - 2))⁻¹

/-- A record of code parameters, a finite set of integer words and its weight counts, together
with the specified size and precision constraints. -/
structure ICQCode where

  params : ICQParams

  α : ℝ

  hα : 0 < α

  B : ℕ

  hB : 1 ≤ B

  hB_le : (B : ℝ) ≤ α * (params.k : ℝ) ^ params.s

  hB_lt : α * (params.k : ℝ) ^ params.s < (B : ℝ) + 1

  eq12 : (params.n : ℝ) * α * (params.k : ℝ) ^ params.s =
    (params.q : ℝ) ^ params.k - 1

  words : Finset (Fin params.n → ℤ)

  weightCounts : ℕ → ℕ

  weightCounts_spec : ∀ i,
    weightCounts i = (words.filter (fun w => hammingWeightOf w = i)).card

  h14 : params.ε ≤
    (params.q : ℝ) ^ (thetaOf params.q params.n B hB - 1) /
      (4 * Real.sqrt ((params.q : ℝ) ^ params.k))

/-- The enumerator of an `ICQCode` equals the sum of its word monomials. -/
lemma weightEnumerator_weightCounts (code : ICQCode) :
    weightEnumerator code.params.n code.weightCounts =
      ∑ w ∈ code.words,
        (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ) ^ (code.params.n - hammingWeightOf w) *
          MvPolynomial.X 1 ^ hammingWeightOf w := by
  rw [← weightEnumerator_eq_sum_words]
  congr 1
  funext i
  exact code.weightCounts_spec i

/-- The real-valued mass assigned to an outcome by a probability mass function. -/
def successProbability {Ω : Type*} (μ : PMF Ω) (a : Ω) : ℝ := (μ a).toReal

/-- A record assigning a distribution on bivariate integer polynomials and a natural runtime to
each `ICQCode`. -/
structure QuantumWeightEnumeratorAlgorithm where

  run : ICQCode → PMF (MvPolynomial (Fin 2) ℤ)

  runtime : ICQCode → ℕ

/-- The real-valued mass of an outcome is nonnegative. -/
lemma successProbability_nonneg {Ω : Type*} (μ : PMF Ω) (a : Ω) :
    0 ≤ successProbability μ a := ENNReal.toReal_nonneg

/-- The real-valued mass of an outcome is at most one. -/
lemma successProbability_le_one {Ω : Type*} (μ : PMF Ω) (a : Ω) :
    successProbability μ a ≤ 1 := by
  unfold successProbability
  calc (μ a).toReal ≤ (1 : ℝ≥0∞).toReal :=
        ENNReal.toReal_mono ENNReal.one_ne_top (μ.coe_le_one a)
    _ = 1 := ENNReal.toReal_one

/-- Round `a / g` to an integer and multiply by `g` to obtain an integer lattice value. -/
def roundToLattice (g : ℕ) (a : ℝ) : ℤ := round (a / (g : ℝ)) * (g : ℤ)

/-- Rounding recovers a multiple `w` of positive `g` whenever the approximation error is
strictly less than `g / 2`. -/
theorem roundToLattice_eq_of_dvd {g : ℕ} (hg : 0 < g) {a : ℝ} {w : ℤ}
    (hdvd : (g : ℤ) ∣ w) (hclose : |a - (w : ℝ)| < (g : ℝ) / 2) :
    roundToLattice g a = w := by
  obtain ⟨k, rfl⟩ := hdvd
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have hclose' : |a - (k : ℝ) * (g : ℝ)| < (g : ℝ) / 2 := by
    simpa [Int.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hclose
  have hk : |a / (g : ℝ) - (k : ℝ)| < 1 / 2 := by
    have hsub : a / (g : ℝ) - (k : ℝ) = (a - (k : ℝ) * (g : ℝ)) / (g : ℝ) := by
      field_simp
    rw [hsub, abs_div, abs_of_pos hgR, div_lt_iff₀ hgR]
    nlinarith [hclose']
  unfold roundToLattice
  have hround : round (a / (g : ℝ)) = k := by
    rw [round_eq_iff]
    simp only [Set.mem_Ico]
    have h := abs_lt.mp hk
    constructor <;> linarith
  rw [hround]
  ring

/-- Two multiples of positive `g` both within `g / 2` of the same real number must be equal. -/
theorem eq_of_dvd_of_close {g : ℕ} (hg : 0 < g) {a : ℝ} {w w' : ℤ}
    (hw : (g : ℤ) ∣ w) (hw' : (g : ℤ) ∣ w')
    (h1 : |a - (w : ℝ)| < (g : ℝ) / 2) (h2 : |a - (w' : ℝ)| < (g : ℝ) / 2) :
    w = w' := by
  rw [← roundToLattice_eq_of_dvd hg hw h1, ← roundToLattice_eq_of_dvd hg hw' h2]

/-- Rounding sufficiently accurate weight approximations to the known lattice recovers the
number of words of any specified weight. -/
theorem weightCount_round_eq {n : ℕ} (words : Finset (Fin n → ℤ))
    (approx : (Fin n → ℤ) → ℝ) {g : ℕ} (hg : 0 < g)
    (hdiv : ∀ w ∈ words, (g : ℤ) ∣ (hammingWeightOf w : ℤ))
    (hclose : ∀ w ∈ words, |approx w - (hammingWeightOf w : ℝ)| < (g : ℝ) / 2)
    (i : ℕ) :
    (words.filter (fun w => roundToLattice g (approx w) = (i : ℤ))).card =
      (words.filter (fun w => hammingWeightOf w = i)).card := by
  classical
  congr 1
  refine Finset.filter_congr ?_
  intro w hw
  constructor
  · intro h
    have h1 : roundToLattice g (approx w) = ((hammingWeightOf w : ℕ) : ℤ) :=
      roundToLattice_eq_of_dvd hg (hdiv w hw) (hclose w hw)
    rw [h1] at h
    exact_mod_cast h
  · intro h
    have hr : roundToLattice g (approx w) = ((hammingWeightOf w : ℕ) : ℤ) :=
      roundToLattice_eq_of_dvd hg (hdiv w hw) (hclose w hw)
    rw [hr]
    exact_mod_cast h

/-- Rounding sufficiently accurate lattice-spaced weight approximations leaves the weight
enumerator unchanged. -/
theorem weightEnumerator_round_eq {n : ℕ} (words : Finset (Fin n → ℤ))
    (approx : (Fin n → ℤ) → ℝ) {g : ℕ} (hg : 0 < g)
    (hdiv : ∀ w ∈ words, (g : ℤ) ∣ (hammingWeightOf w : ℤ))
    (hclose : ∀ w ∈ words, |approx w - (hammingWeightOf w : ℝ)| < (g : ℝ) / 2) :
    weightEnumerator n
        (fun i : ℕ => (words.filter (fun w => roundToLattice g (approx w) = (i : ℤ))).card) =
      weightEnumerator n (fun i => (words.filter (fun w => hammingWeightOf w = i)).card) := by
  have hfun : (fun i : ℕ => (words.filter (fun w => roundToLattice g (approx w) = (i : ℤ))).card) =
      (fun i => (words.filter (fun w => hammingWeightOf w = i)).card) := by
    funext i
    exact weightCount_round_eq words approx hg hdiv hclose i
  rw [hfun]

/-- For an `ICQCode` with weights divisible by positive `g`, errors strictly below `g / 2`
suffice to recover its exact weight enumerator by lattice rounding. See
[GeraciVanBussel2007]. -/
theorem theorem13_exact_weight_enumerator (code : ICQCode)
    (approx : (Fin code.params.n → ℤ) → ℝ) {g : ℕ} (hg : 0 < g)
    (hdiv : ∀ w ∈ code.words, (g : ℤ) ∣ (hammingWeightOf w : ℤ))
    (hclose : ∀ w ∈ code.words, |approx w - (hammingWeightOf w : ℝ)| < (g : ℝ) / 2) :
    weightEnumerator code.params.n
        (fun i : ℕ => (code.words.filter (fun w => roundToLattice g (approx w) = (i : ℤ))).card) =
      weightEnumerator code.params.n code.weightCounts := by
  rw [weightEnumerator_round_eq code.words approx hg hdiv hclose]
  rw [weightEnumerator_eq_sum_words]
  exact (weightEnumerator_weightCounts code).symm

/-- The parameter `delta` is positive when `(q ^ k - 1) ^ 2 * ε` is greater than two. -/
lemma delta_pos {p : ICQParams} (h : 2 < (((p.q : ℝ) ^ p.k - 1) ^ 2 * p.ε)) :
    0 < delta p := by
  unfold delta
  exact inv_pos.mpr (by nlinarith)

/-- The parameter `delta` is at most one half when `(q ^ k - 1) ^ 2 * ε` is at least three. -/
lemma delta_le_half {p : ICQParams} (h : 3 ≤ (((p.q : ℝ) ^ p.k - 1) ^ 2 * p.ε)) :
    delta p ≤ 1 / 2 := by
  unfold delta
  have hden : (2 : ℝ) ≤ 2 * ((((p.q : ℝ) ^ p.k - 1) ^ 2 * p.ε) - 2) := by nlinarith
  have hpos : (0 : ℝ) < 2 := by norm_num
  have := one_div_le_one_div_of_le hpos hden
  simpa [one_div] using this

/-- The quantity `1 - delta` is at least one half when `(q ^ k - 1) ^ 2 * ε` is at least three. -/
lemma one_sub_delta_ge_half {p : ICQParams}
    (h : 3 ≤ (((p.q : ℝ) ^ p.k - 1) ^ 2 * p.ε)) : 1 / 2 ≤ 1 - delta p := by
  have := delta_le_half h
  linarith

end Qatlib.Papers.WeightEnum07.MainResults
