/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Qatlib.Papers.PhaseEst07.MainResults.QubitExample

@[expose] public section


/-!
# Optimality of balanced identical-qubit preparations

The derivative coefficients of the normalized odd binomial-affinity polynomial have one sign
change. Pairing reflected coefficients proves that balancing the two preparation amplitudes
maximizes their adjacent correlation.

The final theorem preserves the product-state cost and all hypotheses of the fixed source
statement. The proof supplies the missing global-maximum argument for arbitrary positive N;
symmetry alone would give only a critical point. The amplitude-ratio variable r=b/a yields
P(r)/(1+r²)^N. Its derivative numerator has antisymmetric coefficients, positive before the
middle index. Pairing their powers on [0,1] proves monotonicity, and binomial reflection handles
the other half of the normalized preparation circle.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.PhaseEst07.MainResults.QubitExample

open Qatlib.Papers.PhaseEst07.MainResults.QubitExample

/-- The adjacent square-root binomial coefficient. -/
def weight (N k : ℕ) : ℝ :=
  Real.sqrt ((N.choose k : ℝ) * (N.choose (k + 1) : ℝ))

/-- Coefficients of the numerator of the derivative of the normalized affinity. -/
def slopeCoeff (N k : ℕ) : ℝ :=
  if k = 0 then weight N 0 else
    (2 * (k : ℝ) + 1) * weight N k - (2 * ((N - k : ℕ) : ℝ) + 1) * weight N (k - 1)

/-- The adjacent binomial coefficients are nonnegative. -/
theorem weight_nonneg (N k : ℕ) : 0 ≤ weight N k := Real.sqrt_nonneg _

/-- The adjacent binomial coefficient at the terminal index vanishes. -/
theorem weight_last (N : ℕ) : weight N N = 0 := by
  simp [weight]

/-- Reflection about the middle adjacent pair preserves its coefficient. -/
theorem weight_mirror {N k : ℕ} (hk : k < N) : weight N (N - 1 - k) = weight N k := by
  have h1 : N - 1 - k = N - (k + 1) := by omega
  have h2 : N - (k + 1) + 1 = N - k := by omega
  unfold weight
  rw [h1, h2, Nat.choose_symm (by omega : k + 1 ≤ N),
    Nat.choose_symm (by omega : k ≤ N)]
  rw [mul_comm]

/-- The coefficients of the derivative numerator are antisymmetric. -/
theorem slope_mirror {N k : ℕ} (hN : 0 < N) (hk : k ≤ N) :
    slopeCoeff N (N - k) = -slopeCoeff N k := by
  by_cases hk0 : k = 0
  · subst k
    have hm : weight N (N - 1) = weight N 0 := by simpa using weight_mirror (k := 0) hN
    simp [slopeCoeff, Nat.ne_of_gt hN, weight_last, hm]
  by_cases hkN : k = N
  · subst k
    have hm : weight N (N - 1) = weight N 0 := by simpa using weight_mirror (k := 0) hN
    simp [slopeCoeff, Nat.ne_of_gt hN, weight_last, hm]
  have hnk : N - k ≠ 0 := by omega
  have hm1 : weight N (N - k) = weight N (k - 1) := by
    have hh := weight_mirror (N := N) (k := k - 1) (by omega)
    simpa only [show N - 1 - (k - 1) = N - k by omega] using hh
  have hm2 : weight N (N - k - 1) = weight N k := by
    simpa only [show N - k - 1 = N - 1 - k by omega] using
      weight_mirror (N := N) (k := k) (by omega)
  simp only [slopeCoeff, hk0, hnk, ite_false, hm1, hm2,
    Nat.sub_sub_self hk]
  ring

/-- Before the middle index, the derivative coefficients are nonnegative. -/
theorem slope_nonneg {N k : ℕ} (hk : 2 * k ≤ N) : 0 ≤ slopeCoeff N k := by
  by_cases hk0 : k = 0
  · subst k
    simpa [slopeCoeff] using weight_nonneg N 0
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hplus : (N.choose (k + 1) : ℝ) * ((k : ℝ) + 1) =
      (N.choose k : ℝ) * ((N - k : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq N k
  have hminus : (N.choose k : ℝ) * (k : ℝ) =
      (N.choose (k - 1) : ℝ) * (((N - k : ℕ) : ℝ) + 1) := by
    have hh := Nat.choose_succ_right_eq N (k - 1)
    rw [Nat.sub_add_cancel hkpos] at hh
    have hn : N - (k - 1) = N - k + 1 := by omega
    rw [hn] at hh
    exact_mod_cast hh
  have hsplus : (weight N k) ^ 2 = (N.choose k : ℝ) * (N.choose (k + 1) : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsminus : (weight N (k - 1)) ^ 2 =
      (N.choose (k - 1) : ℝ) * (N.choose k : ℝ) := by
    simpa [weight, Nat.sub_add_cancel hkpos] using
      Real.sq_sqrt (show 0 ≤ (N.choose (k - 1) : ℝ) * (N.choose k : ℝ) by positivity)
  have hfactor : 0 < ((k : ℝ) + 1) * (((N - k : ℕ) : ℝ) + 1) := by positivity
  have hid :
      (((2 * (k : ℝ) + 1) * weight N k) ^ 2 -
        ((2 * ((N - k : ℕ) : ℝ) + 1) * weight N (k - 1)) ^ 2) *
        (((k : ℝ) + 1) * (((N - k : ℕ) : ℝ) + 1)) =
      (N.choose k : ℝ) ^ 2 * (((N - k : ℕ) : ℝ) - (k : ℝ)) *
        (((N - k : ℕ) : ℝ) + (k : ℝ) + 1) := by
    rw [mul_pow, mul_pow, hsplus, hsminus]
    calc
      _ = (N.choose k : ℝ) *
          ((2 * (k : ℝ) + 1) ^ 2 * ((N.choose (k + 1) : ℝ) * ((k : ℝ) + 1)) *
            (((N - k : ℕ) : ℝ) + 1) -
          (2 * ((N - k : ℕ) : ℝ) + 1) ^ 2 *
            ((N.choose (k - 1) : ℝ) * (((N - k : ℕ) : ℝ) + 1)) * ((k : ℝ) + 1)) := by ring
      _ = _ := by rw [hplus, ← hminus]; ring
  have hdiff : 0 ≤ ((N - k : ℕ) : ℝ) - (k : ℝ) := by
    have hh : (k : ℝ) ≤ ((N - k : ℕ) : ℝ) := by exact_mod_cast (show k ≤ N - k by omega)
    linarith
  have hright : 0 ≤ (N.choose k : ℝ) ^ 2 * (((N - k : ℕ) : ℝ) - (k : ℝ)) *
      (((N - k : ℕ) : ℝ) + (k : ℝ) + 1) := by positivity
  have hsq : ((2 * ((N - k : ℕ) : ℝ) + 1) * weight N (k - 1)) ^ 2 ≤
      ((2 * (k : ℝ) + 1) * weight N k) ^ 2 := by nlinarith [hid, hright]
  have hleft : 0 ≤ (2 * (k : ℝ) + 1) * weight N k :=
    mul_nonneg (by positivity) (weight_nonneg N k)
  have hright' : 0 ≤ (2 * ((N - k : ℕ) : ℝ) + 1) * weight N (k - 1) :=
    mul_nonneg (by positivity) (weight_nonneg N (k - 1))
  simp only [slopeCoeff, hk0, ite_false]
  nlinarith


/-- The odd polynomial before dividing out the normalization of the preparation. -/
def oddPoly (N : ℕ) (r : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, weight N k * r ^ (2 * k + 1)

/-- The derivative of the odd polynomial, written as a finite sum. -/
def oddSlope (N : ℕ) (r : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, weight N k * (2 * (k : ℝ) + 1) * r ^ (2 * k)

/-- The polynomial that controls the sign of the normalized affinity derivative. -/
def slopePoly (N : ℕ) (r : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), slopeCoeff N k * r ^ (2 * k)

/-- Reflected opposite coefficients give a nonnegative derivative numerator on the unit interval. -/
theorem slopePoly_nonneg {N : ℕ} (hN : 0 < N) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    0 ≤ slopePoly N r := by
  have href : (∑ k ∈ Finset.range (N + 1),
      slopeCoeff N (N - k) * r ^ (2 * (N - k))) = slopePoly N r := by
    simpa [slopePoly] using Finset.sum_range_reflect
      (fun k => slopeCoeff N k * r ^ (2 * k)) (N + 1)
  have hneg : (∑ k ∈ Finset.range (N + 1),
      slopeCoeff N k * r ^ (2 * (N - k))) = -slopePoly N r := by
    calc
      _ = ∑ k ∈ Finset.range (N + 1),
          -(slopeCoeff N (N - k) * r ^ (2 * (N - k))) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [slope_mirror hN (by have := Finset.mem_range.mp hk; omega)]
        ring
      _ = _ := by rw [Finset.sum_neg_distrib, href]
  have hpairs : 0 ≤ ∑ k ∈ Finset.range (N + 1),
      slopeCoeff N k * (r ^ (2 * k) - r ^ (2 * (N - k))) := by
    apply Finset.sum_nonneg
    intro k hk
    have hkN : k ≤ N := by have := Finset.mem_range.mp hk; omega
    by_cases hhalf : 2 * k ≤ N
    · exact mul_nonneg (slope_nonneg hhalf) (sub_nonneg.mpr
        (pow_le_pow_of_le_one hr0 hr1 (by omega)))
    · have hcoef : slopeCoeff N k ≤ 0 := by
        have hh := slope_nonneg (N := N) (k := N - k) (by omega)
        rw [slope_mirror hN hkN] at hh
        linarith
      exact mul_nonneg_of_nonpos_of_nonpos hcoef (sub_nonpos.mpr
        (pow_le_pow_of_le_one hr0 hr1 (by omega)))
  simp_rw [mul_sub] at hpairs
  rw [Finset.sum_sub_distrib, hneg] at hpairs
  change 0 ≤ slopePoly N r - -slopePoly N r at hpairs
  linarith

/-- Differentiation of the finite odd affinity polynomial. -/
theorem oddPoly_hasDeriv (N : ℕ) (r : ℝ) :
    HasDerivAt (oddPoly N) (oddSlope N r) r := by
  unfold oddPoly oddSlope
  simpa [Nat.cast_add, Nat.cast_mul, mul_assoc] using
    HasDerivAt.fun_sum (fun k (_hk : k ∈ Finset.range N) =>
      ((hasDerivAt_id r).pow (2 * k + 1)).const_mul (weight N k))


/-- Combining the two shifted finite sums gives the derivative numerator. -/
theorem slopePoly_eq (N : ℕ) (r : ℝ) :
    slopePoly N r = (1 + r ^ 2) * oddSlope N r - 2 * (N : ℝ) * r * oddPoly N r := by
  let A := fun k : ℕ => (2 * (k : ℝ) + 1) * weight N k * r ^ (2 * k)
  let B := fun k : ℕ => if k = 0 then 0 else
    (2 * ((N - k : ℕ) : ℝ) + 1) * weight N (k - 1) * r ^ (2 * k)
  have hs : slopePoly N r = (∑ k ∈ Finset.range (N + 1), A k) -
      ∑ k ∈ Finset.range (N + 1), B k := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases hk0 : k = 0
    · simp [slopeCoeff, A, B, hk0]
    · simp only [slopeCoeff, A, B, hk0, ite_false]
      ring
  have hA : A N = 0 := by simp [A, weight_last]
  have hB : B 0 = 0 := by simp [B]
  rw [Finset.sum_range_succ, Finset.sum_range_succ', hA, hB, add_zero, add_zero] at hs
  rw [hs, ← Finset.sum_sub_distrib]
  unfold oddSlope oddPoly
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k + 1 ≤ N := Finset.mem_range.mp hk
  have hcast : ((N - (k + 1) : ℕ) : ℝ) = (N : ℝ) - (k : ℝ) - 1 := by
    rw [Nat.cast_sub hkN, Nat.cast_add, Nat.cast_one]
    ring
  have hp : r ^ (2 * (k + 1)) = r ^ (2 * k) * r ^ 2 := by
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
  simp only [A, B, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
    Nat.add_sub_cancel, hcast, hp, pow_succ]
  ring

/-- The adjacent affinity of a product preparation with amplitude ratio r. -/
def affinity (N : ℕ) (r : ℝ) : ℝ := oddPoly N r / (1 + r ^ 2) ^ N

/-- The derivative numerator is exactly the antisymmetric coefficient polynomial. -/
theorem affinity_hasDeriv {N : ℕ} (hN : 0 < N) (r : ℝ) :
    HasDerivAt (affinity N) (slopePoly N r / (1 + r ^ 2) ^ (N + 1)) r := by
  have hden : 1 + r ^ 2 ≠ 0 := by positivity
  have hd := (oddPoly_hasDeriv N r).div
    (((hasDerivAt_const r 1).add ((hasDerivAt_id r).pow 2)).pow N) (pow_ne_zero N hden)
  unfold affinity
  apply hd.congr_deriv
  dsimp
  rw [slopePoly_eq]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  simp only [Nat.succ_sub_one, mul_one, zero_add, pow_succ]
  field_simp

/-- The affinity increases until the two product-state amplitudes are balanced. -/
theorem affinity_monotone {N : ℕ} (hN : 0 < N) :
    MonotoneOn (affinity N) (Set.Icc (0 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
  · exact fun r _hr => (affinity_hasDeriv hN r).continuousAt.continuousWithinAt
  · exact fun r _hr => (affinity_hasDeriv hN r).differentiableAt.differentiableWithinAt
  · intro r hr
    have hr' : r ∈ Set.Icc (0 : ℝ) 1 := interior_subset hr
    rw [(affinity_hasDeriv hN r).deriv]
    exact div_nonneg (slopePoly_nonneg hN hr'.1 hr'.2) (by positivity)


/-- The adjacent correlation of the binomial preparation amplitudes. -/
def correlation (N : ℕ) (a b : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N,
    sourceQubitAmplitude N a b k * sourceQubitAmplitude N a b (k + 1)

/-- A preparation amplitude becomes a monomial in its amplitude ratio. -/
theorem amplitude_ratio {N k : ℕ} (hk : k ≤ N) (a r : ℝ) :
    sourceQubitAmplitude N a (a * r) k =
      Real.sqrt (N.choose k : ℝ) * a ^ N * r ^ k := by
  unfold sourceQubitAmplitude
  rw [mul_pow]
  calc
    _ = Real.sqrt (N.choose k : ℝ) * (a ^ (N - k) * a ^ k) * r ^ k := by ring
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hk]

/-- Normalization converts the homogeneous correlation into the rational affinity. -/
theorem correlation_ratio (N : ℕ) (a r : ℝ) (h : a ^ 2 + (a * r) ^ 2 = 1) :
    correlation N a (a * r) = affinity N r := by
  have hbase : a ^ 2 * (1 + r ^ 2) = 1 := by nlinarith [h]
  have hscale : a ^ (2 * N) * (1 + r ^ 2) ^ N = 1 := by
    rw [pow_mul, ← mul_pow, hbase, one_pow]
  have hden : (1 + r ^ 2) ^ N ≠ 0 := by positivity
  unfold affinity oddPoly correlation
  apply (eq_div_iff hden).mpr
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ≤ N := by have := Finset.mem_range.mp hk; omega
  have hkN' : k + 1 ≤ N := Finset.mem_range.mp hk
  rw [amplitude_ratio hkN, amplitude_ratio hkN']
  have hsqrt : Real.sqrt (N.choose k : ℝ) * Real.sqrt (N.choose (k + 1) : ℝ) =
      weight N k := by rw [weight, Real.sqrt_mul (by positivity)]
  have haPow : a ^ N * a ^ N = a ^ (2 * N) := by
    rw [← pow_add]
    congr 1
    omega
  have hrPow : r ^ k * r ^ (k + 1) = r ^ (2 * k + 1) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ = (Real.sqrt (N.choose k : ℝ) * Real.sqrt (N.choose (k + 1) : ℝ)) *
        (a ^ N * a ^ N) * (r ^ k * r ^ (k + 1)) * (1 + r ^ 2) ^ N := by ring
    _ = weight N k * r ^ (2 * k + 1) * (a ^ (2 * N) * (1 + r ^ 2) ^ N) := by
      rw [hsqrt, haPow, hrPow]
      ring
    _ = _ := by rw [hscale, mul_one]

/-- Reflection of the binomial multiplet exchanges the two preparation amplitudes. -/
theorem amplitude_mirror {N k : ℕ} (hk : k ≤ N) (a b : ℝ) :
    sourceQubitAmplitude N b a (N - k) = sourceQubitAmplitude N a b k := by
  unfold sourceQubitAmplitude
  rw [Nat.choose_symm hk, Nat.sub_sub_self hk]
  ring

/-- The adjacent correlation is symmetric in the two preparation amplitudes. -/
theorem correlation_symm (N : ℕ) (a b : ℝ) :
    correlation N a b = correlation N b a := by
  unfold correlation
  rw [← Finset.sum_range_reflect
    (fun k => sourceQubitAmplitude N b a k * sourceQubitAmplitude N b a (k + 1)) N]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ≤ N := by have := Finset.mem_range.mp hk; omega
  have hkN' : k + 1 ≤ N := Finset.mem_range.mp hk
  rw [show N - 1 - k = N - (k + 1) by omega,
    show N - (k + 1) + 1 = N - k by omega,
    amplitude_mirror hkN' a b, amplitude_mirror hkN a b]
  ring

/-- An ordered normalized preparation has correlation at most the balanced affinity. -/
theorem correlation_ordered {N : ℕ} (hN : 0 < N) (a b : ℝ)
    (hb : 0 ≤ b) (hba : b ≤ a) (h : a ^ 2 + b ^ 2 = 1) :
    correlation N a b ≤ affinity N 1 := by
  have ha : 0 < a := by nlinarith
  let r := b / a
  have hr0 : 0 ≤ r := div_nonneg hb ha.le
  have hr1 : r ≤ 1 := (div_le_one ha).mpr hba
  have hbr : b = a * r := by dsimp [r]; field_simp
  rw [hbr] at h ⊢
  rw [correlation_ratio N a r h]
  exact affinity_monotone hN ⟨hr0, hr1⟩ ⟨by norm_num, le_rfl⟩ hr1

/-- Every normalized nonnegative preparation is bounded by the balanced affinity. -/
theorem correlation_balanced {N : ℕ} (hN : 0 < N) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 + b ^ 2 = 1) :
    correlation N a b ≤ affinity N 1 := by
  rcases le_total b a with hba | hab
  · exact correlation_ordered hN a b hb hba h
  · rw [correlation_symm N a b]
    exact correlation_ordered hN b a ha hab (by linarith)

/-- The closed balanced cost equals one half of one minus the balanced affinity. -/
theorem minCost_affinity (N : ℕ) :
    sourceQubitMinCost N = (1 - affinity N 1) / 2 := by
  simp only [sourceQubitMinCost, affinity, oddPoly, one_pow, mul_one, weight, one_add_one_eq_two]
  rw [pow_succ]
  field_simp

end Qatlib.Papers.PhaseEst07.MainResults.QubitExample
