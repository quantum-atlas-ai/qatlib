/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-!
# Cited strongly regular graph families

The search analysis of [JanmarkMeyerWong2014] is stated for the known strongly
regular graph families, including the Paley prime-power graphs with parameters
`(N, k, λ, μ) = (4t + 1, 2t, t - 1, t)` and the geometric Latin-square
families `(N, k, λ, μ) = (t², d(t - 1), d² - 3d + t, d(d - 1))`. This module
verifies the finite parameter content of those citations: both families
satisfy the strongly regular counting identity `k * (k - λ - 1) = (N - k - 1) * μ`
together with the non-degeneracy conditions and the degree bound used in the
source, for explicit parameter ranges. Graph existence, asymptotics, and
automorphism asymmetry remain cited context rather than constructed objects,
per the block boundary.

## Main statements

* `paley_param_identity`, `paley_nondegenerate`, `paley_degree_bound`: the
  Paley prime-power family in natural parameters.
* `latin_square_param_identity`, `latin_square_nondegenerate`,
  `latin_square_nat_nondegenerate`, `latin_square_degree_bound`: the geometric
  Latin-square family over the integers and its natural-parameter
  non-degeneracy.

## References

* [Janmark et al., 2014][JanmarkMeyerWong2014]
-/

set_option autoImplicit false

namespace Qatlib.Papers.NoGlobalSym14.GraphFamilies

/-- The Paley prime-power parameter tuple `(4t + 1, 2t, t - 1, t)` cited in
[JanmarkMeyerWong2014] satisfies the strongly regular counting identity
`k * (k - λ - 1) = (N - k - 1) * μ` in natural-number arithmetic for every
positive `t`. -/
theorem paley_param_identity (t : ℕ) (ht : 0 < t) :
    2 * t * (2 * t - (t - 1) - 1) = (4 * t + 1 - 2 * t - 1) * t := by
  have e1 : 2 * t - (t - 1) - 1 = t := by omega
  have e2 : 4 * t + 1 - 2 * t - 1 = 2 * t := by omega
  rw [e1, e2]

/-- The Paley parameters are non-degenerate for positive `t`: positive degree
and a positive nonneighbor cell. -/
theorem paley_nondegenerate (t : ℕ) (ht : 0 < t) :
    0 < 2 * t ∧ 0 < 4 * t + 1 - 2 * t - 1 := by
  refine ⟨Nat.mul_pos (by decide) ht, ?_⟩
  omega

/-- For positive `t`, the Paley parameters satisfy the finite inequality
`√N < k + 1` underlying the degree growth in [JanmarkMeyerWong2014], Eq. (3). -/
theorem paley_degree_bound (t : ℕ) (ht : 0 < t) :
    Real.sqrt (4 * t + 1 : ℝ) < (2 * t : ℝ) + 1 := by
  have ht' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hsq : 4 * (t : ℝ) + 1 < (2 * (t : ℝ) + 1) ^ 2 := by nlinarith [sq_pos_of_pos ht']
  have hpos : (0 : ℝ) < 2 * (t : ℝ) + 1 := by positivity
  rw [show (4 * t + 1 : ℝ) = 4 * (t : ℝ) + 1 by norm_num,
    show (2 * t : ℝ) + 1 = 2 * (t : ℝ) + 1 by norm_num]
  exact (Real.sqrt_lt' hpos).mpr hsq

/-- The geometric Latin-square parameter tuple `(t², d(t - 1), d² - 3d + t,
d(d - 1))` cited in [JanmarkMeyerWong2014] satisfies the strongly regular
counting identity over the integers for all parameters. Over the family domain
`2 ≤ d ≤ t` every term is nonnegative, so this is the natural-number counting
identity without truncation. -/
theorem latin_square_param_identity (d t : ℤ) :
    d * (t - 1) * (d * (t - 1) - (d ^ 2 - 3 * d + t) - 1)
      = (t ^ 2 - d * (t - 1) - 1) * (d * (d - 1)) := by ring

/-- In the family domain `2 ≤ d ≤ t`, the Latin-square parameters are
non-degenerate: positive degree, positive nonneighbor cell, nonnegative
`λ = d² - 3d + t`, and positive `μ = d(d - 1)`. -/
theorem latin_square_nondegenerate (d t : ℤ) (hd : 2 ≤ d) (hdt : d ≤ t) :
    0 < d * (t - 1) ∧ 0 < t ^ 2 - d * (t - 1) - 1 ∧ 0 ≤ d ^ 2 - 3 * d + t ∧
      0 < d * (d - 1) := by
  have ht : 2 ≤ t := le_trans hd hdt
  have hcell : (0 : ℤ) < (t - 1) * (t + 1 - d) :=
    mul_pos (by linarith) (by linarith)
  have hlam : (0 : ℤ) ≤ (d - 1) * (d - 2) :=
    mul_nonneg (by linarith) (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact mul_pos (by linarith) (by linarith)
  · nlinarith
  · nlinarith
  · exact mul_pos (by linarith) (by linarith)

/-- Natural-parameter non-degeneracy of the Latin-square family in the domain
`2 ≤ d ≤ t`: positive degree, positive nonneighbor cell, an untruncated
subtraction in `λ = d² + t - 3d`, and positive `μ`. -/
theorem latin_square_nat_nondegenerate (d t : ℕ) (hd : 2 ≤ d) (hdt : d ≤ t) :
    0 < d * (t - 1) ∧ 0 < t * t - d * (t - 1) - 1 ∧ 3 * d ≤ d * d + t ∧
      0 < d * (d - 1) := by
  have ht : 2 ≤ t := le_trans hd hdt
  have ht1 : 1 ≤ t := by omega
  have h2 : t * (t - 1) + 2 ≤ t * t := by
    have h : (t : ℤ) * (t - 1) + 2 ≤ (t : ℤ) * t := by nlinarith
    have e : ((t * (t - 1) : ℕ) : ℤ) = (t : ℤ) * ((t : ℕ) - 1) := by
      rw [Nat.cast_mul, Int.natCast_sub ht1]; norm_num
    have e2 : ((t * t : ℕ) : ℤ) = (t : ℤ) * t := by push_cast; ring
    have h' : ((t * (t - 1) + 2 : ℕ) : ℤ) ≤ ((t * t : ℕ) : ℤ) := by
      rw [Nat.cast_add, Nat.cast_two, e, e2]; exact h
    exact_mod_cast h'
  have hdk : d * (t - 1) ≤ t * (t - 1) := by gcongr
  have hlam := (latin_square_nondegenerate (d : ℤ) (t : ℤ)
    (by exact_mod_cast hd) (by exact_mod_cast hdt)).2.2.1
  have hlam' : (3 : ℤ) * d ≤ (d : ℤ) * d + t := by nlinarith only [hlam]
  refine ⟨Nat.mul_pos (by omega) (by omega), ?_, by exact_mod_cast hlam',
    Nat.mul_pos (by omega) (by omega)⟩
  omega

/-- In the family domain `2 ≤ d ≤ t`, the Latin-square parameters satisfy the
finite inequality `√N < k + 1` underlying the degree growth in
[JanmarkMeyerWong2014], Eq. (3), with `N = t²` and `k = d(t - 1)`. -/
theorem latin_square_degree_bound (d t : ℤ) (hd : 2 ≤ d) (hdt : d ≤ t) :
    Real.sqrt ((t : ℝ) ^ 2) < ((d * (t - 1) : ℤ) : ℝ) + 1 := by
  have ht : 2 ≤ t := le_trans hd hdt
  have hgt : t < (d * (t - 1) : ℤ) + 1 := by
    have h1 : (1 : ℤ) ≤ d - 1 := by linarith
    have h2 : (1 : ℤ) ≤ t - 1 := by linarith
    have hp : (1 : ℤ) ≤ (d - 1) * (t - 1) :=
      mul_le_mul h1 h2 (by norm_num) (by linarith)
    have e : d * (t - 1) = (d - 1) * (t - 1) + (t - 1) := by ring
    linarith
  have hgt' : (t : ℝ) < ((d * (t - 1) : ℤ) : ℝ) + 1 := by exact_mod_cast hgt
  have htr : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (by linarith : (0 : ℤ) ≤ t)
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg htr]
  exact hgt'

end Qatlib.Papers.NoGlobalSym14.GraphFamilies
