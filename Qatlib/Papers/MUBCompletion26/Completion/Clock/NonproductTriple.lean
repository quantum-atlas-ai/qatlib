/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Qatlib.Papers.MUBCompletion26.Completion.Clock.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Exact Nonproduct Mutually Unbiased Triple in Dimension Six

This module formalizes Section 9.1, Equations (9.1)--(9.2) of Sun on the exact
nonproduct mutually unbiased triple in `ℂ^3 ⊗ ℂ^2`, establishing that both the
first-orbit and complementary-orbit seed columns have Schmidt rank `2` in the
native qutrit-qubit factorization and that the anchor transition cross-ratio
`t̄ = (1 - 3i) / √10` is not a root of unity.

## Main definitions

* `t9`, `cvec`, `svec`, `pvec`, `seedCol`, `seedColComp`: deformed clock-orbit
  seed parameters and columns of Eq. (9.1).
* `SchmidtRank`, `PhaseCrossRatio`, `IsNonproductAnchor`: Schmidt rank in
  `ℂ^3 ⊗ ℂ^2` and `2 × 2` transition cross-ratio certificate of Eq. (9.2).

## Main statements

* `nonproduct_seed_schmidt_rank_two`: Section 9.1, Eq. (9.1), Schmidt rank `2`
  for both seed orbits.
* `t9_star_not_root_of_unity`, `nonproduct_anchor_cross_ratio_not_root_of_unity`:
  Section 9.1, Eq. (9.2), `t̄` is not a root of unity.

## References

* [Sun, 2026][Sun2026], Section 9.1, Equations (9.1)--(9.2).
-/

open Matrix
open scoped Matrix BigOperators

set_option autoImplicit false

namespace Qatlib.Papers.MUBCompletion26.Completion.Clock

noncomputable section

/-- The parameter `t = (1 + 3i)/√10` of (9.1). -/
def t9 : ℂ := (1 + 3 * Complex.I) / ((Real.sqrt 10 : ℝ) : ℂ)

/-- The cosine amplitudes `c = (√(2/3), √(2/3), 1/√6)` of (9.1). -/
def cvec (j : Fin 3) : ℝ := if j = 2 then (Real.sqrt 6)⁻¹ else Real.sqrt (2 / 3)

/-- The sine amplitudes `s = (1/√3, 1/√3, √(5/6))` of (9.1). -/
def svec (j : Fin 3) : ℝ := if j = 2 then Real.sqrt (5 / 6) else Real.sqrt (1 / 3)

/-- The qutrit phase sequence `p = (1, ω, ζ)` with `ζ = -ω²`. -/
def pvec (ω : ℂ) (j : Fin 3) : ℂ := if j = 0 then 1 else if j = 1 then ω else -ω ^ 2

/-- The first-orbit seed columns `g_j = p_j(c_j + i s_j, c_j - i s_j)/√6`. -/
def seedCol (ω : ℂ) (j : Fin 3) (a : Fin 2) : ℂ :=
  pvec ω j *
      (if a = 0 then ((cvec j : ℂ) + Complex.I * (svec j : ℂ))
        else ((cvec j : ℂ) - Complex.I * (svec j : ℂ))) /
    ((Real.sqrt 6 : ℝ) : ℂ)

/-- The complementary-orbit seed columns, with phase sequence `p̄` and the
opposite qubit vector `(c_j - i s_j, c_j + i s_j)/√6` (eq. (8.18) with `η`). -/
def seedColComp (ω : ℂ) (j : Fin 3) (a : Fin 2) : ℂ :=
  star (pvec ω j) *
      (if a = 0 then ((cvec j : ℂ) - Complex.I * (svec j : ℂ))
        else ((cvec j : ℂ) + Complex.I * (svec j : ℂ))) /
    ((Real.sqrt 6 : ℝ) : ℂ)

/-- Schmidt rank of a vector in `ℂ³ ⊗ ℂ²`, i.e. the rank of its coefficient
matrix `M_{j,a}` in the native qutrit--qubit order. -/
def SchmidtRank (v : Fin 3 × Fin 2 → ℂ) : ℕ :=
  Matrix.rank (fun j (a : Fin 2) => v (j, a))

private lemma rank_two_of_minor (M : Matrix (Fin 3) (Fin 2) ℂ)
    (hdet : M 0 0 * M 2 1 - M 0 1 * M 2 0 ≠ 0) : M.rank = 2 := by
  have hinj : Function.Injective M.mulVecLin := by
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    have h0 := congrFun hv 0
    have h2 := congrFun hv 2
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Pi.zero_apply] at h0 h2
    have hv0 : v 0 = 0 := by
      apply (mul_eq_zero.mp (show
        (M 0 0 * M 2 1 - M 0 1 * M 2 0) * v 0 = 0 by
          linear_combination M 2 1 * h0 - M 0 1 * h2)).resolve_left hdet
    have hv1 : v 1 = 0 := by
      apply (mul_eq_zero.mp (show
        (M 0 0 * M 2 1 - M 0 1 * M 2 0) * v 1 = 0 by
          linear_combination M 0 0 * h2 - M 2 0 * h0)).resolve_left hdet
    ext a
    fin_cases a <;> assumption
  rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj]
  simp

private lemma amplitude_minor_ne_zero :
    (cvec 0 : ℂ) * (svec 2 : ℂ) - (svec 0 : ℂ) * (cvec 2 : ℂ) ≠ 0 := by
  have hc0 : cvec 0 ^ 2 = 2 / 3 := by
    change Real.sqrt (2 / 3) ^ 2 = 2 / 3
    exact Real.sq_sqrt (by norm_num)
  have hs0 : svec 0 ^ 2 = 1 / 3 := by
    change Real.sqrt (1 / 3) ^ 2 = 1 / 3
    exact Real.sq_sqrt (by norm_num)
  have hc2 : cvec 2 ^ 2 = 1 / 6 := by
    change (Real.sqrt 6)⁻¹ ^ 2 = 1 / 6
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hs2 : svec 2 ^ 2 = 5 / 6 := by
    change Real.sqrt (5 / 6) ^ 2 = 5 / 6
    exact Real.sq_sqrt (by norm_num)
  norm_cast
  intro h
  have hsq := congrArg (fun x : ℝ => x ^ 2) (sub_eq_zero.mp h)
  rw [mul_pow, mul_pow, hc0, hs2, hs0, hc2] at hsq
  norm_num at hsq

private lemma seed_matrix_rank_two (p : Fin 3 → ℂ) (hp0 : p 0 ≠ 0) (hp2 : p 2 ≠ 0)
    (z : ℂ) (hz : z ≠ 0) :
    Matrix.rank (fun (j : Fin 3) (a : Fin 2) =>
      p j * (if a = 0 then (cvec j : ℂ) + z * (svec j : ℂ)
        else (cvec j : ℂ) - z * (svec j : ℂ)) / (Real.sqrt 6 : ℂ)) = 2 := by
  apply rank_two_of_minor
  norm_num only [Fin.isValue, ↓reduceIte, Fin.reduceEq]
  have hr : (Real.sqrt 6 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 6)))
  have hminor :
      p 0 * ((cvec 0 : ℂ) + z * (svec 0 : ℂ)) / (Real.sqrt 6 : ℂ) *
          (p 2 * ((cvec 2 : ℂ) - z * (svec 2 : ℂ)) / (Real.sqrt 6 : ℂ)) -
        p 0 * ((cvec 0 : ℂ) - z * (svec 0 : ℂ)) / (Real.sqrt 6 : ℂ) *
          (p 2 * ((cvec 2 : ℂ) + z * (svec 2 : ℂ)) / (Real.sqrt 6 : ℂ)) =
        -2 * z * p 0 * p 2 *
          ((cvec 0 : ℂ) * (svec 2 : ℂ) - (svec 0 : ℂ) * (cvec 2 : ℂ)) /
            (Real.sqrt 6 : ℂ) ^ 2 := by ring
  rw [hminor]
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hz) hp0) hp2)
      amplitude_minor_ne_zero) (pow_ne_zero 2 hr)

/-- §9.1, first paragraph of the nonproduct application (arXiv:2610.12180v1,
after eq. (9.1)).  All six constructed columns of the seed and of its
complementary orbit have Schmidt rank two in the native `ℂ³ ⊗ ℂ²` order. -/
theorem nonproduct_seed_schmidt_rank_two (ω : ℂ) (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    SchmidtRank (fun p : Fin 3 × Fin 2 => seedCol ω p.1 p.2) = 2 ∧
      SchmidtRank (fun p : Fin 3 × Fin 2 => seedColComp ω p.1 p.2) = 2 := by
  have hcycl : ω ^ 2 + ω + 1 = 0 :=
    (mul_eq_zero.mp (by linear_combination hω :
      (ω - 1) * (ω ^ 2 + ω + 1) = 0)).resolve_left (sub_ne_zero.mpr hω1)
  have hphase : -ω ^ 2 = ω + 1 := by linear_combination -hcycl
  have hsum : ω + 1 ≠ 0 := by
    intro h
    have hneg : ω = -1 := by linear_combination h
    norm_num [hneg] at hω
  have hp0 : pvec ω 0 ≠ 0 := by norm_num [pvec]
  have hp2 : pvec ω 2 ≠ 0 := by simpa [pvec, hphase] using hsum
  constructor
  · exact seed_matrix_rank_two (pvec ω) hp0 hp2 Complex.I Complex.I_ne_zero
  · simpa only [SchmidtRank, seedColComp, neg_mul, sub_eq_add_neg, neg_neg] using
      seed_matrix_rank_two (fun j => star (pvec ω j))
        (by simpa using hp0) (by simpa using hp2) (-Complex.I)
        (neg_ne_zero.mpr Complex.I_ne_zero)

/-- The phase cross-ratio of a `2 × 2` submatrix of a flat transition matrix
(rows `p, r`, columns `q, s`): the product of the diagonal entries divided by
the product of the off-diagonal entries. -/
def PhaseCrossRatio (K : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ)
    (p q r s : Fin 3 × Fin 2) : ℂ :=
  (K p q * K r s) / (K p s * K r q)

/-- The anchor-transition certificate (9.2): the `2 × 2` phase cross-ratio at
rows `(0,0),(2,0)` and columns `(0,0),(0,1)` equals `t̄`. -/
structure IsNonproductAnchor (K : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) : Prop where
  cross_ratio : PhaseCrossRatio K (0, 0) (0, 0) (2, 0) (0, 1) = star t9

/-- §9.1, eq. (9.2) (arXiv:2610.12180v1).  The complex number `t̄` is not a root
of unity. -/
theorem t9_star_not_root_of_unity : ¬ IsRootOfUnity (star t9) := by
  rintro ⟨n, hn, hpow⟩
  have hr : (Real.sqrt 10 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 10)))
  have hrsq : (Real.sqrt 10 : ℂ) ^ 2 = 10 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10))
  have hstar : star t9 = (1 - 3 * Complex.I) / (Real.sqrt 10 : ℂ) := by
    simp [t9, sub_eq_add_neg]
  have hunit : t9 * star t9 = 1 := by
    rw [hstar, t9, div_mul_div_comm, ← sq]
    apply (div_eq_one_iff_eq (pow_ne_zero 2 hr)).mpr
    rw [hrsq]
    calc
      (1 + 3 * Complex.I) * (1 - 3 * Complex.I) = 1 - 9 * Complex.I ^ 2 := by ring
      _ = 10 := by rw [Complex.I_sq]; norm_num
  have htpow : t9 ^ n = 1 := by
    calc
      t9 ^ n = t9 ^ n * (star t9) ^ n := by rw [hpow, mul_one]
      _ = (t9 * star t9) ^ n := (mul_pow _ _ _).symm
      _ = 1 := by rw [hunit, one_pow]
  have hint (z : ℂ) (hz : z ^ n = 1) : IsIntegral ℤ z := by
    refine ⟨Polynomial.X ^ n - Polynomial.C 1,
      Polynomial.monic_X_pow_sub_C 1 hn.ne', ?_⟩
    simp [hz]
  have hintsum : IsIntegral ℤ ((t9 + star t9) ^ 2) :=
    ((hint t9 htpow).add (hint (star t9) hpow)).pow 2
  have hsum : t9 + star t9 = 2 / (Real.sqrt 10 : ℂ) := by
    rw [hstar, t9]
    ring
  have hsq : (t9 + star t9) ^ 2 = algebraMap ℚ ℂ (2 / 5) := by
    rw [hsum, div_pow, hrsq]
    norm_num
  rw [hsq] at hintsum
  have hrat : IsIntegral ℤ (2 / 5 : ℚ) := isIntegral_algebraMap_iff.mp hintsum
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hrat
  have hmrat : (5 : ℚ) * m = 2 := by
    have hm' : (m : ℚ) = 2 / 5 := by simpa using hm
    rw [hm']
    norm_num
  have hmint : (5 : ℤ) * m = 2 := by exact_mod_cast hmrat
  omega

/-- §9.1, eq. (9.2) (arXiv:2610.12180v1).  For the anchor transition `K` of the
nonproduct triple, the phase cross-ratio `t̄` is not a root of unity.  This is
the invariant that excludes equivalence to both product models, all of whose
transition cross-ratios are roots of unity. -/
theorem nonproduct_anchor_cross_ratio_not_root_of_unity
    (K : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) (hK : IsNonproductAnchor K) :
    ¬ IsRootOfUnity (PhaseCrossRatio K (0, 0) (0, 0) (2, 0) (0, 1)) := by
  rw [hK.cross_ratio]
  exact t9_star_not_root_of_unity

end

end Qatlib.Papers.MUBCompletion26.Completion.Clock
