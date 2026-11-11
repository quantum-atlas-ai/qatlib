/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PoissonEq12.MainResults.TrigQuadrature
import Qatlib.Papers.PoissonEq12.MainResults.RepeatedSquaring

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 2 of *Quantum algorithm and circuit design solving the Poisson equation*
(arXiv:1207.2485, Appendix 2)

Combining Lemma 1 (`|exp (i x) - W ^ r| ≤ 2 ^ 7 / r`) with Proposition 1
(`|W ^ r - Ŵ_r| ≤ 2 ^ (ν + 9) / 2 ^ s`) gives, for `s = max {2ν + 9, 11 + ν + log₂ M}`,

`|sin x - Im Ŵ_r| ≤ 2 ^ (-(ν - 1))`,

and hence the two error bounds on the periodic eigenvalues `4 M ^ 2 sin ^ 2 (j π / (2 M))` of
`h ^ (-2) L_h` that the paper uses to build the d-dimensional spectrum: the untruncated bound
`2 ^ (-(ν - 4)) M ^ 2` and, after truncating to `ν` bits, `17 · 2 ^ (-ν) M ^ 2`.

The paper derives the second and third parts "immediately" from the first; here they are
separate lemmas because the truncation of `ℓ_j` to `ν` bits is an explicit hypothesis
(`|ℓ - 4 M ^ 2 (Im Ŵ_r) ^ 2| ≤ 2 ^ (-ν)`) rather than a construction.
-/

namespace Qatlib.Papers.PoissonEq12.MainResults

set_option autoImplicit false

open Complex

/-- `2 ^ 7 / 2 ^ (ν + 7) = 2 ^ (-ν)`. -/
lemma two_pow_seven_div_two_pow_add_seven (ν : ℕ) :
    128 / (2 : ℝ) ^ (ν + 7) = 1 / 2 ^ ν := by
  have h : (2 : ℝ) ^ (ν + 7) = (2 : ℝ) ^ ν * 128 := by
    rw [pow_add]
    norm_num
  rw [h]
  field_simp

/-- `2 ^ (ν + 9) / 2 ^ s ≤ 2 ^ (-ν)` for `s ≥ 2ν + 9`. -/
lemma two_pow_add_div_two_pow_le {ν s : ℕ} (hs : 2 * ν + 9 ≤ s) :
    (2 : ℝ) ^ (ν + 9) / 2 ^ s ≤ 1 / 2 ^ ν := by
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ s) (by positivity : (0 : ℝ) < 2 ^ ν),
    one_mul, ← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- **Proposition 2** of arXiv:1207.2485, first part: for `x ∈ [0, π / 2)` and
`s ≥ 2ν + 9`, the imaginary part of the repeated-squaring approximation `Ŵ_r` approximates
`sin x` within `2 ^ (-(ν - 1))`. -/
theorem prop2_sin {ν s : ℕ} (hν : 1 ≤ ν) (hs : 2 * ν + 9 ≤ s) (T : BitTruncation s) {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x < Real.pi / 2) :
    |Real.sin x - (repeatedSquaring T (wQuad (x / (2 : ℝ) ^ (ν + 7))) (ν + 7)).im|
      ≤ 2 / 2 ^ ν := by
  have hrpos : (0 : ℝ) < (2 : ℝ) ^ (ν + 7) := by positivity
  have hr4 : (4 : ℝ) ≤ (2 : ℝ) ^ (ν + 7) := by
    have h1 : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ (ν + 7) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ 2 = 4 := by norm_num
    linarith
  have hx2 : x ≤ 2 := by linarith [Real.pi_lt_four, Real.pi_pos]
  set y : ℝ := x / (2 : ℝ) ^ (ν + 7) with hy
  have hy0 : 0 ≤ y := by
    rw [hy]
    positivity
  have hy1 : y ≤ 1 := by
    rw [hy, div_le_iff₀ hrpos]
    linarith
  have h1 := lemma1 hν hx0 hx
  have h2 := prop1 (ν := ν) T hy0 hy1
  have hsin : (exp ((x : ℂ) * I)).im = Real.sin x := Complex.exp_ofReal_mul_I_im x
  have hdiff : |Real.sin x - (repeatedSquaring T (wQuad (x / (2 : ℝ) ^ (ν + 7))) (ν + 7)).im|
      ≤ ‖exp ((x : ℂ) * I) - repeatedSquaring T (wQuad y) (ν + 7)‖ := by
    rw [← hy, ← hsin, ← Complex.sub_im]
    exact abs_im_le_norm' _
  refine hdiff.trans ?_
  have hdec : exp ((x : ℂ) * I) - repeatedSquaring T (wQuad y) (ν + 7)
      = (exp ((x : ℂ) * I) - wQuad y ^ (2 ^ (ν + 7)))
        + (wQuad y ^ (2 ^ (ν + 7)) - repeatedSquaring T (wQuad y) (ν + 7)) := by
    ring
  calc ‖exp ((x : ℂ) * I) - repeatedSquaring T (wQuad y) (ν + 7)‖
      ≤ ‖exp ((x : ℂ) * I) - wQuad y ^ (2 ^ (ν + 7))‖
        + ‖wQuad y ^ (2 ^ (ν + 7)) - repeatedSquaring T (wQuad y) (ν + 7)‖ := by
        rw [hdec]
        exact norm_add_le _ _
    _ ≤ 128 / (2 : ℝ) ^ (ν + 7) + (2 : ℝ) ^ (ν + 9) / 2 ^ s := add_le_add h1 h2
    _ ≤ 1 / 2 ^ ν + 1 / 2 ^ ν :=
        add_le_add (le_of_eq (two_pow_seven_div_two_pow_add_seven ν))
          (two_pow_add_div_two_pow_le hs)
    _ = 2 / 2 ^ ν := by ring

/-- **Proposition 2**, second part (`(i)`): the untruncated squared-sine eigenvalues satisfy
`|4 M ^ 2 sin ^ 2 θ - 4 M ^ 2 t ^ 2| ≤ 2 ^ (-(ν - 4)) M ^ 2` whenever `t` approximates `sin θ`
within `2 ^ (-(ν - 1))` and `|t| ≤ 1`. -/
theorem prop2_eigenvalue {ν M : ℕ} (hM : 1 ≤ M) {θ t : ℝ}
    (h : |Real.sin θ - t| ≤ 2 / 2 ^ ν) (ht : |t| ≤ 1) :
    |(4 : ℝ) * (M : ℝ) ^ 2 * Real.sin θ ^ 2 - (4 : ℝ) * (M : ℝ) ^ 2 * t ^ 2|
      ≤ (16 : ℝ) * (M : ℝ) ^ 2 / 2 ^ ν := by
  have hsin1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have hsq : Real.sin θ ^ 2 - t ^ 2 = (Real.sin θ - t) * (Real.sin θ + t) := by ring
  have hsum : |Real.sin θ + t| ≤ 2 := by
    calc |Real.sin θ + t| ≤ |Real.sin θ| + |t| := abs_add_le _ _
      _ ≤ 1 + 1 := by linarith
      _ = 2 := by norm_num
  have hprod : |Real.sin θ ^ 2 - t ^ 2| ≤ (2 / 2 ^ ν) * 2 := by
    rw [hsq, abs_mul]
    exact mul_le_mul h hsum (abs_nonneg _) (by positivity)
  have hfactor : (4 : ℝ) * (M : ℝ) ^ 2 * Real.sin θ ^ 2 - (4 : ℝ) * (M : ℝ) ^ 2 * t ^ 2
      = (4 : ℝ) * (M : ℝ) ^ 2 * (Real.sin θ ^ 2 - t ^ 2) := by ring
  rw [hfactor, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * (M : ℝ) ^ 2)]
  calc (4 : ℝ) * (M : ℝ) ^ 2 * |Real.sin θ ^ 2 - t ^ 2|
      ≤ (4 : ℝ) * (M : ℝ) ^ 2 * ((2 / 2 ^ ν) * 2) := by gcongr
    _ = (16 : ℝ) * (M : ℝ) ^ 2 / 2 ^ ν := by ring_nf

/-- **Proposition 2**, third part (`(ii)`): truncating `4 M ^ 2 (Im Ŵ_r) ^ 2` to `ν` bits after
the decimal point (`|ℓ - 4 M ^ 2 (Im Ŵ_r) ^ 2| ≤ 2 ^ (-ν)`) gives
`|4 M ^ 2 sin ^ 2 θ - ℓ| ≤ 17 · 2 ^ (-ν) M ^ 2` for `M ≥ 1`. -/
theorem prop2_eigenvalue_truncated {ν M : ℕ} (hM : 1 ≤ M) {θ t ℓ : ℝ}
    (h : |Real.sin θ - t| ≤ 2 / 2 ^ ν) (ht : |t| ≤ 1)
    (hℓ : |ℓ - (4 : ℝ) * (M : ℝ) ^ 2 * t ^ 2| ≤ 1 / 2 ^ ν) :
    |(4 : ℝ) * (M : ℝ) ^ 2 * Real.sin θ ^ 2 - ℓ| ≤ (17 : ℝ) * (M : ℝ) ^ 2 / 2 ^ ν := by
  have h1 := prop2_eigenvalue (M := M) hM h ht
  have hM2 : (1 : ℝ) ≤ (M : ℝ) ^ 2 := by
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    nlinarith
  have hdec : (4 : ℝ) * (M : ℝ) ^ 2 * Real.sin θ ^ 2 - ℓ
      = ((4 : ℝ) * (M : ℝ) ^ 2 * Real.sin θ ^ 2 - (4 : ℝ) * (M : ℝ) ^ 2 * t ^ 2)
        + ((4 : ℝ) * (M : ℝ) ^ 2 * t ^ 2 - ℓ) := by ring
  rw [hdec]
  refine (abs_add_le _ _).trans ?_
  have hℓ' : |(4 : ℝ) * (M : ℝ) ^ 2 * t ^ 2 - ℓ| ≤ 1 / 2 ^ ν := by
    rw [abs_sub_comm]
    exact hℓ
  refine (add_le_add h1 hℓ').trans ?_
  have hadd : (16 : ℝ) * (M : ℝ) ^ 2 / 2 ^ ν + 1 / 2 ^ ν
      = ((16 : ℝ) * (M : ℝ) ^ 2 + 1) / 2 ^ ν := by rw [← add_div]
  rw [hadd]
  gcongr
  nlinarith

/-- Proposition 2 instantiated at one grid point: the imaginary part of the repeated-squaring
evaluation of `W` approximates `sin x` within `2 ^ (-(ν - 1))`, hence the squared eigenvalue
`4 M ^ 2 sin ^ 2 x` is approximated by `4 M ^ 2 (Im Ŵ_r) ^ 2` within `2 ^ (-(ν - 4)) M ^ 2`. -/
theorem prop2_sine_eigenvalue {ν s M : ℕ} (hν : 1 ≤ ν) (hM : 1 ≤ M) (hs : 2 * ν + 9 ≤ s)
    (T : BitTruncation s) {x : ℝ} (hx0 : 0 ≤ x) (hx : x < Real.pi / 2) :
    |(4 : ℝ) * (M : ℝ) ^ 2 * Real.sin x ^ 2
        - (4 : ℝ) * (M : ℝ) ^ 2
          * ((repeatedSquaring T (wQuad (x / (2 : ℝ) ^ (ν + 7))) (ν + 7)).im) ^ 2|
      ≤ (16 : ℝ) * (M : ℝ) ^ 2 / 2 ^ ν := by
  have hrpos : (0 : ℝ) < (2 : ℝ) ^ (ν + 7) := by positivity
  have hr4 : (4 : ℝ) ≤ (2 : ℝ) ^ (ν + 7) := by
    have h1 : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ (ν + 7) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ 2 = 4 := by norm_num
    linarith
  have hx2 : x ≤ 2 := by linarith [Real.pi_lt_four, Real.pi_pos]
  have hy1 : x / (2 : ℝ) ^ (ν + 7) ≤ 1 := by
    rw [div_le_iff₀ hrpos]
    linarith
  have hy0 : 0 ≤ x / (2 : ℝ) ^ (ν + 7) := by positivity
  have hW : ‖wQuad (x / (2 : ℝ) ^ (ν + 7))‖ ≤ 1 := norm_wQuad_le_one hy0 hy1
  have htrunc : |(repeatedSquaring T (wQuad (x / (2 : ℝ) ^ (ν + 7))) (ν + 7)).im| ≤ 1 :=
    (abs_im_le_norm' _).trans (norm_repeatedSquaring_le_one T hW (ν + 7))
  exact prop2_eigenvalue hM (prop2_sin hν hs T hx0 hx) htrunc

end Qatlib.Papers.PoissonEq12.MainResults
