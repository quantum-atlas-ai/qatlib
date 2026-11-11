/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HighOrderODE10.MainResults.SourceModel
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option backward.isDefEq.respectTransparency false

/-!
# HighOrderODE10 — Lemma 4: global error scaling

Fixed source: Berry, arXiv:1010.2745v2 (28 Jan 2014), Lemma 4 and its proof,
p. 5–6, Eq. (18)–(25).

Paper proof route (all constants absorbed into `C`):

* Theorem 3 (Hairer–Wanner Thm 7.6, Ref. [20]) — globally
  `‖x(t_m) − x_m‖ ≤ M κ_V (max_{0≤j<k}‖x(t_j) − x_j‖ + h^p ∫_{t_0}^{t_m}‖x^{(p+1)}(ξ)‖dξ)`
  — reproduced as Eq. (17).
* Euler starting values give `max_{0≤j<k}‖x(t_j) − x_j‖ ≤ M_E κ_V h²(k−1)
  max ‖x^{(2)}‖` (Eq. 20–21).
* With constant `b`, `x(t) = e^{A(t−t_0)}(x_init + A⁻¹b) − A⁻¹b` (Eq. 22) and
  `‖x^{(ℓ)}(t)‖ ≤ κ_V(‖A‖^ℓ‖x_init‖ + ‖A‖^{ℓ−1}‖b‖)` (Eq. 23–24).
* Substituting into Eq. (17) yields Eq. (25), which is Eq. (19) with the big-O
  understood as an explicit method-only constant.

The statement below keeps `err = ‖x(t_m) − x_m‖`, the Theorem 3 bound, and the
Eq. (21)/(24) derivative bounds as the paper's own displayed hypotheses (the
first is a cited theorem, the others are derived in the paper).  The final
algebraic assembly of Eq. (25) is **proved** in `lemma4_globalError_isO`: the
starting-value term matches the `κ_V(h‖A‖)²` summand and the integral term the
`m(h‖A‖)^{p+1}` summand of Eq. (19).  Only the three displayed bounds
themselves are not reproved here.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HighOrderODE10.MainResults

open Finset
open scoped BigOperators

/-- **Lemma 4** (Berry, arXiv:1010.2745v2, p. 5–6, Eq. (18)–(19)).
For a multistep method of order `p`, `A(α)`-stable and stable at infinity, with
`A = V diag(λ) V⁻¹` and eigenvalues in the wedge `|arg(−λ_i)| ≤ α` (formalised
by `Re λ_i ≤ 0`), and constant `b`, the global error satisfies

`‖x(t_m) − x_m‖ = O(κ_V²(‖x_init‖ + ‖b‖/‖A‖)[κ_V(h‖A‖)² + m(h‖A‖)^{p+1}])`.

The bound is Eq. (19); `sourceGlobalErrorExpr` is its right-hand side.

**Fixed source:** arXiv:1010.2745v2 (28 Jan 2014), Lemma 4, p. 5–6.
**Paper proof steps:** Eq. (17) (cited Hairer–Wanner Thm 7.6), Eq. (20)–(21)
(Euler starting error), Eq. (22)–(24) (exact-solution derivative bounds),
Eq. (25) (assembly).
**Lean content:** the three displayed inequalities of the paper — the cited
Theorem 3 bound (`hThm3`), the Euler starting-value bound (`hStart`) and the
derivative bound (`hDeriv`) — are taken as the paper's own hypotheses, and the
Eq. (25) assembly is proved here concretely: the starting-value term and the
integral term are matched against the two summands of Eq. (19) with witness
`C = M_T(M_E(k−1)+1)+1`, using `h^{p+1} = h·h^p`, `(h‖A‖)^{p+1} =
h^{p+1}‖A‖^{p+1}` and `(‖x‖+‖b‖/‖A‖)‖A‖ = ‖A‖‖x‖+‖b‖`.  The only ingredients
not proved here are the three cited/derived bounds themselves. -/
theorem lemma4_globalError_isO
    (m : SourceMultistepMethod) (n : ℕ)
    (A V : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ)
    (hdiag : A = V * Matrix.diagonal d * V⁻¹)
    (hangle : ∀ i, (d i).re ≤ 0)
    (κV h M xinNorm bNorm err startErr derivInt ME MT : ℝ) (tm : ℝ) (steps : ℕ)
    (p : ℕ) (hp : 0 < p)
    (hκV : 0 ≤ κV) (hh : 0 ≤ h) (hM : 0 < M) (hxin : 0 ≤ xinNorm) (hb : 0 ≤ bNorm)
    (hMT : 0 < MT) (hME : 0 ≤ ME)
    (hThm3 : err ≤ MT * κV * (startErr + h ^ p * derivInt))
    (hStart : startErr ≤ ME * κV * h ^ 2 * ((m.k : ℝ) - 1) * κV *
      (M ^ 2 * xinNorm + M * bNorm))
    (hDeriv : derivInt ≤ tm * κV * (M ^ (p + 1) * xinNorm + M ^ p * bNorm))
    (hTm : tm = (steps : ℝ) * h) :
    ∃ C : ℝ, 0 < C ∧ err ≤ C * sourceGlobalErrorExpr κV h M xinNorm bNorm p steps := by
  have hkpos : (0 : ℝ) < (m.k : ℝ) := by exact_mod_cast m.hk
  have hkm1 : 0 ≤ (m.k : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ m.k := m.hk
    have h1' : (1 : ℝ) ≤ (m.k : ℝ) := by exact_mod_cast h1
    linarith
  have hMne : M ≠ 0 := ne_of_gt hM
  have hX : 0 ≤ M ^ 2 * xinNorm + M * bNorm := by
    have h1 : 0 ≤ M ^ 2 * xinNorm := mul_nonneg (sq_nonneg M) hxin
    have h2 : 0 ≤ M * bNorm := mul_nonneg (le_of_lt hM) hb
    linarith
  -- Eq. (20)-(21): Euler starting values, regrouped in the shape of Eq. (25).
  have hstart : startErr ≤
      ME * ((m.k : ℝ) - 1) * κV ^ 2 * h ^ 2 * (M ^ 2 * xinNorm + M * bNorm) := by
    calc startErr
        ≤ ME * κV * h ^ 2 * ((m.k : ℝ) - 1) * κV * (M ^ 2 * xinNorm + M * bNorm) :=
          hStart
      _ = ME * ((m.k : ℝ) - 1) * κV ^ 2 * h ^ 2 * (M ^ 2 * xinNorm + M * bNorm) := by
          ring
  -- Eq. (23)-(24): the derivative bound, with the `h^p` absorbed into the integral.
  have hderiv : h ^ p * derivInt ≤
      steps * h ^ (p + 1) * κV * (M ^ (p + 1) * xinNorm + M ^ p * bNorm) := by
    have hp0 : (0 : ℝ) ≤ h ^ p := pow_nonneg hh p
    have hmul := mul_le_mul_of_nonneg_left hDeriv hp0
    calc h ^ p * derivInt
        ≤ h ^ p * (tm * κV * (M ^ (p + 1) * xinNorm + M ^ p * bNorm)) := hmul
      _ = steps * h ^ (p + 1) * κV * (M ^ (p + 1) * xinNorm + M ^ p * bNorm) := by
          rw [hTm, pow_succ']
          ring
  have hMTkV : (0 : ℝ) ≤ MT * κV := mul_nonneg (le_of_lt hMT) hκV
  -- Eq. (17) with the two displayed bounds inserted.
  have herr : err ≤ MT * κV *
      (ME * ((m.k : ℝ) - 1) * κV ^ 2 * h ^ 2 * (M ^ 2 * xinNorm + M * bNorm) +
        steps * h ^ (p + 1) * κV * (M ^ (p + 1) * xinNorm + M ^ p * bNorm)) := by
    calc err ≤ MT * κV * (startErr + h ^ p * derivInt) := hThm3
      _ ≤ MT * κV *
          (ME * ((m.k : ℝ) - 1) * κV ^ 2 * h ^ 2 * (M ^ 2 * xinNorm + M * bNorm) +
            steps * h ^ (p + 1) * κV * (M ^ (p + 1) * xinNorm + M ^ p * bNorm)) :=
          mul_le_mul_of_nonneg_left (add_le_add hstart hderiv) hMTkV
  -- The method-only constant of Eq. (25).
  have hmk : 0 ≤ ME * ((m.k : ℝ) - 1) := mul_nonneg hME hkm1
  have hC1 : MT * ME * ((m.k : ℝ) - 1) ≤ MT * (ME * ((m.k : ℝ) - 1) + 1) + 1 := by
    nlinarith [hMT, hmk]
  have hC2 : MT ≤ MT * (ME * ((m.k : ℝ) - 1) + 1) + 1 := by
    have h3 : 0 ≤ MT * (ME * ((m.k : ℝ) - 1)) := mul_nonneg (le_of_lt hMT) hmk
    nlinarith
  have hCpos : 0 < MT * (ME * ((m.k : ℝ) - 1) + 1) + 1 := by
    have h3 : 0 ≤ MT * (ME * ((m.k : ℝ) - 1)) := mul_nonneg (le_of_lt hMT) hmk
    linarith
  refine ⟨MT * (ME * ((m.k : ℝ) - 1) + 1) + 1, hCpos, ?_⟩
  rw [sourceGlobalErrorExpr]
  -- First summand of Eq. (19): the `κ_V(h‖A‖)^2` term.
  have hT1 : MT * κV *
      (ME * ((m.k : ℝ) - 1) * κV ^ 2 * h ^ 2 * (M ^ 2 * xinNorm + M * bNorm)) ≤
      (MT * (ME * ((m.k : ℝ) - 1) + 1) + 1) *
        (κV ^ 2 * (xinNorm + bNorm / M) * (κV * (h * M) ^ 2)) := by
    have hnn : 0 ≤ κV ^ 3 * h ^ 2 * (M ^ 2 * xinNorm + M * bNorm) := by positivity
    calc MT * κV *
          (ME * ((m.k : ℝ) - 1) * κV ^ 2 * h ^ 2 * (M ^ 2 * xinNorm + M * bNorm))
        = (MT * ME * ((m.k : ℝ) - 1)) *
            (κV ^ 3 * h ^ 2 * (M ^ 2 * xinNorm + M * bNorm)) := by ring
      _ ≤ (MT * (ME * ((m.k : ℝ) - 1) + 1) + 1) *
            (κV ^ 3 * h ^ 2 * (M ^ 2 * xinNorm + M * bNorm)) :=
          mul_le_mul_of_nonneg_right hC1 hnn
      _ = (MT * (ME * ((m.k : ℝ) - 1) + 1) + 1) *
            (κV ^ 2 * (xinNorm + bNorm / M) * (κV * (h * M) ^ 2)) := by
          rw [mul_pow]
          field_simp
  -- Second summand of Eq. (19): the `m(h‖A‖)^{p+1}` term.
  have hT2 : MT * κV *
      (steps * h ^ (p + 1) * κV * (M ^ (p + 1) * xinNorm + M ^ p * bNorm)) ≤
      (MT * (ME * ((m.k : ℝ) - 1) + 1) + 1) *
        (κV ^ 2 * (xinNorm + bNorm / M) * (steps * (h * M) ^ (p + 1))) := by
    have hnn : 0 ≤ κV ^ 2 * (steps : ℝ) * h ^ (p + 1) *
        (M ^ p * (M * xinNorm + bNorm)) := by positivity
    calc MT * κV *
          (steps * h ^ (p + 1) * κV * (M ^ (p + 1) * xinNorm + M ^ p * bNorm))
        = MT * (κV ^ 2 * (steps : ℝ) * h ^ (p + 1) *
            (M ^ p * (M * xinNorm + bNorm))) := by
          rw [pow_succ' M p]
          ring
      _ ≤ (MT * (ME * ((m.k : ℝ) - 1) + 1) + 1) *
            (κV ^ 2 * (steps : ℝ) * h ^ (p + 1) * (M ^ p * (M * xinNorm + bNorm))) :=
          mul_le_mul_of_nonneg_right hC2 hnn
      _ = (MT * (ME * ((m.k : ℝ) - 1) + 1) + 1) *
            (κV ^ 2 * (xinNorm + bNorm / M) * (steps * (h * M) ^ (p + 1))) := by
          rw [mul_pow, pow_succ' M p, pow_succ' h p]
          field_simp
  calc err
      ≤ MT * κV *
          (ME * ((m.k : ℝ) - 1) * κV ^ 2 * h ^ 2 * (M ^ 2 * xinNorm + M * bNorm) +
            steps * h ^ (p + 1) * κV * (M ^ (p + 1) * xinNorm + M ^ p * bNorm)) := herr
    _ = MT * κV *
          (ME * ((m.k : ℝ) - 1) * κV ^ 2 * h ^ 2 * (M ^ 2 * xinNorm + M * bNorm)) +
        MT * κV *
          (steps * h ^ (p + 1) * κV * (M ^ (p + 1) * xinNorm + M ^ p * bNorm)) := by ring
    _ ≤ (MT * (ME * ((m.k : ℝ) - 1) + 1) + 1) *
          (κV ^ 2 * (xinNorm + bNorm / M) * (κV * (h * M) ^ 2)) +
        (MT * (ME * ((m.k : ℝ) - 1) + 1) + 1) *
          (κV ^ 2 * (xinNorm + bNorm / M) * (steps * (h * M) ^ (p + 1))) :=
        add_le_add hT1 hT2
    _ = (MT * (ME * ((m.k : ℝ) - 1) + 1) + 1) *
          (κV ^ 2 * (xinNorm + bNorm / M) *
            (κV * (h * M) ^ 2 + steps * (h * M) ^ (p + 1))) := by ring

end Qatlib.Papers.HighOrderODE10.MainResults
