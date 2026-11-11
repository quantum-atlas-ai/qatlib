/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CirculantPrec18.SVETransport.Model
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# Source error estimate (Lemma 3, Eq.(9))

Shao--Xiang, fixed arXiv:1807.04563v1, Lemma 3, p.6, Eq. (9).

Source statement.  Assume

  `|φ⟩ = Z^{-1/2} Σⱼ aⱼ uⱼ`,   `|ψ⟩ = W^{-1/2} Σⱼ bⱼ vⱼ`,

where `{uⱼ}` and `{vⱼ}` are orthogonal bases (not necessarily unit), and
`|aⱼ − bⱼ| ≤ η₀`, `‖uⱼ − vⱼ‖² ≤ η₁`, `|Z − W| ≤ η₂`, `maxⱼ‖vⱼ‖² = η₃`,
`1/minⱼ‖uⱼ‖² = η₄`.  Then

  `‖|φ⟩ − |ψ⟩‖² ≤ 3η₁η₄ + 3η₂²η₃η₄ / (W(√W + √(W−η₂))²) + 3nη₀²η₃ / W`.  (9)

Proof (source).  Write `xⱼ = √W aⱼ uⱼ − √Z bⱼ vⱼ`.  Then
`xⱼ = √W aⱼ(uⱼ−vⱼ) + (√W−√Z)aⱼ vⱼ + √Z(aⱼ−bⱼ)vⱼ`, and the elementary bound
`(p+q+r)² ≤ 3(p²+q²+r²)` gives

  `‖xⱼ‖² ≤ 3(W aⱼ²‖uⱼ−vⱼ‖² + (√W−√Z)² aⱼ²‖vⱼ‖² + Z(aⱼ−bⱼ)²‖vⱼ‖²)`.

Summing over `j`, using `‖Σⱼ xⱼ‖² = Σⱼ‖xⱼ‖²` (the displayed source derivation
uses that the cross terms `⟨uⱼ,u_k⟩`, `⟨vⱼ,v_k⟩`, `⟨uⱼ,v_k⟩` for `j ≠ k`
vanish), `Σⱼ aⱼ² ≤ η₄ Z`, the bounds `η₁,η₀,η₃`, then dividing by `ZW` and using
`(√W−√Z)² = (W−Z)²/(√W+√Z)²`, `1/(√W+√Z)² ≤ 1/(√W+√(W−η₂))²`, `|W−Z| ≤ η₂`,
gives (9).

Formalisation notes.  The paper states (9) for the abstract families `uⱼ, vⱼ`.
The displayed derivation — `‖φ−ψ‖² = (ZW)⁻¹ Σⱼ ‖√W aⱼ uⱼ − √Z bⱼ vⱼ‖²` — is an
equality only when the two families are cross-orthogonal across indices.  In
the application of §3.2 both families are Fourier vectors with the same index
set, so this holds; we expose it as the hypothesis `hcross`.  Without it only
the weaker bound with an extra `n` on the `η₁` term follows from the stated
hypotheses, so the hypothesis is exactly the paper's implicit one rather than a
mathematical strengthening.  The state space is a real Hilbert space: the
inequality involves only norms, so the real form of the source's vector
statement is the faithful instance (complex amplitudes enter only through their
norms).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open scoped BigOperators InnerProductSpace

open Qatlib.Papers.CirculantPrec18.SVETransport

namespace Qatlib.Papers.CirculantPrec18.ErrorScope

/-- Elementary three-term inequality `(p+q+r)² ≤ 3(p²+q²+r²)`. -/
theorem sq_add_add_le_three (p q r : ℝ) : (p + q + r) ^ 2 ≤ 3 * (p ^ 2 + q ^ 2 + r ^ 2) := by
  nlinarith [sq_nonneg (p - q), sq_nonneg (q - r), sq_nonneg (p - r)]

/-- Fixed arXiv:1807.04563v1, Lemma 3, Eq. (9) (p.6): the squared distance
between `Z^{-1/2}Σaⱼuⱼ` and `W^{-1/2}Σbⱼvⱼ` is bounded by
`3η₁η₄ + 3η₂²η₃η₄/(W(√W+√(W−η₂))²) + 3nη₀²η₃/W`. -/
theorem source_error_estimate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι]
    (u v : ι → E) (a b : ι → ℝ) (Z W η0 η1 η2 η3 η4 : ℝ)
    (hZpos : 0 < Z) (hWpos : 0 < W)
    (hZ : Z = ∑ j, (a j) ^ 2 * ‖u j‖ ^ 2)
    (_hW : W = ∑ j, (b j) ^ 2 * ‖v j‖ ^ 2)
    (hu : ∀ j k, j ≠ k → ⟪u j, u k⟫_ℝ = 0)
    (hv : ∀ j k, j ≠ k → ⟪v j, v k⟫_ℝ = 0)
    (hcross : ∀ j k, j ≠ k → ⟪u j, v k⟫_ℝ = 0)
    (hη0 : ∀ j, |a j - b j| ≤ η0)
    (hη1 : ∀ j, ‖u j - v j‖ ^ 2 ≤ η1)
    (hη2 : |Z - W| ≤ η2)
    (hη3 : ∀ j, ‖v j‖ ^ 2 ≤ η3)
    (hη4pos : 0 < η4)
    (hη4 : ∀ j, 1 ≤ η4 * ‖u j‖ ^ 2)
    (hη0nn : 0 ≤ η0) (hη1nn : 0 ≤ η1) (hη3nn : 0 ≤ η3) :
    ‖((Real.sqrt Z : ℝ))⁻¹ • (∑ j, a j • u j)
        - ((Real.sqrt W : ℝ))⁻¹ • (∑ j, b j • v j)‖ ^ 2 ≤
      3 * η1 * η4 +
        3 * η2 ^ 2 * η3 * η4 / (W * (Real.sqrt W + Real.sqrt (W - η2)) ^ 2) +
        3 * (Fintype.card ι : ℝ) * η0 ^ 2 * η3 / W := by
  classical
  set κ : ℝ := (Fintype.card ι : ℝ) with hκdef
  set S : E := ∑ j, a j • u j with hSdef
  set T : E := ∑ j, b j • v j with hTdef
  set phi : E := ((Real.sqrt Z : ℝ))⁻¹ • S with hphidef
  set psi : E := ((Real.sqrt W : ℝ))⁻¹ • T with hpsidef
  set x : ι → E := fun j => (Real.sqrt W * a j) • u j - (Real.sqrt Z * b j) • v j with hxdef
  have hZpos' : (0 : ℝ) < Real.sqrt Z := Real.sqrt_pos.mpr hZpos
  have hWpos' : (0 : ℝ) < Real.sqrt W := Real.sqrt_pos.mpr hWpos
  have hsqrtZ_ne : (Real.sqrt Z : ℝ) ≠ 0 := ne_of_gt hZpos'
  have hsqrtW_ne : (Real.sqrt W : ℝ) ≠ 0 := ne_of_gt hWpos'
  have hWne : (W : ℝ) ≠ 0 := ne_of_gt hWpos
  have hZne : (Z : ℝ) ≠ 0 := ne_of_gt hZpos
  -- `S = √Z • phi` and `T = √W • psi`.
  have hS_eq : (Real.sqrt Z) • phi = S := by
    simp only [phi]; rw [smul_smul, mul_inv_cancel₀ hsqrtZ_ne, one_smul]
  have hT_eq : (Real.sqrt W) • psi = T := by
    simp only [psi]; rw [smul_smul, mul_inv_cancel₀ hsqrtW_ne, one_smul]
  -- `Σⱼ xⱼ = √(WZ) • (phi − psi)`.
  have hsum_eq : ∑ j, x j = (Real.sqrt W * Real.sqrt Z) • (phi - psi) := by
    have hS' : ∑ j, a j • u j = S := hSdef.symm
    have hT' : ∑ j, b j • v j = T := hTdef.symm
    have h1 : ∑ j, (Real.sqrt W * a j) • u j = (Real.sqrt W) • S := by
      have hcongr : ∑ j, (Real.sqrt W * a j) • u j = ∑ j, Real.sqrt W • (a j • u j) := by
        apply Finset.sum_congr rfl; intro j _; rw [smul_smul]
      rw [hcongr, ← Finset.smul_sum, hS']
    have h2 : ∑ j, (Real.sqrt Z * b j) • v j = (Real.sqrt Z) • T := by
      have hcongr : ∑ j, (Real.sqrt Z * b j) • v j = ∑ j, Real.sqrt Z • (b j • v j) := by
        apply Finset.sum_congr rfl; intro j _; rw [smul_smul]
      rw [hcongr, ← Finset.smul_sum, hT']
    have hsum_explicit : ∑ j, x j = (Real.sqrt W) • S - (Real.sqrt Z) • T := by
      simp only [x]; rw [Finset.sum_sub_distrib, h1, h2]
    have e1 : (Real.sqrt W * Real.sqrt Z) • ((Real.sqrt Z)⁻¹ • S) = (Real.sqrt W) • S := by
      rw [smul_smul]
      rw [show Real.sqrt W * Real.sqrt Z * (Real.sqrt Z)⁻¹ = Real.sqrt W by
            rw [mul_assoc, mul_inv_cancel₀ hsqrtZ_ne, mul_one]]
    have e2 : (Real.sqrt W * Real.sqrt Z) • ((Real.sqrt W)⁻¹ • T) = (Real.sqrt Z) • T := by
      rw [smul_smul]
      rw [show Real.sqrt W * Real.sqrt Z * (Real.sqrt W)⁻¹ = Real.sqrt Z by
            rw [mul_comm (Real.sqrt W) (Real.sqrt Z), mul_assoc,
              mul_inv_cancel₀ hsqrtW_ne, mul_one]]
    have hrhs : (Real.sqrt W * Real.sqrt Z) • (phi - psi)
        = (Real.sqrt W) • S - (Real.sqrt Z) • T := by
      change (Real.sqrt W * Real.sqrt Z) • ((Real.sqrt Z)⁻¹ • S - (Real.sqrt W)⁻¹ • T)
        = (Real.sqrt W) • S - (Real.sqrt Z) • T
      rw [smul_sub, e1, e2]
    exact hsum_explicit.trans hrhs.symm
  -- Norm relation `‖Σx‖ = √(WZ)·‖phi−psi‖`.
  have hnorm : ‖∑ j, x j‖ = Real.sqrt (W * Z) * ‖phi - psi‖ := by
    rw [hsum_eq, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg W) (Real.sqrt_nonneg Z)),
      Real.sqrt_mul (le_of_lt hWpos)]
  -- `‖phi−psi‖² = ‖Σx‖² / (WZ)`.
  have hWZpos : 0 < W * Z := mul_pos hWpos hZpos
  have hsq_norm : ‖phi - psi‖ ^ 2 = ‖∑ j, x j‖ ^ 2 / (W * Z) := by
    have hsq : ‖∑ j, x j‖ ^ 2 = (W * Z) * ‖phi - psi‖ ^ 2 := by
      rw [hnorm, mul_pow, Real.sq_sqrt (le_of_lt hWZpos)]
    rw [hsq, mul_div_cancel_left₀ _ (ne_of_gt hWZpos)]
  -- `Σⱼ‖xⱼ‖² = ‖Σx‖²`.
  have horth : ∀ j k, j ≠ k → ⟪x j, x k⟫_ℝ = 0 := by
    intro j k hjk
    have hvu : ⟪v j, u k⟫_ℝ = 0 := by
      rw [real_inner_comm, hcross k j (Ne.symm hjk)]
    simp only [x]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    simp only [hu j k hjk, hv j k hjk, hcross j k hjk, hvu]
    ring
  have hsum_sq : ‖∑ j, x j‖ ^ 2 = ∑ j, ‖x j‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    rw [sum_inner]
    simp_rw [inner_sum]
    rw [show (∑ j, ∑ k, ⟪x j, x k⟫_ℝ) = ∑ j, ⟪x j, x j⟫_ℝ by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_eq_single j]
      · intro k _ hk; exact horth j k (Ne.symm hk)
      · intro h; exact absurd (Finset.mem_univ j) h]
    simp
  -- Per-term decomposition and bound.
  have hxvec : ∀ j, x j = (Real.sqrt W * a j) • (u j - v j)
      + ((Real.sqrt W - Real.sqrt Z) * a j) • v j
      + (Real.sqrt Z * (a j - b j)) • v j := by
    intro j; simp only [x]; module
  have hxj_norm : ∀ j, ‖x j‖ ≤ Real.sqrt W * |a j| * ‖u j - v j‖
      + |Real.sqrt W - Real.sqrt Z| * |a j| * ‖v j‖
      + Real.sqrt Z * |a j - b j| * ‖v j‖ := by
    intro j
    rw [hxvec j]
    calc
      ‖(Real.sqrt W * a j) • (u j - v j) + ((Real.sqrt W - Real.sqrt Z) * a j) • v j
          + (Real.sqrt Z * (a j - b j)) • v j‖
          ≤ ‖(Real.sqrt W * a j) • (u j - v j) + ((Real.sqrt W - Real.sqrt Z) * a j) • v j‖
              + ‖(Real.sqrt Z * (a j - b j)) • v j‖ := norm_add_le _ _
      _ ≤ (‖(Real.sqrt W * a j) • (u j - v j)‖
              + ‖((Real.sqrt W - Real.sqrt Z) * a j) • v j‖)
              + ‖(Real.sqrt Z * (a j - b j)) • v j‖ := by
            gcongr; exact norm_add_le _ _
      _ = Real.sqrt W * |a j| * ‖u j - v j‖
            + |Real.sqrt W - Real.sqrt Z| * |a j| * ‖v j‖
            + Real.sqrt Z * |a j - b j| * ‖v j‖ := by
            rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
              abs_of_nonneg (Real.sqrt_nonneg W), abs_of_nonneg (Real.sqrt_nonneg Z)]
  have hxj_sq : ∀ j, ‖x j‖ ^ 2 ≤ 3 * (W * (a j) ^ 2 * ‖u j - v j‖ ^ 2
      + (Real.sqrt W - Real.sqrt Z) ^ 2 * (a j) ^ 2 * ‖v j‖ ^ 2
      + Z * (a j - b j) ^ 2 * ‖v j‖ ^ 2) := by
    intro j
    have hsq : ‖x j‖ ^ 2 ≤ (Real.sqrt W * |a j| * ‖u j - v j‖
        + |Real.sqrt W - Real.sqrt Z| * |a j| * ‖v j‖
        + Real.sqrt Z * |a j - b j| * ‖v j‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hxj_norm j) 2
    set p : ℝ := Real.sqrt W * |a j| * ‖u j - v j‖ with hpdef
    set q : ℝ := |Real.sqrt W - Real.sqrt Z| * |a j| * ‖v j‖ with hqdef
    set r : ℝ := Real.sqrt Z * |a j - b j| * ‖v j‖ with hrdef
    have hp2 : p ^ 2 = W * (a j) ^ 2 * ‖u j - v j‖ ^ 2 := by
      rw [hpdef, mul_pow, mul_pow, sq_abs, Real.sq_sqrt hWpos.le]
    have hq2 : q ^ 2 = (Real.sqrt W - Real.sqrt Z) ^ 2 * (a j) ^ 2 * ‖v j‖ ^ 2 := by
      rw [hqdef, mul_pow, mul_pow, sq_abs, sq_abs]
    have hr2 : r ^ 2 = Z * (a j - b j) ^ 2 * ‖v j‖ ^ 2 := by
      rw [hrdef, mul_pow, mul_pow, sq_abs, Real.sq_sqrt hZpos.le]
    calc ‖x j‖ ^ 2 ≤ (p + q + r) ^ 2 := hsq
      _ ≤ 3 * (p ^ 2 + q ^ 2 + r ^ 2) := sq_add_add_le_three p q r
      _ = 3 * (W * (a j) ^ 2 * ‖u j - v j‖ ^ 2
            + (Real.sqrt W - Real.sqrt Z) ^ 2 * (a j) ^ 2 * ‖v j‖ ^ 2
            + Z * (a j - b j) ^ 2 * ‖v j‖ ^ 2) := by rw [hp2, hq2, hr2]
  -- Replace `‖u−v‖², ‖v‖², |a−b|²` by the η bounds.
  have hxj_sq' : ∀ j, ‖x j‖ ^ 2 ≤ 3 * (W * η1 * (a j) ^ 2
      + (Real.sqrt W - Real.sqrt Z) ^ 2 * η3 * (a j) ^ 2
      + Z * η0 ^ 2 * η3) := by
    intro j
    refine (hxj_sq j).trans ?_
    have ha2 : 0 ≤ (a j) ^ 2 := sq_nonneg _
    have hc : 0 ≤ (Real.sqrt W - Real.sqrt Z) ^ 2 := sq_nonneg _
    have t1 : W * (a j) ^ 2 * ‖u j - v j‖ ^ 2 ≤ W * η1 * (a j) ^ 2 := by
      calc W * (a j) ^ 2 * ‖u j - v j‖ ^ 2 ≤ W * (a j) ^ 2 * η1 :=
            mul_le_mul_of_nonneg_left (hη1 j) (mul_nonneg hWpos.le ha2)
        _ = W * η1 * (a j) ^ 2 := by ring
    have t2 : (Real.sqrt W - Real.sqrt Z) ^ 2 * (a j) ^ 2 * ‖v j‖ ^ 2
        ≤ (Real.sqrt W - Real.sqrt Z) ^ 2 * η3 * (a j) ^ 2 := by
      calc (Real.sqrt W - Real.sqrt Z) ^ 2 * (a j) ^ 2 * ‖v j‖ ^ 2
            ≤ (Real.sqrt W - Real.sqrt Z) ^ 2 * (a j) ^ 2 * η3 :=
            mul_le_mul_of_nonneg_left (hη3 j) (mul_nonneg hc ha2)
        _ = (Real.sqrt W - Real.sqrt Z) ^ 2 * η3 * (a j) ^ 2 := by ring
    have hab2 : (a j - b j) ^ 2 ≤ η0 ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hη0nn]
      exact hη0 j
    have t3 : Z * (a j - b j) ^ 2 * ‖v j‖ ^ 2 ≤ Z * η0 ^ 2 * η3 := by
      calc Z * (a j - b j) ^ 2 * ‖v j‖ ^ 2 ≤ Z * η0 ^ 2 * ‖v j‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hab2 hZpos.le) (sq_nonneg _)
        _ ≤ Z * η0 ^ 2 * η3 := by
            apply mul_le_mul_of_nonneg_left (hη3 j); positivity
    have hmono : W * (a j) ^ 2 * ‖u j - v j‖ ^ 2
        + (Real.sqrt W - Real.sqrt Z) ^ 2 * (a j) ^ 2 * ‖v j‖ ^ 2
        + Z * (a j - b j) ^ 2 * ‖v j‖ ^ 2
        ≤ W * η1 * (a j) ^ 2 + (Real.sqrt W - Real.sqrt Z) ^ 2 * η3 * (a j) ^ 2
          + Z * η0 ^ 2 * η3 := by linarith [t1, t2, t3]
    exact mul_le_mul_of_nonneg_left hmono (by norm_num)
  -- Sum the per-term bounds.
  have hsum_bound : ∑ j, ‖x j‖ ^ 2 ≤ 3 * (W * η1 * (∑ j, (a j) ^ 2)
      + (Real.sqrt W - Real.sqrt Z) ^ 2 * η3 * (∑ j, (a j) ^ 2)
      + Z * η0 ^ 2 * η3 * κ) := by
    calc ∑ j, ‖x j‖ ^ 2
        ≤ ∑ j, 3 * (W * η1 * (a j) ^ 2
            + (Real.sqrt W - Real.sqrt Z) ^ 2 * η3 * (a j) ^ 2
            + Z * η0 ^ 2 * η3) := Finset.sum_le_sum (fun j _ => hxj_sq' j)
      _ = 3 * (W * η1 * (∑ j, (a j) ^ 2)
            + (Real.sqrt W - Real.sqrt Z) ^ 2 * η3 * (∑ j, (a j) ^ 2)
            + Z * η0 ^ 2 * η3 * κ) := by
          rw [← Finset.mul_sum]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          rw [← Finset.mul_sum, ← Finset.mul_sum]
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← hκdef]
          ring
  -- `Σⱼ aⱼ² ≤ η₄·Z`.
  have hSa2 : ∑ j, (a j) ^ 2 ≤ η4 * Z := by
    have hZle : (1 / η4) * (∑ j, (a j) ^ 2) ≤ Z := by
      rw [hZ, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      have ha2 : 0 ≤ (a j) ^ 2 := sq_nonneg _
      have hprod := mul_le_mul_of_nonneg_left (hη4 j) ha2
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hη4pos]
      nlinarith [hprod, ha2]
    have hmul := mul_le_mul_of_nonneg_right hZle hη4pos.le
    have h2 : (1 / η4) * (∑ j, (a j) ^ 2) * η4 = ∑ j, (a j) ^ 2 := by
      field_simp
    rw [h2] at hmul
    linarith [hmul]
  -- Combine.
  have hsum_eta : ∑ j, ‖x j‖ ^ 2 ≤ 3 * (W * η1 * (η4 * Z)
      + (Real.sqrt W - Real.sqrt Z) ^ 2 * η3 * (η4 * Z)
      + Z * η0 ^ 2 * η3 * κ) := by
    refine hsum_bound.trans ?_
    have hT1 : W * η1 * (∑ j, (a j) ^ 2) ≤ W * η1 * (η4 * Z) := by
      apply mul_le_mul_of_nonneg_left hSa2
      positivity
    have hT2 : (Real.sqrt W - Real.sqrt Z) ^ 2 * η3 * (∑ j, (a j) ^ 2)
        ≤ (Real.sqrt W - Real.sqrt Z) ^ 2 * η3 * (η4 * Z) := by
      apply mul_le_mul_of_nonneg_left hSa2
      positivity
    have hmono : W * η1 * (∑ j, (a j) ^ 2)
        + (Real.sqrt W - Real.sqrt Z) ^ 2 * η3 * (∑ j, (a j) ^ 2)
        + Z * η0 ^ 2 * η3 * κ
        ≤ W * η1 * (η4 * Z) + (Real.sqrt W - Real.sqrt Z) ^ 2 * η3 * (η4 * Z)
          + Z * η0 ^ 2 * η3 * κ := by linarith [hT1, hT2]
    exact mul_le_mul_of_nonneg_left hmono (by norm_num)
  -- Divide by W·Z.
  have hmain : ‖phi - psi‖ ^ 2 ≤ 3 * (W * η1 * (η4 * Z)
      + (Real.sqrt W - Real.sqrt Z) ^ 2 * η3 * (η4 * Z)
      + Z * η0 ^ 2 * η3 * κ) / (W * Z) := by
    rw [hsq_norm, hsum_sq]
    exact div_le_div_of_nonneg_right hsum_eta hWZpos.le
  -- Rewrite the divided right-hand side.
  have hmain_eq : 3 * (W * η1 * (η4 * Z)
      + (Real.sqrt W - Real.sqrt Z) ^ 2 * η3 * (η4 * Z)
      + Z * η0 ^ 2 * η3 * κ) / (W * Z)
      = 3 * η1 * η4 + 3 * (Real.sqrt W - Real.sqrt Z) ^ 2 * η3 * η4 / W
        + 3 * κ * η0 ^ 2 * η3 / W := by
    field_simp
  -- The `(√W−√Z)²` term against `η₂²/(√W+√(W−η₂))²`.
  have hc_bound : (Real.sqrt W - Real.sqrt Z) ^ 2
      ≤ η2 ^ 2 / (Real.sqrt W + Real.sqrt (W - η2)) ^ 2 := by
    have hWZ : Real.sqrt W * Real.sqrt Z = Real.sqrt (W * Z) :=
      (Real.sqrt_mul hWpos.le Z).symm
    have hη2nn : 0 ≤ η2 := le_trans (abs_nonneg _) hη2
    have hdiff : (Real.sqrt W - Real.sqrt Z) * (Real.sqrt W + Real.sqrt Z) = W - Z := by
      have h1 : (Real.sqrt W) ^ 2 = W := Real.sq_sqrt hWpos.le
      have h2 : (Real.sqrt Z) ^ 2 = Z := Real.sq_sqrt hZpos.le
      nlinarith [h1, h2]
    have hWml : W - η2 ≤ Z := by
      have := (abs_le.mp hη2).1; linarith
    have hsqrtle : Real.sqrt (W - η2) ≤ Real.sqrt Z := Real.sqrt_le_sqrt hWml
    have hden2 : 0 < Real.sqrt W + Real.sqrt (W - η2) := by
      have h := Real.sqrt_pos.mpr hWpos
      linarith [Real.sqrt_nonneg (W - η2)]
    have hden_le : Real.sqrt W + Real.sqrt (W - η2) ≤ Real.sqrt W + Real.sqrt Z := by
      linarith
    have hd1nn : 0 ≤ Real.sqrt W + Real.sqrt (W - η2) := hden2.le
    have hd2nn : 0 ≤ Real.sqrt W + Real.sqrt Z := by positivity
    have hsq : (Real.sqrt W - Real.sqrt Z) ^ 2 = (W - Z) ^ 2 / (Real.sqrt W + Real.sqrt Z) ^ 2 := by
      have hdne : (Real.sqrt W + Real.sqrt Z) ≠ 0 := ne_of_gt (by positivity)
      field_simp
      have hsq2 : ((Real.sqrt W - Real.sqrt Z) * (Real.sqrt W + Real.sqrt Z)) ^ 2 = (W - Z) ^ 2 := by
        rw [hdiff]
      nlinarith [hsq2]
    have hD2pos : 0 < (Real.sqrt W + Real.sqrt Z) ^ 2 := by
      have h := Real.sqrt_pos.mpr hWpos
      exact pow_pos (by linarith [Real.sqrt_nonneg Z]) 2
    rw [hsq]
    rw [div_le_div_iff₀ hD2pos (pow_pos hden2 2)]
    have hnum : (W - Z) ^ 2 ≤ η2 ^ 2 := by
      rw [sq_le_sq, abs_sub_comm, abs_of_nonneg hη2nn]
      exact hη2
    have hD : (Real.sqrt W + Real.sqrt (W - η2)) ^ 2 ≤ (Real.sqrt W + Real.sqrt Z) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hd1nn, abs_of_nonneg hd2nn]
      exact hden_le
    have hstep1 : (W - Z) ^ 2 * (Real.sqrt W + Real.sqrt (W - η2)) ^ 2
        ≤ η2 ^ 2 * (Real.sqrt W + Real.sqrt (W - η2)) ^ 2 :=
      mul_le_mul_of_nonneg_right hnum (sq_nonneg _)
    have hstep2 : η2 ^ 2 * (Real.sqrt W + Real.sqrt (W - η2)) ^ 2
        ≤ η2 ^ 2 * (Real.sqrt W + Real.sqrt Z) ^ 2 :=
      mul_le_mul_of_nonneg_left hD (sq_nonneg _)
    linarith [hstep1, hstep2]
  -- Middle-term inequality.
  have hmid : 3 * (Real.sqrt W - Real.sqrt Z) ^ 2 * η3 * η4 / W
      ≤ 3 * η2 ^ 2 * η3 * η4 / (W * (Real.sqrt W + Real.sqrt (W - η2)) ^ 2) := by
    have hη3η4nn : 0 ≤ η3 * η4 := mul_nonneg hη3nn hη4pos.le
    have step1 : (Real.sqrt W - Real.sqrt Z) ^ 2 * (η3 * η4) / W
        ≤ (η2 ^ 2 / (Real.sqrt W + Real.sqrt (W - η2)) ^ 2) * (η3 * η4) / W := by
      have h1 : (Real.sqrt W - Real.sqrt Z) ^ 2 * (η3 * η4)
          ≤ (η2 ^ 2 / (Real.sqrt W + Real.sqrt (W - η2)) ^ 2) * (η3 * η4) :=
        mul_le_mul_of_nonneg_right hc_bound hη3η4nn
      exact div_le_div_of_nonneg_right h1 hWpos.le
    have e1 : 3 * (Real.sqrt W - Real.sqrt Z) ^ 2 * η3 * η4 / W
        = 3 * ((Real.sqrt W - Real.sqrt Z) ^ 2 * (η3 * η4) / W) := by ring_nf
    have hDpos : 0 < Real.sqrt W + Real.sqrt (W - η2) := by
      have h := Real.sqrt_pos.mpr hWpos
      linarith [Real.sqrt_nonneg (W - η2)]
    have hD2ne : (Real.sqrt W + Real.sqrt (W - η2)) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (ne_of_gt hDpos)
    have e2 : 3 * η2 ^ 2 * η3 * η4 / (W * (Real.sqrt W + Real.sqrt (W - η2)) ^ 2)
        = 3 * ((η2 ^ 2 / (Real.sqrt W + Real.sqrt (W - η2)) ^ 2) * (η3 * η4) / W) := by
      field_simp
    rw [e1, e2]
    linarith [step1]
  calc ‖phi - psi‖ ^ 2
      ≤ 3 * (W * η1 * (η4 * Z)
          + (Real.sqrt W - Real.sqrt Z) ^ 2 * η3 * (η4 * Z)
          + Z * η0 ^ 2 * η3 * κ) / (W * Z) := hmain
    _ = 3 * η1 * η4 + 3 * (Real.sqrt W - Real.sqrt Z) ^ 2 * η3 * η4 / W
          + 3 * κ * η0 ^ 2 * η3 / W := hmain_eq
    _ ≤ 3 * η1 * η4
          + 3 * η2 ^ 2 * η3 * η4 / (W * (Real.sqrt W + Real.sqrt (W - η2)) ^ 2)
          + 3 * κ * η0 ^ 2 * η3 / W := by linarith [hmid]

end Qatlib.Papers.CirculantPrec18.ErrorScope
