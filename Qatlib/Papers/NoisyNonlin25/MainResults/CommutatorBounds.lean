/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-! Commutator bounds for
"Quantum simulation of a noisy classical nonlinear dynamics"
(arXiv:2507.06198, 2025), Section 3.

The paper simulates the Kolmogorov equation of a divergence-free
nonlinear SDE by second quantization: the dissipation operator `A`
is diagonal, the drift and cubic terms `B`, `C` are anti-hermitian,
and all energy estimates flow through commutator inequalities for
`[A^p, B + C]` and through a diagonal-dominance criterion.

This block proves the two finite-dimensional cores:

- `commutator_bound_kappa1` (**c006**, Corollary 1): from the
  Lemma-2 square-root bound
  `⟨ψ|[A,B+C]|ψ⟩ ≤ 2Jsλ₁^{-1/2}(1+4√q λ₁^{-1/2}) √(α₁α₂)` with
  `α₁ = ⟨ψ|A|ψ⟩`, `α₂ = ⟨ψ|A²|ψ⟩`, the Young/AM-GM step
  `√(α₁α₂) ≤ (βα₂ + β⁻¹α₁)/2` with the paper's choice of `β`
  yields `⟨ψ|[A,B+C]|ψ⟩ ≤ α₂ + κ₁ α₁` with
  `κ₁ = 2J²s²λ₁^{-1}(1+16qλ₁^{-1})`; the constant sharpening
  `(1+4u)² ≤ 2(1+16u²)` (equivalently `(1−4u)² ≥ 0`) recovers the
  paper's `κ₁` exactly.
- `diagonal_dominance_psd` (**c019**, Proposition 4): hermitian `Y`
  diagonal, hermitian `X` with zero diagonal and
  `Y_mm ≥ ∑_n |X_nm|` for all `m` imply `Y − X` positive
  semidefinite. The proof is the paper's ordered double-sum
  AM-GM argument, reproduced verbatim.

Restricted: the Fock-space embedding (operators on `F₀`, the
`A`-moments as `α₁, α₂`) enters abstractly through real parameters
(c006) resp. through a finite basis-index type (c019); the
Lemma-2 hypothesis of c006 is an explicit input.

No axiom beyond the three standard ones, no `sorry`. -/
set_option autoImplicit false

namespace Qatlib.Papers.NoisyNonlin25.MainResults

/-! ## Young/AM-GM preparatory lemma -/

/-- For nonnegative `a1, a2` and any `β > 0` one has
`√(a1 a2) ≤ (β a2 + β⁻¹ a1)/2` (the inequality quoted before
Corollary 1). -/
theorem sqrt_prod_le_half (a1 a2 β : ℝ) (hβ : 0 < β) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) :
    Real.sqrt (a1 * a2) ≤ (β * a2 + β⁻¹ * a1) / 2 := by
  have hbne : β ≠ 0 := ne_of_gt hβ
  have hR : 0 ≤ (β * a2 + β⁻¹ * a1) / 2 := by positivity
  have hkey : a1 * a2 ≤ ((β * a2 + β⁻¹ * a1) / 2) ^ 2 := by
    have h2 : ((β * a2 + β⁻¹ * a1) / 2) ^ 2 - a1 * a2
        = ((β * a2 - β⁻¹ * a1) / 2) ^ 2 := by
      field_simp
      ring
    linarith [h2, sq_nonneg (β * a2 - β⁻¹ * a1)]
  calc Real.sqrt (a1 * a2) ≤ Real.sqrt (((β * a2 + β⁻¹ * a1) / 2) ^ 2) :=
        Real.sqrt_le_sqrt hkey
    _ = (β * a2 + β⁻¹ * a1) / 2 := Real.sqrt_sq hR

/-! ## c006: Corollary 1 (Commutator bound) -/

/-- **c006 (Corollary 1)**: the square-root commutator bound of
Lemma 2 implies `x ≤ α₂ + κ₁ α₁` with the explicit coefficient
`κ₁ = 2J²s²λ₁⁻¹(1 + 16 q λ₁⁻¹)`, by Young's inequality with the
paper's choice `β Js λ₁^{-1/2}(1 + 4√q λ₁^{-1/2}) = 1` and the
sharpening `(1 + 4u)² ≤ 2(1 + 16u²)`. -/
theorem commutator_bound_kappa1 (J s lam1 q a1 a2 x : ℝ)
    (hJ : 0 < J) (hs : 0 < s) (hlam : 0 < lam1) (hq : 0 < q)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (h : x ≤ 2 * J * s / Real.sqrt lam1 * (1 + 4 * Real.sqrt q / Real.sqrt lam1)
          * Real.sqrt (a1 * a2)) :
    x ≤ a2 + 2 * J ^ 2 * s ^ 2 / lam1 * (1 + 16 * q / lam1) * a1 := by
  have hsl : Real.sqrt lam1 * Real.sqrt lam1 = lam1 := Real.mul_self_sqrt (le_of_lt hlam)
  have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt (le_of_lt hq)
  have hlam_nn : 0 ≤ lam1 := le_of_lt hlam
  have hsl_ne : Real.sqrt lam1 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hlam)
  have hl_ne : lam1 ≠ 0 := ne_of_gt hlam
  -- the Lemma-2 prefactor and the Young step
  set C : ℝ := 2 * J * s / Real.sqrt lam1 * (1 + 4 * Real.sqrt q / Real.sqrt lam1) with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have hβ : 0 < 2 / C := by positivity
  have hy := sqrt_prod_le_half a1 a2 (2 / C) hβ ha1 ha2
  have hinv : (2 / C) ⁻¹ = C / 2 := by field_simp
  rw [hinv] at hy
  have heq : ((2 / C) * a2 + (C / 2) * a1) / 2 = a2 / C + C * a1 / 4 := by
    field_simp
    ring
  rw [heq] at hy
  -- assemble: x ≤ C * sqrt ≤ C * (a2/C + C a1/4) = a2 + C²/4 a1
  have hstep1 : x ≤ C * (a2 / C + C * a1 / 4) :=
    le_trans h (mul_le_mul_of_nonneg_left hy (le_of_lt hCpos))
  have hstep2 : C * (a2 / C + C * a1 / 4) = a2 + C ^ 2 / 4 * a1 := by
    field_simp
  rw [hstep2] at hstep1
  -- the constant sharpening (1 + 4u)^2 ≤ 2 (1 + 16 u^2)
  have hw : 4 * Real.sqrt q / Real.sqrt lam1 * (4 * Real.sqrt q / Real.sqrt lam1)
      = 16 * q / lam1 := by
    have e : (4 * Real.sqrt q) * (4 * Real.sqrt q) = 16 * q := by
      calc (4 * Real.sqrt q) * (4 * Real.sqrt q)
          = 16 * (Real.sqrt q * Real.sqrt q) := by ring
        _ = 16 * q := by rw [hsq]
    rw [div_mul_div_comm, hsl, e]
  have hdisc : (1 - 4 * Real.sqrt q / Real.sqrt lam1) ^ 2 ≥ 0 := sq_nonneg _
  have hu : (1 + 4 * Real.sqrt q / Real.sqrt lam1) ^ 2 ≤ 2 * (1 + 16 * q / lam1) := by
    nlinarith [hdisc, hw]
  have hC2 : C ^ 2 / 4 = J ^ 2 * s ^ 2 / lam1 * (1 + 4 * Real.sqrt q / Real.sqrt lam1) ^ 2 := by
    rw [hCdef, mul_pow, div_pow, Real.sq_sqrt hlam_nn]
    field_simp [hsl_ne, hl_ne]
    ring
  have hlast : C ^ 2 / 4 * a1 ≤ 2 * J ^ 2 * s ^ 2 / lam1 * (1 + 16 * q / lam1) * a1 := by
    rw [hC2]
    refine mul_le_mul_of_nonneg_right ?_ ha1
    calc J ^ 2 * s ^ 2 / lam1 * (1 + 4 * Real.sqrt q / Real.sqrt lam1) ^ 2
        ≤ J ^ 2 * s ^ 2 / lam1 * (2 * (1 + 16 * q / lam1)) :=
          mul_le_mul_of_nonneg_left hu (by positivity)
      _ = 2 * J ^ 2 * s ^ 2 / lam1 * (1 + 16 * q / lam1) := by
          field_simp
  exact le_trans hstep1 (add_le_add (le_refl a2) hlast)

/-! ## c019: Proposition 4 (Diagonal dominance) -/

section DiagonalDominance

variable {I : Type*} [Fintype I]

/-- The quadratic form of a hermitian-form summand: for any `c`,
`(star a * (c * a)).re = ‖a‖² * c.re` (used with `c` a real
diagonal entry, so the form is real-valued). -/
private theorem conj_mul_self_re (a c : ℂ) :
    (star a * (c * a)).re = (‖a‖) ^ 2 * c.re := by
  have hn : ((Complex.normSq a : ℝ) : ℂ) = star a * a := by
    have h0 : ((Complex.normSq a : ℝ) : ℂ) = starRingEnd ℂ a * a :=
      Complex.normSq_eq_conj_mul_self
    rw [starRingEnd_apply] at h0
    exact h0
  rw [show star a * (c * a) = c * (star a * a) from by ring, ← hn,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.normSq_eq_norm_sq]
  ring

/-- **c019 (Proposition 4)**: if `Y` is hermitian and diagonal, `X`
is hermitian with zero diagonal, and every diagonal entry of `Y`
dominates the absolute column sums of `X`, then `Y − X` is positive
semidefinite in the quadratic-form sense. The proof is the paper's
ordered double-sum AM-GM argument. -/
theorem diagonal_dominance_psd (X Y : Matrix I I ℂ)
    (hX : Matrix.conjTranspose X = X) (_hY : Matrix.conjTranspose Y = Y)
    (hYdiag : ∀ i j : I, i ≠ j → Y i j = 0)
    (_hXdiag : ∀ i : I, X i i = 0)
    (hdom : ∀ m : I, ∑ n, ‖X n m‖ ≤ (Y m m).re) :
    ∀ v : I → ℂ, 0 ≤ (∑ m, star (v m) * Matrix.mulVec (Y - X) v m).re := by
  intro v
  -- hermitian symmetry gives the entry identities
  have habs : ∀ i j : I, ‖X j i‖ = ‖X i j‖ := by
    intro i j
    have hh : (Matrix.conjTranspose X) j i = X j i := congrArg (fun M : Matrix I I ℂ => M j i) hX
    rw [Matrix.conjTranspose_apply] at hh
    rw [← hh, norm_star]
  -- the Y part of the quadratic form is diagonal
  have hYv : ∀ m : I, ∑ n, Y m n * v n = Y m m * v m := by
    intro m
    rw [Fintype.sum_eq_single m]
    intro b hb
    have hbne : b ≠ m := by simpa using hb
    rw [hYdiag m b ((ne_comm).mp hbne), zero_mul]
  have hvec : ∀ m : I, Matrix.mulVec (Y - X) v m = Y m m * v m - ∑ n, X m n * v n := by
    intro m
    have h1 : ∀ n : I, (Y - X) m n * v n = Y m n * v n - X m n * v n := by
      intro n; rw [Matrix.sub_apply, sub_mul]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_congr rfl (fun n _ => h1 n),
      Finset.sum_sub_distrib (f := fun n => Y m n * v n) (g := fun n => X m n * v n), hYv m]
  -- split the quadratic form into the Y and X parts
  have hsplit : (∑ m, star (v m) * Matrix.mulVec (Y - X) v m)
      = (∑ m, star (v m) * (Y m m * v m))
        - ∑ m, star (v m) * (∑ n, X m n * v n) := by
    have hterm2 : ∀ m : I, star (v m) * Matrix.mulVec (Y - X) v m
        = star (v m) * (Y m m * v m) - star (v m) * (∑ n, X m n * v n) := by
      intro m; rw [hvec m, mul_sub]
    rw [Finset.sum_congr rfl (fun m _ => hterm2 m),
      Finset.sum_sub_distrib (f := fun m => star (v m) * (Y m m * v m))
        (g := fun m => star (v m) * (∑ n, X m n * v n))]
  rw [hsplit, Complex.sub_re, Complex.re_sum, Complex.re_sum, sub_nonneg]
  -- the X part, bounded by the ordered double-sum AM-GM
  have h3 : ∀ m : I, ‖star (v m) * (∑ n, X m n * v n)‖
      ≤ ∑ n, ‖X m n‖ * (((‖v m‖) ^ 2 + (‖v n‖) ^ 2) / 2) := by
    intro m
    calc ‖star (v m) * (∑ n, X m n * v n)‖
        = ‖v m‖ * ‖∑ n, X m n * v n‖ := by rw [norm_mul, norm_star]
      _ ≤ ‖v m‖ * ∑ n, ‖X m n * v n‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
      _ = ∑ n, ‖v m‖ * (‖X m n‖ * ‖v n‖) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun n _ => by rw [norm_mul])
      _ ≤ ∑ n, ‖X m n‖ * (((‖v m‖) ^ 2 + (‖v n‖) ^ 2) / 2) := by
          refine Finset.sum_le_sum (fun n _ => ?_)
          have h2 : (‖v m‖ - ‖v n‖) ^ 2 ≥ 0 := sq_nonneg _
          have key : 2 * (‖v m‖ * ‖v n‖) ≤ (‖v m‖) ^ 2 + (‖v n‖) ^ 2 := by nlinarith [h2]
          have hnn : 0 ≤ ‖X m n‖ := norm_nonneg _
          field_simp
          nlinarith [key, hnn, h2]
  have hmid : (∑ m, (star (v m) * (∑ n, X m n * v n)).re)
      ≤ ∑ m, ∑ n, ‖X m n‖ * (((‖v m‖) ^ 2 + (‖v n‖) ^ 2) / 2) := by
    calc (∑ m, (star (v m) * (∑ n, X m n * v n)).re)
        ≤ ∑ m, ‖star (v m) * (∑ n, X m n * v n)‖ :=
          Finset.sum_le_sum (fun m _ => Complex.re_le_norm _)
      _ ≤ ∑ m, ∑ n, ‖X m n‖ * (((‖v m‖) ^ 2 + (‖v n‖) ^ 2) / 2) :=
          Finset.sum_le_sum (fun m _ => h3 m)
  -- symmetrize the double sum with the column sums of X
  have hswap : ∀ F : I → I → ℝ, (∑ m, ∑ n, F m n) = ∑ m, ∑ n, F n m :=
    fun F => Finset.sum_comm
  have hA : (∑ m, ∑ n, (‖v m‖) ^ 2 * ‖X n m‖) = ∑ m, (‖v m‖) ^ 2 * ∑ n, ‖X n m‖ := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← Finset.mul_sum]
  have hent : ∀ m n : I, (‖v m‖) ^ 2 * ‖X m n‖ = (‖v m‖) ^ 2 * ‖X n m‖ := by
    intro m n; rw [habs n m]
  have hB : (∑ m, ∑ n, (‖v n‖) ^ 2 * ‖X n m‖) = ∑ m, (‖v m‖) ^ 2 * ∑ n, ‖X n m‖ := by
    rw [hswap (fun m n => (‖v n‖) ^ 2 * ‖X n m‖),
      Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => hent m n))]
    exact hA
  have hA' : (∑ m, ∑ n, (1 / 2 : ℝ) * ((‖v m‖) ^ 2 * ‖X n m‖))
      = (1 / 2 : ℝ) * ∑ m, (‖v m‖) ^ 2 * ∑ n, ‖X n m‖ := by
    have ha1 : ∀ m : I, ∑ n : I, (1 / 2 : ℝ) * ((‖v m‖) ^ 2 * ‖X n m‖)
        = (1 / 2 : ℝ) * ((‖v m‖) ^ 2 * ∑ n, ‖X n m‖) := by
      intro m; rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun m _ => ha1 m), ← Finset.mul_sum]
  have hB' : (∑ m, ∑ n, (1 / 2 : ℝ) * ((‖v n‖) ^ 2 * ‖X n m‖))
      = (1 / 2 : ℝ) * ∑ m, (‖v m‖) ^ 2 * ∑ n, ‖X n m‖ := by
    have hb1 : ∀ m : I, ∑ n : I, (1 / 2 : ℝ) * ((‖v n‖) ^ 2 * ‖X n m‖)
        = (1 / 2 : ℝ) * (∑ n : I, (‖v n‖) ^ 2 * ‖X n m‖) := by
      intro m; rw [← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun m _ => hb1 m), ← Finset.mul_sum,
      hswap (fun m n => (‖v n‖) ^ 2 * ‖X n m‖),
      Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => hent m n)),
      hA]
  have hfin : (∑ m, ∑ n, ‖X m n‖ * (((‖v m‖) ^ 2 + (‖v n‖) ^ 2) / 2))
      = ∑ m, (‖v m‖) ^ 2 * ∑ n, ‖X n m‖ := by
    have e2 : ∀ m n : I, ‖X m n‖ * (((‖v m‖) ^ 2 + (‖v n‖) ^ 2) / 2)
        = (1 / 2 : ℝ) * ((‖v m‖) ^ 2 * ‖X n m‖)
          + (1 / 2 : ℝ) * ((‖v n‖) ^ 2 * ‖X n m‖) := by
      intro m n
      rw [habs m n]
      field_simp
    rw [Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => e2 m n))]
    simp only [Finset.sum_add_distrib]
    rw [hA', hB']
    ring
  have hXbound : (∑ m, (star (v m) * (∑ n, X m n * v n)).re)
      ≤ ∑ m, (‖v m‖) ^ 2 * ∑ n, ‖X n m‖ := by
    exact le_trans hmid (le_of_eq hfin)
  -- final assembly
  calc (∑ m, (star (v m) * (∑ n, X m n * v n)).re)
      ≤ ∑ m, (‖v m‖) ^ 2 * ∑ n, ‖X n m‖ := hXbound
    _ ≤ ∑ m, (‖v m‖) ^ 2 * (Y m m).re :=
        Finset.sum_le_sum (fun m _ =>
          mul_le_mul_of_nonneg_left (hdom m) (sq_nonneg (‖v m‖)))
    _ = (∑ m, (star (v m) * (Y m m * v m)).re) :=
        (Finset.sum_congr rfl (fun m _ => conj_mul_self_re (v m) (Y m m))).symm

end DiagonalDominance

end Qatlib.Papers.NoisyNonlin25.MainResults
