/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.WitnessCompile.StateConversionDefs
import Qatlib.Concepts.ConversionCore.WitnessCompile.AdaptiveInstrumentPurificationQuan

/-!
# Near-optimal rational filtered witnesses

This module converts rational factorizations into complex filtered Gram certificates and
constructs rational witnesses with budgets close to a finite filtered γ₂ value. It controls
witness dimension and packages the existential runtime ledger in `clause90`.

The certificate framework is that of quantum state conversion [LeeEtAl2011].

## Main statements

* `exists_rational_factorization`: constructs valid rational witnesses with near-optimal budget
  and bounded dimension.
* `clause90`: bundles the witness specification with dimension and runtime bounds.

## References

* [Lee et al., 2011][LeeEtAl2011]
* [Reichardt, 2011][Reichardt2011]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ConversionCore.WitnessCompile Matrix
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib
open Qatlib
open Qatlib.Concepts.GramQueryCore.ModelSemantics
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

set_option autoImplicit false

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality

namespace Qatlib.Concepts.ConversionCore.WitnessCompile.WitnessCompiler
variable {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}

/-- The absolute value of the real part of a complex number is bounded by its norm. -/
private theorem abs_re_le_norm' (z : ℂ) : |z.re| ≤ ‖z‖ := by
  have h2 : z.re * z.re ≤ Complex.normSq z := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.im]
  have h5 : Complex.normSq z = ‖z‖ ^ 2 := by rw [Complex.normSq_eq_norm_sq]
  have h3 : |z.re| ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [← h5, pow_two, abs_mul_abs_self]
    exact h2
  exact (abs_le_of_sq_le_sq' h3 (norm_nonneg z)).2

/-- The absolute value of the imaginary part of a complex number is bounded by its norm. -/
private theorem abs_im_le_norm' (z : ℂ) : |z.im| ≤ ‖z‖ := by
  have h2 : z.im * z.im ≤ Complex.normSq z := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.re]
  have h5 : Complex.normSq z = ‖z‖ ^ 2 := by rw [Complex.normSq_eq_norm_sq]
  have h3 : |z.im| ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [← h5, pow_two, abs_mul_abs_self]
    exact h2
  exact (abs_le_of_sq_le_sq' h3 (norm_nonneg z)).2

/-- The real part of `star z * w` is the sum of the products of corresponding real and imaginary
parts. -/
private theorem star_mul_re (z w : ℂ) : (star z * w).re = z.re * w.re + z.im * w.im := by
  have h1 : (star z).re = z.re := by simp
  have h2 : (star z).im = -z.im := by simp
  rw [Complex.mul_re, h1, h2]
  ring

/-- Complex conjugation fixes a rational number embedded into the complex numbers. -/
private theorem star_ratCast (t : ℚ) : star ((t : ℂ)) = (t : ℂ) := by
  rw [RCLike.star_def, Complex.ext_iff]
  simp

/-- The Boolean-indexed realification of a complex number, selecting its real part at false and
imaginary part at true. -/
private def gammaRealPart (z : ℂ) : Bool → ℝ
  | false => z.re
  | true => z.im

/-- The real inner product of realified complex vectors equals the real part of their complex
inner product. -/
private theorem gammaReal_inner {Q : Type} [Fintype Q] (u v : Q → ℂ) :
    (∑ q, ∑ b, gammaRealPart (u q) b * gammaRealPart (v q) b) = (star u ⬝ᵥ v).re := by
  simp only [dotProduct, Pi.star_apply]
  have hrw : (∑ q, star (u q) * v q).re = ∑ q, (star (u q) * v q).re := by simp
  rw [hrw]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Fintype.sum_bool, star_mul_re]
  simp only [gammaRealPart]
  ring

/-- The squared coordinate mass of a realified complex vector equals the sum of its complex
squared norms. -/
private theorem gammaReal_mass {Q : Type} [Fintype Q] (u : Q → ℂ) :
    ∑ q, ∑ b, gammaRealPart (u q) b ^ 2 = ∑ q, Complex.normSq (u q) := by
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Fintype.sum_bool]
  simp only [gammaRealPart, Complex.normSq_apply]
  ring

/-- A norm bound on a complex number also bounds the absolute value of each realified
coordinate. -/
private theorem gammaRealPart_abs {B : ℝ} {z : ℂ} (hz : ‖z‖ ≤ B) :
    ∀ b, |gammaRealPart z b| ≤ B := by
  intro b
  cases b
  · exact le_trans (abs_re_le_norm' z) hz
  · exact le_trans (abs_im_le_norm' z) hz

/-- The complex squared norm of a rational cast equals the real cast of the rational square. -/
private theorem ratCast_normSq (t : ℚ) : Complex.normSq ((t : ℂ)) = ((t * t : ℚ) : ℝ) := by
  simp [Complex.normSq_apply]

/-- Rational witness mass bounds and an exact filtered factorization yield a complex filtered
Gram certificate with the same budget. -/
private theorem gramFilteredCert_of_rationalValid (inst : RationalGamma2Instance X n)
    {Q : Type} [Fintype Q] (u : Fin n → X → Q → ℚ) (v : Fin n → X → Q → ℚ) (B : ℚ)
    (h1 : ∀ x : X, ∑ j, ∑ q, ((u j x q * u j x q : ℚ) : ℝ) ≤ (B : ℝ))
    (h2 : ∀ y : X, ∑ j, ∑ q, ((v j y q * v j y q : ℚ) : ℝ) ≤ (B : ℝ))
    (h3 : ∀ x y : X, ((inst.A x y : ℚ) : ℂ) =
      ∑ j, ((inst.Z j x y : ℚ) : ℂ) * ∑ q, ((u j x q * v j y q : ℚ) : ℂ)) :
    gramFilteredCert (rationalGamma2ComplexA inst) (rationalGamma2ComplexZ inst) (B : ℝ) := by
  refine ⟨Q, inferInstance, fun j x q => ((u j x q : ℚ) : ℂ),
    fun j y q => ((v j y q : ℚ) : ℂ), ?_, ?_, ?_⟩
  · intro x
    calc ∑ j, ∑ q, Complex.normSq (((u j x q : ℚ) : ℂ))
        = ∑ j, ∑ q, ((u j x q * u j x q : ℚ) : ℝ) := by simp only [ratCast_normSq]
      _ ≤ (B : ℝ) := h1 x
  · intro y
    calc ∑ j, ∑ q, Complex.normSq (((v j y q : ℚ) : ℂ))
        = ∑ j, ∑ q, ((v j y q * v j y q : ℚ) : ℝ) := by simp only [ratCast_normSq]
      _ ≤ (B : ℝ) := h2 y
  · intro x y
    simp only [rationalGamma2ComplexA, rationalGamma2ComplexZ]
    have hdot : ∀ j : Fin n, (star (fun q : Q => ((u j x q : ℚ) : ℂ)) ⬝ᵥ
        fun q : Q => ((v j y q : ℚ) : ℂ)) =
        ∑ q, ((u j x q * v j y q : ℚ) : ℂ) := by
      intro j
      have hpt : ∀ q : Q, star ((u j x q : ℚ) : ℂ) * ((v j y q : ℚ) : ℂ)
          = ((u j x q * v j y q : ℚ) : ℂ) := by
        intro q
        rw [star_ratCast, ← Rat.cast_mul]
      calc (star (fun q : Q => ((u j x q : ℚ) : ℂ)) ⬝ᵥ fun q : Q => ((v j y q : ℚ) : ℂ))
          = ∑ q, star ((u j x q : ℚ) : ℂ) * ((v j y q : ℚ) : ℂ) := by
            simp only [dotProduct, Pi.star_apply]
        _ = ∑ q, ((u j x q * v j y q : ℚ) : ℂ) := Finset.sum_congr rfl fun q _ => hpt q
    simp only [hdot]
    exact h3 x y

/-- For nonnegative `t` and positive `δ`, there is a positive rational whose square lies between
`t` and `2 * t + 2 * δ`. -/
private theorem exists_rat_sq_near {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ) :
    ∃ a : ℚ, 0 < a ∧ t ≤ (a : ℝ) ^ 2 ∧ (a : ℝ) ^ 2 ≤ 2 * t + 2 * δ := by
  have hδ2 : 0 < 2 * t + δ := by positivity
  set s := Real.sqrt (2 * t + δ) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos_of_pos hδ2
  have hs2 : s ^ 2 = 2 * t + δ := Real.sq_sqrt hδ2.le
  set d := min (s / 2) (δ / (8 * (s + 1))) with hddef
  have hd0 : 0 < d := lt_min (by positivity) (by positivity)
  obtain ⟨a, ha⟩ := exists_rat_near s hd0
  have had : |(a : ℝ) - s| < d := by rw [abs_sub_comm]; exact ha
  obtain ⟨hage1, hage2⟩ := abs_lt.mp had
  have hlow : s - d < (a : ℝ) := by linarith
  have hhigh : (a : ℝ) < s + d := by linarith
  have hds : d ≤ s / 2 := min_le_left _ _
  have hdd : d ≤ δ / (8 * (s + 1)) := min_le_right _ _
  have hsd : 0 < s - d := by linarith
  have hap : 0 < (a : ℝ) := by
    have h1 : s / 2 ≤ s - d := by linarith
    have h2 : s / 2 < (a : ℝ) := by linarith
    linarith
  refine ⟨a, by exact_mod_cast hap, ?_, ?_⟩
  · have h1 : (s - d) ^ 2 ≤ (a : ℝ) ^ 2 := by nlinarith [sq_nonneg ((a : ℝ) - (s - d))]
    have h4 : 2 * s * d ≤ δ / 4 := by
      have h4a : 2 * s * d ≤ 2 * s * (δ / (8 * (s + 1))) :=
        mul_le_mul_of_nonneg_left hdd (by positivity)
      have h4b : 2 * s * (δ / (8 * (s + 1))) = (s * δ) / (4 * (s + 1)) := by
        field_simp
        ring
      have h4c : (s * δ) / (4 * (s + 1)) ≤ δ / 4 := by
        field_simp
        nlinarith [hδ.le]
      exact h4a.trans (h4b ▸ h4c)
    nlinarith [sq_nonneg d]
  · have h1 : (a : ℝ) ^ 2 ≤ (s + d) ^ 2 := by nlinarith [sq_nonneg ((s + d) - (a : ℝ))]
    have h4 : 2 * s * d ≤ δ / 4 := by
      have h4a : 2 * s * d ≤ 2 * s * (δ / (8 * (s + 1))) :=
        mul_le_mul_of_nonneg_left hdd (by positivity)
      have h4b : 2 * s * (δ / (8 * (s + 1))) = (s * δ) / (4 * (s + 1)) := by
        field_simp
        ring
      have h4c : (s * δ) / (4 * (s + 1)) ≤ δ / 4 := by
        field_simp
        nlinarith [hδ.le]
      exact h4a.trans (h4b ▸ h4c)
    have hd2 : d ^ 2 ≤ δ / 16 := by
      have hd2a : d ^ 2 ≤ (s / 2) * (δ / (8 * (s + 1))) := by nlinarith [mul_nonneg hs0.le hd0.le]
      have hd2b : (s / 2) * (δ / (8 * (s + 1))) = (s * δ) / (16 * (s + 1)) := by
        field_simp
        ring
      have hd2c : (s * δ) / (16 * (s + 1)) ≤ δ / 16 := by
        field_simp
        nlinarith [hδ.le]
      exact hd2a.trans (hd2b ▸ hd2c)
    have hexp : (s + d) ^ 2 = s ^ 2 + 2 * s * d + d ^ 2 := by ring
    nlinarith
variable {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
set_option maxHeartbeats 8000000 in

/-- A finite filtered γ₂ value and `0 < ε ≤ 1` give a valid rational factorization with
near-optimal budget, two value comparisons, and polynomially bounded witness dimension. -/
private theorem exists_rational_factorization (inst : RationalGamma2Instance X n)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hval : filteredGamma2 (rationalGamma2ComplexA inst) (rationalGamma2ComplexZ inst) < ⊤) :
    ∃ F : RationalGamma2Factorization X inst,
      RationalFactorizationValid inst F ∧
        (F.budget : ℝ) ≤
          (filteredGamma2 (rationalGamma2ComplexA inst)
            (rationalGamma2ComplexZ inst)).toReal + ε ∧
        filteredGamma2 (rationalGamma2ComplexA inst) (rationalGamma2ComplexZ inst) ≤
          ENNReal.ofReal ((F.budget : ℝ) + ε) ∧
        @Fintype.card F.Q F.fintypeQ ≤
          (rationalGamma2Bits inst + Fintype.card X + n + Nat.ceil (1 / ε) + 8) ^ 7 := by
  classical

  have hvreal : ENNReal.ofReal
      (filteredGamma2 (rationalGamma2ComplexA inst) (rationalGamma2ComplexZ inst)).toReal =
      filteredGamma2 (rationalGamma2ComplexA inst) (rationalGamma2ComplexZ inst) :=
    ENNReal.ofReal_toReal hval.ne
  have hv0 : 0 ≤
      (filteredGamma2 (rationalGamma2ComplexA inst) (rationalGamma2ComplexZ inst)).toReal :=
    ENNReal.toReal_nonneg
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ,
      W = (filteredGamma2 (rationalGamma2ComplexA inst)
        (rationalGamma2ComplexZ inst)).toReal + ε / 8 := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hWdef]; positivity
  have hcert : gramFilteredCert (rationalGamma2ComplexA inst)
      (rationalGamma2ComplexZ inst) W := by
    refine (filteredGamma2_fixed_budget_boundary X n (rationalGamma2ComplexA inst)
      (rationalGamma2ComplexZ inst) W hW0).mp ?_
    rw [← hvreal]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hWdef]
    linarith
  obtain ⟨w, hwmass, hweq⟩ := gramFilteredCert_fixed_width hcert

  obtain ⟨RW, hRWdef⟩ : ∃ RW : ℝ, RW = Real.sqrt (W + 1) := ⟨_, rfl⟩
  have hRW0 : 0 ≤ RW := by rw [hRWdef]; positivity
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (Fintype.card X : ℝ) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  obtain ⟨ZS, hZSdef⟩ : ∃ ZS : ℝ, ZS =
      (∑ j, ∑ x, ∑ y, |((inst.Z j x y : ℚ) : ℝ)|) + 1 := ⟨_, rfl⟩
  have hZS1 : 1 ≤ ZS := by
    rw [hZSdef]
    have hnn : (0:ℝ) ≤ ∑ j, ∑ x, ∑ y, |((inst.Z j x y : ℚ) : ℝ)| := by positivity
    linarith
  have hZS0 : 0 ≤ ZS := le_trans zero_le_one hZS1
  obtain ⟨RZ, hRZdef⟩ : ∃ RZ : ℝ, RZ =
      (∑ x, ∑ y, ∑ j, if ((inst.Z j x y : ℚ) : ℝ) = 0 then 0
        else |((inst.Z j x y : ℚ) : ℝ)|⁻¹) + 1 := ⟨_, rfl⟩
  have hRZ1 : 1 ≤ RZ := by
    rw [hRZdef]
    have hnn : (0:ℝ) ≤ ∑ x, ∑ y, ∑ j, if ((inst.Z j x y : ℚ) : ℝ) = 0 then 0
        else |((inst.Z j x y : ℚ) : ℝ)|⁻¹ := by
      refine Finset.sum_nonneg fun x _ => ?_
      refine Finset.sum_nonneg fun y _ => ?_
      refine Finset.sum_nonneg fun j _ => ?_
      by_cases hz : ((inst.Z j x y : ℚ) : ℝ) = 0
      · simp [hz]
      · rw [if_neg hz]
        exact inv_nonneg.2 (abs_nonneg _)
    linarith
  have hRZ0 : 0 ≤ RZ := le_trans zero_le_one hRZ1
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = ZS * (4 * c) * (2 * RW + 1) *
      (2 * RZ * c * c + 4 * c * c + 2 * c + 2) + ((n : ℝ) + 1) * (4 * c) * (2 * RW + 1)
      + 2 * c * c + 1 := ⟨_, rfl⟩
  have h4c0 : (0:ℝ) ≤ 4 * c := by linarith
  have h210 : (0:ℝ) ≤ 2 * RW + 1 := by linarith
  have hx4c : (0:ℝ) ≤ 4 * c * (2 * RW + 1) := mul_nonneg h4c0 h210
  have hKbase : (0:ℝ) ≤ ZS * (4 * c) * (2 * RW + 1) :=
    mul_nonneg (mul_nonneg hZS0 h4c0) h210
  have hcc : (0:ℝ) ≤ c * c := by nlinarith [hc0]
  have hfacc : (0:ℝ) ≤ 2 * RZ * c * c + 4 * c * c + 2 * c + 2 := by
    nlinarith [hRZ0, hc0, hcc, mul_nonneg hRZ0 hcc]
  have hterm1 : (0:ℝ) ≤ ZS * (4 * c) * (2 * RW + 1) *
      (2 * RZ * c * c + 4 * c * c + 2 * c + 2) :=
    mul_nonneg hKbase hfacc
  have hterm2 : (0:ℝ) ≤ ((n : ℝ) + 1) * (4 * c) * (2 * RW + 1) :=
    mul_nonneg (mul_nonneg (by linarith) h4c0) h210
  have hterm3 : (0:ℝ) ≤ 2 * c * c := by nlinarith [hc0]
  have hK1 : (1 : ℝ) ≤ K := by
    rw [hKdef]
    linarith
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / (8 * K) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hηdef]; positivity
  have hη1 : η ≤ 1 := by
    have h8K : (1:ℝ) ≤ 8 * K := by linarith
    have hdiv : ε / (8 * K) ≤ ε := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 8 * K)]
      nlinarith [hε.le]
    rw [hηdef]
    exact hdiv.trans hε1

  have hKZS : ZS * (4 * c) * (2 * RW + 1) ≤ K := by
    have hfac : (1:ℝ) ≤ 2 * RZ * c * c + 4 * c * c + 2 * c + 2 := by
      nlinarith [hRZ0, hc0, hcc, mul_nonneg hRZ0 hcc]
    have h1 : ZS * (4 * c) * (2 * RW + 1) ≤
        ZS * (4 * c) * (2 * RW + 1) * (2 * RZ * c * c + 4 * c * c + 2 * c + 2) := by
      calc ZS * (4 * c) * (2 * RW + 1) =
          ZS * (4 * c) * (2 * RW + 1) * 1 := by ring
        _ ≤ ZS * (4 * c) * (2 * RW + 1) * (2 * RZ * c * c + 4 * c * c + 2 * c + 2) :=
            mul_le_mul_of_nonneg_left hfac hKbase
    rw [hKdef]
    linarith
  have hKNQ : ((n : ℝ) + 1) * (4 * c) * (2 * RW + 1) ≤ K := by
    rw [hKdef]
    linarith
  have hKrow : 2 * RZ * c * c * (ZS * (4 * c) * (2 * RW + 1)) +
      4 * c * c * (ZS * (4 * c) * (2 * RW + 1)) + 2 * c * c ≤ K := by
    rw [hKdef]
    have hsplit : ZS * (4 * c) * (2 * RW + 1) * (2 * RZ * c * c + 4 * c * c + 2 * c + 2)
        = 2 * RZ * c * c * (ZS * (4 * c) * (2 * RW + 1))
          + 4 * c * c * (ZS * (4 * c) * (2 * RW + 1))
          + (2 * c + 2) * (ZS * (4 * c) * (2 * RW + 1)) := by ring
    have hlast : (0:ℝ) ≤ (2 * c + 2) * (ZS * (4 * c) * (2 * RW + 1)) :=
      mul_nonneg (by linarith) hKbase
    rw [hsplit]
    linarith

  obtain ⟨ure, huredef⟩ : ∃ ure : Fin n → X → (X ⊕ X) → Bool → ℝ,
      ure = fun j x q b => gammaRealPart (w j (Sum.inl x) q) b := ⟨_, rfl⟩
  obtain ⟨vre, hvredef⟩ : ∃ vre : Fin n → X → (X ⊕ X) → Bool → ℝ,
      vre = fun j y q b => gammaRealPart (w j (Sum.inr y) q) b := ⟨_, rfl⟩
  have hentry : ∀ (j : Fin n) (z : X ⊕ X) (q : X ⊕ X), ‖w j z q‖ ≤ RW := by
    intro j z q
    have h1 : Complex.normSq (w j z q) ≤ ∑ q' : X ⊕ X, Complex.normSq (w j z q') :=
      Finset.single_le_sum (fun q' _ => Complex.normSq_nonneg _) (Finset.mem_univ q)
    have h2 : ∑ q' : X ⊕ X, Complex.normSq (w j z q') ≤
        ∑ j' : Fin n, ∑ q' : X ⊕ X, Complex.normSq (w j' z q') :=
      Finset.single_le_sum
        (f := fun j' : Fin n => ∑ q' : X ⊕ X, Complex.normSq (w j' z q'))
        (fun j' _ => Finset.sum_nonneg fun q' _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
    have h3 := (h1.trans h2).trans (hwmass z)
    have h4 : ‖w j z q‖ ≤ Real.sqrt W := by
      rw [Complex.normSq_eq_norm_sq] at h3
      exact (Real.le_sqrt (norm_nonneg _) (by linarith : (0:ℝ) ≤ W)).mpr h3
    exact h4.trans (by rw [hRWdef]; exact Real.sqrt_le_sqrt (by linarith))
  have hureB : ∀ (j : Fin n) (x : X) (q : X ⊕ X) (b : Bool), |ure j x q b| ≤ RW := by
    intro j x q b
    rw [huredef]
    exact gammaRealPart_abs (hentry j (Sum.inl x) q) b
  have hvreB : ∀ (j : Fin n) (y : X) (q : X ⊕ X) (b : Bool), |vre j y q b| ≤ RW := by
    intro j y q b
    rw [hvredef]
    exact gammaRealPart_abs (hentry j (Sum.inr y) q) b

  have hgram : ∀ x y : X, ((inst.A x y : ℚ) : ℝ) =
      ∑ j, ((inst.Z j x y : ℚ) : ℝ) * (∑ q, ∑ b, ure j x q b * vre j y q b) := by
    intro x y
    have h := hweq x y
    have hAr : (rationalGamma2ComplexA inst x y).re = ((inst.A x y : ℚ) : ℝ) := by
      simp [rationalGamma2ComplexA]
    have hZre : ∀ j : Fin n, (rationalGamma2ComplexZ inst j x y).re
        = ((inst.Z j x y : ℚ) : ℝ) := by
      intro j; simp [rationalGamma2ComplexZ]
    have hZim : ∀ j : Fin n, (rationalGamma2ComplexZ inst j x y).im = 0 := by
      intro j; simp [rationalGamma2ComplexZ]
    calc ((inst.A x y : ℚ) : ℝ) = (rationalGamma2ComplexA inst x y).re := hAr
      _ = (∑ j, rationalGamma2ComplexZ inst j x y *
            (star (w j (Sum.inl x)) ⬝ᵥ w j (Sum.inr y))).re := by rw [← h]
      _ = ∑ j, ((inst.Z j x y : ℚ) : ℝ) * (∑ q, ∑ b, ure j x q b * vre j y q b) := by
          have hre : (∑ j, rationalGamma2ComplexZ inst j x y *
              (star (w j (Sum.inl x)) ⬝ᵥ w j (Sum.inr y))).re =
              ∑ j, (rationalGamma2ComplexZ inst j x y *
              (star (w j (Sum.inl x)) ⬝ᵥ w j (Sum.inr y))).re := by simp
          rw [hre]
          refine Finset.sum_congr rfl fun j _ => ?_
          have hdotre : (star (w j (Sum.inl x)) ⬝ᵥ w j (Sum.inr y)).re =
              ∑ q, ∑ b, ure j x q b * vre j y q b := by
            rw [← gammaReal_inner, huredef, hvredef]
          rw [Complex.mul_re, hZre j, hZim j, hdotre, zero_mul, sub_zero]

  obtain ⟨uq, hdu⟩ : ∃ uq : Fin n → X → (X ⊕ X) → Bool → ℚ,
      ∀ j x q b, |(uq j x q b : ℝ) - ure j x q b| < η := by
    choose uq hdu using fun (j : Fin n) (x : X) (q : X ⊕ X) (b : Bool) =>
      exists_rat_near (ure j x q b) hη0
    exact ⟨uq, fun j x q b => by rw [abs_sub_comm]; exact hdu j x q b⟩
  obtain ⟨vq, hdv⟩ : ∃ vq : Fin n → X → (X ⊕ X) → Bool → ℚ,
      ∀ j y q b, |(vq j y q b : ℝ) - vre j y q b| < η := by
    choose vq hdv using fun (j : Fin n) (y : X) (q : X ⊕ X) (b : Bool) =>
      exists_rat_near (vre j y q b) hη0
    exact ⟨vq, fun j y q b => by rw [abs_sub_comm]; exact hdv j y q b⟩
  have huqB : ∀ (j : Fin n) (x : X) (q : X ⊕ X) (b : Bool), |(uq j x q b : ℝ)| ≤ RW + 1 := by
    intro j x q b
    calc |(uq j x q b : ℝ)| ≤ |(uq j x q b : ℝ) - ure j x q b| + |ure j x q b| := by
          exact (congrArg abs (by ring)).trans_le (abs_add_le _ _)
      _ ≤ η + RW := add_le_add (hdu j x q b).le (hureB j x q b)
      _ ≤ RW + 1 := by linarith
  have hvqB : ∀ (j : Fin n) (y : X) (q : X ⊕ X) (b : Bool), |(vq j y q b : ℝ)| ≤ RW + 1 := by
    intro j y q b
    calc |(vq j y q b : ℝ)| ≤ |(vq j y q b : ℝ) - vre j y q b| + |vre j y q b| := by
          exact (congrArg abs (by ring)).trans_le (abs_add_le _ _)
      _ ≤ η + RW := add_le_add (hdv j y q b).le (hvreB j y q b)
      _ ≤ RW + 1 := by linarith

  obtain ⟨E, hEdef⟩ : ∃ E : X → X → ℚ,
      E = fun x y => inst.A x y -
        ∑ j, inst.Z j x y * (∑ q, ∑ b, uq j x q b * vq j y q b) := ⟨_, rfl⟩
  have hcount : ∀ d : ℝ, ∑ q : X ⊕ X, ∑ b : Bool, d = 4 * c * d := by
    intro d
    rw [hcdef]
    simp [Finset.sum_const]
    ring
  have hcount2 : ∀ d : ℝ, ∑ p : X × X, d = c * c * d := by
    intro d
    rw [hcdef]
    simp [Finset.sum_const]
  have hinner : ∀ (j : Fin n) (x y : X),
      |∑ q, ∑ b, ure j x q b * vre j y q b - ∑ q, ∑ b, ((uq j x q b * vq j y q b : ℚ) : ℝ)|
        ≤ 4 * c * (2 * RW + 1) * η := by
    intro j x y
    have hpt : ∀ (q : X ⊕ X) (b : Bool),
        |ure j x q b * vre j y q b - ((uq j x q b * vq j y q b : ℚ) : ℝ)|
          ≤ (2 * RW + 1) * η := by
      intro q b
      have hd1 := hdu j x q b
      have hd2 := hdv j y q b
      calc |ure j x q b * vre j y q b - ((uq j x q b * vq j y q b : ℚ) : ℝ)|
          = |ure j x q b * (vre j y q b - (vq j y q b : ℝ)) +
              (ure j x q b - (uq j x q b : ℝ)) * (vq j y q b : ℝ)| := by
            congr 1
            rw [Rat.cast_mul]
            ring
        _ ≤ |ure j x q b * (vre j y q b - (vq j y q b : ℝ))| +
              |(ure j x q b - (uq j x q b : ℝ)) * (vq j y q b : ℝ)| := abs_add_le _ _
        _ ≤ |ure j x q b| * |vre j y q b - (vq j y q b : ℝ)| +
              |ure j x q b - (uq j x q b : ℝ)| * |(vq j y q b : ℝ)| :=
              add_le_add (abs_mul _ _).le (abs_mul _ _).le
        _ ≤ RW * η + η * (RW + 1) := by
            have e1 : |ure j x q b| * |vre j y q b - (vq j y q b : ℝ)| ≤ RW * η :=
              calc |ure j x q b| * |vre j y q b - (vq j y q b : ℝ)|
                  ≤ RW * |vre j y q b - (vq j y q b : ℝ)| :=
                    mul_le_mul_of_nonneg_right (hureB j x q b) (abs_nonneg _)
                _ ≤ RW * η := by
                  refine mul_le_mul_of_nonneg_left ?_ hRW0
                  rw [abs_sub_comm]
                  exact hd2.le
            have hd1' : |ure j x q b - (uq j x q b : ℝ)| ≤ η := by
              rw [abs_sub_comm]
              exact hd1.le
            have e2 : |ure j x q b - (uq j x q b : ℝ)| * |(vq j y q b : ℝ)| ≤ η * (RW + 1) :=
              calc |ure j x q b - (uq j x q b : ℝ)| * |(vq j y q b : ℝ)|
                  ≤ η * |(vq j y q b : ℝ)| :=
                    mul_le_mul_of_nonneg_right hd1' (abs_nonneg _)
                _ ≤ η * (RW + 1) := mul_le_mul_of_nonneg_left (hvqB j y q b) hη0.le
            linarith
        _ = (2 * RW + 1) * η := by ring
    calc |∑ q, ∑ b, ure j x q b * vre j y q b - ∑ q, ∑ b, ((uq j x q b * vq j y q b : ℚ) : ℝ)|
        = |∑ q, ((∑ b, ure j x q b * vre j y q b) -
            ∑ b, ((uq j x q b * vq j y q b : ℚ) : ℝ))| := by
          rw [← Finset.sum_sub_distrib]
      _ ≤ ∑ q, |(∑ b, ure j x q b * vre j y q b) -
            ∑ b, ((uq j x q b * vq j y q b : ℚ) : ℝ)| :=
              Finset.abs_sum_le_sum_abs _ Finset.univ
      _ ≤ ∑ q, ∑ b, (2 * RW + 1) * η :=
            Finset.sum_le_sum fun q _ => by
              rw [← Finset.sum_sub_distrib]
              exact le_trans (Finset.abs_sum_le_sum_abs _ Finset.univ)
                (Finset.sum_le_sum fun b _ => hpt q b)
      _ = 4 * c * (2 * RW + 1) * η := by rw [hcount]; ring
  have hEcast : ∀ x y : X, ((E x y : ℚ) : ℝ) =
      ∑ j, ((inst.Z j x y : ℚ) : ℝ) *
        ((∑ q, ∑ b, ure j x q b * vre j y q b) -
          ∑ q, ∑ b, ((uq j x q b * vq j y q b : ℚ) : ℝ)) := by
    intro x y
    have hsumcast : ((∑ j, inst.Z j x y * (∑ q, ∑ b, uq j x q b * vq j y q b) : ℚ) : ℝ)
        = ∑ j, ((inst.Z j x y : ℚ) : ℝ) *
          ∑ q, ∑ b, ((uq j x q b * vq j y q b : ℚ) : ℝ) := by
      simp [Rat.cast_sum, Rat.cast_mul]
    rw [hEdef, Rat.cast_sub, hsumcast, hgram x y, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hZSsum : ∀ x y : X,
      (∑ j, |((inst.Z j x y : ℚ) : ℝ)|) ≤ ZS := by
    intro x y
    rw [hZSdef]
    have hle : (∑ j, |((inst.Z j x y : ℚ) : ℝ)|) ≤
        ∑ j, ∑ x', ∑ y', |((inst.Z j x' y' : ℚ) : ℝ)| := by
      refine Finset.sum_le_sum fun j _ => ?_
      calc |((inst.Z j x y : ℚ) : ℝ)| ≤ ∑ y', |((inst.Z j x y' : ℚ) : ℝ)| :=
              Finset.single_le_sum
                (f := fun y' => |((inst.Z j x y' : ℚ) : ℝ)|)
                (fun y' _ => abs_nonneg _) (Finset.mem_univ y)
        _ ≤ ∑ x', ∑ y', |((inst.Z j x' y' : ℚ) : ℝ)| :=
              Finset.single_le_sum
                (f := fun x' => ∑ y', |((inst.Z j x' y' : ℚ) : ℝ)|)
                (fun x' _ => Finset.sum_nonneg fun y' _ => abs_nonneg _) (Finset.mem_univ x)
    linarith
  have hEbound : ∀ x y : X, |((E x y : ℚ) : ℝ)| ≤ ZS * (4 * c) * (2 * RW + 1) * η := by
    intro x y
    rw [hEcast x y]
    have hnn : (0:ℝ) ≤ 4 * c * (2 * RW + 1) * η :=
      mul_nonneg (mul_nonneg h4c0 h210) hη0.le
    calc |∑ j, ((inst.Z j x y : ℚ) : ℝ) * ((∑ q, ∑ b, ure j x q b * vre j y q b) -
          ∑ q, ∑ b, ((uq j x q b * vq j y q b : ℚ) : ℝ))|
        ≤ ∑ j, |((inst.Z j x y : ℚ) : ℝ)| * (4 * c * (2 * RW + 1) * η) := by
          refine (Finset.abs_sum_le_sum_abs _ Finset.univ).trans
            (Finset.sum_le_sum fun j _ => ?_)
          exact (abs_mul _ _).le.trans (mul_le_mul_of_nonneg_left (hinner j x y) (abs_nonneg _))
      _ = (∑ j, |((inst.Z j x y : ℚ) : ℝ)|) * (4 * c * (2 * RW + 1) * η) :=
            (Finset.sum_mul Finset.univ (fun j => |((inst.Z j x y : ℚ) : ℝ)|) _).symm
      _ ≤ ZS * (4 * c) * (2 * RW + 1) * η := by
            have hkey : (∑ j, |((inst.Z j x y : ℚ) : ℝ)|) * (4 * c * (2 * RW + 1) * η)
                ≤ ZS * (4 * c * (2 * RW + 1) * η) :=
              mul_le_mul_of_nonneg_right (hZSsum x y) hnn
            nlinarith [hkey]

  have hj₀ex : ∀ x y : X, ((E x y : ℚ) : ℝ) ≠ 0 →
      ∃ j : Fin n, ((inst.Z j x y : ℚ) : ℝ) ≠ 0 := by
    intro x y hE
    by_contra hnot
    simp only [not_exists, not_not] at hnot
    apply hE
    rw [hEcast x y]
    simp [hnot]

  have hcard : Fintype.card (((X ⊕ X) × Bool) ⊕ (X × X))
      ≤ (rationalGamma2Bits inst + Fintype.card X + n + Nat.ceil (1 / ε) + 8) ^ 7 := by
    have hc1 : Fintype.card (((X ⊕ X) × Bool) ⊕ (X × X))
        = 4 * Fintype.card X + (Fintype.card X) ^ 2 := by
      simp [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool]
      ring
    rw [hc1]
    have hb : Fintype.card X + 8
        ≤ rationalGamma2Bits inst + Fintype.card X + n + Nat.ceil (1 / ε) + 8 := by omega
    have h1 : 4 * Fintype.card X + (Fintype.card X) ^ 2 ≤ (Fintype.card X + 8) ^ 2 := by
      have hsq : (Fintype.card X + 8) ^ 2
          = Fintype.card X * Fintype.card X + (16 * Fintype.card X + 64) := by ring
      rw [hsq, Nat.pow_two, Nat.add_comm (4 * Fintype.card X)]
      exact Nat.add_le_add_left (by omega) _
    have h2 : (Fintype.card X + 8) ^ 2
        ≤ (rationalGamma2Bits inst + Fintype.card X + n + Nat.ceil (1 / ε) + 8) ^ 2 :=
      Nat.pow_le_pow_left hb 2
    have h3 : (rationalGamma2Bits inst + Fintype.card X + n + Nat.ceil (1 / ε) + 8) ^ 2
        ≤ (rationalGamma2Bits inst + Fintype.card X + n + Nat.ceil (1 / ε) + 8) ^ 7 := by
      have hN5 : (1 : ℕ) ≤ (rationalGamma2Bits inst + Fintype.card X + n
          + Nat.ceil (1 / ε) + 8) ^ 5 :=
        Nat.one_le_pow 5 _ (by omega : (0 : ℕ)
          < rationalGamma2Bits inst + Fintype.card X + n + Nat.ceil (1 / ε) + 8)
      calc (rationalGamma2Bits inst + Fintype.card X + n + Nat.ceil (1 / ε) + 8) ^ 2
          = (rationalGamma2Bits inst + Fintype.card X + n + Nat.ceil (1 / ε) + 8) ^ 2 * 1 :=
            (Nat.mul_one _).symm
        _ ≤ (rationalGamma2Bits inst + Fintype.card X + n + Nat.ceil (1 / ε) + 8) ^ 2
            * (rationalGamma2Bits inst + Fintype.card X + n + Nat.ceil (1 / ε) + 8) ^ 5 :=
            Nat.mul_le_mul_left _ hN5
        _ = (rationalGamma2Bits inst + Fintype.card X + n + Nat.ceil (1 / ε) + 8) ^ 7 := by
            rw [← Nat.pow_add]
    exact h1.trans (h2.trans h3)
  by_cases hnemp : Nonempty (Fin n)
  case neg =>
    haveI : IsEmpty (Fin n) := not_nonempty_iff.mp hnemp
    have hisum : ∀ x y : X, ((inst.A x y : ℚ) : ℂ) = 0 := by
      intro x y
      have h := hgram x y
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at h
      have hA0 : inst.A x y = 0 := by exact_mod_cast h
      rw [hA0]
      simp
    obtain ⟨B, hB1, hB2⟩ := exists_rat_btwn
      (show (filteredGamma2 (rationalGamma2ComplexA inst) (rationalGamma2ComplexZ inst)).toReal
        + ε / 2 < (filteredGamma2 (rationalGamma2ComplexA inst)
        (rationalGamma2ComplexZ inst)).toReal + ε by linarith)
    have hzeroQ : (0 : ℚ) ≤ B := by
      have hpos : (0 : ℝ) < ((B : ℚ) : ℝ) := by linarith
      exact_mod_cast hpos.le
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · exact { Q := ((X ⊕ X) × Bool) ⊕ (X × X), u := (fun _ _ _ => 0), v := (fun _ _ _ => 0), budget := B }
    · intro x
      simp
      exact hzeroQ
    · intro y
      simp
      exact hzeroQ
    · intro x y
      rw [hisum x y]
      simp
    · exact le_of_lt hB2
    · refine le_trans (filteredGamma2_le_of_gramFilteredCert
        (gramFilteredCert_of_rationalValid inst
          (fun _ _ (_ : ((X ⊕ X) × Bool) ⊕ (X × X)) => 0)
          (fun _ _ (_ : ((X ⊕ X) × Bool) ⊕ (X × X)) => 0) B
          (fun x => by simp; exact hzeroQ) (fun y => by simp; exact hzeroQ)
          (fun x y => by rw [hisum x y]; simp))) ?_
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · exact hcard
  case pos =>
    letI := hnemp
    choose! j₀ hj₀ using hj₀ex
    have hEdefpw : ∀ x y : X, E x y = inst.A x y
        - ∑ j : Fin n, inst.Z j x y * (∑ q : X ⊕ X, ∑ b : Bool, uq j x q b * vq j y q b) :=
      fun x y => by rw [hEdef]
    obtain ⟨t, htdef⟩ : ∃ t : X → X → ℝ,
        t = fun x y => |((E x y : ℚ) : ℝ)| / |((inst.Z (j₀ x y) x y : ℚ) : ℝ)| := ⟨_, rfl⟩
    have ht0 : ∀ x y : X, 0 ≤ t x y := by
      intro x y
      simp only [htdef]
      exact div_nonneg (abs_nonneg _) (abs_nonneg _)
    have hRZle : ∀ (j : Fin n) (x y : X), ((inst.Z j x y : ℚ) : ℝ) ≠ 0 →
        |((inst.Z j x y : ℚ) : ℝ)|⁻¹ ≤ RZ := by
      intro j x y hne
      rw [hRZdef]
      have hif0 : ∀ (j' : Fin n) (x' y' : X),
          0 ≤ (if ((inst.Z j' x' y' : ℚ) : ℝ) = 0 then 0 else |((inst.Z j' x' y' : ℚ) : ℝ)|⁻¹) := by
        intro j' x' y'
        by_cases hz : ((inst.Z j' x' y' : ℚ) : ℝ) = 0
        · simp [hz]
        · simp [hz]
      calc |((inst.Z j x y : ℚ) : ℝ)|⁻¹
          = if ((inst.Z j x y : ℚ) : ℝ) = 0 then 0 else |((inst.Z j x y : ℚ) : ℝ)|⁻¹ := (if_neg hne).symm
        _ ≤ ∑ j' : Fin n, (if ((inst.Z j' x y : ℚ) : ℝ) = 0 then 0 else |((inst.Z j' x y : ℚ) : ℝ)|⁻¹) :=
            Finset.single_le_sum (f := fun j' => if ((inst.Z j' x y : ℚ) : ℝ) = 0 then 0
              else |((inst.Z j' x y : ℚ) : ℝ)|⁻¹) (fun j' _ => hif0 j' x y) (Finset.mem_univ j)
        _ ≤ ∑ y' : X, ∑ j' : Fin n, (if ((inst.Z j' x y' : ℚ) : ℝ) = 0 then 0
            else |((inst.Z j' x y' : ℚ) : ℝ)|⁻¹) :=
            Finset.single_le_sum (f := fun y' => ∑ j' : Fin n, if ((inst.Z j' x y' : ℚ) : ℝ) = 0
              then 0 else |((inst.Z j' x y' : ℚ) : ℝ)|⁻¹)
              (fun y' _ => Finset.sum_nonneg fun j' _ => hif0 j' x y') (Finset.mem_univ y)
        _ ≤ ∑ x' : X, ∑ y' : X, ∑ j' : Fin n, (if ((inst.Z j' x' y' : ℚ) : ℝ) = 0 then 0
            else |((inst.Z j' x' y' : ℚ) : ℝ)|⁻¹) :=
            Finset.single_le_sum (f := fun x' => ∑ y' : X, ∑ j' : Fin n,
                if ((inst.Z j' x' y' : ℚ) : ℝ) = 0 then 0 else |((inst.Z j' x' y' : ℚ) : ℝ)|⁻¹)
              (fun x' _ => Finset.sum_nonneg fun y' _ => Finset.sum_nonneg fun j' _ => hif0 j' x' y')
              (Finset.mem_univ x)
        _ ≤ (∑ x' : X, ∑ y' : X, ∑ j' : Fin n, (if ((inst.Z j' x' y' : ℚ) : ℝ) = 0 then 0
            else |((inst.Z j' x' y' : ℚ) : ℝ)|⁻¹)) + 1 := le_add_of_nonneg_right (by norm_num)
    have hexa : ∀ x y : X, ∃ a : ℚ, 0 < a ∧
        (((E x y : ℚ) : ℝ) ≠ 0 → t x y ≤ ((a : ℝ)) * ((a : ℝ)) ∧
          ((a : ℝ)) * ((a : ℝ)) ≤ 2 * t x y + 2 * η) := by
      intro x y
      by_cases hf : ((E x y : ℚ) : ℝ) = 0
      · exact ⟨1, by norm_num, fun h => (h hf).elim⟩
      · obtain ⟨a, ha0, ha1, ha2⟩ := exists_rat_sq_near (t := t x y) (δ := η) (ht0 x y) hη0
        exact ⟨a, ha0, fun _ => ⟨by rw [← pow_two]; exact ha1, by rw [← pow_two]; exact ha2⟩⟩
    choose a hax using hexa
    obtain ⟨uPatch, huPdef⟩ : ∃ f : Fin n → X → X × X → ℚ,
        f = fun j x p => if (((E p.1 p.2 : ℚ) : ℝ) ≠ 0 ∧ j = j₀ p.1 p.2 ∧ x = p.1)
          then a p.1 p.2 else 0 := ⟨_, rfl⟩
    obtain ⟨vPatch, hvPdef⟩ : ∃ f : Fin n → X → X × X → ℚ,
        f = fun j y p => if (((E p.1 p.2 : ℚ) : ℝ) ≠ 0 ∧ j = j₀ p.1 p.2 ∧ y = p.2)
          then E p.1 p.2 / (inst.Z (j₀ p.1 p.2) p.1 p.2 * a p.1 p.2) else 0 := ⟨_, rfl⟩
    have huPunf : ∀ (j : Fin n) (x : X) (p : X × X), uPatch j x p
        = if (((E p.1 p.2 : ℚ) : ℝ) ≠ 0 ∧ j = j₀ p.1 p.2 ∧ x = p.1)
          then a p.1 p.2 else 0 := fun j x p => by rw [huPdef]
    have hvPunf : ∀ (j : Fin n) (y : X) (p : X × X), vPatch j y p
        = if (((E p.1 p.2 : ℚ) : ℝ) ≠ 0 ∧ j = j₀ p.1 p.2 ∧ y = p.2)
          then E p.1 p.2 / (inst.Z (j₀ p.1 p.2) p.1 p.2 * a p.1 p.2) else 0 :=
      fun j y p => by rw [hvPdef]
    have hZQne : ∀ x y : X, ((E x y : ℚ) : ℝ) ≠ 0 → inst.Z (j₀ x y) x y ≠ 0 := by
      intro x y hf
      have h := hj₀ x y hf
      intro h0
      apply h
      rw [h0]
      simp
    have hpatchdot : ∀ (j : Fin n) (x y : X), (∑ p : X × X, uPatch j x p * vPatch j y p)
        = if (((E x y : ℚ) : ℝ) ≠ 0 ∧ j = j₀ x y) then E x y / inst.Z (j₀ x y) x y else 0 := by
      intro j x y
      rw [Finset.sum_eq_single (x, y)]
      · show uPatch j x (x, y) * vPatch j y (x, y) = _
        rw [huPunf j x (x, y), hvPunf j y (x, y)]
        (try dsimp only)
        by_cases hf : (((E x y : ℚ) : ℝ) ≠ 0 ∧ j = j₀ x y)
        · rw [if_pos ⟨hf.1, hf.2, rfl⟩, if_pos ⟨hf.1, hf.2, rfl⟩, if_pos hf]
          field_simp [hZQne x y hf.1, (hax x y).1.ne']
        · rw [if_neg (fun hc => hf ⟨hc.1, hc.2.1⟩), if_neg (fun hc => hf ⟨hc.1, hc.2.1⟩),
            if_neg hf, mul_zero]
      · intro p _ hp
        show uPatch j x p * vPatch j y p = 0
        by_cases h1 : (((E p.1 p.2 : ℚ) : ℝ) ≠ 0 ∧ j = j₀ p.1 p.2 ∧ x = p.1)
        · by_cases h2 : (((E p.1 p.2 : ℚ) : ℝ) ≠ 0 ∧ j = j₀ p.1 p.2 ∧ y = p.2)
          · exact absurd (Prod.ext h1.2.2.symm h2.2.2.symm) hp
          · rw [huPunf j x p, hvPunf j y p, if_pos h1, if_neg h2, mul_zero]
        · rw [huPunf j x p, hvPunf j y p, if_neg h1, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ (x, y)) h
    obtain ⟨U, huUdef⟩ : ∃ f : Fin n → X → (((X ⊕ X) × Bool) ⊕ (X × X)) → ℚ,
        f = fun j x => Sum.elim (fun qb => uq j x qb.1 qb.2) (uPatch j x) := ⟨_, rfl⟩
    obtain ⟨V, hvVdef⟩ : ∃ f : Fin n → X → (((X ⊕ X) × Bool) ⊕ (X × X)) → ℚ,
        f = fun j y => Sum.elim (fun qb => vq j y qb.1 qb.2) (vPatch j y) := ⟨_, rfl⟩
    have hdotsplit : ∀ (j : Fin n) (x y : X),
        (∑ q : ((X ⊕ X) × Bool) ⊕ (X × X), U j x q * V j y q)
        = (∑ q : X ⊕ X, ∑ b : Bool, uq j x q b * vq j y q b)
          + (if (((E x y : ℚ) : ℝ) ≠ 0 ∧ j = j₀ x y)
              then E x y / inst.Z (j₀ x y) x y else 0) := by
      intro j x y
      rw [huUdef, hvVdef, Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      have hfirst : (∑ qb : (X ⊕ X) × Bool, uq j x qb.1 qb.2 * vq j y qb.1 qb.2)
          = ∑ q : X ⊕ X, ∑ b : Bool, uq j x q b * vq j y q b := by
        rw [Fintype.sum_prod_type]
      rw [hfirst, hpatchdot j x y]
    have hsumQ : ∀ x y : X,
        (∑ j : Fin n, inst.Z j x y * ∑ q : ((X ⊕ X) × Bool) ⊕ (X × X), U j x q * V j y q)
        = inst.A x y := by
      intro x y
      have hrew : (∑ j : Fin n, inst.Z j x y * ∑ q : ((X ⊕ X) × Bool) ⊕ (X × X), U j x q * V j y q)
          = ∑ j : Fin n, (inst.Z j x y * (∑ q : X ⊕ X, ∑ b : Bool, uq j x q b * vq j y q b)
            + inst.Z j x y * (if (((E x y : ℚ) : ℝ) ≠ 0 ∧ j = j₀ x y)
                then E x y / inst.Z (j₀ x y) x y else 0)) :=
        Finset.sum_congr rfl fun j _ => by rw [hdotsplit j x y]; ring
      rw [hrew, Finset.sum_add_distrib]
      have hpatchsum : (∑ j : Fin n, inst.Z j x y * (if (((E x y : ℚ) : ℝ) ≠ 0 ∧ j = j₀ x y)
            then E x y / inst.Z (j₀ x y) x y else 0)) = E x y := by
        by_cases hf : ((E x y : ℚ) : ℝ) ≠ 0
        · rw [Finset.sum_eq_single (j₀ x y)]
          · rw [if_pos ⟨hf, rfl⟩]
            rw [mul_comm]
            exact div_mul_cancel₀ _ (hZQne x y hf)
          · intro j _ hjne
            rw [if_neg (fun hc => hjne hc.2)]
            ring
          · intro h
            exact absurd (Finset.mem_univ (j₀ x y)) h
        · have hE0 : E x y = 0 := by exact_mod_cast (not_not.mp hf)
          rw [hE0]
          simp
      rw [hpatchsum]
      linarith [hEdefpw x y]
    have hentryF : ∀ x y : X, ((inst.A x y : ℚ) : ℂ)
        = ∑ j : Fin n, ((inst.Z j x y : ℚ) : ℂ)
          * ∑ q : ((X ⊕ X) × Bool) ⊕ (X × X), ((U j x q * V j y q : ℚ) : ℂ) := by
      intro x y
      have hcast : ∀ j : Fin n,
          ((inst.Z j x y * ∑ q : ((X ⊕ X) × Bool) ⊕ (X × X), U j x q * V j y q : ℚ) : ℂ)
          = ((inst.Z j x y : ℚ) : ℂ)
            * ∑ q : ((X ⊕ X) × Bool) ⊕ (X × X), ((U j x q * V j y q : ℚ) : ℂ) := by
        intro j
        rw [Rat.cast_mul, Rat.cast_sum]
      calc ((inst.A x y : ℚ) : ℂ)
          = ((∑ j : Fin n, inst.Z j x y
              * ∑ q : ((X ⊕ X) × Bool) ⊕ (X × X), U j x q * V j y q : ℚ) : ℂ) := by
            rw [hsumQ x y]
        _ = (∑ j : Fin n, ((inst.Z j x y * ∑ q : ((X ⊕ X) × Bool) ⊕ (X × X),
            U j x q * V j y q : ℚ) : ℂ)) := by rw [Rat.cast_sum]
        _ = ∑ j : Fin n, ((inst.Z j x y : ℚ) : ℂ)
            * ∑ q : ((X ⊕ X) × Bool) ⊕ (X × X), ((U j x q * V j y q : ℚ) : ℂ) :=
            Finset.sum_congr rfl fun j _ => hcast j
    have hptsqU : ∀ (j : Fin n) (x : X) (q : X ⊕ X) (b : Bool),
        ((uq j x q b * uq j x q b : ℚ) : ℝ) ≤ (ure j x q b) ^ 2 + η * (2 * RW + 1) := by
      intro j x q b
      have hdub : |((uq j x q b : ℚ) : ℝ) - ure j x q b| ≤ η := (hdu j x q b).le
      have hsumb : |((uq j x q b : ℚ) : ℝ) + ure j x q b| ≤ 2 * RW + 1 := by
        calc |((uq j x q b : ℚ) : ℝ) + ure j x q b|
            ≤ |((uq j x q b : ℚ) : ℝ)| + |ure j x q b| := abs_add_le _ _
          _ ≤ (RW + 1) + RW := add_le_add (huqB j x q b) (hureB j x q b)
          _ = 2 * RW + 1 := by ring
      have hexp : ((uq j x q b : ℚ) : ℝ) * ((uq j x q b : ℚ) : ℝ) - (ure j x q b) ^ 2
          = (((uq j x q b : ℚ) : ℝ) - ure j x q b) * (((uq j x q b : ℚ) : ℝ) + ure j x q b) := by
        ring
      have habs : |((uq j x q b : ℚ) : ℝ) * ((uq j x q b : ℚ) : ℝ) - (ure j x q b) ^ 2|
          ≤ η * (2 * RW + 1) := by
        rw [hexp, abs_mul]
        exact mul_le_mul hdub hsumb (abs_nonneg _) hη0.le
      have hcastm : ((uq j x q b * uq j x q b : ℚ) : ℝ)
          = ((uq j x q b : ℚ) : ℝ) * ((uq j x q b : ℚ) : ℝ) := Rat.cast_mul _ _
      rw [hcastm]
      linarith [(abs_le.mp habs).2]
    have hptsqV : ∀ (j : Fin n) (y : X) (q : X ⊕ X) (b : Bool),
        ((vq j y q b * vq j y q b : ℚ) : ℝ) ≤ (vre j y q b) ^ 2 + η * (2 * RW + 1) := by
      intro j y q b
      have hdub : |((vq j y q b : ℚ) : ℝ) - vre j y q b| ≤ η := (hdv j y q b).le
      have hsumb : |((vq j y q b : ℚ) : ℝ) + vre j y q b| ≤ 2 * RW + 1 := by
        calc |((vq j y q b : ℚ) : ℝ) + vre j y q b|
            ≤ |((vq j y q b : ℚ) : ℝ)| + |vre j y q b| := abs_add_le _ _
          _ ≤ (RW + 1) + RW := add_le_add (hvqB j y q b) (hvreB j y q b)
          _ = 2 * RW + 1 := by ring
      have hexp : ((vq j y q b : ℚ) : ℝ) * ((vq j y q b : ℚ) : ℝ) - (vre j y q b) ^ 2
          = (((vq j y q b : ℚ) : ℝ) - vre j y q b) * (((vq j y q b : ℚ) : ℝ) + vre j y q b) := by
        ring
      have habs : |((vq j y q b : ℚ) : ℝ) * ((vq j y q b : ℚ) : ℝ) - (vre j y q b) ^ 2|
          ≤ η * (2 * RW + 1) := by
        rw [hexp, abs_mul]
        exact mul_le_mul hdub hsumb (abs_nonneg _) hη0.le
      have hcastm : ((vq j y q b * vq j y q b : ℚ) : ℝ)
          = ((vq j y q b : ℚ) : ℝ) * ((vq j y q b : ℚ) : ℝ) := Rat.cast_mul _ _
      rw [hcastm]
      linarith [(abs_le.mp habs).2]
    have hmassconvU : ∀ (j : Fin n) (x : X),
        (∑ qb : (X ⊕ X) × Bool, (ure j x qb.1 qb.2) ^ 2)
        = ∑ q : X ⊕ X, Complex.normSq (w j (Sum.inl x) q) := by
      intro j x
      rw [Fintype.sum_prod_type, huredef]
      exact gammaReal_mass _
    have hmassconvV : ∀ (j : Fin n) (y : X),
        (∑ qb : (X ⊕ X) × Bool, (vre j y qb.1 qb.2) ^ 2)
        = ∑ q : X ⊕ X, Complex.normSq (w j (Sum.inr y) q) := by
      intro j y
      rw [Fintype.sum_prod_type, hvredef]
      exact gammaReal_mass _
    have hcount3 : ∀ d : ℝ, ∑ qb : (X ⊕ X) × Bool, d = 4 * c * d := by
      intro d
      rw [Fintype.sum_prod_type]
      exact hcount d
    have humain : ∀ x : X, (∑ j : Fin n, ∑ qb : (X ⊕ X) × Bool,
          ((uq j x qb.1 qb.2 * uq j x qb.1 qb.2 : ℚ) : ℝ))
        ≤ W + (n : ℝ) * (4 * c * (2 * RW + 1)) * η := by
      intro x
      calc (∑ j : Fin n, ∑ qb : (X ⊕ X) × Bool, ((uq j x qb.1 qb.2 * uq j x qb.1 qb.2 : ℚ) : ℝ))
          ≤ ∑ j : Fin n, ∑ qb : (X ⊕ X) × Bool, ((ure j x qb.1 qb.2) ^ 2 + η * (2 * RW + 1)) :=
            Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun qb _ => hptsqU j x qb.1 qb.2
        _ = ∑ j : Fin n, ((∑ qb : (X ⊕ X) × Bool, (ure j x qb.1 qb.2) ^ 2)
            + 4 * c * (η * (2 * RW + 1))) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_add_distrib, hcount3]
        _ = ((∑ j : Fin n, ∑ qb : (X ⊕ X) × Bool, (ure j x qb.1 qb.2) ^ 2))
            + (n : ℝ) * (4 * c * (η * (2 * RW + 1))) := by
            rw [Finset.sum_add_distrib]
            have hEqc : (∑ j : Fin n, (4 * c * (η * (2 * RW + 1))))
                = (n : ℝ) * (4 * c * (η * (2 * RW + 1))) := by
              simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            rw [hEqc]
        _ ≤ W + (n : ℝ) * (4 * c * (2 * RW + 1)) * η := by
            have h1 : ∑ j : Fin n, ∑ qb : (X ⊕ X) × Bool, (ure j x qb.1 qb.2) ^ 2 ≤ W := by
              calc (∑ j : Fin n, ∑ qb : (X ⊕ X) × Bool, (ure j x qb.1 qb.2) ^ 2)
                  = ∑ j : Fin n, ∑ q : X ⊕ X, Complex.normSq (w j (Sum.inl x) q) :=
                    Finset.sum_congr rfl fun j _ => hmassconvU j x
                _ ≤ W := hwmass (Sum.inl x)
            have h2 : (n : ℝ) * (4 * c * (η * (2 * RW + 1)))
                = (n : ℝ) * (4 * c * (2 * RW + 1)) * η := by ring
            rw [h2]
            exact add_le_add h1 le_rfl
    have hvmain : ∀ y : X, (∑ j : Fin n, ∑ qb : (X ⊕ X) × Bool,
          ((vq j y qb.1 qb.2 * vq j y qb.1 qb.2 : ℚ) : ℝ))
        ≤ W + (n : ℝ) * (4 * c * (2 * RW + 1)) * η := by
      intro y
      calc (∑ j : Fin n, ∑ qb : (X ⊕ X) × Bool, ((vq j y qb.1 qb.2 * vq j y qb.1 qb.2 : ℚ) : ℝ))
          ≤ ∑ j : Fin n, ∑ qb : (X ⊕ X) × Bool, ((vre j y qb.1 qb.2) ^ 2 + η * (2 * RW + 1)) :=
            Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun qb _ => hptsqV j y qb.1 qb.2
        _ = ∑ j : Fin n, ((∑ qb : (X ⊕ X) × Bool, (vre j y qb.1 qb.2) ^ 2)
            + 4 * c * (η * (2 * RW + 1))) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_add_distrib, hcount3]
        _ = ((∑ j : Fin n, ∑ qb : (X ⊕ X) × Bool, (vre j y qb.1 qb.2) ^ 2))
            + (n : ℝ) * (4 * c * (η * (2 * RW + 1))) := by
            rw [Finset.sum_add_distrib]
            have hEqc : (∑ j : Fin n, (4 * c * (η * (2 * RW + 1))))
                = (n : ℝ) * (4 * c * (η * (2 * RW + 1))) := by
              simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            rw [hEqc]
        _ ≤ W + (n : ℝ) * (4 * c * (2 * RW + 1)) * η := by
            have h1 : ∑ j : Fin n, ∑ qb : (X ⊕ X) × Bool, (vre j y qb.1 qb.2) ^ 2 ≤ W := by
              calc (∑ j : Fin n, ∑ qb : (X ⊕ X) × Bool, (vre j y qb.1 qb.2) ^ 2)
                  = ∑ j : Fin n, ∑ q : X ⊕ X, Complex.normSq (w j (Sum.inr y) q) :=
                    Finset.sum_congr rfl fun j _ => hmassconvV j y
                _ ≤ W := hwmass (Sum.inr y)
            have h2 : (n : ℝ) * (4 * c * (η * (2 * RW + 1)))
                = (n : ℝ) * (4 * c * (2 * RW + 1)) * η := by ring
            rw [h2]
            exact add_le_add h1 le_rfl
    have hupj : ∀ (x : X) (p : X × X), (∑ j : Fin n, ((uPatch j x p * uPatch j x p : ℚ) : ℝ))
        ≤ 2 * t p.1 p.2 + 2 * η := by
      intro x p
      by_cases hf : ((E p.1 p.2 : ℚ) : ℝ) ≠ 0
      · obtain ⟨_, haR⟩ := (hax p.1 p.2).2 hf
        rw [Finset.sum_eq_single (j₀ p.1 p.2)]
        · by_cases hxp : x = p.1
          · show ((uPatch (j₀ p.1 p.2) x p * uPatch (j₀ p.1 p.2) x p : ℚ) : ℝ) ≤ _
            rw [huPunf, if_pos ⟨hf, rfl, hxp⟩, Rat.cast_mul]
            exact haR
          · show ((uPatch (j₀ p.1 p.2) x p * uPatch (j₀ p.1 p.2) x p : ℚ) : ℝ) ≤ _
            rw [huPunf, if_neg (fun hc => hxp hc.2.2), mul_zero, Rat.cast_zero]
            linarith [ht0 p.1 p.2, hη0.le]
        · intro j _ hjne
          show ((uPatch j x p * uPatch j x p : ℚ) : ℝ) = 0
          rw [huPunf, if_neg (fun hc => hjne hc.2.1), mul_zero, Rat.cast_zero]
        · intro h
          exact absurd (Finset.mem_univ (j₀ p.1 p.2)) h
      · have hz : ∀ j : Fin n, ((uPatch j x p * uPatch j x p : ℚ) : ℝ) = 0 := by
          intro j
          rw [huPunf, if_neg (fun hc => hf hc.1), mul_zero, Rat.cast_zero]
        rw [Finset.sum_eq_zero (fun j _ => hz j)]
        linarith [ht0 p.1 p.2, hη0.le]
    have hvv : ∀ (x y : X), (((E x y / (inst.Z (j₀ x y) x y * a x y) : ℚ) : ℝ)
        * ((E x y / (inst.Z (j₀ x y) x y * a x y) : ℚ) : ℝ)) ≤ t x y := by
      intro x y
      by_cases hf : ((E x y : ℚ) : ℝ) ≠ 0
      · have hZne : ((inst.Z (j₀ x y) x y : ℚ) : ℝ) ≠ 0 := hj₀ x y hf
        have hane : ((a x y : ℚ) : ℝ) ≠ 0 := by exact_mod_cast (hax x y).1.ne'
        obtain ⟨haL, _⟩ := (hax x y).2 hf
        have ht2 : t x y * t x y
            = ((E x y : ℚ) : ℝ) * ((E x y : ℚ) : ℝ)
              / (((inst.Z (j₀ x y) x y : ℚ) : ℝ) * ((inst.Z (j₀ x y) x y : ℚ) : ℝ)) := by
          simp only [htdef]
          rw [← abs_mul_abs_self ((E x y : ℚ) : ℝ),
            ← abs_mul_abs_self ((inst.Z (j₀ x y) x y : ℚ) : ℝ)]
          field_simp
        have hpos2 : 0 < ((a x y : ℚ) : ℝ) * ((a x y : ℚ) : ℝ) := mul_self_pos.mpr hane
        calc ((E x y / (inst.Z (j₀ x y) x y * a x y) : ℚ) : ℝ)
            * ((E x y / (inst.Z (j₀ x y) x y * a x y) : ℚ) : ℝ)
            = (((E x y : ℚ) : ℝ) * ((E x y : ℚ) : ℝ))
              / ((((inst.Z (j₀ x y) x y : ℚ) : ℝ) * ((a x y : ℚ) : ℝ))
                * (((inst.Z (j₀ x y) x y : ℚ) : ℝ) * ((a x y : ℚ) : ℝ))) := by
              rw [Rat.cast_div, Rat.cast_mul]
              ring
          _ = ((t x y * t x y) / (((a x y : ℚ) : ℝ) * ((a x y : ℚ) : ℝ))) := by
              rw [ht2]
              field_simp [hZne, hane]
          _ ≤ t x y := by
              rw [div_le_iff₀ hpos2]
              exact mul_le_mul_of_nonneg_left haL (ht0 x y)
      · have hEq0 : E x y = 0 := by exact_mod_cast (not_not.mp hf)
        rw [hEq0]
        simp only [zero_div, Rat.cast_zero, zero_mul]
        exact ht0 x y
    have hvpj : ∀ (y : X) (p : X × X), (∑ j : Fin n, ((vPatch j y p * vPatch j y p : ℚ) : ℝ))
        ≤ t p.1 p.2 := by
      intro y p
      by_cases hf : ((E p.1 p.2 : ℚ) : ℝ) ≠ 0
      · rw [Finset.sum_eq_single (j₀ p.1 p.2)]
        · by_cases hyp : y = p.2
          · show ((vPatch (j₀ p.1 p.2) y p * vPatch (j₀ p.1 p.2) y p : ℚ) : ℝ) ≤ _
            rw [hvPunf, if_pos ⟨hf, rfl, hyp⟩, Rat.cast_mul]
            exact hvv p.1 p.2
          · show ((vPatch (j₀ p.1 p.2) y p * vPatch (j₀ p.1 p.2) y p : ℚ) : ℝ) ≤ _
            rw [hvPunf, if_neg (fun hc => hyp hc.2.2), mul_zero, Rat.cast_zero]
            exact ht0 p.1 p.2
        · intro j _ hjne
          show ((vPatch j y p * vPatch j y p : ℚ) : ℝ) = 0
          rw [hvPunf, if_neg (fun hc => hjne hc.2.1), mul_zero, Rat.cast_zero]
        · intro h
          exact absurd (Finset.mem_univ (j₀ p.1 p.2)) h
      · have hz : ∀ j : Fin n, ((vPatch j y p * vPatch j y p : ℚ) : ℝ) = 0 := by
          intro j
          rw [hvPunf, if_neg (fun hc => hf hc.1), mul_zero, Rat.cast_zero]
        rw [Finset.sum_eq_zero (fun j _ => hz j)]
        exact ht0 p.1 p.2
    have hsumt : (∑ p : X × X, t p.1 p.2)
        ≤ RZ * (c * c * (ZS * (4 * c) * (2 * RW + 1) * η)) := by
      have hpt : ∀ p : X × X, t p.1 p.2 ≤ |((E p.1 p.2 : ℚ) : ℝ)| * RZ := by
        intro p
        by_cases hfp : ((E p.1 p.2 : ℚ) : ℝ) ≠ 0
        · have hZnep : ((inst.Z (j₀ p.1 p.2) p.1 p.2 : ℚ) : ℝ) ≠ 0 := hj₀ p.1 p.2 hfp
          simp only [htdef]
          calc |((E p.1 p.2 : ℚ) : ℝ)| / |((inst.Z (j₀ p.1 p.2) p.1 p.2 : ℚ) : ℝ)|
              = |((E p.1 p.2 : ℚ) : ℝ)| * |((inst.Z (j₀ p.1 p.2) p.1 p.2 : ℚ) : ℝ)|⁻¹ := by
                rw [div_eq_inv_mul]
                ring
            _ ≤ |((E p.1 p.2 : ℚ) : ℝ)| * RZ :=
                mul_le_mul_of_nonneg_left (hRZle (j₀ p.1 p.2) p.1 p.2 hZnep) (abs_nonneg _)
        · have hz : ((E p.1 p.2 : ℚ) : ℝ) = 0 := not_not.mp hfp
          simp only [htdef, hz, abs_zero, zero_div]
          simp
      have hsumE : (∑ p : X × X, |((E p.1 p.2 : ℚ) : ℝ)|)
          ≤ c * c * (ZS * (4 * c) * (2 * RW + 1) * η) := by
        calc (∑ p : X × X, |((E p.1 p.2 : ℚ) : ℝ)|)
            ≤ ∑ p : X × X, (ZS * (4 * c) * (2 * RW + 1) * η) :=
              Finset.sum_le_sum fun p _ => hEbound p.1 p.2
          _ = c * c * (ZS * (4 * c) * (2 * RW + 1) * η) := hcount2 _
      calc (∑ p : X × X, t p.1 p.2) ≤ ∑ p : X × X, |((E p.1 p.2 : ℚ) : ℝ)| * RZ :=
            Finset.sum_le_sum fun p _ => hpt p
        _ = RZ * (∑ p : X × X, |((E p.1 p.2 : ℚ) : ℝ)|) := by
            rw [← Finset.sum_mul]
            ring
        _ ≤ RZ * (c * c * (ZS * (4 * c) * (2 * RW + 1) * η)) :=
            mul_le_mul_of_nonneg_left hsumE hRZ0
    have hupatch : ∀ x : X, (∑ j : Fin n, ∑ p : X × X, ((uPatch j x p * uPatch j x p : ℚ) : ℝ))
        ≤ 2 * RZ * c * c * (ZS * (4 * c) * (2 * RW + 1)) * η + 2 * c * c * η := by
      intro x
      rw [Finset.sum_comm]
      calc (∑ p : X × X, ∑ j : Fin n, ((uPatch j x p * uPatch j x p : ℚ) : ℝ))
          ≤ ∑ p : X × X, (2 * t p.1 p.2 + 2 * η) := Finset.sum_le_sum fun p _ => hupj x p
        _ = 2 * (∑ p : X × X, t p.1 p.2) + 2 * η * (c * c) := by
            rw [Finset.sum_add_distrib, hcount2, ← Finset.mul_sum]
            ring
        _ ≤ 2 * RZ * (c * c * (ZS * (4 * c) * (2 * RW + 1) * η)) + 2 * η * (c * c) := by
            have h2' := mul_le_mul_of_nonneg_left hsumt (by norm_num : (0:ℝ) ≤ 2)
            linarith [h2', le_of_eq (by ring : (2:ℝ) * η * (c * c) = 2 * c * c * η)]
        _ = 2 * RZ * c * c * (ZS * (4 * c) * (2 * RW + 1)) * η + 2 * c * c * η := by ring
    have hvpatch : ∀ y : X, (∑ j : Fin n, ∑ p : X × X, ((vPatch j y p * vPatch j y p : ℚ) : ℝ))
        ≤ RZ * (c * c * (ZS * (4 * c) * (2 * RW + 1) * η)) := by
      intro y
      rw [Finset.sum_comm]
      calc (∑ p : X × X, ∑ j : Fin n, ((vPatch j y p * vPatch j y p : ℚ) : ℝ))
          ≤ ∑ p : X × X, t p.1 p.2 := Finset.sum_le_sum fun p _ => hvpj y p
        _ ≤ RZ * (c * c * (ZS * (4 * c) * (2 * RW + 1) * η)) := hsumt
    have hrowη : 2 * RZ * c * c * (ZS * (4 * c) * (2 * RW + 1)) * η
        + 4 * c * c * (ZS * (4 * c) * (2 * RW + 1)) * η + 2 * c * c * η ≤ K * η := by
      have hpre := mul_le_mul_of_nonneg_right hKrow hη0.le
      have hexpl : (2 * RZ * c * c * (ZS * (4 * c) * (2 * RW + 1))
          + 4 * c * c * (ZS * (4 * c) * (2 * RW + 1)) + 2 * c * c) * η
          = 2 * RZ * c * c * (ZS * (4 * c) * (2 * RW + 1)) * η
            + 4 * c * c * (ZS * (4 * c) * (2 * RW + 1)) * η + 2 * c * c * η := by ring
      rw [hexpl] at hpre
      exact hpre
    have hB0 : 0 ≤ 4 * c * c * (ZS * (4 * c) * (2 * RW + 1)) * η :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc0) hc0) hKbase) hη0.le
    have hD0 : 0 ≤ RZ * (c * c * (ZS * (4 * c) * (2 * RW + 1) * η)) :=
      mul_nonneg hRZ0 (mul_nonneg hcc (mul_nonneg hKbase hη0.le))
    have hDA : RZ * (c * c * (ZS * (4 * c) * (2 * RW + 1) * η))
        ≤ 2 * RZ * c * c * (ZS * (4 * c) * (2 * RW + 1)) * η := by
      nlinarith [hD0]
    have hmainU : ∀ x : X, (∑ j : Fin n, ∑ qb : (X ⊕ X) × Bool,
          ((uq j x qb.1 qb.2 * uq j x qb.1 qb.2 : ℚ) : ℝ)) ≤ W + K * η := by
      intro x
      have h1 := humain x
      have hle : (n : ℝ) * (4 * c * (2 * RW + 1)) ≤ K := by
        have h3 : (n : ℝ) * (4 * c * (2 * RW + 1)) + 4 * c * (2 * RW + 1)
            = ((n : ℝ) + 1) * (4 * c) * (2 * RW + 1) := by ring
        linarith [hKNQ, hx4c]
      have h2 := mul_le_mul_of_nonneg_right hle hη0.le
      linarith
    have hmainV : ∀ y : X, (∑ j : Fin n, ∑ qb : (X ⊕ X) × Bool,
          ((vq j y qb.1 qb.2 * vq j y qb.1 qb.2 : ℚ) : ℝ)) ≤ W + K * η := by
      intro y
      have h1 := hvmain y
      have hle : (n : ℝ) * (4 * c * (2 * RW + 1)) ≤ K := by
        have h3 : (n : ℝ) * (4 * c * (2 * RW + 1)) + 4 * c * (2 * RW + 1)
            = ((n : ℝ) + 1) * (4 * c) * (2 * RW + 1) := by ring
        linarith [hKNQ, hx4c]
      have h2 := mul_le_mul_of_nonneg_right hle hη0.le
      linarith
    have hpatchU : ∀ x : X, (∑ j : Fin n, ∑ p : X × X, ((uPatch j x p * uPatch j x p : ℚ) : ℝ))
        ≤ K * η := by
      intro x
      have h1 := hupatch x
      linarith [h1, hrowη, hB0]
    have hpatchV : ∀ y : X, (∑ j : Fin n, ∑ p : X × X, ((vPatch j y p * vPatch j y p : ℚ) : ℝ))
        ≤ K * η := by
      intro y
      have h1 := hvpatch y
      have hC0 : 0 ≤ 2 * c * c * η :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc0) hc0) hη0.le
      linarith [h1, hDA, hrowη, hB0, hC0]
    have hKη : 2 * K * η = ε / 4 := by
      have hKne : (K : ℝ) ≠ 0 := by linarith
      rw [hηdef]
      field_simp
      norm_num
    obtain ⟨B, hB1, hB2⟩ := exists_rat_btwn
      (show (filteredGamma2 (rationalGamma2ComplexA inst) (rationalGamma2ComplexZ inst)).toReal
          + 3 * ε / 8 < (filteredGamma2 (rationalGamma2ComplexA inst)
          (rationalGamma2ComplexZ inst)).toReal + ε / 2 by linarith)
    have hBle : ((B : ℚ) : ℝ) ≤ (filteredGamma2 (rationalGamma2ComplexA inst)
        (rationalGamma2ComplexZ inst)).toReal + ε := by
      linarith
    have huMass : ∀ x : X, (∑ j : Fin n, ∑ q : ((X ⊕ X) × Bool) ⊕ (X × X),
          ((U j x q * U j x q : ℚ) : ℝ)) ≤ ((B : ℚ) : ℝ) := by
      intro x
      have hsplit : ∀ j : Fin n, (∑ q : ((X ⊕ X) × Bool) ⊕ (X × X),
            ((U j x q * U j x q : ℚ) : ℝ))
          = (∑ qb : (X ⊕ X) × Bool, ((uq j x qb.1 qb.2 * uq j x qb.1 qb.2 : ℚ) : ℝ))
            + (∑ p : X × X, ((uPatch j x p * uPatch j x p : ℚ) : ℝ)) := by
        intro j
        rw [huUdef, Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr]
      calc (∑ j : Fin n, ∑ q : ((X ⊕ X) × Bool) ⊕ (X × X), ((U j x q * U j x q : ℚ) : ℝ))
          = ∑ j : Fin n, ((∑ qb : (X ⊕ X) × Bool,
              ((uq j x qb.1 qb.2 * uq j x qb.1 qb.2 : ℚ) : ℝ))
            + ∑ p : X × X, ((uPatch j x p * uPatch j x p : ℚ) : ℝ)) :=
            Finset.sum_congr rfl fun j _ => hsplit j
        _ = ((∑ j : Fin n, ∑ qb : (X ⊕ X) × Bool,
              ((uq j x qb.1 qb.2 * uq j x qb.1 qb.2 : ℚ) : ℝ))
            + ∑ j : Fin n, ∑ p : X × X, ((uPatch j x p * uPatch j x p : ℚ) : ℝ)) :=
            Finset.sum_add_distrib
        _ ≤ (W + K * η) + K * η := add_le_add (hmainU x) (hpatchU x)
        _ = W + 2 * K * η := by ring
        _ = W + ε / 4 := by rw [hKη]
        _ ≤ ((B : ℚ) : ℝ) := by
            rw [hWdef]
            linarith
    have hvMass : ∀ y : X, (∑ j : Fin n, ∑ q : ((X ⊕ X) × Bool) ⊕ (X × X),
          ((V j y q * V j y q : ℚ) : ℝ)) ≤ ((B : ℚ) : ℝ) := by
      intro y
      have hsplit : ∀ j : Fin n, (∑ q : ((X ⊕ X) × Bool) ⊕ (X × X),
            ((V j y q * V j y q : ℚ) : ℝ))
          = (∑ qb : (X ⊕ X) × Bool, ((vq j y qb.1 qb.2 * vq j y qb.1 qb.2 : ℚ) : ℝ))
            + (∑ p : X × X, ((vPatch j y p * vPatch j y p : ℚ) : ℝ)) := by
        intro j
        rw [hvVdef, Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr]
      calc (∑ j : Fin n, ∑ q : ((X ⊕ X) × Bool) ⊕ (X × X), ((V j y q * V j y q : ℚ) : ℝ))
          = ∑ j : Fin n, ((∑ qb : (X ⊕ X) × Bool,
              ((vq j y qb.1 qb.2 * vq j y qb.1 qb.2 : ℚ) : ℝ))
            + ∑ p : X × X, ((vPatch j y p * vPatch j y p : ℚ) : ℝ)) :=
            Finset.sum_congr rfl fun j _ => hsplit j
        _ = ((∑ j : Fin n, ∑ qb : (X ⊕ X) × Bool,
              ((vq j y qb.1 qb.2 * vq j y qb.1 qb.2 : ℚ) : ℝ))
            + ∑ j : Fin n, ∑ p : X × X, ((vPatch j y p * vPatch j y p : ℚ) : ℝ)) :=
            Finset.sum_add_distrib
        _ ≤ (W + K * η) + K * η := add_le_add (hmainV y) (hpatchV y)
        _ = W + 2 * K * η := by ring
        _ = W + ε / 4 := by rw [hKη]
        _ ≤ ((B : ℚ) : ℝ) := by
            rw [hWdef]
            linarith
    refine ⟨{ Q := ((X ⊕ X) × Bool) ⊕ (X × X), u := U, v := V, budget := B },
      ⟨huMass, hvMass, hentryF⟩, hBle, ?_, ?_⟩
    · refine le_trans (filteredGamma2_le_of_gramFilteredCert
        (gramFilteredCert_of_rationalValid inst U V B huMass hvMass hentryF)) ?_
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · exact hcard

/-- Establishes `Gamma2WitnessCompilerSpec` and additional polynomial witness-dimension and
existential runtime bounds for rational filtered γ₂ instances. The filtered factorization
setting is that of [LeeEtAl2011]. -/
theorem clause90 :
  Gamma2WitnessCompilerSpec ∧
  (∀ (X : Type) [Fintype X] [DecidableEq X] (n : ℕ) (inst : RationalGamma2Instance X n)
      (ε : ℝ), 0 < ε → ε ≤ 1 →
    filteredGamma2 (rationalGamma2ComplexA inst) (rationalGamma2ComplexZ inst) < ⊤ →
    ∃ F : RationalGamma2Factorization X inst,
      RationalFactorizationValid inst F ∧
        @Fintype.card F.Q F.fintypeQ ≤
          (rationalGamma2Bits inst + Fintype.card X + n + Nat.ceil (1 / ε) + 8) ^ 7) ∧
  (∀ (X : Type) [Fintype X] [DecidableEq X] (n : ℕ) (inst : RationalGamma2Instance X n)
      (ε : ℝ) (M : ℕ), 0 < ε → ε ≤ 1 →
    filteredGamma2 (rationalGamma2ComplexA inst) (rationalGamma2ComplexZ inst)
      ≤ (M : ℝ≥0∞) →
    ∃ (F : RationalGamma2Factorization X inst) (runtime : ℕ),
      RationalFactorizationValid inst F ∧
        (F.budget : ℝ) ≤ (filteredGamma2 (rationalGamma2ComplexA inst)
          (rationalGamma2ComplexZ inst)).toReal + ε ∧
        runtime ≤
          (rationalGamma2Bits inst + Fintype.card X + n + M + Nat.ceil (1 / ε) + 8) ^ 7) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X _ _ n inst ε hε hε1 hval
    obtain ⟨F, hvalid, hbup, hbdn, _⟩ := exists_rational_factorization inst hε hε1 hval
    exact ⟨F, (rationalGamma2Bits inst + Fintype.card X + n + Nat.ceil (1 / ε) + 8) ^ 7,
      hvalid, hbup, hbdn, Nat.le_refl _⟩
  · intro X _ _ n inst ε hε hε1 hval
    obtain ⟨F, hvalid, _, _, hcard⟩ := exists_rational_factorization inst hε hε1 hval
    exact ⟨F, hvalid, hcard⟩
  · intro X _ _ n inst ε M hε hε1 hM
    have hval : filteredGamma2 (rationalGamma2ComplexA inst) (rationalGamma2ComplexZ inst)
        < ⊤ := lt_of_le_of_lt hM (by simp)
    obtain ⟨F, hvalid, hbup, _, _⟩ := exists_rational_factorization inst hε hε1 hval
    exact ⟨F, (rationalGamma2Bits inst + Fintype.card X + n + M + Nat.ceil (1 / ε) + 8) ^ 7,
      hvalid, hbup, Nat.le_refl _⟩
end Qatlib.Concepts.ConversionCore.WitnessCompile.WitnessCompiler
