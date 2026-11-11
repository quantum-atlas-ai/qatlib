/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NativeNumerics.NlfftPipeline.InverseNLFFTSU2
import Qatlib.Concepts.NativeNumerics.NlfftPipeline.FiniteFFTPolynomialMul

/-!
# Finite Fourier implementation of the inverse nonlinear transform

This module implements `inverseNLFFTFiniteSU2` using explicit coefficient prefixes, conjugate
reversals, and `finiteFFTPolynomialMul`. It connects finite polynomial arithmetic to inverse
SU(2) nonlinear Fourier transforms; see [AlexisEtAl2026] for nonlinear Fourier background.

The output has the prescribed parameter length and polynomial degree bounds. Under
`LayerStripExact`, it agrees with sequential stripping, with an explicit bound of order `n *
(log n)^2` on the operation counter.

## Main statements

* `inverseNLFFTFiniteSU2_degree_bounds`: Both output polynomials have natural degree at most
  `n-1`.
* `inverseNLFFTFiniteSU2_gammas`: Finite Fourier arithmetic preserves the exact sequential
  stripping output.
* `inverseNLFFTFiniteSU2_operations`: The finite implementation satisfies the stated operation
  bound.

## References

* [Alexis et al., 2026][AlexisEtAl2026]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT

namespace Qatlib.Concepts.NativeNumerics.NlfftPipeline
open Polynomial
set_option maxHeartbeats 1000000

/-- The inverse SU(2) nonlinear Fourier transform implemented by finite coefficient arrays and
radix-two Fourier polynomial multiplication, with an accumulated operation count. -/
def inverseNLFFTFiniteSU2 (A B : Polynomial ℂ) : ℕ → InverseNLFFTRunSU2
  | 0 => { gammas := [], eta := 1, xi := 0, operations := 0 }
  | 1 =>
      let γ := B.coeff 0 / A.coeff 0
      let c : ℂ := ((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ)
      { gammas := [γ], eta := C c, xi := C (c * γ), operations := 8 }
  | n + 2 =>
      let N := n + 2
      let m := (N + 1) / 2
      let a := finiteCoefficientPrefix N A
      let b := finiteCoefficientPrefix N B
      let ru := inverseNLFFTFiniteSU2
        (finiteCoefficientPrefix m a) (finiteCoefficientPrefix m b) m
      let er := finiteCoefficientConjRev m ru.eta
      let xr := finiteCoefficientConjRev m ru.xi
      let q := Nat.clog 2 (4 * (2 + n))
      let t₁ := finiteFFTPolynomialMul q er a
      let t₂ := finiteFFTPolynomialMul q xr b
      let t₃ := finiteFFTPolynomialMul q ru.eta b
      let t₄ := finiteFFTPolynomialMul q ru.xi a
      let aM := finiteCoefficientPolynomial (N - m)
        (fun j => t₁.polynomial.coeff (m + j) + t₂.polynomial.coeff (m + j))
      let bM := finiteCoefficientPolynomial (N - m)
        (fun j => t₃.polynomial.coeff (m + j) - t₄.polynomial.coeff (m + j))
      let rd := inverseNLFFTFiniteSU2 aM bM (N - m)
      let u₁ := finiteFFTPolynomialMul q ru.eta rd.eta
      let u₂ := finiteFFTPolynomialMul q xr rd.xi
      let u₃ := finiteFFTPolynomialMul q er rd.xi
      let u₄ := finiteFFTPolynomialMul q ru.xi rd.eta
      { gammas := ru.gammas ++ rd.gammas
        eta := finiteCoefficientPolynomial N
          (fun j => u₁.polynomial.coeff j - u₂.polynomial.coeff j)
        xi := finiteCoefficientPolynomial N
          (fun j => u₃.polynomial.coeff j + u₄.polynomial.coeff j)
        operations := ru.operations + rd.operations
          + t₁.operations + t₂.operations + t₃.operations + t₄.operations
          + u₁.operations + u₂.operations + u₃.operations + u₄.operations
          + 2 * (N - m) + 2 * N + 2 * (m + 1) }
  termination_by n => n
  decreasing_by
    · simp_wf; omega
    · simp_wf; omega

set_option backward.isDefEq.respectTransparency false

/-- For positive `n`, a polynomial of degree less than `n` also has natural degree less than
`n`. -/
private theorem natDegree_lt_of_degree_lt {p : Polynomial ℂ} {n : ℕ} (hn : 0 < n)
    (h : p.degree < (n : WithBot ℕ)) : p.natDegree < n := by
  rcases eq_or_ne p 0 with rfl | hp
  · rw [Polynomial.natDegree_zero]
    exact hn
  · exact (Polynomial.natDegree_lt_iff_degree_lt hp).mpr h

/-- A polynomial assembled from `n` coefficients has natural degree at most `n-1`. -/
private theorem finiteCoefficientPolynomial_natDegree_le (n : ℕ) (f : ℕ → ℂ) :
    (finiteCoefficientPolynomial n f).natDegree ≤ n - 1 := by
  by_cases hn : n = 0
  · rw [show finiteCoefficientPolynomial n f = 0 from by
      subst hn; simp [finiteCoefficientPolynomial], Polynomial.natDegree_zero]
    omega
  · have hlt := natDegree_lt_of_degree_lt (by omega)
      (finiteCoefficientPolynomial_degree_lt n f)
    omega

/-- Every coefficient at index at least `n` vanishes after reduction modulo `X^n`. -/
private theorem coeff_mod_X_pow_zero (p : Polynomial ℂ) (n i : ℕ) (hi : n ≤ i) :
    (p % X ^ n).coeff i = 0 := by
  have hd : (p % X ^ n).degree < (n : WithBot ℕ) := by
    rw [← Polynomial.modByMonic_eq_mod p (Polynomial.monic_X_pow n)]
    have hlt := Polynomial.degree_modByMonic_lt p (Polynomial.monic_X_pow n)
    rwa [Polynomial.degree_X_pow] at hlt
  rw [Polynomial.degree_lt_iff_coeff_zero] at hd
  exact hd i hi

/-- Taking a prefix of length `m ≤ N` after a prefix of length `N` equals reduction of the
original polynomial modulo `X^m`. -/
private theorem prefix_prefix (m N : ℕ) (hmN : m ≤ N) (p : Polynomial ℂ) :
    finiteCoefficientPrefix m (finiteCoefficientPrefix N p) = p % X ^ m := by
  have hmod : (p % X ^ N) % X ^ m = p % X ^ m := by
    ext i
    by_cases hi : i < m
    · rw [coeff_mod_X_pow _ _ _ hi, coeff_mod_X_pow _ _ _ (by omega : i < N),
        coeff_mod_X_pow _ _ _ hi]
    · rw [coeff_mod_X_pow_zero _ _ _ (by omega), coeff_mod_X_pow_zero _ _ _ (by omega)]
  rw [finiteCoefficientPrefix_eq_mod N p, finiteCoefficientPrefix_eq_mod, hmod]

/-- A polynomial with natural degree less than `n` is unchanged by reduction modulo `X^n`. -/
private theorem mod_X_pow_self (n : ℕ) (p : Polynomial ℂ) (h : p.natDegree < n) :
    p % X ^ n = p := by
  ext i
  by_cases hi : i < n
  · rw [coeff_mod_X_pow _ _ _ hi]
  · rw [coeff_mod_X_pow_zero _ _ _ (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- The finite inverse transform returns exactly `n` parameters. -/
theorem inverseNLFFTFiniteSU2_gammas_length (A B : Polynomial ℂ) (n : ℕ) :
    (inverseNLFFTFiniteSU2 A B n).gammas.length = n := by
  induction n using Nat.strong_induction_on generalizing A B with
  | _ n ih =>
    cases n with
    | zero =>
      rw [inverseNLFFTFiniteSU2.eq_1]
      rfl
    | succ n =>
      cases n with
      | zero =>
        rw [inverseNLFFTFiniteSU2.eq_2]
        rfl
      | succ n =>
        rw [inverseNLFFTFiniteSU2.eq_3]
        dsimp only []
        rw [List.length_append, ih _ (by omega), ih _ (by omega)]
        omega

/-- Both polynomials returned by the finite inverse transform have natural degree at most `n-1`. -/
theorem inverseNLFFTFiniteSU2_degree_bounds (A B : Polynomial ℂ) (n : ℕ) :
    (inverseNLFFTFiniteSU2 A B n).eta.natDegree ≤ n - 1 ∧
    (inverseNLFFTFiniteSU2 A B n).xi.natDegree ≤ n - 1 := by
  cases n with
  | zero =>
    rw [inverseNLFFTFiniteSU2.eq_1]
    exact ⟨by rw [Polynomial.natDegree_one], by rw [Polynomial.natDegree_zero]⟩
  | succ n =>
    cases n with
    | zero =>
      rw [inverseNLFFTFiniteSU2.eq_2]
      dsimp only []
      exact ⟨by rw [Polynomial.natDegree_C], by rw [Polynomial.natDegree_C]⟩
    | succ n =>
      rw [inverseNLFFTFiniteSU2.eq_3]
      dsimp only []
      exact ⟨finiteCoefficientPolynomial_natDegree_le _ _,
        finiteCoefficientPolynomial_natDegree_le _ _⟩

/-- Under `LayerStripExact A B n`, the finite inverse transform returns the sequential stripping
parameters and their nonlinear Fourier polynomial pair. -/
theorem inverseNLFFTFiniteSU2_gammas (A B : Polynomial ℂ) (n : ℕ)
    (hex : LayerStripExact A B n) :
    (inverseNLFFTFiniteSU2 A B n).gammas = (layerStripSU2 A B n).gammas
    ∧ (inverseNLFFTFiniteSU2 A B n).eta = (nlftSU2 (layerStripSU2 A B n).gammas).1
    ∧ (inverseNLFFTFiniteSU2 A B n).xi = (nlftSU2 (layerStripSU2 A B n).gammas).2 := by
  induction n using Nat.strong_induction_on generalizing A B with
  | _ n ih =>
    cases n with
    | zero =>
      refine ⟨?_, ?_, ?_⟩
      · rw [inverseNLFFTFiniteSU2.eq_1]
        rfl
      · rw [inverseNLFFTFiniteSU2.eq_1]
        show (1 : Polynomial ℂ) = (nlftSU2 (layerStripSU2 A B 0).gammas).1
        rw [show (layerStripSU2 A B 0).gammas = [] from rfl]
        rfl
      · rw [inverseNLFFTFiniteSU2.eq_1]
        show (0 : Polynomial ℂ) = (nlftSU2 (layerStripSU2 A B 0).gammas).2
        rw [show (layerStripSU2 A B 0).gammas = [] from rfl]
        rfl
    | succ n =>
      cases n with
      | zero =>
        refine ⟨?_, ?_, ?_⟩
        · rw [inverseNLFFTFiniteSU2.eq_2]
          rfl
        · rw [inverseNLFFTFiniteSU2.eq_2]
          show (C ((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)))
              = (nlftSU2 (layerStripSU2 A B 1).gammas).1
          rw [show (layerStripSU2 A B 1).gammas = [B.coeff 0 / A.coeff 0] from rfl,
            nlftSU2_singleton]
        · rw [inverseNLFFTFiniteSU2.eq_2]
          show (C ((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)
              * (B.coeff 0 / A.coeff 0))) = (nlftSU2 (layerStripSU2 A B 1).gammas).2
          rw [show (layerStripSU2 A B 1).gammas = [B.coeff 0 / A.coeff 0] from rfl,
            nlftSU2_singleton]
      | succ n =>
        rw [inverseNLFFTFiniteSU2.eq_3]
        dsimp only []
        rw [show 2 + n = n + 2 from Nat.add_comm 2 n]
        set N := n + 2 with hN
        set m := (N + 1) / 2 with hm
        rw [show finiteCoefficientPrefix m (finiteCoefficientPrefix N A) = A % X ^ m from
            prefix_prefix m N (by omega) A,
          show finiteCoefficientPrefix m (finiteCoefficientPrefix N B) = B % X ^ m from
            prefix_prefix m N (by omega) B]
        have hmN : m + (N - m) = N := by omega
        have hm1 : 1 ≤ m := by omega
        have hmN2 : m ≤ N := by omega
        have hN2 : 2 ≤ N := by omega
        have hexm : LayerStripExact (A % X ^ m) (B % X ^ m) m := by
          apply layerStripExact_congr _ (layerStripExact_of_le hmN2 hex)
          intro i hi
          exact ⟨(coeff_mod_X_pow A m i hi).symm, (coeff_mod_X_pow B m i hi).symm⟩
        obtain ⟨ihg, ihe, ihx⟩ := ih m (by omega) (A % X ^ m) (B % X ^ m) hexm
        obtain ⟨htA, htB⟩ := layerStripSU2_transfer m A B hm1 (layerStripExact_of_le hmN2 hex)
        have ihe' : (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta = (nlftSU2 (layerStripSU2 A B m).gammas).1 := by
          rw [← layerStripSU2_truncate_gammas m m A B le_rfl]
          exact ihe
        have ihx' : (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi = (nlftSU2 (layerStripSU2 A B m).gammas).2 := by
          rw [← layerStripSU2_truncate_gammas m m A B le_rfl]
          exact ihx
        have hmlen : (layerStripSU2 A B m).gammas.length = m := layerStripSU2_gammas_length A B m
        have hmne : (layerStripSU2 A B m).gammas ≠ [] := by
          intro hc
          rw [hc] at hmlen
          simp at hmlen
          omega
        have hdeger : (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta).natDegree ≤ m :=
          finiteCoefficientPolynomial_natDegree_le (m + 1)
            (fun i => (starRingEnd ℂ) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta.coeff (m - i)))
        have hdegxr : (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi).natDegree ≤ m :=
          finiteCoefficientPolynomial_natDegree_le (m + 1)
            (fun i => (starRingEnd ℂ) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi.coeff (m - i)))
        have hdegA : (finiteCoefficientPrefix N A).natDegree ≤ N - 1 :=
          finiteCoefficientPolynomial_natDegree_le N A.coeff
        have hdegB : (finiteCoefficientPrefix N B).natDegree ≤ N - 1 :=
          finiteCoefficientPolynomial_natDegree_le N B.coeff
        have hdeg1e : (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta.natDegree ≤ m - 1 :=
          (inverseNLFFTFiniteSU2_degree_bounds (A % X ^ m) (B % X ^ m) m).1
        have hdeg1x : (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi.natDegree ≤ m - 1 :=
          (inverseNLFFTFiniteSU2_degree_bounds (A % X ^ m) (B % X ^ m) m).2
        have her : finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta = conjRevN m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta :=
          finiteCoefficientConjRev_eq m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta (by omega)
        have hxr : finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi = conjRevN m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi :=
          finiteCoefficientConjRev_eq m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi (by omega)
        have h2q : 4 * N ≤ 2 ^ Nat.clog 2 (4 * N) :=
          Nat.le_pow_clog (b := 2) (by decide) (4 * N)
        have ht1 : (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial = (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) * (finiteCoefficientPrefix N A) :=
          finiteFFTPolynomialMul_semantics _ _ _ (by omega)
        have ht2 : (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial = (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) * (finiteCoefficientPrefix N B) :=
          finiteFFTPolynomialMul_semantics _ _ _ (by omega)
        have ht3 : (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial = ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) * (finiteCoefficientPrefix N B) :=
          finiteFFTPolynomialMul_semantics _ _ _ (by omega)
        have ht4 : (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial = ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) * (finiteCoefficientPrefix N A) :=
          finiteFFTPolynomialMul_semantics _ _ _ (by omega)
        have haPc : ∀ i, i < N → (finiteCoefficientPrefix N A).coeff i = A.coeff i := fun i hi => by
          rw [finiteCoefficientPrefix_eq_mod, coeff_mod_X_pow A N i hi]
        have hbPc : ∀ i, i < N → (finiteCoefficientPrefix N B).coeff i = B.coeff i := fun i hi => by
          rw [finiteCoefficientPrefix_eq_mod, coeff_mod_X_pow B N i hi]
        have hprod : ∀ (p : Polynomial ℂ) (j : ℕ), m + j < N →
            (p * (finiteCoefficientPrefix N A)).coeff (m + j) = (p * A).coeff (m + j) := by
          intro p j hj
          rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
          refine Finset.sum_congr rfl fun x hx => ?_
          have hxm : x.1 + x.2 = m + j := Finset.mem_antidiagonal.mp hx
          rw [haPc x.2 (by omega)]
        have hprodb : ∀ (p : Polynomial ℂ) (j : ℕ), m + j < N →
            (p * (finiteCoefficientPrefix N B)).coeff (m + j) = (p * B).coeff (m + j) := by
          intro p j hj
          rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
          refine Finset.sum_congr rfl fun x hx => ?_
          have hxm : x.1 + x.2 = m + j := Finset.mem_antidiagonal.mp hx
          rw [hbPc x.2 (by omega)]
        have hfa : ∀ j, j < N - m → (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)).coeff j
            = (layerStripSU2 A B m).finalA.coeff j := by
          intro j hj
          rw [finiteCoefficientPolynomial_coeff, if_pos hj, ht1, ht2, hprod _ j (by omega), hprodb _ j (by omega), her, hxr, ihe', ihx',
            ← Polynomial.coeff_add, ← htA, Nat.add_comm m j, Polynomial.coeff_X_pow_mul]
        have hfb : ∀ j, j < N - m → (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)).coeff j
            = (layerStripSU2 A B m).finalB.coeff j := by
          intro j hj
          rw [finiteCoefficientPolynomial_coeff, if_pos hj, ht3, ht4, hprodb _ j (by omega), hprod _ j (by omega), ihe', ihx',
            ← Polynomial.coeff_sub, ← htB, Nat.add_comm m j, Polynomial.coeff_X_pow_mul]
        have haMp : (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) = finiteCoefficientPrefix (N - m) (layerStripSU2 A B m).finalA := by
          ext j
          by_cases hj : j < N - m
          · rw [hfa j hj, finiteCoefficientPrefix_eq_mod, coeff_mod_X_pow _ _ _ hj]
          · rw [finiteCoefficientPolynomial_coeff, if_neg hj,
              finiteCoefficientPrefix_eq_mod, coeff_mod_X_pow_zero _ _ _ (by omega)]
        have hbMp : (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) = finiteCoefficientPrefix (N - m) (layerStripSU2 A B m).finalB := by
          ext j
          by_cases hj : j < N - m
          · rw [hfb j hj, finiteCoefficientPrefix_eq_mod, coeff_mod_X_pow _ _ _ hj]
          · rw [finiteCoefficientPolynomial_coeff, if_neg hj,
              finiteCoefficientPrefix_eq_mod, coeff_mod_X_pow_zero _ _ _ (by omega)]
        have hexcont : LayerStripExact (layerStripSU2 A B m).finalA
            (layerStripSU2 A B m).finalB (N - m) :=
          layerStripExact_add (N - m) (by rwa [hmN])
        have hexM : LayerStripExact (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m) := by
          rw [haMp, hbMp]
          apply layerStripExact_congr _ hexcont
          intro i hi
          rw [finiteCoefficientPrefix_eq_mod (N - m) (layerStripSU2 A B m).finalA,
            finiteCoefficientPrefix_eq_mod (N - m) (layerStripSU2 A B m).finalB]
          exact ⟨(coeff_mod_X_pow _ _ _ hi).symm, (coeff_mod_X_pow _ _ _ hi).symm⟩
        obtain ⟨ihg2, ihe2, ihx2⟩ :=
            ih (N - m) (by omega)
            (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) hexM
        have ig2 : (layerStripSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).gammas
            = (layerStripSU2 (layerStripSU2 A B m).finalA
                (layerStripSU2 A B m).finalB (N - m)).gammas := by
          rw [haMp, hbMp, finiteCoefficientPrefix_eq_mod, finiteCoefficientPrefix_eq_mod,
            layerStripSU2_truncate_gammas (N - m) (N - m) _ _ le_rfl]
        rw [ig2] at ihg2 ihe2 ihx2
        have hdeg2e : (inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).eta.natDegree ≤ N - m - 1 :=
          (inverseNLFFTFiniteSU2_degree_bounds (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).1
        have hdeg2x : (inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).xi.natDegree ≤ N - m - 1 :=
          (inverseNLFFTFiniteSU2_degree_bounds (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).2
        have hu1 : (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).eta)).polynomial = ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) * ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).eta) :=
          finiteFFTPolynomialMul_semantics _ _ _ (by omega)
        have hu2 : (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).xi)).polynomial = (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) * ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).xi) :=
          finiteFFTPolynomialMul_semantics _ _ _ (by omega)
        have hu3 : (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).xi)).polynomial = (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) * ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).xi) :=
          finiteFFTPolynomialMul_semantics _ _ _ (by omega)
        have hu4 : (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).eta)).polynomial = ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) * ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).eta) :=
          finiteFFTPolynomialMul_semantics _ _ _ (by omega)
        have hmodfin : ∀ (P : Polynomial ℂ) (f : ℕ → ℂ), P.natDegree < N →
            (∀ j, f j = P.coeff j) → finiteCoefficientPolynomial N f = P := by
          intro P f hdegP hf
          ext j
          by_cases hj : j < N
          · rw [finiteCoefficientPolynomial_coeff, if_pos hj, hf j]
          · rw [finiteCoefficientPolynomial_coeff, if_neg hj,
              Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        have hgarw : (layerStripSU2 A B N).gammas
            = (layerStripSU2 A B m).gammas
              ++ (layerStripSU2 (layerStripSU2 A B m).finalA
                (layerStripSU2 A B m).finalB (N - m)).gammas := by
          have e := layerStripSU2_add_gammas m (N - m) A B
          rwa [hmN] at e
        refine ⟨?_, ?_, ?_⟩
        · rw [hgarw, ihg, layerStripSU2_truncate_gammas m m A B le_rfl, ihg2]
        · have hPdeg : ((((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) * ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).eta)) - ((finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) * ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).xi))).natDegree < N := by
            have h1 : (((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) * ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).eta)).natDegree ≤ ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta).natDegree + ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).eta).natDegree :=
              Polynomial.natDegree_mul_le
            have h2 : ((finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) * ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).xi)).natDegree ≤ (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi).natDegree + ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).xi).natDegree :=
              Polynomial.natDegree_mul_le
            have h3 :=
                Polynomial.natDegree_sub_le
                (((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) * ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).eta)) ((finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) * ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).xi))
            omega
          have hPP : (finiteCoefficientPolynomial N
              fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).eta)).polynomial.coeff j - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).xi)).polynomial.coeff j)
              = (((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) * ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).eta)) - ((finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) * ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).xi)) := by
            rw [hu1, hu2]
            exact hmodfin _ _ hPdeg fun j => by rw [Polynomial.coeff_sub]
          rw [hPP, hgarw, ihe2, ihx2, ihe', hxr, ihx',
            nlftSU2_append _ _ hmne, hmlen,
            ← conjRevN_succ_eq_X_mul_conjRevN (m - 1)
              ((nlftSU2 (layerStripSU2 A B m).gammas).2)
              ((nlftSU2_snd_natDegree_le _).trans (by
                have h := layerStripSU2_gammas_length A B m
                omega)),
            Nat.sub_add_cancel hm1]
        · have hPdeg : (((finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) * ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).xi)) + (((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) * ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).eta))).natDegree < N := by
            have h1 : ((finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) * ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).xi)).natDegree ≤ (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta).natDegree + ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).xi).natDegree :=
              Polynomial.natDegree_mul_le
            have h2 : (((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) * ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).eta)).natDegree ≤ ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi).natDegree + ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).eta).natDegree :=
              Polynomial.natDegree_mul_le
            have h3 :=
                Polynomial.natDegree_add_le
                ((finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) * ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).xi)) (((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) * ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).eta))
            omega
          have hPP : (finiteCoefficientPolynomial N
              fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).xi)).polynomial.coeff j + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).eta)).polynomial.coeff j)
              = ((finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) * ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).xi)) + (((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) * ((inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) (finiteCoefficientConjRev m (inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j)) (finiteCoefficientPolynomial (N - m) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).eta) (finiteCoefficientPrefix N B)).polynomial.coeff (m + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * N)) ((inverseNLFFTFiniteSU2 (A % X ^ m) (B % X ^ m) m).xi) (finiteCoefficientPrefix N A)).polynomial.coeff (m + j)) (N - m)).eta)) := by
            rw [hu3, hu4]
            exact hmodfin _ _ hPdeg fun j => by rw [Polynomial.coeff_add]
          rw [hPP, hgarw, ihe2, ihx2, her, ihe', ihx',
            nlftSU2_append _ _ hmne, hmlen,
            ← conjRevN_succ_eq_X_mul_conjRevN (m - 1)
              ((nlftSU2 (layerStripSU2 A B m).gammas).1)
              ((nlftSU2_fst_natDegree_le _).trans (by
                have h := layerStripSU2_gammas_length A B m
                omega)),
            Nat.sub_add_cancel hm1]

/-- For positive `x`, the base-two ceiling logarithm is at most the base-two floor logarithm
plus one. -/
private theorem clog_two_le_succ_log (x : ℕ) (_hx : 1 ≤ x) :
    Nat.clog 2 x ≤ Nat.log 2 x + 1 := by
  by_contra h
  push Not at h
  have h1 : Nat.log 2 x + 1 < Nat.clog 2 x := by omega
  rw [Nat.lt_clog_iff_pow_lt (b := 2) (by decide)] at h1
  have h2 := Nat.lt_pow_succ_log_self (b := 2) (by decide) x
  omega

/-- For positive `x`, the least power of two at least `x` is at most `2*x`. -/
private theorem two_pow_clog_two_mul (x : ℕ) (hx : 1 ≤ x) :
    2 ^ Nat.clog 2 x ≤ 2 * x := by
  have hb2 : (1:ℕ) ≤ 2 := by decide
  calc 2 ^ Nat.clog 2 x ≤ 2 ^ (Nat.log 2 x + 1) :=
        Nat.pow_le_pow_right hb2 (clog_two_le_succ_log x hx)
    _ = 2 * 2 ^ Nat.log 2 x := by rw [pow_succ']
    _ ≤ 2 * x := Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 (by omega))

/-- For `N ≥ 2`, the ceiling logarithm of its upper half-size plus one is at most the ceiling
logarithm of `N`. -/
private theorem clog_two_ceil_half_le (m N : ℕ) (hN : 2 ≤ N) (hm : m = (N + 1) / 2) :
    Nat.clog 2 m + 1 ≤ Nat.clog 2 N := by
  have hc : N ≤ 2 ^ Nat.clog 2 N := Nat.le_pow_clog (b := 2) (by decide) N
  have hc1 : 1 ≤ Nat.clog 2 N := by
    by_contra h
    have h0 : Nat.clog 2 N = 0 := by omega
    rw [h0] at hc
    simp at hc
    omega
  have h2 : Nat.clog 2 m ≤ Nat.clog 2 N - 1 := by
    rw [Nat.clog_le_iff_le_pow (b := 2) (by decide)]
    have h2m : 2 * m ≤ 2 ^ Nat.clog 2 N + 1 := by
      rw [hm]
      omega
    have hpow : 2 ^ Nat.clog 2 N = 2 * 2 ^ (Nat.clog 2 N - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hc1]
    omega
  omega

/-- For `N ≥ 2`, the ceiling logarithm of its lower half-size plus one is at most the ceiling
logarithm of `N`. -/
private theorem clog_two_floor_half_le (m N : ℕ) (hN : 2 ≤ N) (hm : m = N / 2) :
    Nat.clog 2 m + 1 ≤ Nat.clog 2 N := by
  have hc : N ≤ 2 ^ Nat.clog 2 N := Nat.le_pow_clog (b := 2) (by decide) N
  have hc1 : 1 ≤ Nat.clog 2 N := by
    by_contra h
    have h0 : Nat.clog 2 N = 0 := by omega
    rw [h0] at hc
    simp at hc
    omega
  have h2 : Nat.clog 2 m ≤ Nat.clog 2 N - 1 := by
    rw [Nat.clog_le_iff_le_pow (b := 2) (by decide)]
    have h2m : 2 * m ≤ 2 ^ Nat.clog 2 N + 1 := by
      rw [hm]
      omega
    have hpow : 2 ^ Nat.clog 2 N = 2 * 2 ^ (Nat.clog 2 N - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hc1]
    omega
  omega

/-- For positive `n`, the finite inverse transform uses at most `2048 * n * (Nat.clog 2 n +
5)^2` counted operations. -/
theorem inverseNLFFTFiniteSU2_operations (A B : Polynomial ℂ) (n : ℕ) (hn : 1 ≤ n) :
    (inverseNLFFTFiniteSU2 A B n).operations ≤ 2048 * n * (Nat.clog 2 n + 5) ^ 2 := by
  have hmain : ∀ N : ℕ, 1 ≤ N → (inverseNLFFTFiniteSU2 A B N).operations
      ≤ 332 * N * (Nat.clog 2 N + 3) * (Nat.clog 2 N + 5) := by
    intro N
    induction N using Nat.strong_induction_on generalizing A B with
    | _ N ih =>
      intro hN
      cases N with
      | zero => omega
      | succ N =>
        cases N with
        | zero =>
          rw [inverseNLFFTFiniteSU2.eq_2]
          dsimp only []
          rw [Nat.clog_one_right]
          omega
        | succ N =>
          rw [inverseNLFFTFiniteSU2.eq_3]
          dsimp only []
          rw [show 2 + N = N + 2 from Nat.add_comm 2 N]
          set M := (N + 2 + 1) / 2 with hM
          have hM1 : 1 ≤ M := by omega
          have hMs : Nat.clog 2 M + 1 ≤ Nat.clog 2 (N + 2) :=
            clog_two_ceil_half_le M (N + 2) (by omega) hM.symm
          have hMs2 : Nat.clog 2 (N + 2 - M) + 1 ≤ Nat.clog 2 (N + 2) := by
            apply clog_two_floor_half_le (N + 2 - M) (N + 2) (by omega)
            omega
          have h1 := ih M (by omega) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A))
            (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) hM1
          have h2 :=
              ih (N + 2 - M) (by omega)
              ((finiteCoefficientPolynomial (N + 2 - M) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (finiteCoefficientConjRev M (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).eta) (finiteCoefficientPrefix (N + 2) A)).polynomial.coeff (M + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (finiteCoefficientConjRev M (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).xi) (finiteCoefficientPrefix (N + 2) B)).polynomial.coeff (M + j))) ((finiteCoefficientPolynomial (N + 2 - M) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).eta (finiteCoefficientPrefix (N + 2) B)).polynomial.coeff (M + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).xi (finiteCoefficientPrefix (N + 2) A)).polynomial.coeff (M + j))) (by omega)
          have hS8 : 2 ^ Nat.clog 2 (4 * (N + 2)) ≤ 8 * (N + 2) :=
            (two_pow_clog_two_mul (4 * (N + 2)) (by omega)).trans (by omega)
          have hqc : Nat.clog 2 (4 * (N + 2)) ≤ Nat.clog 2 (N + 2) + 2 := by
            rw [Nat.clog_le_iff_le_pow (b := 2) (by decide)]
            calc 4 * (N + 2) ≤ 4 * 2 ^ Nat.clog 2 (N + 2) :=
                  Nat.mul_le_mul_left _ (Nat.le_pow_clog (b := 2) (by decide) (N + 2))
              _ = 2 ^ (Nat.clog 2 (N + 2) + 2) := by rw [pow_add, pow_two]; ring
          have hff : ∀ p₁ p₂ : Polynomial ℂ,
              (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) p₁ p₂).operations
                ≤ 10 * (8 * (N + 2)) * (Nat.clog 2 (N + 2) + 3) := by
            intro p₁ p₂
            have h := finiteFFTPolynomialMul_operations (Nat.clog 2 (4 * (N + 2))) p₁ p₂
            have h3 : 10 * 2 ^ Nat.clog 2 (4 * (N + 2)) * (Nat.clog 2 (4 * (N + 2)) + 1)
                ≤ 10 * (8 * (N + 2)) * (Nat.clog 2 (N + 2) + 3) := by
              apply Nat.mul_le_mul
              · apply Nat.mul_le_mul_left
                exact hS8
              · omega
            exact h.trans h3
          have hextra : 2 * (N + 2 - M) + 2 * (N + 2) + 2 * (M + 1) ≤ 24 * (N + 2) := by omega
          have hX : 332 * M * (Nat.clog 2 M + 3) * (Nat.clog 2 M + 5)
              ≤ 332 * M * ((Nat.clog 2 (N + 2) + 2) * (Nat.clog 2 (N + 2) + 4)) :=
            calc 332 * M * (Nat.clog 2 M + 3) * (Nat.clog 2 M + 5)
                = (332 * M) * ((Nat.clog 2 M + 3) * (Nat.clog 2 M + 5)) := by ring
              _ ≤ (332 * M) * ((Nat.clog 2 (N + 2) + 2) * (Nat.clog 2 (N + 2) + 4)) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
          have hX2 : 332 * (N + 2 - M) * (Nat.clog 2 (N + 2 - M) + 3)
                * (Nat.clog 2 (N + 2 - M) + 5)
              ≤ 332 * (N + 2 - M) * ((Nat.clog 2 (N + 2) + 2) * (Nat.clog 2 (N + 2) + 4)) :=
            calc 332 * (N + 2 - M) * (Nat.clog 2 (N + 2 - M) + 3)
                  * (Nat.clog 2 (N + 2 - M) + 5)
                = (332 * (N + 2 - M)) * ((Nat.clog 2 (N + 2 - M) + 3)
                    * (Nat.clog 2 (N + 2 - M) + 5)) := by ring
              _ ≤ (332 * (N + 2 - M)) * ((Nat.clog 2 (N + 2) + 2)
                    * (Nat.clog 2 (N + 2) + 4)) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
          have hb1 : (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A))
                (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).operations
              ≤ 332 * M * ((Nat.clog 2 (N + 2) + 2) * (Nat.clog 2 (N + 2) + 4)) :=
            h1.trans hX
          have hb2 : (inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N + 2 - M) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (finiteCoefficientConjRev M (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).eta) (finiteCoefficientPrefix (N + 2) A)).polynomial.coeff (M + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (finiteCoefficientConjRev M (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).xi) (finiteCoefficientPrefix (N + 2) B)).polynomial.coeff (M + j)) (finiteCoefficientPolynomial (N + 2 - M) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).eta (finiteCoefficientPrefix (N + 2) B)).polynomial.coeff (M + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).xi (finiteCoefficientPrefix (N + 2) A)).polynomial.coeff (M + j)) (N + 2 - M)).operations
              ≤ 332 * (N + 2 - M) * ((Nat.clog 2 (N + 2) + 2) * (Nat.clog 2 (N + 2) + 4)) :=
            h2.trans hX2
          have hkey : 2 * (Nat.clog 2 (N + 2) + 3)
              + (Nat.clog 2 (N + 2) + 2) * (Nat.clog 2 (N + 2) + 4)
              ≤ (Nat.clog 2 (N + 2) + 3) * (Nat.clog 2 (N + 2) + 5) := by
            have e1 : 2 * (Nat.clog 2 (N + 2) + 3)
                + (Nat.clog 2 (N + 2) + 2) * (Nat.clog 2 (N + 2) + 4)
                = Nat.clog 2 (N + 2) ^ 2 + 8 * Nat.clog 2 (N + 2) + 14 := by ring
            have e2 : (Nat.clog 2 (N + 2) + 3) * (Nat.clog 2 (N + 2) + 5)
                = Nat.clog 2 (N + 2) ^ 2 + 8 * Nat.clog 2 (N + 2) + 15 := by ring
            omega
          have hsplit : M * ((Nat.clog 2 (N + 2) + 2) * (Nat.clog 2 (N + 2) + 4))
              + (N + 2 - M) * ((Nat.clog 2 (N + 2) + 2) * (Nat.clog 2 (N + 2) + 4))
              = (N + 2) * ((Nat.clog 2 (N + 2) + 2) * (Nat.clog 2 (N + 2) + 4)) := by
            rw [← Nat.add_mul, Nat.add_sub_cancel' (by omega : M ≤ N + 2)]
          have hcomb : 664 * (N + 2) * (Nat.clog 2 (N + 2) + 3)
              + 332 * (N + 2) * ((Nat.clog 2 (N + 2) + 2) * (Nat.clog 2 (N + 2) + 4))
              ≤ 332 * (N + 2) * ((Nat.clog 2 (N + 2) + 3) * (Nat.clog 2 (N + 2) + 5)) := by
            have hkm := Nat.mul_le_mul_left (332 * (N + 2)) hkey
            calc 664 * (N + 2) * (Nat.clog 2 (N + 2) + 3)
                  + 332 * (N + 2) * ((Nat.clog 2 (N + 2) + 2) * (Nat.clog 2 (N + 2) + 4))
                = 332 * (N + 2) * (2 * (Nat.clog 2 (N + 2) + 3)
                    + (Nat.clog 2 (N + 2) + 2) * (Nat.clog 2 (N + 2) + 4)) := by ring
              _ ≤ 332 * (N + 2) * ((Nat.clog 2 (N + 2) + 3) * (Nat.clog 2 (N + 2) + 5)) := hkm
          have e1 :=
              hff (finiteCoefficientConjRev M (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).eta) (finiteCoefficientPrefix (N + 2) A)
          have e2 :=
              hff (finiteCoefficientConjRev M (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).xi) (finiteCoefficientPrefix (N + 2) B)
          have e3 :=
              hff (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).eta (finiteCoefficientPrefix (N + 2) B)
          have e4 :=
              hff (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).xi (finiteCoefficientPrefix (N + 2) A)
          have e5 :=
              hff (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).eta (inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N + 2 - M) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (finiteCoefficientConjRev M (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).eta) (finiteCoefficientPrefix (N + 2) A)).polynomial.coeff (M + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (finiteCoefficientConjRev M (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).xi) (finiteCoefficientPrefix (N + 2) B)).polynomial.coeff (M + j)) (finiteCoefficientPolynomial (N + 2 - M) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).eta (finiteCoefficientPrefix (N + 2) B)).polynomial.coeff (M + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).xi (finiteCoefficientPrefix (N + 2) A)).polynomial.coeff (M + j)) (N + 2 - M)).eta
          have e6 :=
              hff (finiteCoefficientConjRev M (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).xi) (inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N + 2 - M) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (finiteCoefficientConjRev M (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).eta) (finiteCoefficientPrefix (N + 2) A)).polynomial.coeff (M + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (finiteCoefficientConjRev M (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).xi) (finiteCoefficientPrefix (N + 2) B)).polynomial.coeff (M + j)) (finiteCoefficientPolynomial (N + 2 - M) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).eta (finiteCoefficientPrefix (N + 2) B)).polynomial.coeff (M + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).xi (finiteCoefficientPrefix (N + 2) A)).polynomial.coeff (M + j)) (N + 2 - M)).xi
          have e7 :=
              hff (finiteCoefficientConjRev M (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).eta) (inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N + 2 - M) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (finiteCoefficientConjRev M (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).eta) (finiteCoefficientPrefix (N + 2) A)).polynomial.coeff (M + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (finiteCoefficientConjRev M (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).xi) (finiteCoefficientPrefix (N + 2) B)).polynomial.coeff (M + j)) (finiteCoefficientPolynomial (N + 2 - M) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).eta (finiteCoefficientPrefix (N + 2) B)).polynomial.coeff (M + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).xi (finiteCoefficientPrefix (N + 2) A)).polynomial.coeff (M + j)) (N + 2 - M)).xi
          have e8 :=
              hff (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).xi (inverseNLFFTFiniteSU2 (finiteCoefficientPolynomial (N + 2 - M) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (finiteCoefficientConjRev M (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).eta) (finiteCoefficientPrefix (N + 2) A)).polynomial.coeff (M + j) + (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (finiteCoefficientConjRev M (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).xi) (finiteCoefficientPrefix (N + 2) B)).polynomial.coeff (M + j)) (finiteCoefficientPolynomial (N + 2 - M) fun j => (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).eta (finiteCoefficientPrefix (N + 2) B)).polynomial.coeff (M + j) - (finiteFFTPolynomialMul (Nat.clog 2 (4 * (N + 2))) (inverseNLFFTFiniteSU2 (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) A)) (finiteCoefficientPrefix M (finiteCoefficientPrefix (N + 2) B)) M).xi (finiteCoefficientPrefix (N + 2) A)).polynomial.coeff (M + j)) (N + 2 - M)).eta
          nlinarith [e1, e2, e3, e4, e5, e6, e7, e8, hextra, hb1, hb2, hsplit, hcomb]
  calc (inverseNLFFTFiniteSU2 A B n).operations
      ≤ 332 * n * (Nat.clog 2 n + 3) * (Nat.clog 2 n + 5) := hmain n hn
    _ ≤ 2048 * n * (Nat.clog 2 n + 5) ^ 2 := by
        have h1 : 332 * n ≤ 2048 * n := Nat.mul_le_mul_right _ (by omega)
        have h2 : (Nat.clog 2 n + 3) * (Nat.clog 2 n + 5)
            ≤ (Nat.clog 2 n + 5) * (Nat.clog 2 n + 5) :=
          Nat.mul_le_mul_right _ (by omega)
        calc 332 * n * (Nat.clog 2 n + 3) * (Nat.clog 2 n + 5)
            = (332 * n) * ((Nat.clog 2 n + 3) * (Nat.clog 2 n + 5)) := by ring
          _ ≤ (2048 * n) * ((Nat.clog 2 n + 5) * (Nat.clog 2 n + 5)) := Nat.mul_le_mul h1 h2
          _ = 2048 * n * (Nat.clog 2 n + 5) ^ 2 := by ring

end Qatlib.Concepts.NativeNumerics.NlfftPipeline
