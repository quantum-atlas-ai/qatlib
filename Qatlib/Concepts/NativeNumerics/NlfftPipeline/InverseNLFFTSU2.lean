/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NativeNumerics.NlfftPipeline.NonlinearFourierSU2

/-!
# Divide-and-conquer inverse nonlinear Fourier transform

This module defines `inverseNLFFTSU2`, a recursive inverse transform returning a list of complex
parameters, its nonlinear Fourier polynomial pair, and an operation count. For nonlinear Fourier
transforms in the quantum signal processing setting, see [AlexisEtAl2026].

Under `LayerStripExact`, the divide-and-conquer output agrees with sequential layer stripping.
The counted work is bounded by `2048 * n * (Nat.clog 2 n + 5)^2` for positive `n`.

## Main statements

* `inverseNLFFTSU2_gammas`: The parameters and polynomial pair agree with sequential layer
  stripping.
* `inverseNLFFTSU2_operations`: An explicit bound of order `n * (log n)^2` on the operation
  counter.

## References

* [Alexis et al., 2026][AlexisEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.NativeNumerics.NlfftPipeline

open Polynomial

set_option autoImplicit false

/-- The size-dependent operation budget for a polynomial multiplication padded to the next power
of two above `4*N`. -/
def nlfftMulOps (N : ℕ) : ℕ :=
  let S := 2 ^ (Nat.clog 2 (4 * N))
  10 * S * (Nat.log2 S + 1)

/-- The parameter list, nonlinear Fourier polynomial pair, and operation count returned by an
inverse transform run. -/
structure InverseNLFFTRunSU2 where
  gammas : List ℂ
  eta : Polynomial ℂ
  xi : Polynomial ℂ
  operations : ℕ

/-- The divide-and-conquer inverse SU(2) nonlinear Fourier transform, recursively stripping a
coefficient prefix, transforming the residual pair, and combining the resulting polynomial
pairs. -/
noncomputable def inverseNLFFTSU2 (A B : Polynomial ℂ) : ℕ → InverseNLFFTRunSU2
  | 0 => { gammas := [], eta := 1, xi := 0, operations := 0 }
  | 1 =>
      let γ := B.coeff 0 / A.coeff 0
      let c : ℂ := ((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ)
      { gammas := [γ], eta := C c, xi := C (c * γ), operations := 6 }
  | n + 2 =>
      let N := n + 2
      let m := (N + 1) / 2
      let ru := inverseNLFFTSU2 (A % X ^ m) (B % X ^ m) m
      let aM := (conjRevN m ru.eta * A + conjRevN m ru.xi * B) /ₘ (X ^ m)
      let bM := (ru.eta * B - ru.xi * A) /ₘ (X ^ m)
      let rd := inverseNLFFTSU2 aM bM (N - m)
      { gammas := ru.gammas ++ rd.gammas,
        eta := ru.eta * rd.eta - conjRevN m ru.xi * rd.xi,
        xi := conjRevN m ru.eta * rd.xi + ru.xi * rd.eta,
        operations := 8 * nlfftMulOps N + 24 * N + ru.operations + rd.operations }
  termination_by n => n
  decreasing_by
    · simp_wf; omega
    · simp_wf; omega

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

/-- For `N ≥ 2`, the ceiling logarithm of the upper half-size plus one is at most the ceiling
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

/-- For `N ≥ 2`, the ceiling logarithm of the lower half-size plus one is at most the ceiling
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

/-- For positive `N`, the nonrecursive node budget `8 * nlfftMulOps N + 24*N` is at most `664 *
N * (Nat.clog 2 N + 3)`. -/
private theorem nodeOps_le (N : ℕ) (hN : 1 ≤ N) :
    8 * nlfftMulOps N + 24 * N ≤ 664 * N * (Nat.clog 2 N + 3) := by
  have hS : 2 ^ Nat.clog 2 (4 * N) ≤ 8 * N :=
      (two_pow_clog_two_mul (4 * N) (by omega)).trans (by omega)
  have hc : Nat.clog 2 (4 * N) ≤ Nat.clog 2 N + 2 := by
    rw [Nat.clog_le_iff_le_pow (b := 2) (by decide)]
    calc 4 * N ≤ 4 * 2 ^ Nat.clog 2 N := Nat.mul_le_mul_left _ (Nat.le_pow_clog (b := 2) (by decide) N)
      _ = 2 ^ (Nat.clog 2 N + 2) := by rw [pow_add, pow_two]; ring
  have hlogS : Nat.log2 (2 ^ Nat.clog 2 (4 * N)) = Nat.clog 2 (4 * N) := by
    rw [Nat.log2_eq_log_two, Nat.log_pow (b := 2) (by decide)]
  unfold nlfftMulOps
  simp only [hlogS]
  have hc3 : Nat.clog 2 (4 * N) + 1 ≤ Nat.clog 2 N + 3 := by omega
  calc 8 * (10 * 2 ^ Nat.clog 2 (4 * N) * (Nat.clog 2 (4 * N) + 1)) + 24 * N
      ≤ 8 * (10 * (8 * N) * (Nat.clog 2 N + 3)) + 24 * N := by
        apply Nat.add_le_add_right
        apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul
        · apply Nat.mul_le_mul_left
          exact hS
        · exact hc3
    _ = 640 * N * (Nat.clog 2 N + 3) + 24 * N := by ring
    _ ≤ 640 * N * (Nat.clog 2 N + 3) + 24 * N * (Nat.clog 2 N + 3) := by
        apply Nat.add_le_add_left
        exact le_mul_of_one_le_right (Nat.zero_le _) (by omega)
    _ = 664 * N * (Nat.clog 2 N + 3) := by ring

/-- The inverse transform returns exactly `n` complex parameters. -/
theorem inverseNLFFTSU2_gammas_length (A B : Polynomial ℂ) (n : ℕ) :
    (inverseNLFFTSU2 A B n).gammas.length = n := by
  induction n using Nat.strong_induction_on generalizing A B with
  | _ n ih =>
    cases n with
    | zero =>
      rw [inverseNLFFTSU2.eq_1]
      rfl
    | succ n =>
      cases n with
      | zero =>
        rw [inverseNLFFTSU2.eq_2]
        rfl
      | succ n =>
        rw [inverseNLFFTSU2.eq_3]
        dsimp only []
        rw [List.length_append, ih _ (by omega), ih _ (by omega)]
        omega

/-- Exactness for `n+1` sequential layer-stripping steps implies exactness for `n` steps. -/
private theorem layerStripExact_succ_mono {A B : Polynomial ℂ} {n : ℕ}
    (hex : LayerStripExact A B (n + 1)) : LayerStripExact A B n := by
  induction n generalizing A B with
  | zero => trivial
  | succ n ih =>
    obtain ⟨h0, hex'⟩ := hex
    exact ⟨h0, ih hex'⟩

/-- Exactness for `N` sequential layer-stripping steps implies exactness for every `m ≤ N`. -/
theorem layerStripExact_of_le {A B : Polynomial ℂ} {m N : ℕ} (hmn : m ≤ N)
    (hex : LayerStripExact A B N) : LayerStripExact A B m := by
  induction N generalizing m with
  | zero =>
    have h0 : m = 0 := by omega
    subst h0
    exact hex
  | succ N ih =>
    by_cases hm : m = N + 1
    · subst hm
      exact hex
    · have hm2 : m ≤ N := by omega
      exact ih hm2 (layerStripExact_succ_mono hex)

/-- After `m` steps of an exact `m+k`-step layer stripping, the residual polynomial pair is
exact for another `k` steps. -/
theorem layerStripExact_add {m : ℕ} {A B : Polynomial ℂ} (k : ℕ)
    (hex : LayerStripExact A B (m + k)) :
    LayerStripExact (layerStripSU2 A B m).finalA (layerStripSU2 A B m).finalB k := by
  induction m generalizing A B k with
  | zero =>
    rw [zero_add] at hex
    exact hex
  | succ m ih =>
    rw [Nat.add_right_comm] at hex
    obtain ⟨-, hex'⟩ := hex
    exact ih _ hex'

/-- Agreement of the first `m` coefficients of both input polynomials transfers `m`-step
layer-stripping exactness to the second pair. -/
theorem layerStripExact_congr {A B A' B' : Polynomial ℂ} {m : ℕ}
    (h : ∀ i, i < m → A.coeff i = A'.coeff i ∧ B.coeff i = B'.coeff i)
    (hex : LayerStripExact A B m) : LayerStripExact A' B' m := by
  induction m generalizing A B A' B' with
  | zero => trivial
  | succ m ih =>
    obtain ⟨hA0, hB0⟩ := h 0 (Nat.zero_lt_succ m)
    obtain ⟨hA1, hex2⟩ := hex
    have hA0' : A'.coeff 0 ≠ 0 := by rwa [hA0] at hA1
    refine ⟨hA0', ?_⟩
    refine ih (A := (layerStripStepSU2 A B).2.1) (B := (layerStripStepSU2 A B).2.2)
      (A' := (layerStripStepSU2 A' B').2.1) (B' := (layerStripStepSU2 A' B').2.2) ?_ hex2
    intro i hi
    obtain ⟨hAi, hBi⟩ := h i (Nat.lt_succ_of_lt hi)
    obtain ⟨hAi1, hBi1⟩ := h (i + 1) (Nat.succ_lt_succ hi)
    obtain ⟨_, h2f, h3f⟩ := layerStripStepSU2_apply A B
    obtain ⟨_, h2g, h3g⟩ := layerStripStepSU2_apply A' B'
    constructor
    · rw [h2f, h2g, coeff_smul, coeff_add, coeff_smul, coeff_smul, coeff_add, coeff_smul, hAi,
        hBi, hA0, hB0]
    · rw [h3f, h3g, coeff_smul, Polynomial.coeff_divX, coeff_sub, coeff_smul, coeff_smul,
        Polynomial.coeff_divX, coeff_sub, coeff_smul, hBi1, hAi1, hA0, hB0]

/-- The parameters from `m+k` sequential stripping steps are the first `m` parameters followed
by the `k` parameters stripped from the residual pair. -/
theorem layerStripSU2_add_gammas (m k : ℕ) (A B : Polynomial ℂ) :
    (layerStripSU2 A B (m + k)).gammas
      = (layerStripSU2 A B m).gammas
        ++ (layerStripSU2 (layerStripSU2 A B m).finalA (layerStripSU2 A B m).finalB k).gammas := by
  induction m generalizing A B k with
  | zero =>
    rw [zero_add, show (layerStripSU2 A B 0).gammas = [] from rfl, List.nil_append]
    rfl
  | succ m ih =>
    rw [Nat.add_right_comm]
    show (layerStripStepSU2 A B).1 :: (layerStripSU2 (layerStripStepSU2 A B).2.1
          (layerStripStepSU2 A B).2.2 (m + k)).gammas
      = ((layerStripStepSU2 A B).1 :: (layerStripSU2 (layerStripStepSU2 A B).2.1
          (layerStripStepSU2 A B).2.2 m).gammas)
        ++ (layerStripSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1
            (layerStripStepSU2 A B).2.2 m).finalA
          (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 m).finalB k).gammas
    rw [List.cons_append, ← ih k (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2]

/-- Under `LayerStripExact A B n`, the inverse transform returns the sequential stripping
parameters and their exact nonlinear Fourier polynomial pair. -/
theorem inverseNLFFTSU2_gammas (A B : Polynomial ℂ) (n : ℕ) (hex : LayerStripExact A B n) :
    (inverseNLFFTSU2 A B n).gammas = (layerStripSU2 A B n).gammas
    ∧ (inverseNLFFTSU2 A B n).eta = (nlftSU2 (layerStripSU2 A B n).gammas).1
    ∧ (inverseNLFFTSU2 A B n).xi = (nlftSU2 (layerStripSU2 A B n).gammas).2 := by
  induction n using Nat.strong_induction_on generalizing A B with
  | _ n ih =>
    cases n with
    | zero =>
      refine ⟨?_, ?_, ?_⟩
      · rw [inverseNLFFTSU2.eq_1]
        rfl
      · rw [inverseNLFFTSU2.eq_1]
        show (1 : Polynomial ℂ) = (nlftSU2 (layerStripSU2 A B 0).gammas).1
        rw [show (layerStripSU2 A B 0).gammas = [] from rfl]
        rfl
      · rw [inverseNLFFTSU2.eq_1]
        show (0 : Polynomial ℂ) = (nlftSU2 (layerStripSU2 A B 0).gammas).2
        rw [show (layerStripSU2 A B 0).gammas = [] from rfl]
        rfl
    | succ n =>
      cases n with
      | zero =>
        refine ⟨?_, ?_, ?_⟩
        · rw [inverseNLFFTSU2.eq_2]
          rfl
        · rw [inverseNLFFTSU2.eq_2]
          show (C ((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)))
            = (nlftSU2 (layerStripSU2 A B 1).gammas).1
          rw [show (layerStripSU2 A B 1).gammas = [B.coeff 0 / A.coeff 0] from rfl,
            nlftSU2_singleton]
        · rw [inverseNLFFTSU2.eq_2]
          show (C ((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)
              * (B.coeff 0 / A.coeff 0))) = (nlftSU2 (layerStripSU2 A B 1).gammas).2
          rw [show (layerStripSU2 A B 1).gammas = [B.coeff 0 / A.coeff 0] from rfl,
            nlftSU2_singleton]
      | succ n =>
        rw [inverseNLFFTSU2.eq_3]
        dsimp only []
        set N := n + 2 with hN
        set m := (N + 1) / 2 with hm
        have hmN : m + (N - m) = N := by omega
        have hm1 : 1 ≤ m := by omega
        have hmN2 : m ≤ N := by omega
        have hexm : LayerStripExact (A % X ^ m) (B % X ^ m) m := by
          apply layerStripExact_congr _ (layerStripExact_of_le hmN2 hex)
          intro i hi
          exact ⟨(coeff_mod_X_pow A m i hi).symm, (coeff_mod_X_pow B m i hi).symm⟩
        obtain ⟨ihg, ihe, ihx⟩ := ih m (by omega) (A % X ^ m) (B % X ^ m) hexm
        obtain ⟨htA, htB⟩ := layerStripSU2_transfer m A B hm1
          (layerStripExact_of_le hmN2 hex)
        have ihe' : (inverseNLFFTSU2 (A % X ^ m) (B % X ^ m) m).eta
            = (nlftSU2 (layerStripSU2 A B m).gammas).1 := by
          rw [← layerStripSU2_truncate_gammas m m A B le_rfl]; exact ihe
        have ihx' : (inverseNLFFTSU2 (A % X ^ m) (B % X ^ m) m).xi
            = (nlftSU2 (layerStripSU2 A B m).gammas).2 := by
          rw [← layerStripSU2_truncate_gammas m m A B le_rfl]; exact ihx
        have hfinA' : (conjRevN m (inverseNLFFTSU2 (A % X ^ m) (B % X ^ m) m).eta * A
              + conjRevN m (inverseNLFFTSU2 (A % X ^ m) (B % X ^ m) m).xi * B) /ₘ X ^ m
            = (layerStripSU2 A B m).finalA := by
          rw [ihe', ihx', ← htA]
          exact Polynomial.mul_divByMonic_cancel_left _ (Polynomial.monic_X_pow m)
        have hfinB' : ((inverseNLFFTSU2 (A % X ^ m) (B % X ^ m) m).eta * B
              - (inverseNLFFTSU2 (A % X ^ m) (B % X ^ m) m).xi * A) /ₘ X ^ m
            = (layerStripSU2 A B m).finalB := by
          rw [ihe', ihx', ← htB]
          exact Polynomial.mul_divByMonic_cancel_left _ (Polynomial.monic_X_pow m)
        have hexcont : LayerStripExact (layerStripSU2 A B m).finalA
            (layerStripSU2 A B m).finalB (N - m) :=
          layerStripExact_add (N - m) (by rwa [hmN])
        obtain ⟨ihg2, ihe2, ihx2⟩ := ih (N - m) (by omega)
          ((conjRevN m (inverseNLFFTSU2 (A % X ^ m) (B % X ^ m) m).eta * A
              + conjRevN m (inverseNLFFTSU2 (A % X ^ m) (B % X ^ m) m).xi * B) /ₘ X ^ m)
          (((inverseNLFFTSU2 (A % X ^ m) (B % X ^ m) m).eta * B
              - (inverseNLFFTSU2 (A % X ^ m) (B % X ^ m) m).xi * A) /ₘ X ^ m)
          (by rwa [hfinA', hfinB'])
        rw [hfinA'] at ihg2 ihe2 ihx2
        rw [hfinB'] at ihg2 ihe2 ihx2
        have hgarw : (layerStripSU2 A B N).gammas
            = (layerStripSU2 A B m).gammas
              ++ (layerStripSU2 (layerStripSU2 A B m).finalA (layerStripSU2 A B m).finalB
                (N - m)).gammas := by
          have e := layerStripSU2_add_gammas m (N - m) A B
          rwa [hmN] at e
        have hmlen : (layerStripSU2 A B m).gammas.length = m := layerStripSU2_gammas_length A B m
        have hmne : (layerStripSU2 A B m).gammas ≠ [] := by
          intro hc
          rw [hc] at hmlen
          simp at hmlen
          omega
        refine ⟨?_, ?_, ?_⟩
        · rw [hfinA', hfinB', ihg, ihg2, layerStripSU2_truncate_gammas m m A B le_rfl, hgarw]
        · rw [hfinA', hfinB', ihe, ihx, ihe2, ihx2,
            layerStripSU2_truncate_gammas m m A B le_rfl, hgarw]
          rw [nlftSU2_append _ _ hmne, hmlen,
            ← conjRevN_succ_eq_X_mul_conjRevN (m - 1)
              ((nlftSU2 (layerStripSU2 A B m).gammas).2)
              ((nlftSU2_snd_natDegree_le _).trans (by
                have h := layerStripSU2_gammas_length A B m
                omega)),
            Nat.sub_add_cancel hm1]
        · rw [hfinA', hfinB', ihe, ihx, ihe2, ihx2,
            layerStripSU2_truncate_gammas m m A B le_rfl, hgarw]
          rw [nlftSU2_append _ _ hmne, hmlen,
            ← conjRevN_succ_eq_X_mul_conjRevN (m - 1)
              ((nlftSU2 (layerStripSU2 A B m).gammas).1)
              ((nlftSU2_fst_natDegree_le _).trans (by
                have h := layerStripSU2_gammas_length A B m
                omega)),
            Nat.sub_add_cancel hm1]

/-- For positive `n`, the inverse transform's operation count is at most `2048 * n * (Nat.clog 2
n + 5)^2`. -/
theorem inverseNLFFTSU2_operations (A B : Polynomial ℂ) (n : ℕ) (hn : 1 ≤ n) :
    (inverseNLFFTSU2 A B n).operations ≤ 2048 * n * (Nat.clog 2 n + 5) ^ 2 := by
  have hmain : ∀ N : ℕ, 1 ≤ N → (inverseNLFFTSU2 A B N).operations
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
          rw [inverseNLFFTSU2.eq_2]
          dsimp only []
          rw [Nat.clog_one_right]
          omega
        | succ N =>
          rw [inverseNLFFTSU2.eq_3]
          dsimp only []
          set M := (N + 2 + 1) / 2 with hM
          have hM1 : 1 ≤ M := by omega
          have hMs : Nat.clog 2 M + 1 ≤ Nat.clog 2 (N + 2)
              := clog_two_ceil_half_le M (N + 2) (by omega) hM.symm
          have hMs2 : Nat.clog 2 (N + 2 - M) + 1 ≤ Nat.clog 2 (N + 2) := by
            apply clog_two_floor_half_le (N + 2 - M) (N + 2) (by omega)
            omega
          have h1 := ih M (by omega) (A % X ^ M) (B % X ^ M) hM1
          have h2 := ih (N + 2 - M) (by omega)
            ((conjRevN M (inverseNLFFTSU2 (A % X ^ M) (B % X ^ M) M).eta * A
                + conjRevN M (inverseNLFFTSU2 (A % X ^ M) (B % X ^ M) M).xi * B) /ₘ X ^ M)
            (((inverseNLFFTSU2 (A % X ^ M) (B % X ^ M) M).eta * B
              - (inverseNLFFTSU2 (A % X ^ M) (B % X ^ M) M).xi * A) /ₘ X ^ M) (by omega)
          have hnode := nodeOps_le (N + 2) (by omega)
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
          have hb1 : (inverseNLFFTSU2 (A % X ^ M) (B % X ^ M) M).operations
              ≤ 332 * M * ((Nat.clog 2 (N + 2) + 2) * (Nat.clog 2 (N + 2) + 4)) :=
            h1.trans hX
          have hb2 : (inverseNLFFTSU2
                ((conjRevN M (inverseNLFFTSU2 (A % X ^ M) (B % X ^ M) M).eta * A
                    + conjRevN M (inverseNLFFTSU2 (A % X ^ M) (B % X ^ M) M).xi * B) /ₘ X ^ M)
                (((inverseNLFFTSU2 (A % X ^ M) (B % X ^ M) M).eta * B
                  - (inverseNLFFTSU2 (A % X ^ M) (B % X ^ M) M).xi * A) /ₘ X ^ M)
                (N + 2 - M)).operations
              ≤ 332 * (N + 2 - M) * ((Nat.clog 2 (N + 2) + 2) * (Nat.clog 2 (N + 2) + 4)) :=
            h2.trans hX2
          have hcomb : 664 * (N + 2) * (Nat.clog 2 (N + 2) + 3)
              + 332 * (N + 2) * ((Nat.clog 2 (N + 2) + 2) * (Nat.clog 2 (N + 2) + 4))
              ≤ 332 * (N + 2) * ((Nat.clog 2 (N + 2) + 3) * (Nat.clog 2 (N + 2) + 5)) := by
            have hkm := Nat.mul_le_mul_left (332 * (N + 2)) hkey
            calc 664 * (N + 2) * (Nat.clog 2 (N + 2) + 3)
                  + 332 * (N + 2) * ((Nat.clog 2 (N + 2) + 2) * (Nat.clog 2 (N + 2) + 4))
                = 332 * (N + 2) * (2 * (Nat.clog 2 (N + 2) + 3)
                    + (Nat.clog 2 (N + 2) + 2) * (Nat.clog 2 (N + 2) + 4)) := by ring
              _ ≤ 332 * (N + 2) * ((Nat.clog 2 (N + 2) + 3) * (Nat.clog 2 (N + 2) + 5)) := hkm
          nlinarith [hnode, hb1, hb2, hsplit, hcomb]
  calc (inverseNLFFTSU2 A B n).operations
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
