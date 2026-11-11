/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.PaidComparator
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option backward.isDefEq.respectTransparency false

/-!
# Explicit nonempty original paid separation regime

The original dyadic dimensions d=2 or 3, N>=256, lambda=N-squared,
beta=1 and public p0=256/N-squared meet the original promise and
strict finite-output comparison without an input-dependent certificate.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexOrder HermitianMat
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Foundations.FiniteStats.BornEstimator
local instance (d N : ℕ) : DecidableEq (Fin d → Fin N) := Classical.decEq _

/-- The source's explicit lambda=N² choice also gives a nonempty finite-output beta=1 separation regime on every original d=2 or 3 dyadic N≥256 grid. -/
theorem physical_pair_explicit_nonempty_regime (d r : ℕ) (hd : d=2 ∨ d=3) (hr : 8≤r) :
    32*(d : ℝ)*(paidGridSize d r : ℝ)/(2*Real.pi/((2^r : ℕ) : ℝ))^4 <
      ((((2^r : ℕ) : ℝ)^4*(Real.sin (2*Real.pi/((2^r : ℕ) : ℝ)))^2/
        (2*Real.pi/((2^r : ℕ) : ℝ))^2)-1)^2/24-1 := by
  let N : ℝ := ((2^r : ℕ) : ℝ)
  let h : ℝ := 2*Real.pi/N
  let A : ℝ := N^4*(Real.sin h)^2
  have hnat : 256≤2^r := by
    calc 256=2^8 := by decide
         _ ≤2^r := Nat.pow_le_pow_right (by decide : 1≤2) hr
  have hN : (256 : ℝ)≤N := by dsimp only [N]; exact_mod_cast hnat
  have hNp : 0<N := by linarith
  have hN0 : N≠0 := ne_of_gt hNp
  have hN4 : (4 : ℝ)≤N := by linarith
  have hhp : 0<h := div_pos (by positivity) hNp
  have hhhalf : h≤Real.pi/2 := by
    dsimp only [h]
    rw [div_le_iff₀ hNp]
    calc 2*Real.pi=(Real.pi/2)*4 := by ring
         _ ≤(Real.pi/2)*N := mul_le_mul_of_nonneg_left hN4 (by positivity)
  have hh2 : h≤2 := by
    dsimp only [h]
    rw [div_le_iff₀ hNp]
    nlinarith [Real.pi_lt_four]
  have hs : 4/N≤Real.sin h := by
    have hj := Real.mul_le_sin (le_of_lt hhp) hhhalf
    calc 4/N=2/Real.pi*h := by dsimp only [h]; field_simp [hN0,ne_of_gt Real.pi_pos]; ring
         _ ≤_ := hj
  have hs2 : (4/N)^2≤(Real.sin h)^2 :=
    pow_le_pow_left₀ (by positivity : (0 : ℝ)≤4/N) hs 2
  have hA : 16*N^2≤A := by
    calc 16*N^2=N^4*(4/N)^2 := by field_simp [hN0]; ring
         _ ≤A := mul_le_mul_of_nonneg_left hs2 (by positivity)
  have hhSq : h^2≤4 := by nlinarith
  have hhFourth : h^4≤16 := by nlinarith [sq_nonneg (h^2)]
  have hD : 15*N^2≤A-h^2 := by nlinarith [sq_nonneg N]
  have hD2 : (15*N^2)^2≤(A-h^2)^2 :=
    pow_le_pow_left₀ (by positivity) hD 2
  have hM : (paidGridSize d r : ℝ)=N^d := by
    dsimp only [paidGridSize,N]
    rw [Nat.mul_comm d r,Nat.pow_mul]
    push_cast
    rfl
  have hN1 : (1 : ℝ)≤N := by linarith
  have hMle : (paidGridSize d r : ℝ)≤N^3 := by
    rw [hM]
    rcases hd with rfl | rfl
    · nlinarith [mul_nonneg (sq_nonneg N) (sub_nonneg.mpr hN1)]
    · exact le_rfl
  have hd3 : (d : ℝ)≤3 := by rcases hd with rfl | rfl <;> norm_num
  have hdM : (d : ℝ)*(paidGridSize d r : ℝ)≤3*N^3 := by
    calc _ ≤3*(paidGridSize d r : ℝ) := mul_le_mul_of_nonneg_right hd3 (by positivity)
         _ ≤_ := mul_le_mul_of_nonneg_left hMle (by norm_num)
  have hN3 : (1 : ℝ)≤N^3 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤1) hN1 3
  have hpoly : 2304*N^3+384<225*N^4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) (pow_nonneg (le_of_lt hNp) 3)]
  have hcore : 32*(d : ℝ)*(paidGridSize d r : ℝ)<(A-h^2)^2/24-h^4 := by
    nlinarith
  change 32*(d : ℝ)*(paidGridSize d r : ℝ)/h^4 < (A/h^2-1)^2/24-1
  apply (div_lt_iff₀ (pow_pos hhp 4)).2
  have he : ((A/h^2-1)^2/24-1)*h^4=(A-h^2)^2/24-h^4 := by
    field_simp [ne_of_gt hhp]
  rw [he]
  exact hcore

/-- The explicit nonempty regime also has a valid original common public promise threshold below one half. -/
theorem physical_pair_explicit_promise (r : ℕ) (hr : 8≤r) :
    (Real.sin (2*Real.pi/((2^r : ℕ) : ℝ)))^2/2≤256/(((2^r : ℕ) : ℝ)^2) ∧
      256/(((2^r : ℕ) : ℝ)^2)≤1/2 := by
  let N : ℝ := ((2^r : ℕ) : ℝ)
  have hn : 256≤2^r := Nat.pow_le_pow_right (by decide : 1≤2) hr
  have hN : (256 : ℝ)≤N := by dsimp only [N]; exact_mod_cast hn
  have hNp : 0<N := by linarith
  have hN0 : N≠0 := ne_of_gt hNp
  have hs : (Real.sin (2*Real.pi/N))^2≤(2*Real.pi/N)^2 := Real.sin_sq_le_sq
  change (Real.sin (2*Real.pi/N))^2/2≤256/N^2 ∧ 256/N^2≤1/2
  constructor
  · apply (le_div_iff₀ (pow_pos hNp 2)).2
    calc _ ≤(2*Real.pi/N)^2/2*N^2 := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hs (by norm_num)) (sq_nonneg N)
         _ =2*Real.pi^2 := by field_simp [hN0]
         _ ≤256 := by nlinarith [Real.pi_pos,Real.pi_lt_four]
  · apply (div_le_iff₀ (pow_pos hNp 2)).2
    nlinarith [sq_nonneg (N-256)]

/-- Explicit original legal parameters give a strict finite-output physical separation against every uniformly bounded-bias full-address PSD-separable two-copy estimator. -/
theorem physical_pair_original_explicit_separation {O K : Type*} [Fintype O] [Fintype K]
    (d r : ℕ) (hd : d=2 ∨ d=3) (hr : 8≤r)
    (P : POVM O (((Fin d → Fin (2^r)) × Fin 2) × ((Fin d → Fin (2^r)) × Fin 2)))
    (E F : O → K → HermitianMat ((Fin d → Fin (2^r)) × Fin 2) ℂ)
    (hE : ∀ o k,0≤E o k) (hF : ∀ o k,0≤F o k)
    (hsep : ∀ o,P.mats o=∑ k,E o k ⊗ₖ F o k) (y : O → ℝ)
    (hbias : ∀ ψ : PairGrid d r → Bool → ℂ,
      OriginalPeriodicPromise d (2^r) (256/(((2^r : ℕ) : ℝ)^2)) ψ →
      |mean (literalFieldOutcome P ψ) y-
        originalPeriodicLoss d (2^r) (((2^r : ℕ) : ℝ)^2) ψ|≤1) :
    256/(((2^r : ℕ) : ℝ)^2)≤1/2 ∧
    ∃ c,paidPairPlanQ d r (((2^r : ℕ) : ℚ)^2) 1=some c ∧
      ∃ ψ : PairGrid d r → Bool → ℂ,
      ∃ hp : OriginalPeriodicPromise d (2^r) (256/(((2^r : ℕ) : ℝ)^2)) ψ,
        originalPeriodicLoss d (2^r) (((2^r : ℕ) : ℝ)^2) ψ=0 ∧
        (physicalPairLaw d r ψ hp.1).variance
          (fun z => (physicalPairOutputQ d r (((2^r : ℕ) : ℚ)^2) c z : ℝ)) <
          variance (literalFieldOutcome P ψ) y := by
  have hp := physical_pair_explicit_promise r hr
  have hlamBound : (0 : ℚ)<((2^r : ℕ) : ℚ)^2 := by positivity
  have hbetaBound : (0 : ℚ)<1 := by norm_num
  have he := physical_pair_strict_null_risk_separation d r hd (by omega)
    P E F hE hF hsep (((2^r : ℕ) : ℚ)^2) 1 hlamBound hbetaBound
    (256/(((2^r : ℕ) : ℝ)^2)) hp.1
    (by simpa only [Rat.cast_pow,Rat.cast_natCast,Rat.cast_one,← pow_mul,Nat.reduceMul,one_pow] using
      physical_pair_explicit_nonempty_regime d r hd hr)
    y (by simpa only [Rat.cast_pow,Rat.cast_natCast,Rat.cast_one] using hbias)
  refine ⟨hp.2,?_⟩
  simpa only [Rat.cast_pow,Rat.cast_natCast] using he

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
