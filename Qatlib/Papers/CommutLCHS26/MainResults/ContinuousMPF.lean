/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.QuadratureCmp.RawMPF
import Qatlib.Papers.CommutLCHS26.MainResults.KernelStrip
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Continuous-window multi-product error bounds

This module transfers pointwise multi-product error certificates to weighted operator integrals
on finite real windows, for the continuous Hamiltonian combinations of [AftabAnTrivisa2026].
Repeated-step bounds retain the factor (1 + η)^(r - 1), and bounded nonnegative profiles yield
estimates in terms of their weighted integrals.

Continuity lemmas for exponential words, coefficients, masses, and certificates establish
integrability for concrete word families, including repeated Strang words and the
rational-Gaussian kernel.

## Main statements

* `one_step_profile_from_words`: integrates a local word-family profile bound.
* `full_time_profile_from_words`: gives integrated full-time error bounds.
* `kernel_window_from_coefficients`: specializes coefficient certificates to the kernel weight.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.ContinuousMPF

open Matrix Set MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Papers.CommutLCHS26.MainResults.MPFRemainder
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.RawMPF

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]

local instance : ContinuousENorm (Matrix I I ℂ) :=
  SeminormedAddGroup.toESeminormedAddMonoid.toContinuousENorm
local instance : NormedAlgebra ℚ (Matrix I I ℂ) := .restrictScalars ℚ ℝ _

/-- For unitary targets and pointwise error bounds η, the weighted integral of the r-th power
error is bounded by r times the integral of ‖f‖η(1 + η)^(r - 1), assuming this scalar
function is integrable. -/
theorem integral_power_error (C V : ℝ → Matrix I I ℂ) (f : ℝ → ℂ)
    (η : ℝ → ℝ) (R : ℝ) (r : ℕ)
    (hV : ∀ k ∈ Icc (-R) R, V k ∈ Matrix.unitaryGroup I ℂ)
    (he : ∀ k ∈ Icc (-R) R, ‖C k - V k‖ ≤ η k)
    (hi : IntegrableOn (fun k => ‖f k‖ * η k * (1 + η k) ^ (r - 1)) (Icc (-R) R)) :
    ‖∫ k in Icc (-R) R, f k • (C k ^ r - V k ^ r)‖ ≤
      (r : ℝ) * ∫ k in Icc (-R) R, ‖f k‖ * η k * (1 + η k) ^ (r - 1) := by
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (hi.const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with k hk
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (power_error (C k) (V k) (hV k hk)
    (η k) (he k hk) r) (norm_nonneg _)).trans_eq (by ring)

/-- Continuous matrix families and an integrable scalar weight yield an integrable weighted
difference of their r-th powers on a finite window. -/
theorem error_integrable (C V : ℝ → Matrix I I ℂ) (f : ℝ → ℂ) (R : ℝ) (r : ℕ)
    (hC : ContinuousOn C (Icc (-R) R)) (hV : ContinuousOn V (Icc (-R) R))
    (hf : IntegrableOn f (Icc (-R) R)) :
    IntegrableOn (fun k => f k • (C k ^ r - V k ^ r)) (Icc (-R) R) :=
  hf.smul_continuousOn ((hC.pow r).sub (hV.pow r)) isCompact_Icc

/-- An integrable scalar weight times a measurable nonnegative bounded profile is integrable on
the finite window. -/
theorem profile_integrable (f : ℝ → ℂ) (Φ : ℝ → ℝ) (R B : ℝ)
    (hf : IntegrableOn f (Icc (-R) R))
    (hm : AEStronglyMeasurable Φ (volume.restrict (Icc (-R) R)))
    (hn : ∀ k ∈ Icc (-R) R, 0 ≤ Φ k)
    (hb : ∀ k ∈ Icc (-R) R, Φ k ≤ B) :
    IntegrableOn (fun k => ‖f k‖ * Φ k) (Icc (-R) R) := by
  apply hf.norm.mul_bdd hm
  filter_upwards [ae_restrict_mem measurableSet_Icc] with k hk
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hn k hk)] using! hb k hk

/-- A pointwise local error profile integrates to the sum of its weighted profile contribution
and its weighted constant remainder. -/
theorem one_step_profile
    (C : ℝ → ℝ → Matrix I I ℂ) (Z : ℝ → Matrix I I ℂ)
    (f : ℝ → ℂ) (Φ : ℝ → ℝ) (Cm Rm R cap s : ℝ) (m : ℕ)
    (hf : IntegrableOn f (Icc (-R) R))
    (hΦ : IntegrableOn (fun k => ‖f k‖ * Φ k) (Icc (-R) R))
    (hs : 0 < s) (hcap : s ≤ cap)
    (hlocal : ∀ k, |k| ≤ R → ∀ t, 0 < t → t ≤ cap →
      ‖C k t - NormedSpace.exp (t • Z k)‖ ≤ Cm * t ^ (2 * m + 1) * Φ k + Rm) :
    ‖∫ k in Icc (-R) R, f k • (C k s - NormedSpace.exp (s • Z k))‖ ≤
      Cm * s ^ (2 * m + 1) * (∫ k in Icc (-R) R, ‖f k‖ * Φ k) +
        (∫ k in Icc (-R) R, ‖f k‖) * Rm := by
  have hi : IntegrableOn (fun k => Cm * s ^ (2 * m + 1) * (‖f k‖ * Φ k) + ‖f k‖ * Rm)
      (Icc (-R) R) :=
    (hΦ.const_mul (Cm * s ^ (2 * m + 1))).add (hf.norm.mul_const Rm)
  have h := norm_integral_le_of_norm_le
    (f := fun k => f k • (C k s - NormedSpace.exp (s • Z k))) hi (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with k hk
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left
      (hlocal k (abs_le.mpr hk) s hs hcap) (norm_nonneg _)).trans_eq (by ring))
  simpa only [integral_add (hΦ.const_mul _) (hf.norm.mul_const _),
    integral_const_mul, integral_mul_const] using! h

/-- Under the local profile and integrability hypotheses, the full-time integral error is
bounded by r times the integral of ‖f‖η(1 + η)^(r - 1) [Aftab et al., Proposition
3.14][AftabAnTrivisa2026]. -/
theorem full_time_chain
    (C : ℝ → ℝ → Matrix I I ℂ) (Z : ℝ → Matrix I I ℂ)
    (f : ℝ → ℂ) (Φ : ℝ → ℝ) (Cm Rm R cap T : ℝ) (m r : ℕ)
    (hZ : ∀ k ∈ Icc (-R) R, (Z k)ᴴ = -Z k)
    (hr : 0 < r) (hT : 0 < T) (hstep : T / r ≤ cap)
    (hlocal : ∀ k, |k| ≤ R → ∀ s, 0 < s → s ≤ cap →
      ‖C k s - NormedSpace.exp (s • Z k)‖ ≤ Cm * s ^ (2 * m + 1) * Φ k + Rm)
    (hi : IntegrableOn (fun k => ‖f k‖ *
      (Cm * (T / r) ^ (2 * m + 1) * Φ k + Rm) *
      (1 + (Cm * (T / r) ^ (2 * m + 1) * Φ k + Rm)) ^ (r - 1)) (Icc (-R) R)) :
    let η := fun k => Cm * (T / r) ^ (2 * m + 1) * Φ k + Rm
    ‖∫ k in Icc (-R) R, f k • (C k (T / r) ^ r - NormedSpace.exp (T • Z k))‖ ≤
      (r : ℝ) * ∫ k in Icc (-R) R, ‖f k‖ * η k * (1 + η k) ^ (r - 1) := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  simpa only [target_power _ T r hr] using!
    integral_power_error (fun k => C k (T / r))
      (fun k => NormedSpace.exp ((T / r) • Z k)) f
      (fun k => Cm * (T / r) ^ (2 * m + 1) * Φ k + Rm) R r
      (fun k hk => general_trotter_exp_unitary _ _ (hZ k hk))
      (fun k hk => hlocal k (abs_le.mpr hk) _ (div_pos hT hrpos) hstep) hi

/-- A bounded nonnegative local profile gives both an integrated repeated-step bound and a bound
using the supremum local error and weighted profile mass. -/
theorem full_time_profile
    (C : ℝ → ℝ → Matrix I I ℂ) (Z : ℝ → Matrix I I ℂ)
    (f : ℝ → ℂ) (Φ : ℝ → ℝ) (Cm Rm R cap T B : ℝ) (m r : ℕ)
    (hf : IntegrableOn f (Icc (-R) R))
    (hm : AEStronglyMeasurable Φ (volume.restrict (Icc (-R) R)))
    (hn : ∀ k ∈ Icc (-R) R, 0 ≤ Φ k) (hb : ∀ k ∈ Icc (-R) R, Φ k ≤ B)
    (hCm : 0 ≤ Cm) (hRm : 0 ≤ Rm)
    (hZ : ∀ k ∈ Icc (-R) R, (Z k)ᴴ = -Z k)
    (hr : 0 < r) (hT : 0 < T) (hstep : T / r ≤ cap)
    (hlocal : ∀ k, |k| ≤ R → ∀ s, 0 < s → s ≤ cap →
      ‖C k s - NormedSpace.exp (s • Z k)‖ ≤ Cm * s ^ (2 * m + 1) * Φ k + Rm) :
    let η := fun k => Cm * (T / r) ^ (2 * m + 1) * Φ k + Rm
    let E := sSup (η '' Icc (-R) R)
    ‖∫ k in Icc (-R) R, f k • (C k (T / r) ^ r - NormedSpace.exp (T • Z k))‖ ≤
      (r : ℝ) * ∫ k in Icc (-R) R, ‖f k‖ * η k * (1 + η k) ^ (r - 1) ∧
    ‖∫ k in Icc (-R) R, f k • (C k (T / r) ^ r - NormedSpace.exp (T • Z k))‖ ≤
      (1 + E) ^ (r - 1) *
        (Cm * T ^ (2 * m + 1) / (r : ℝ) ^ (2 * m) *
          (∫ k in Icc (-R) R, ‖f k‖ * Φ k) +
            (r : ℝ) * (∫ k in Icc (-R) R, ‖f k‖) * Rm) := by
  (try dsimp only)
  let η := fun k => Cm * (T / r) ^ (2 * m + 1) * Φ k + Rm
  let E := sSup (η '' Icc (-R) R)
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hs : 0 ≤ Cm * (T / r) ^ (2 * m + 1) :=
    mul_nonneg hCm (pow_nonneg (div_pos hT hrpos).le _)
  have hηn (k : ℝ) (hk : k ∈ Icc (-R) R) : 0 ≤ η k := by
    dsimp [η]; exact add_nonneg (mul_nonneg hs (hn k hk)) hRm
  have hηm : AEStronglyMeasurable η (volume.restrict (Icc (-R) R)) :=
    (hm.const_mul _).add_const _
  have hbounded : BddAbove (η '' Icc (-R) R) := by
    refine ⟨Cm * (T / r) ^ (2 * m + 1) * B + Rm, ?_⟩
    rintro _ ⟨k, hk, rfl⟩
    dsimp [η]
    linarith [mul_le_mul_of_nonneg_left (hb k hk) hs]
  have hE (k : ℝ) (hk : k ∈ Icc (-R) R) : η k ≤ E :=
    le_csSup hbounded (mem_image_of_mem _ hk)
  have hΦi := profile_integrable f Φ R B hf hm hn hb
  have hηi := profile_integrable f η R E hf hηm hηn hE
  have hgrowth (k : ℝ) (hk : k ∈ Icc (-R) R) :
      (1 + η k) ^ (r - 1) ≤ (1 + E) ^ (r - 1) :=
    pow_le_pow_left₀ (by linarith [hηn k hk]) (by linarith [hE k hk]) _
  have hi : IntegrableOn (fun k => ‖f k‖ * η k * (1 + η k) ^ (r - 1)) (Icc (-R) R) := by
    apply hηi.mul_bdd ((aestronglyMeasurable_const.add hηm).pow _)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with k hk
    change ‖(1 + η k) ^ (r - 1)‖ ≤ (1 + E) ^ (r - 1)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith [hηn k hk]) _)]
    exact hgrowth k hk
  have hchain := full_time_chain C Z f Φ Cm Rm R cap T m r hZ hr hT hstep hlocal hi
  refine ⟨hchain, hchain.trans ?_⟩
  have hint := setIntegral_mono_on hi (hηi.mul_const ((1 + E) ^ (r - 1))) measurableSet_Icc
    (fun k hk => mul_le_mul_of_nonneg_left (hgrowth k hk)
      (mul_nonneg (norm_nonneg _) (hηn k hk)))
  have hscale : (r : ℝ) * (T / r) ^ (2 * m + 1) =
      T ^ (2 * m + 1) / (r : ℝ) ^ (2 * m) := by
    rw [div_pow, pow_succ (r : ℝ)]
    field_simp [ne_of_gt hrpos]
  have hsum : (∫ k in Icc (-R) R, ‖f k‖ * η k) =
      Cm * (T / r) ^ (2 * m + 1) * (∫ k in Icc (-R) R, ‖f k‖ * Φ k) +
        (∫ k in Icc (-R) R, ‖f k‖) * Rm := by
    calc
      _ = ∫ k in Icc (-R) R, Cm * (T / r) ^ (2 * m + 1) * (‖f k‖ * Φ k) + ‖f k‖ * Rm := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro k _; dsimp [η]; ring
      _ = _ := by
        rw [integral_add (hΦi.const_mul _) (hf.norm.mul_const _),
          integral_const_mul, integral_mul_const]
  calc
    _ ≤ (r : ℝ) * (∫ k in Icc (-R) R, ‖f k‖ * η k * (1 + E) ^ (r - 1)) :=
      mul_le_mul_of_nonneg_left hint hrpos.le
    _ = (1 + E) ^ (r - 1) *
        (Cm * ((r : ℝ) * (T / r) ^ (2 * m + 1)) *
          (∫ k in Icc (-R) R, ‖f k‖ * Φ k) +
            (r : ℝ) * (∫ k in Icc (-R) R, ‖f k‖) * Rm) := by
      rw [integral_mul_const, hsum]; ring
    _ = _ := by rw [hscale]; ring

/-- An exponential word built from continuous parameter-dependent generators depends
continuously on the parameter. -/
theorem word_continuous (ws : List (ℝ → Matrix I I ℂ))
    (hw : ∀ X ∈ ws, Continuous X) (t : ℝ) :
    Continuous (fun k => suzukiExponentialWord (ws.map (fun X => X k)) t) := by
  induction ws with
  | nil => simp only [List.map_nil, suzukiExponentialWord, List.prod_nil]; fun_prop
  | cons X xs ih =>
    simp only [List.map_cons, suzukiExponentialWord, List.prod_cons]
    exact (NormedSpace.exp_continuous.comp ((hw X (by simp)).const_smul t)).mul
      (ih (fun Y hY => hw Y (by simp [hY])))

/-- A finite weighted multi-product of continuous generator families is continuous in the
parameter. -/
theorem multiProduct_continuous (ws : J → List (ℝ → Matrix I I ℂ)) (a : J → ℝ)
    (hw : ∀ j X, X ∈ ws j → Continuous X) (t : ℝ) :
    Continuous (fun k => multiProduct (fun j => (ws j).map (fun X => X k)) a t) := by
  apply continuous_finsetSum
  intro j _
  exact (word_continuous (ws j) (hw j) t).const_smul (a j)

/-- Continuous generator words give an integrable one-step weighted error satisfying the stated
integrated local profile bound [Aftab et al., Lemma 3.13][AftabAnTrivisa2026]. -/
theorem one_step_profile_from_words
    (ws : J → List (ℝ → Matrix I I ℂ)) (a : J → ℝ) (Z : ℝ → Matrix I I ℂ)
    (f : ℝ → ℂ) (Φ : ℝ → ℝ) (Cm Rm R cap s : ℝ) (m : ℕ)
    (hw : ∀ j X, X ∈ ws j → Continuous X) (hZ : Continuous Z)
    (hf : IntegrableOn f (Icc (-R) R))
    (hΦ : IntegrableOn (fun k => ‖f k‖ * Φ k) (Icc (-R) R))
    (hs : 0 < s) (hcap : s ≤ cap)
    (hlocal : ∀ k, |k| ≤ R → ∀ t, 0 < t → t ≤ cap →
      ‖multiProduct (fun j => (ws j).map (fun X => X k)) a t -
        NormedSpace.exp (t • Z k)‖ ≤ Cm * t ^ (2 * m + 1) * Φ k + Rm) :
    let C := fun k => multiProduct (fun j => (ws j).map (fun X => X k)) a s
    IntegrableOn (fun k => f k • (C k - NormedSpace.exp (s • Z k))) (Icc (-R) R) ∧
    ‖∫ k in Icc (-R) R, f k • (C k - NormedSpace.exp (s • Z k))‖ ≤
      Cm * s ^ (2 * m + 1) * (∫ k in Icc (-R) R, ‖f k‖ * Φ k) +
        (∫ k in Icc (-R) R, ‖f k‖) * Rm := by
  refine ⟨?_, one_step_profile _ Z f Φ Cm Rm R cap s m hf hΦ hs hcap hlocal⟩
  simpa only [pow_one] using! error_integrable _ _ f R 1
    (multiProduct_continuous ws a hw s).continuousOn
    (NormedSpace.exp_continuous.comp (hZ.const_smul s)).continuousOn hf

/-- Continuous generator words with the stated bounded profile yield an integrable full-time
error and both repeated-step profile bounds [Aftab et al., Proposition
3.14][AftabAnTrivisa2026]. -/
theorem full_time_profile_from_words
    (ws : J → List (ℝ → Matrix I I ℂ)) (a : J → ℝ) (Z : ℝ → Matrix I I ℂ)
    (f : ℝ → ℂ) (Φ : ℝ → ℝ) (Cm Rm R cap T B : ℝ) (m r : ℕ)
    (hw : ∀ j X, X ∈ ws j → Continuous X) (hZ : Continuous Z)
    (hf : IntegrableOn f (Icc (-R) R))
    (hm : AEStronglyMeasurable Φ (volume.restrict (Icc (-R) R)))
    (hn : ∀ k ∈ Icc (-R) R, 0 ≤ Φ k) (hb : ∀ k ∈ Icc (-R) R, Φ k ≤ B)
    (hCm : 0 ≤ Cm) (hRm : 0 ≤ Rm)
    (hskew : ∀ k ∈ Icc (-R) R, (Z k)ᴴ = -Z k)
    (hr : 0 < r) (hT : 0 < T) (hstep : T / r ≤ cap)
    (hlocal : ∀ k, |k| ≤ R → ∀ s, 0 < s → s ≤ cap →
      ‖multiProduct (fun j => (ws j).map (fun X => X k)) a s -
        NormedSpace.exp (s • Z k)‖ ≤ Cm * s ^ (2 * m + 1) * Φ k + Rm) :
    let C := fun k => multiProduct (fun j => (ws j).map (fun X => X k)) a (T / r)
    let η := fun k => Cm * (T / r) ^ (2 * m + 1) * Φ k + Rm
    let E := sSup (η '' Icc (-R) R)
    IntegrableOn (fun k => f k • (C k ^ r - NormedSpace.exp (T • Z k))) (Icc (-R) R) ∧
    (‖∫ k in Icc (-R) R, f k • (C k ^ r - NormedSpace.exp (T • Z k))‖ ≤
      (r : ℝ) * ∫ k in Icc (-R) R, ‖f k‖ * η k * (1 + η k) ^ (r - 1) ∧
    ‖∫ k in Icc (-R) R, f k • (C k ^ r - NormedSpace.exp (T • Z k))‖ ≤
      (1 + E) ^ (r - 1) *
        (Cm * T ^ (2 * m + 1) / (r : ℝ) ^ (2 * m) *
          (∫ k in Icc (-R) R, ‖f k‖ * Φ k) +
            (r : ℝ) * (∫ k in Icc (-R) R, ‖f k‖) * Rm)) := by
  refine ⟨?_, full_time_profile _ Z f Φ Cm Rm R cap T B m r hf hm hn hb
    hCm hRm hskew hr hT hstep hlocal⟩
  simpa only [target_power _ T r hr] using! error_integrable
    (fun k => multiProduct (fun j => (ws j).map (fun X => X k)) a (T / r))
    (fun k => NormedSpace.exp ((T / r) • Z k)) f R r
    (multiProduct_continuous ws a hw (T / r)).continuousOn
    (NormedSpace.exp_continuous.comp (hZ.const_smul (T / r))).continuousOn hf

/-- Each coefficient of an exponential word is continuous in a parameter when its generators are
continuous. -/
theorem series_continuous (ws : List (ℝ → Matrix I I ℂ))
    (hw : ∀ X ∈ ws, Continuous X) (n : ℕ) :
    Continuous (fun k => suzukiSeries (ws.map (fun X => X k)) n) := by
  induction ws generalizing n with
  | nil => cases n <;> exact continuous_const
  | cons X xs ih =>
    simp only [List.map_cons, suzukiSeries]
    apply continuous_finsetSum
    intro p _
    have hX : Continuous X := hw X (by simp)
    have hih : Continuous (fun k => suzukiSeries (xs.map (fun Y => Y k)) p.2) :=
      ih (fun Y hY => hw Y (by simp [hY])) p.2
    fun_prop

/-- The generator norm mass is continuous in the parameter for a list of continuous generator
families. -/
theorem mass_continuous (ws : List (ℝ → Matrix I I ℂ))
    (hw : ∀ X ∈ ws, Continuous X) :
    Continuous (fun k => suzukiMass (ws.map (fun X => X k))) := by
  induction ws with
  | nil => exact continuous_const
  | cons X xs ih =>
    simp only [List.map_cons, suzukiMass, List.sum_cons]
    exact (hw X (by simp)).norm.add (ih (fun Y hY => hw Y (by simp [hY])))

/-- The local coefficient error certificate is continuous when all word generators and the
target generator are continuous. -/
theorem certificate_continuous (ws : J → List (ℝ → Matrix I I ℂ)) (a : J → ℝ)
    (Z : ℝ → Matrix I I ℂ) (hw : ∀ j X, X ∈ ws j → Continuous X)
    (hZ : Continuous Z) (t : ℝ) (d : ℕ) :
    Continuous (fun k => localCertificate (fun j => (ws j).map (fun X => X k)) a (Z k) t d) := by
  have hcoeff (n : ℕ) : Continuous (fun k =>
      coefficient (fun j => (ws j).map (fun X => X k)) a n) := by
    apply continuous_finsetSum
    intro j _
    have hs := series_continuous (ws j) (hw j) n
    fun_prop
  have hmass (j : J) := mass_continuous (ws j) (hw j)
  unfold localCertificate
  apply Continuous.add
  · apply Continuous.add
    · apply continuous_finsetSum
      intro n _
      have hc := hcoeff n
      fun_prop
    · apply continuous_finsetSum
      intro j _
      fun_prop
  · fun_prop

/-- The coefficient certificate yields integrability of the full-time weighted error and an
integrated rη(1 + η)^(r - 1) bound. -/
theorem window_from_coefficients (ws : J → List (ℝ → Matrix I I ℂ)) (a : J → ℝ)
    (Z : ℝ → Matrix I I ℂ) (f : ℝ → ℂ) (R T : ℝ) (d r : ℕ)
    (hw : ∀ j X, X ∈ ws j → Continuous X) (hZ : Continuous Z)
    (hskew : ∀ k ∈ Icc (-R) R, (Z k)ᴴ = -Z k)
    (hf : IntegrableOn f (Icc (-R) R)) (hr : 0 < r) :
    let C := fun k => multiProduct (fun j => (ws j).map (fun X => X k)) a (T / r)
    let η := fun k => localCertificate (fun j => (ws j).map (fun X => X k)) a (Z k) (T / r) d
    IntegrableOn (fun k => f k • (C k ^ r - NormedSpace.exp (T • Z k))) (Icc (-R) R) ∧
    ‖∫ k in Icc (-R) R, f k • (C k ^ r - NormedSpace.exp (T • Z k))‖ ≤
      (r : ℝ) * ∫ k in Icc (-R) R, ‖f k‖ * η k * (1 + η k) ^ (r - 1) := by
  (try dsimp only)
  have hC := multiProduct_continuous ws a hw (T / r)
  have hV : Continuous (fun k => NormedSpace.exp ((T / r) • Z k)) := by fun_prop
  have hη := certificate_continuous ws a Z hw hZ (T / r) d
  have hη_pow : Continuous (fun k => localCertificate (fun j => (ws j).map (fun X => X k)) a (Z k) (T / r) d *
      (1 + localCertificate (fun j => (ws j).map (fun X => X k)) a (Z k) (T / r) d) ^ (r - 1)) := by fun_prop
  have hi := IntegrableOn.mul_continuousOn hf.norm hη_pow.continuousOn isCompact_Icc
  have h := integral_power_error
    (fun k => multiProduct (fun j => (ws j).map (fun X => X k)) a (T / r))
    (fun k => NormedSpace.exp ((T / r) • Z k)) f
    (fun k => localCertificate (fun j => (ws j).map (fun X => X k)) a (Z k) (T / r) d)
    R r (fun k hk => general_trotter_exp_unitary _ _ (hskew k hk))
    (fun k _ => local_error_from_coefficients _ a (Z k) (T / r) d)
    (by simpa only [mul_assoc] using! hi)
  simpa only [target_power _ T r hr] using!
    And.intro (error_integrable _ _ f R r hC.continuousOn hV.continuousOn hf) h

/-- The list of parameter-dependent generators for q repeated Strang steps, with X scaled by
1/(2q) and Y by 1/q. -/
def strangFamily (X Y : ℝ → Matrix I I ℂ) (q : ℕ) : List (ℝ → Matrix I I ℂ) :=
  (List.replicate q [fun k => (1 / (2 * (q : ℝ))) • X k,
    fun k => (1 / (q : ℝ)) • Y k, fun k => (1 / (2 * (q : ℝ))) • X k]).flatten

omit [Fintype I] [DecidableEq I] in

/-- Evaluating a Strang generator family at a parameter gives the repeated Strang word for the
evaluated generators. -/
theorem strangFamily_at (X Y : ℝ → Matrix I I ℂ) (q : ℕ) (k : ℝ) :
    (strangFamily X Y q).map (fun F => F k) = strangRepeats (X k) (Y k) q := by
  simp [strangFamily, strangRepeats, List.map_flatten, List.map_replicate]

omit [Fintype I] [DecidableEq I] in

/-- Every generator in a Strang family is continuous when both input matrix families are
continuous. -/
theorem strangFamily_continuous (X Y : ℝ → Matrix I I ℂ) (q : ℕ)
    (hX : Continuous X) (hY : Continuous Y) :
    ∀ F ∈ strangFamily X Y q, Continuous F := by
  intro F hF
  obtain ⟨xs, hxs, hF⟩ := List.mem_flatten.mp hF
  have he := (List.mem_replicate.mp hxs).2
  subst xs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl | rfl
  · fun_prop
  · fun_prop
  · fun_prop

/-- For b > 0, the rational-Gaussian kernel coefficient is integrable on every finite real
window. -/
theorem kernel_window_integrable (n : ℕ) (b c d R : ℝ) (hb : 0 < b) :
    IntegrableOn (fun k : ℝ => KernelStrip.coefficient n b c d (k : ℂ)) (Icc (-R) R) := by
  have hf : Continuous (fun k : ℝ => KernelStrip.coefficient n b c d (k : ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro k
    exact ((KernelStrip.coefficient_analytic n b c d (ρ := 0) (by norm_num)
      (Or.inr hb) _ (by simp)).continuousAt.comp
        (by fun_prop : ContinuousAt (fun x : ℝ => (x : ℂ)) k))
  exact hf.continuousOn.integrableOn_Icc

/-- For b > 0 and continuous generator words, the kernel-weighted full-time error is integrable
and bounded by the integral of its repeated-step coefficient certificate. -/
theorem kernel_window_from_coefficients
    (ws : J → List (ℝ → Matrix I I ℂ)) (a : J → ℝ) (Z : ℝ → Matrix I I ℂ)
    (n : ℕ) (b c d R T : ℝ) (order r : ℕ) (hb : 0 < b)
    (hw : ∀ j X, X ∈ ws j → Continuous X) (hZ : Continuous Z)
    (hskew : ∀ k ∈ Icc (-R) R, (Z k)ᴴ = -Z k) (hr : 0 < r) :
    let C := fun k => multiProduct (fun j => (ws j).map (fun X => X k)) a (T / r)
    let η := fun k => localCertificate (fun j => (ws j).map (fun X => X k)) a (Z k) (T / r) order
    IntegrableOn (fun k : ℝ => KernelStrip.coefficient n b c d (k : ℂ) •
      (C k ^ r - NormedSpace.exp (T • Z k))) (Icc (-R) R) ∧
    ‖∫ k : ℝ in Icc (-R) R, KernelStrip.coefficient n b c d (k : ℂ) •
      (C k ^ r - NormedSpace.exp (T • Z k))‖ ≤
      (r : ℝ) * ∫ k : ℝ in Icc (-R) R, ‖KernelStrip.coefficient n b c d (k : ℂ)‖ *
        η k * (1 + η k) ^ (r - 1) :=
  window_from_coefficients ws a Z _ R T order r hw hZ hskew
    (kernel_window_integrable n b c d R hb) hr

end Qatlib.Papers.CommutLCHS26.MainResults.ContinuousMPF
