/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Quaternion
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Qatlib.Concepts.UnbiasedBases.ThreeBasis.EulerDecomposition
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

open scoped Quaternion
open Quaternion
open Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo
open Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo.SU2
open Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo.Euler

namespace Qatlib.Papers.AnyonicSpin06.MainResults.SU2Euler

def Iq : ℍ[ℝ] := ⟨0, 1, 0, 0⟩

def Jq : ℍ[ℝ] := ⟨0, 0, 1, 0⟩

def expq (θ : ℝ) : ℍ[ℝ] := (Real.cos θ : ℍ[ℝ]) + (Real.sin θ : ℍ[ℝ]) * Iq

def expqJ (θ : ℝ) : ℍ[ℝ] := (Real.cos θ : ℍ[ℝ]) + (Real.sin θ : ℍ[ℝ]) * Jq

def expUnit (θ : ℝ) (u : ℍ[ℝ]) : ℍ[ℝ] :=
  (Real.cos θ : ℍ[ℝ]) + (Real.sin θ : ℍ[ℝ]) * u

theorem euler_identity (a b c : ℝ) :
    expq a * expqJ b * expq c
      = (Real.cos b : ℍ[ℝ]) * expq (a + c)
          + (Real.sin b : ℍ[ℝ]) * (expq (a - c) * Jq) := by
  ext <;> simp only [expq, expqJ, Iq, Jq, re_mul, imI_mul, imJ_mul, imK_mul,
    re_add, imI_add, imJ_add, imK_add, re_coe, imI_coe, imJ_coe, imK_coe,
    Real.cos_add, Real.sin_add, Real.cos_sub, Real.sin_sub] <;> ring

theorem exists_euler_rz_ry_rz {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hdet : U.det = 1) :
    ∃ β γ δ : ℝ, U = rzMat β * ryMat γ * rzMat δ :=
  exists_euler_of_det_one hU hdet

theorem rz_ry_rz_matrix_form (β γ δ : ℝ) :
    rzMat β * ryMat γ * rzMat δ =
      !![expI (-((β + δ) / 2)) * (Real.cos (γ / 2) : ℂ),
          -(expI (-((β - δ) / 2)) * (Real.sin (γ / 2) : ℂ));
         expI ((β - δ) / 2) * (Real.sin (γ / 2) : ℂ),
          expI ((β + δ) / 2) * (Real.cos (γ / 2) : ℂ)] :=
  rz_ry_rz_eq β γ δ

lemma exists_cos_sin_of_sq_add_one {u v : ℝ} (h : u ^ 2 + v ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = u ∧ Real.sin θ = v := by
  have hu_le : u ≤ 1 := by nlinarith [sq_nonneg v, sq_nonneg (u - 1)]
  have hu_ge : -1 ≤ u := by nlinarith [sq_nonneg v, sq_nonneg (u + 1)]
  have hsq : 1 - u ^ 2 = v ^ 2 := by linarith
  have hsqrt : Real.sqrt (1 - u ^ 2) = |v| := by
    rw [hsq, Real.sqrt_sq_eq_abs]
  by_cases hv : 0 ≤ v
  · refine ⟨Real.arccos u, Real.cos_arccos hu_ge hu_le, ?_⟩
    rw [Real.sin_arccos, hsqrt, abs_of_nonneg hv]
  · rw [not_le] at hv
    refine ⟨-Real.arccos u, ?_, ?_⟩
    · rw [Real.cos_neg, Real.cos_arccos hu_ge hu_le]
    · rw [Real.sin_neg, Real.sin_arccos, hsqrt, abs_of_neg hv]; ring

lemma exists_mul_cos_sin {p u v : ℝ} (hp : 0 ≤ p) (h : p ^ 2 = u ^ 2 + v ^ 2) :
    ∃ θ : ℝ, p * Real.cos θ = u ∧ p * Real.sin θ = v := by
  rcases eq_or_lt_of_le hp with hp0 | hpos
  · subst hp0
    have hu : u = 0 := by nlinarith [h, sq_nonneg u, sq_nonneg v]
    have hv : v = 0 := by nlinarith [h, sq_nonneg u, sq_nonneg v]
    exact ⟨0, by simp [hu], by simp [hv]⟩
  · have hpne : p ≠ 0 := ne_of_gt hpos
    have h1 : (u / p) ^ 2 + (v / p) ^ 2 = 1 := by
      rw [div_pow, div_pow, ← add_div, ← h]
      exact div_self (pow_ne_zero 2 hpne)
    obtain ⟨θ, hc, hs⟩ := exists_cos_sin_of_sq_add_one h1
    refine ⟨θ, ?_, ?_⟩
    · rw [hc]; field_simp
    · rw [hs]; field_simp

theorem exists_euler_angles (q : ℍ[ℝ]) (hq : normSq q = 1) :
    ∃ a b c : ℝ, q = expq a * expqJ b * expq c := by
  obtain ⟨w, x, y, z⟩ := q
  rw [Quaternion.normSq_def'] at hq
  set p : ℝ := Real.sqrt (w ^ 2 + x ^ 2) with hpdef
  set s : ℝ := Real.sqrt (y ^ 2 + z ^ 2) with hsdef
  have hpnn : 0 ≤ p := Real.sqrt_nonneg _
  have hsnn : 0 ≤ s := Real.sqrt_nonneg _
  have hp2 : p ^ 2 = w ^ 2 + x ^ 2 := by
    rw [hpdef, Real.sq_sqrt (by positivity)]
  have hs2 : s ^ 2 = y ^ 2 + z ^ 2 := by
    rw [hsdef, Real.sq_sqrt (by positivity)]
  have hps : p ^ 2 + s ^ 2 = 1 := by rw [hp2, hs2]; linarith
  obtain ⟨b, hbcos, hbsin⟩ := exists_cos_sin_of_sq_add_one hps
  obtain ⟨t1, hc1, hs1⟩ := exists_mul_cos_sin hpnn hp2
  obtain ⟨t2, hc2, hs2'⟩ := exists_mul_cos_sin hsnn hs2
  refine ⟨(t1 + t2) / 2, b, (t1 - t2) / 2, ?_⟩
  rw [euler_identity]
  have h1 : (t1 + t2) / 2 + (t1 - t2) / 2 = t1 := by ring
  have h2 : (t1 + t2) / 2 - (t1 - t2) / 2 = t2 := by ring
  rw [h1, h2]
  ext <;> simp only [expq, Iq, Jq, re_mul, imI_mul, imJ_mul, imK_mul,
    re_add, imI_add, imJ_add, imK_add, re_coe, imI_coe, imJ_coe, imK_coe] <;>
    simp only [hbcos, hbsin] <;> ring_nf <;> nlinarith [hc1, hs1, hc2, hs2']

def EulerTwoAxis : Prop :=
  ∀ (u v : ℍ[ℝ]), u.re = 0 → v.re = 0 → normSq u = 1 → normSq v = 1 →
    u ≠ v → u ≠ -v →
    ∀ q : ℍ[ℝ], normSq q = 1 →
      ∃ a b c : ℝ, q = expUnit a u * expUnit b v * expUnit c u

end Qatlib.Papers.AnyonicSpin06.MainResults.SU2Euler
