/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Concepts.AmpTransform.ErrorStream.Lemma16Stat

open Qatlib.Concepts.AmpTransform.ErrorStream.Lemma16Spec

namespace Qatlib.Concepts.AmpTransform.ErrorStream

open Real

private theorem amplified_qft_lemma16_aux
    {N T θ : ℝ} (hN : 0 < N) (hT : 0 < T) (hTN : T < N)
    (hθ : θ = Real.arcsin (Real.sqrt (T / N))) (x : ℝ) :
    (T / Real.sqrt N) * (Real.sin x / Real.sqrt T - Real.cos x / Real.sqrt (N - T)) =
      Real.tan θ * Real.sin (x - θ) := by
  have hTNdiv : 0 < T / N := div_pos hT hN
  have hlt1 : T / N < 1 := by
    rw [div_lt_one hN]
    exact hTN
  have hsqrt_le : Real.sqrt (T / N) ≤ 1 := by
    have h := Real.sqrt_le_sqrt hlt1.le
    rwa [Real.sqrt_one] at h

  have hs : Real.sin θ = Real.sqrt (T / N) := by
    rw [hθ]
    exact Real.sin_arcsin (by have h := Real.sqrt_nonneg (T / N); linarith) hsqrt_le
  have hlt1' : 0 < 1 - T / N := sub_pos.2 hlt1
  have hc2 : Real.cos θ ^ 2 = 1 - T / N := by
    rw [Real.cos_sq', hs, Real.sq_sqrt hTNdiv.le]
  have hcc : Real.cos θ * Real.cos θ = 1 - T / N := by
    rw [← pow_two]
    exact hc2
  have hcpos : 0 < Real.cos θ := by
    rw [hθ, Real.cos_arcsin, Real.sq_sqrt hTNdiv.le]
    exact Real.sqrt_pos.2 hlt1'
  have hss : Real.sin θ * Real.sin θ = T / N := by
    rw [hs]
    exact Real.mul_self_sqrt hTNdiv.le
  have hs_nonneg : 0 ≤ Real.sin θ := by
    rw [hs]
    exact Real.sqrt_nonneg _

  have hsc : Real.sqrt (T / (N - T)) = Real.sin θ / Real.cos θ := by
    rw [Real.sqrt_eq_iff_mul_self_eq (div_nonneg hT.le (sub_pos.2 hTN).le)
      (div_nonneg hs_nonneg hcpos.le)]
    rw [div_mul_div_comm, hss, hcc]
    have hNne : (N : ℝ) ≠ 0 := hN.ne'
    have h1ne : 1 - T / N ≠ 0 := hlt1'.ne'
    have hNTne : N - T ≠ 0 := (sub_pos.2 hTN).ne'
    field_simp

  have hcoef1 : T / Real.sqrt N / Real.sqrt T = Real.sin θ := by
    have hTne : Real.sqrt T ≠ 0 := (Real.sqrt_pos.2 hT).ne'
    have h1 : T / Real.sqrt T = Real.sqrt T :=
      (div_eq_iff hTne).2 (Real.mul_self_sqrt hT.le).symm
    rw [div_right_comm, h1, hs, Real.sqrt_div hT.le N]

  have hkey : T / Real.sqrt N / Real.sqrt (N - T) =
      Real.sqrt (T / N) * Real.sqrt (T / (N - T)) := by
    rw [Real.sqrt_div hT.le N, Real.sqrt_div hT.le (N - T), div_mul_div_comm,
      Real.mul_self_sqrt hT.le, ← div_div]
  have hcoef2 : T / Real.sqrt N / Real.sqrt (N - T) =
      Real.sin θ * (Real.sin θ / Real.cos θ) := by
    rw [hkey, hsc, ← hs]

  calc (T / Real.sqrt N) * (Real.sin x / Real.sqrt T - Real.cos x / Real.sqrt (N - T))
      = (T / Real.sqrt N / Real.sqrt T) * Real.sin x
        - (T / Real.sqrt N / Real.sqrt (N - T)) * Real.cos x := by ring
    _ = Real.sin θ * Real.sin x
        - Real.sin θ * (Real.sin θ / Real.cos θ) * Real.cos x := by
        rw [hcoef1, hcoef2]
    _ = Real.tan θ * (Real.sin x * Real.cos θ - Real.cos x * Real.sin θ) := by
        rw [Real.tan_eq_sin_div_cos]
        have hc : Real.cos θ ≠ 0 := hcpos.ne'
        field_simp
    _ = Real.tan θ * Real.sin (x - θ) := by
        rw [Real.sin_sub]

theorem amplified_qft_lemma16 :
    ∀ (n L M : ℕ), 0 < L + M → L + M < 2 ^ n →
      let N : ℝ := ((2 ^ n : ℕ) : ℝ)
      let T : ℝ := ((L + M : ℕ) : ℝ)
      let θ : ℝ := Real.arcsin (Real.sqrt (T / N))
      let k : ℕ := Nat.floor (Real.pi / (4 * θ))
      let a_k : ℝ := Real.sin ((2 * (k : ℝ) + 1) * θ) / Real.sqrt T
      let b_k : ℝ := Real.cos ((2 * (k : ℝ) + 1) * θ) / Real.sqrt (N - T)
      (T / Real.sqrt N) * (a_k - b_k) =
        Real.tan θ * Real.sin (2 * (k : ℝ) * θ) := by
  intro n L M hpos hlt N T θ k a_k b_k
  have hN : (0 : ℝ) < N := by
    have h : (0 : ℕ) < 2 ^ n := by positivity
    show (0 : ℝ) < ((2 ^ n : ℕ) : ℝ)
    exact_mod_cast h
  have hT : (0 : ℝ) < T := by
    show (0 : ℝ) < ((L + M : ℕ) : ℝ)
    exact_mod_cast hpos
  have hTN : T < N := by
    show ((L + M : ℕ) : ℝ) < ((2 ^ n : ℕ) : ℝ)
    exact_mod_cast hlt
  show (T / Real.sqrt N) * (Real.sin ((2 * (k : ℝ) + 1) * θ) / Real.sqrt T
        - Real.cos ((2 * (k : ℝ) + 1) * θ) / Real.sqrt (N - T))
      = Real.tan θ * Real.sin (2 * (k : ℝ) * θ)
  have e : (2 * (k : ℝ) * θ) = (2 * (k : ℝ) + 1) * θ - θ := by ring
  rw [e]
  exact amplified_qft_lemma16_aux hN hT hTN rfl _

theorem amplified_qft_lemma16_contract :
    Lemma16Spec.expected :=
  amplified_qft_lemma16

end Qatlib.Concepts.AmpTransform.ErrorStream
