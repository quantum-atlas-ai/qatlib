/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Concepts.AmpTransform.ErrorStream.Lemma20RestrictedStat

open Qatlib.Concepts.AmpTransform.ErrorStream.Lemma20RestrictedSpec

namespace Qatlib.Concepts.AmpTransform.ErrorStream

open scoped BigOperators

theorem zoo_amplified_qft_lemma20_omega_norm (N k : ℕ) :
    ‖amplifiedQFTOmega N ^ k‖ = 1 := by
  have h : ‖amplifiedQFTOmega N‖ = 1 := by
    have key : amplifiedQFTOmega N =
        Complex.exp ((((-2 * Real.pi / (N : ℝ)) : ℝ) : ℂ) * Complex.I) := by
      unfold amplifiedQFTOmega
      norm_cast
    rw [key]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [norm_pow, h, one_pow]

theorem zoo_amplified_qft_lemma20_norm_sum_le_card (G : Finset ℕ) (f : ℕ → ℂ)
    (hf : ∀ z ∈ G, ‖f z‖ = 1) : ‖∑ z ∈ G, f z‖ ≤ (G.card : ℝ) := by
  calc ‖∑ z ∈ G, f z‖ ≤ ∑ z ∈ G, ‖f z‖ := norm_sum_le G f
    _ = ∑ _z ∈ G, (1 : ℝ) := Finset.sum_congr rfl fun z hz => hf z hz
    _ = (G.card : ℝ) := by simp

theorem zoo_amplified_qft_lemma20 (n N M L T s P y : ℕ) (A G : Finset ℕ)
    (hN : N = 2 ^ n)
    (hA : A = (Finset.range M).image (fun r => s + r * P))
    (hA_sub : A ⊆ Finset.range N)
    (hG_sub : G ⊆ Finset.range N)
    (hA_card : A.card = M)
    (hG_card : G.card = L)
    (hdisj : Disjoint A G)
    (hT : T = M + L)
    (hTpos : 0 < T)
    (hy : y < N)
    (hy0 : y ≠ 0)
    (hcyc : (P * y) % N = 0) :
    ‖(M : ℂ) / (T : ℂ) * amplifiedQFTOmega N ^ (s * y) +
      (1 : ℂ) / (T : ℂ) *
        (∑ z ∈ G, amplifiedQFTOmega N ^ (z * y))‖ ^ 2 ≤ (1 : ℝ) := by
  have hTposℝ : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hTpos
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTposℝ

  have ha : ‖(M : ℂ) / (T : ℂ) * amplifiedQFTOmega N ^ (s * y)‖
      = (M : ℝ) / (T : ℝ) := by
    rw [norm_mul, norm_div, zoo_amplified_qft_lemma20_omega_norm, mul_one,
      RCLike.norm_natCast, RCLike.norm_natCast]

  have hb : ‖(1 : ℂ) / (T : ℂ) * (∑ z ∈ G, amplifiedQFTOmega N ^ (z * y))‖
      ≤ (L : ℝ) / (T : ℝ) := by
    have hsum : ‖∑ z ∈ G, amplifiedQFTOmega N ^ (z * y)‖ ≤ (G.card : ℝ) :=
      zoo_amplified_qft_lemma20_norm_sum_le_card G _ fun z _ =>
        zoo_amplified_qft_lemma20_omega_norm N (z * y)
    have hGL : (G.card : ℝ) = (L : ℝ) := by exact_mod_cast hG_card
    rw [norm_mul, norm_div, norm_one, RCLike.norm_natCast]
    calc (1 : ℝ) / (T : ℝ) * ‖∑ z ∈ G, amplifiedQFTOmega N ^ (z * y)‖
        ≤ (1 : ℝ) / (T : ℝ) * (L : ℝ) :=
          mul_le_mul_of_nonneg_left (hsum.trans hGL.le) (by positivity)
      _ = (L : ℝ) / (T : ℝ) := by ring

  have hbound : ‖(M : ℂ) / (T : ℂ) * amplifiedQFTOmega N ^ (s * y) +
      (1 : ℂ) / (T : ℂ) * (∑ z ∈ G, amplifiedQFTOmega N ^ (z * y))‖ ≤ 1 := by
    have hT' : (T : ℝ) = (M : ℝ) + (L : ℝ) := by exact_mod_cast hT
    calc ‖(M : ℂ) / (T : ℂ) * amplifiedQFTOmega N ^ (s * y) +
            (1 : ℂ) / (T : ℂ) * (∑ z ∈ G, amplifiedQFTOmega N ^ (z * y))‖
        ≤ ‖(M : ℂ) / (T : ℂ) * amplifiedQFTOmega N ^ (s * y)‖ +
            ‖(1 : ℂ) / (T : ℂ) * (∑ z ∈ G, amplifiedQFTOmega N ^ (z * y))‖ :=
          norm_add_le _ _
      _ ≤ (M : ℝ) / (T : ℝ) + (L : ℝ) / (T : ℝ) := add_le_add ha.le hb
      _ = ((M : ℝ) + (L : ℝ)) / (T : ℝ) := (add_div _ _ _).symm
      _ = (T : ℝ) / (T : ℝ) := by rw [← hT']
      _ = 1 := div_self hTne

  have hnn : 0 ≤ ‖(M : ℂ) / (T : ℂ) * amplifiedQFTOmega N ^ (s * y) +
      (1 : ℂ) / (T : ℂ) * (∑ z ∈ G, amplifiedQFTOmega N ^ (z * y))‖ :=
    norm_nonneg _
  nlinarith [hbound, hnn]

example :
    Lemma20RestrictedSpec.expected :=
  zoo_amplified_qft_lemma20

end Qatlib.Concepts.AmpTransform.ErrorStream
