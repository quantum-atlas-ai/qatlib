/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabLimit07.MainResults.ProbabilityFlow
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AdiabLimit07.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath
open scoped BigOperators Matrix

variable {n : ℕ}

theorem sub_le_of_deriv_bound {p : ℝ → ℝ} {T B : ℝ} (hT : 0 ≤ T)
    (hdiff : ∀ t ∈ Set.Icc 0 T, DifferentiableAt ℝ p t)
    (hbound : ∀ t ∈ Set.Icc 0 T, |deriv p t| ≤ B) :
    p T - p 0 ≤ B * T := by
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) T) := convex_Icc _ _
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Icc (0 : ℝ) T)
    (f := p) (C := B) hdiff
    (fun t ht => by rw [Real.norm_eq_abs]; exact hbound t ht) hconv
    (Set.left_mem_Icc.mpr hT) (Set.right_mem_Icc.mpr hT)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg hT] at h
  exact (le_abs_self (p T - p 0)).trans h

theorem runtime_lower_bound {p : ℝ → ℝ} {T B c p0 : ℝ} (hT : 0 ≤ T) (hB : 0 < B)
    (hdiff : ∀ t ∈ Set.Icc 0 T, DifferentiableAt ℝ p t)
    (hbound : ∀ t ∈ Set.Icc 0 T, |deriv p t| ≤ B)
    (hp0 : p 0 = p0) (hpT : c ≤ p T) :
    (c - p0) / B ≤ T := by
  have hsub := sub_le_of_deriv_bound hT hdiff hbound
  rw [hp0] at hsub
  have hc : c - p0 ≤ p T - p0 := by linarith
  have hle : c - p0 ≤ B * T := hc.trans hsub
  rw [div_le_iff₀ hB]
  linarith

theorem runtime_lower_bound_eq21 {p : ℝ → ℝ} {T c : ℝ} {cardP0 maxF compDim : ℝ}
    {N : ℝ} (hN : 0 < N) (hT : 0 ≤ T) (hcard : 0 < cardP0) (hmaxF : 0 < maxF)
    (hcomp : 0 < compDim) (hsq : Real.sqrt N ^ 2 = N)
    (hdiff : ∀ t ∈ Set.Icc 0 T, DifferentiableAt ℝ p t)
    (hbound : ∀ t ∈ Set.Icc 0 T,
      |deriv p t| ≤ 2 * cardP0 * maxF * compDim / Real.sqrt N)
    (hp0 : p 0 = cardP0 / N) (hpT : c ≤ p T) :
    (c * Real.sqrt N - cardP0 / Real.sqrt N) / (2 * cardP0 * maxF * compDim) ≤ T := by
  have hsqrtpos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hB : 0 < 2 * cardP0 * maxF * compDim / Real.sqrt N := by positivity
  have hmain := runtime_lower_bound hT hB hdiff hbound hp0 hpT

  have hrewrite :
      (c - cardP0 / N) / (2 * cardP0 * maxF * compDim / Real.sqrt N)
        = (c * Real.sqrt N - cardP0 / Real.sqrt N) / (2 * cardP0 * maxF * compDim) := by
    have hNpos : N ≠ 0 := ne_of_gt hN
    field_simp
    nlinarith [hsq]
  rwa [hrewrite] at hmain

theorem runtime_lower_bound_eq21_initialUniform {q p : ℕ}
    (F : Fin (q + 1) → ℝ) (qIdx : Reg n → Fin (q + 1))
    (E : Fin (p + 1) → ℝ) (pIdx : Reg n → Fin (p + 1)) (K : Fin (q + 1))
    (hmono : ∀ a b : Fin (q + 1), a ≤ b → F a ≤ F b)
    (hF0 : 0 ≤ F 0) (maxF : ℝ) (hmax : ∀ k, F k ≤ maxF)
    (s : ℝ → ℝ) (hs0 : ∀ t, 0 ≤ s t) (hs1 : ∀ t, s t ≤ 1)
    (ψ : ℝ → QState (Reg n)) (T c : ℝ) (hT : 0 ≤ T)
    (hSchrod : SchrodingerIVP
      (fun t => genHamiltonian (s t) (hadamardHamiltonian F qIdx)
        (computationalHamiltonian E pIdx)) ψ T)
    (hψnorm : ∀ t ∈ Set.Icc 0 T, Normalized (ψ t))
    (hcard : 0 < ((solutionSet pIdx).card : ℝ)) (hmaxF : 0 < maxF)
    (hcomp : 0 < eigenspaceComplementDim qIdx K)
    (hinit : InitialUniform ψ) (hpT : c ≤ solutionProb pIdx (ψ T)) :
    (c * Real.sqrt (((2 : ℕ) ^ n : ℝ)) - ((solutionSet pIdx).card : ℝ) /
        Real.sqrt (((2 : ℕ) ^ n : ℝ))) /
      (2 * ((solutionSet pIdx).card : ℝ) * maxF * eigenspaceComplementDim qIdx K) ≤ T := by
  have hp0 : solutionProb pIdx (ψ 0) =
      ((solutionSet pIdx).card : ℝ) / (((2 : ℕ) ^ n : ℝ)) := by
    rw [InitialUniform] at hinit
    rw [hinit]
    exact solutionProb_initialUniform pIdx
  refine runtime_lower_bound_eq21
    (p := fun u => solutionProb pIdx (ψ u)) (T := T) (c := c)
    (cardP0 := ((solutionSet pIdx).card : ℝ)) (maxF := maxF)
    (compDim := eigenspaceComplementDim qIdx K) (N := ((2 : ℕ) ^ n : ℝ))
    (by positivity) hT hcard hmaxF hcomp (Real.sq_sqrt (by positivity)) ?_ ?_ hp0 hpT
  · intro t ht
    exact (hasDerivAt_solutionProb pIdx hSchrod ht).differentiableAt
  · exact probability_flow_bound F qIdx E pIdx K hmono hF0 maxF hmax s hs0 hs1
      ψ T hSchrod hψnorm

end Qatlib.Papers.AdiabLimit07.MainResults
