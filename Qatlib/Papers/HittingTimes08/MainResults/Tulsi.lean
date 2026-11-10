/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HittingTimes08.MainResults.Comparison
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HittingTimes08.MainResults

open scoped BigOperators

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x

structure TulsiData (A : Type*) [Fintype A] [DecidableEq A] where

  W : A → ℝ
  W_pos : ∀ a, 0 < W a

  alpha : A → ℝ
  alpha_pos : ∀ a, 0 < alpha a

  a0 : ℝ
  a0_ne : a0 ≠ 0

  theta : ℝ

  mu : A → ℂ

  phi : A → ℂ

  inner_mu : ∀ a, ∑ b, (if b = a then (1 : ℂ) else 0) * mu b * (W b : ℂ) = 1

  inner_phi : ∀ a, ∑ b, (if b = a then (1 : ℂ) else 0) * phi b * (W b : ℂ)
      = Complex.I * (a0 : ℂ) * (cot (alpha a / 2) : ℂ)

  Wt : A → ℝ
  Wt_pos : ∀ a, 0 < Wt a

  alphaT : A → ℝ
  alphaT_pos : ∀ a, 0 < alphaT a

  target : A → ℂ

  phiTheta : A → ℂ

  inner_target : ∀ a, ∑ b, (if b = a then (1 : ℂ) else 0) * target b * (Wt b : ℂ) = 1

  inner_phiTheta : ∀ a, ∑ b, (if b = a then (1 : ℂ) else 0) * phiTheta b * (Wt b : ℂ)
      = Complex.I * (a0 : ℂ) * (Real.cos theta : ℂ) * (cot (alphaT a / 2) : ℂ)

namespace TulsiData

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem lemma_4_1 (D : TulsiData A) :
    (∀ a, D.mu a = (1 : ℂ) / (D.W a : ℂ)) ∧
      (∀ a, D.phi a =
        (Complex.I * (D.a0 : ℂ) * (cot (D.alpha a / 2) : ℂ)) / (D.W a : ℂ)) := by
  constructor
  · intro a
    have hsum : ∑ b, (if b = a then (1 : ℂ) else 0) * D.mu b * (D.W b : ℂ)
        = D.mu a * (D.W a : ℂ) := by simp
    have h := D.inner_mu a
    rw [hsum] at h
    have hW : (D.W a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (D.W_pos a))
    rw [eq_div_iff hW]
    simpa using h
  · intro a
    have hsum : ∑ b, (if b = a then (1 : ℂ) else 0) * D.phi b * (D.W b : ℂ)
        = D.phi a * (D.W a : ℂ) := by simp
    have h := D.inner_phi a
    rw [hsum] at h
    have hW : (D.W a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (D.W_pos a))
    rw [eq_div_iff hW]
    simpa using h

theorem corollary_4_5 (D : TulsiData A) :
    (∀ a, D.target a = (1 : ℂ) / (D.Wt a : ℂ)) ∧
      (∀ a, D.phiTheta a =
        (Complex.I * (D.a0 : ℂ) * (Real.cos D.theta : ℂ) *
            (cot (D.alphaT a / 2) : ℂ)) / (D.Wt a : ℂ)) := by
  constructor
  · intro a
    have hsum : ∑ b, (if b = a then (1 : ℂ) else 0) * D.target b * (D.Wt b : ℂ)
        = D.target a * (D.Wt a : ℂ) := by simp
    have h := D.inner_target a
    rw [hsum] at h
    have hW : (D.Wt a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (D.Wt_pos a))
    rw [eq_div_iff hW]
    simpa using h
  · intro a
    have hsum : ∑ b, (if b = a then (1 : ℂ) else 0) * D.phiTheta b * (D.Wt b : ℂ)
        = D.phiTheta a * (D.Wt a : ℂ) := by simp
    have h := D.inner_phiTheta a
    rw [hsum] at h
    have hW : (D.Wt a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (D.Wt_pos a))
    rw [eq_div_iff hW]
    simpa using h

end TulsiData

end Qatlib.Papers.HittingTimes08.MainResults
