/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NativeNumerics.NlfftPipeline.NonlinearFourierSU2
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.NativeNumerics.NlfftPipeline

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.FiniteLocc.LOCCProgram.LayerStrippingCertifiedStability

open Polynomial Qatlib

noncomputable def layerC (γ : ℂ) : ℂ :=
  (((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)

private theorem norm_ofReal' (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by
  rw [Complex.norm_real, Real.norm_eq_abs]

theorem layerC_ne_zero (γ : ℂ) : layerC γ ≠ 0 := by
  have hpos : (0 : ℝ) < 1 + Complex.normSq γ :=
    add_pos_of_pos_of_nonneg zero_lt_one (Complex.normSq_nonneg γ)
  intro h0
  have hinv : ((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) = 0 :=
    Complex.ofReal_injective h0
  rw [inv_eq_zero, Real.sqrt_eq_zero (by positivity : (0 : ℝ) ≤ 1 + Complex.normSq γ)] at hinv
  linarith

theorem layerC_norm_le_one (γ : ℂ) : ‖layerC γ‖ ≤ 1 := by
  have hpos : (0 : ℝ) < 1 + Complex.normSq γ :=
    add_pos_of_pos_of_nonneg zero_lt_one (Complex.normSq_nonneg γ)
  have h1 : (1 : ℝ) ≤ Real.sqrt (1 + Complex.normSq γ) := by
    have h2 : Real.sqrt (1 : ℝ) ≤ Real.sqrt (1 + Complex.normSq γ) :=
      Real.sqrt_le_sqrt (by have := Complex.normSq_nonneg γ; linarith)
    rwa [Real.sqrt_one] at h2
  rw [layerC, norm_ofReal', abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact (inv_le_one₀ (Real.sqrt_pos.mpr hpos)).mpr h1

private theorem real_invSqrt_lipschitz (s t : ℝ) :
    |(Real.sqrt (1 + s ^ 2))⁻¹ - (Real.sqrt (1 + t ^ 2))⁻¹| ≤ |s - t| := by
  have hs2 : (0 : ℝ) ≤ s ^ 2 := sq_nonneg s
  have ht2 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  set u : ℝ := Real.sqrt (1 + s ^ 2) with hu
  set v : ℝ := Real.sqrt (1 + t ^ 2) with hv
  have hu2 : u ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (by positivity)
  have hv2 : v ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hu1 : (1 : ℝ) ≤ u := by nlinarith
  have hv1 : (1 : ℝ) ≤ v := by nlinarith
  have habs_s : |s| ≤ u := by
    have hss : |s| * |s| = s * s := abs_mul_abs_self s
    nlinarith
  have habs_t : |t| ≤ v := by
    have htt : |t| * |t| = t * t := abs_mul_abs_self t
    nlinarith
  have hsub : |v - u| ≤ |s - t| := by
    have hchain : |v - u| * (u + v) = |s - t| * |t + s| := by
      have e : (v - u) * (u + v) = (t - s) * (t + s) := by
        have e' : v * v - u * u = t * t - s * s := by nlinarith [hv2, hu2]
        linear_combination e'
      calc |v - u| * (u + v) = |(v - u) * (u + v)| := by
            rw [abs_mul, abs_of_nonneg (add_nonneg hu0 hv0)]
        _ = |(t - s) * (t + s)| := by rw [e]
        _ = |t - s| * |t + s| := abs_mul _ _
        _ = |s - t| * |t + s| := by
            rw [show (t - s : ℝ) = -(s - t) from by ring, abs_neg]
    have h2 : |t + s| ≤ u + v := by
      have ha := abs_add_le t s
      linarith
    have h3 : |s - t| * |t + s| ≤ |s - t| * (u + v) :=
      mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    have huvpos : (0 : ℝ) < u + v := by linarith
    by_contra hcontra
    push Not at hcontra
    have hgt : |s - t| * (u + v) < |v - u| * (u + v) :=
      mul_lt_mul_of_pos_right hcontra huvpos
    have h4 : |v - u| * (u + v) ≤ |s - t| * (u + v) := le_trans (le_of_eq hchain) h3
    linarith
  have huvpos2 : (0 : ℝ) < u * v := by nlinarith [hu1, hv1]
  have hfrac : |u⁻¹ - v⁻¹| = |v - u| / (u * v) := by
    have he : u⁻¹ - v⁻¹ = (v - u) / (u * v) := by
      field_simp
    rw [he, abs_div, abs_of_pos huvpos2]
  have huv1 : (1 : ℝ) ≤ u * v := by nlinarith
  rw [hfrac]
  have habsnonneg : (0 : ℝ) ≤ |v - u| := abs_nonneg _
  have hdivle : |v - u| / (u * v) ≤ |v - u| := by
    rw [div_le_iff₀ huvpos2]
    nlinarith
  exact le_trans hdivle hsub

theorem layerC_lipschitz (γ δ : ℂ) : ‖layerC γ - layerC δ‖ ≤ ‖γ - δ‖ := by
  rw [layerC, layerC, ← Complex.ofReal_sub, norm_ofReal',
    Complex.normSq_eq_norm_sq γ, Complex.normSq_eq_norm_sq δ]
  exact le_trans (real_invSqrt_lipschitz ‖γ‖ ‖δ‖) (abs_norm_sub_norm_le γ δ)

noncomputable def certRefA (γ : ℂ) (A B : Polynomial ℂ) : Polynomial ℂ :=
  layerC γ • (A + (starRingEnd ℂ γ) • B)

noncomputable def certRefB (γ : ℂ) (A B : Polynomial ℂ) : Polynomial ℂ :=
  layerC γ • (B - γ • A).divX

theorem certRefA_coeff (γ : ℂ) (A B : Polynomial ℂ) (i : ℕ) :
    (certRefA γ A B).coeff i
      = layerC γ * (A.coeff i + (starRingEnd ℂ γ) * B.coeff i) := by
  simp [certRefA, coeff_smul, coeff_add, smul_eq_mul, mul_add]

theorem certRefB_coeff (γ : ℂ) (A B : Polynomial ℂ) (i : ℕ) :
    (certRefB γ A B).coeff i
      = layerC γ * (B.coeff (i + 1) - γ * A.coeff (i + 1)) := by
  simp [certRefB, coeff_smul, Polynomial.coeff_divX, coeff_sub, smul_eq_mul]

theorem certRefA_eq_step (A B : Polynomial ℂ) :
    certRefA (B.coeff 0 / A.coeff 0) A B = (layerStripStepSU2 A B).2.1 := rfl

theorem certRefB_eq_step (A B : Polynomial ℂ) :
    certRefB (B.coeff 0 / A.coeff 0) A B = (layerStripStepSU2 A B).2.2 := rfl

noncomputable def idealPair (A B : Polynomial ℂ) (k : ℕ) :
    Polynomial ℂ × Polynomial ℂ :=
  ((layerStripSU2 A B k).finalA, (layerStripSU2 A B k).finalB)

noncomputable def idealGamma (A B : Polynomial ℂ) (k : ℕ) : ℂ :=
  (idealPair A B k).2.coeff 0 / (idealPair A B k).1.coeff 0

noncomputable def stepPair (P : Polynomial ℂ × Polynomial ℂ) :
    Polynomial ℂ × Polynomial ℂ :=
  ((layerStripStepSU2 P.1 P.2).2.1, (layerStripStepSU2 P.1 P.2).2.2)

theorem idealPair_zero (A B : Polynomial ℂ) : idealPair A B 0 = (A, B) := rfl

theorem idealPair_succ (A B : Polynomial ℂ) (k : ℕ) :
    idealPair A B (k + 1) = stepPair (idealPair A B k) := by
  induction k generalizing A B with
  | zero => rfl
  | succ k ih =>
    have h1 : idealPair A B (k + 2)
        = idealPair (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (k + 1) := rfl
    have h2 : idealPair (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 k
        = idealPair A B (k + 1) := rfl
    rw [h1, ih (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2, h2]

private theorem idealPair_step (A B : Polynomial ℂ) (k : ℕ) :
    idealPair (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 k
      = idealPair A B (k + 1) := rfl

private theorem idealGamma_step (A B : Polynomial ℂ) (k : ℕ) :
    idealGamma (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 k
      = idealGamma A B (k + 1) := by
  simp only [idealGamma]
  rw [idealPair_step]

theorem layerStrip_gammas_getD (A B : Polynomial ℂ) (n k : ℕ) (hk : k < n) :
    (layerStripSU2 A B n).gammas.getD k 0 = idealGamma A B k := by
  induction n generalizing A B k with
  | zero => exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k =>
      rw [show (layerStripSU2 A B (n + 1)).gammas
          = (layerStripStepSU2 A B).1
            :: (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 n).gammas
          from rfl,
        List.getD_cons_succ,
        ih (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 k (by omega)]
      rw [idealGamma_step]

structure CertStepData (η : ℝ) (A B : Polynomial ℂ) where

  γ : ℂ

  A' : Polynomial ℂ

  B' : Polynomial ℂ

  readOK : ‖γ - B.coeff 0 / A.coeff 0‖ ≤ η

  rotAOK : ∀ i, ‖A'.coeff i - (certRefA γ A B).coeff i‖ ≤ η

  rotBOK : ∀ i, ‖B'.coeff i - (certRefB γ A B).coeff i‖ ≤ η

inductive CertLayerStrip (η γc : ℝ) : Polynomial ℂ → Polynomial ℂ → Type where
  | stop (A B : Polynomial ℂ) : CertLayerStrip η γc A B
  | more (A B : Polynomial ℂ) (s : CertStepData η A B)
      (hdiv : γc ≤ ‖A.coeff 0‖)
      (rest : CertLayerStrip η γc s.A' s.B') :
      CertLayerStrip η γc A B

def certStepOpCount (m : ℕ) : ℕ := 6 * m + 5 + 2 * m + 3

namespace CertLayerStrip

def certSteps {η γc : ℝ} {A B : Polynomial ℂ} : CertLayerStrip η γc A B → ℕ
  | .stop _ _ => 0
  | .more _ _ _ _ rest => certSteps rest + 1

def certGammas {η γc : ℝ} {A B : Polynomial ℂ} : CertLayerStrip η γc A B → List ℂ
  | .stop _ _ => []
  | .more _ _ s _ rest => s.γ :: certGammas rest

def certPairAt {η γc : ℝ} {A B : Polynomial ℂ} :
    CertLayerStrip η γc A B → ℕ → Polynomial ℂ × Polynomial ℂ
  | .stop A B, _ => (A, B)
  | .more A B _ _ _, 0 => (A, B)
  | .more _ _ _ _ r, k + 1 => certPairAt r k

theorem certGammas_length {η γc : ℝ} {A B : Polynomial ℂ} (r : CertLayerStrip η γc A B) :
    r.certGammas.length = r.certSteps := by
  induction r with
  | stop _ _ => rfl
  | more _ _ s _ _ ih => simp [certGammas, certSteps, ih]

theorem certPairAt_more_succ {η γc : ℝ} (A B : Polynomial ℂ) (s : CertStepData η A B)
    (hdiv : γc ≤ ‖A.coeff 0‖) (r : CertLayerStrip η γc s.A' s.B') (k : ℕ) :
    certPairAt (CertLayerStrip.more A B s hdiv r) (k + 1) = certPairAt r k := rfl

theorem certGammas_more_getD_succ {η γc : ℝ} (A B : Polynomial ℂ) (s : CertStepData η A B)
    (hdiv : γc ≤ ‖A.coeff 0‖) (r : CertLayerStrip η γc s.A' s.B') (k : ℕ) :
    (certGammas (CertLayerStrip.more A B s hdiv r)).getD (k + 1) 0
      = (certGammas r).getD k 0 := by
  simp [certGammas]

def certOps {η γc : ℝ} {A B : Polynomial ℂ} : CertLayerStrip η γc A B → ℕ
  | .stop _ _ => 0
  | .more _ _ _ _ r => certStepOpCount (certSteps r + 1) + certOps r

theorem certOps_eq {η γc : ℝ} {A B : Polynomial ℂ} (r : CertLayerStrip η γc A B) :
    r.certOps = 4 * r.certSteps ^ 2 + 12 * r.certSteps := by
  induction r with
  | stop _ _ => simp [certOps, certSteps]
  | more _ _ s hdiv rest ih =>
    show certStepOpCount (certSteps rest + 1) + certOps rest
        = 4 * (certSteps rest + 1) ^ 2 + 12 * (certSteps rest + 1)
    rw [ih]
    simp only [certStepOpCount]
    ring

end CertLayerStrip

noncomputable def certRespBound (η γc M δ0 : ℝ) : ℕ → ℝ
  | 0 => δ0
  | k + 1 => η + (1 + M / γc + η) * certRespBound η γc M δ0 k
      + (η + 2 * M * certRespBound η γc M δ0 k / γc ^ 2) * (2 * M + M ^ 2 / γc)

noncomputable def certPhaseBound (η γc M δ0 : ℝ) (k : ℕ) : ℝ :=
  η + 2 * M * certRespBound η γc M δ0 k / γc ^ 2

theorem certRespBound_shift (η γc M δ0 : ℝ) (k : ℕ) :
    certRespBound η γc M (certRespBound η γc M δ0 1) k
      = certRespBound η γc M δ0 (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    calc certRespBound η γc M (certRespBound η γc M δ0 1) (k + 1)
        = η + (1 + M / γc + η) * certRespBound η γc M (certRespBound η γc M δ0 1) k
            + (η + 2 * M * certRespBound η γc M (certRespBound η γc M δ0 1) k / γc ^ 2)
              * (2 * M + M ^ 2 / γc) := rfl
      _ = η + (1 + M / γc + η) * certRespBound η γc M δ0 (k + 1)
            + (η + 2 * M * certRespBound η γc M δ0 (k + 1) / γc ^ 2)
              * (2 * M + M ^ 2 / γc) := by rw [ih]
      _ = certRespBound η γc M δ0 (k + 1 + 1) := rfl

theorem certPhaseBound_shift (η γc M δ0 : ℝ) (k : ℕ) :
    certPhaseBound η γc M (certRespBound η γc M δ0 1) k
      = certPhaseBound η γc M δ0 (k + 1) := by
  simp only [certPhaseBound]
  rw [certRespBound_shift]

theorem certRead_norm_le {η γc M : ℝ} (hγc : 0 < γc)
    (A B : Polynomial ℂ) (γ : ℂ)
    (hmagB0 : ‖B.coeff 0‖ ≤ M)
    (hdivC : γc ≤ ‖A.coeff 0‖)
    (hread : ‖γ - B.coeff 0 / A.coeff 0‖ ≤ η) :
    ‖γ‖ ≤ M / γc + η := by
  have hq : ‖B.coeff 0 / A.coeff 0‖ ≤ M / γc := by
    rw [norm_div]
    have hdenpos : (0 : ℝ) < ‖A.coeff 0‖ := lt_of_lt_of_le hγc hdivC
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hmagB0
    rw [div_le_div_iff₀ hdenpos hγc]
    calc ‖B.coeff 0‖ * γc ≤ M * γc := mul_le_mul_of_nonneg_right hmagB0 (le_of_lt hγc)
      _ ≤ M * ‖A.coeff 0‖ := mul_le_mul_of_nonneg_left hdivC hM0
  have htr : ‖γ‖ ≤ ‖γ - B.coeff 0 / A.coeff 0‖ + ‖B.coeff 0 / A.coeff 0‖ := by
    have h2 : ‖γ‖ = ‖(γ - B.coeff 0 / A.coeff 0) + B.coeff 0 / A.coeff 0‖ := by
      congr 1
      ring
    rw [h2]
    exact norm_add_le _ _
  linarith

theorem certRefA_coeff_norm_le (γ : ℂ) (A B : Polynomial ℂ) (i : ℕ) :
    ‖(certRefA γ A B).coeff i‖ ≤ ‖A.coeff i‖ + ‖γ‖ * ‖B.coeff i‖ := by
  rw [certRefA_coeff, Complex.norm_mul]
  have h2 : ‖A.coeff i + (starRingEnd ℂ γ) * B.coeff i‖
      ≤ ‖A.coeff i‖ + ‖γ‖ * ‖B.coeff i‖ := by
    refine le_trans (norm_add_le _ _) (add_le_add (le_refl _) ?_)
    rw [← Complex.norm_conj γ, Complex.norm_mul]
  exact le_trans (mul_le_mul (layerC_norm_le_one γ) h2 (norm_nonneg _) zero_le_one)
    (le_of_eq (one_mul _))

theorem certRefB_coeff_norm_le (γ : ℂ) (A B : Polynomial ℂ) (i : ℕ) :
    ‖(certRefB γ A B).coeff i‖ ≤ ‖B.coeff (i + 1)‖ + ‖γ‖ * ‖A.coeff (i + 1)‖ := by
  rw [certRefB_coeff, Complex.norm_mul]
  have h2 : ‖B.coeff (i + 1) - γ * A.coeff (i + 1)‖
      ≤ ‖B.coeff (i + 1)‖ + ‖γ‖ * ‖A.coeff (i + 1)‖ := by
    refine le_trans (norm_sub_le _ _) (add_le_add (le_refl _) ?_)
    exact norm_mul_le _ _
  exact le_trans (mul_le_mul (layerC_norm_le_one γ) h2 (norm_nonneg _) zero_le_one)
    (le_of_eq (one_mul _))

theorem certStep_stability {η γc M d : ℝ} (hγc : 0 < γc)
    (A B Ai Bi : Polynomial ℂ) (γ : ℂ) (A' B' : Polynomial ℂ)
    (hmag : ∀ i, ‖A.coeff i‖ ≤ M ∧ ‖B.coeff i‖ ≤ M
      ∧ ‖Ai.coeff i‖ ≤ M ∧ ‖Bi.coeff i‖ ≤ M)
    (hdev : ∀ i, ‖A.coeff i - Ai.coeff i‖ ≤ d ∧ ‖B.coeff i - Bi.coeff i‖ ≤ d)
    (hdivC : γc ≤ ‖A.coeff 0‖) (hdivI : γc ≤ ‖Ai.coeff 0‖)
    (hread : ‖γ - B.coeff 0 / A.coeff 0‖ ≤ η)
    (hrotA : ∀ i, ‖A'.coeff i - (certRefA γ A B).coeff i‖ ≤ η)
    (hrotB : ∀ i, ‖B'.coeff i - (certRefB γ A B).coeff i‖ ≤ η) :
    ‖γ - Bi.coeff 0 / Ai.coeff 0‖ ≤ η + 2 * M * d / γc ^ 2
    ∧ (∀ i, ‖A'.coeff i - (certRefA (Bi.coeff 0 / Ai.coeff 0) Ai Bi).coeff i‖
        ≤ η + (1 + M / γc + η) * d
          + (η + 2 * M * d / γc ^ 2) * (2 * M + M ^ 2 / γc))
    ∧ (∀ i, ‖B'.coeff i - (certRefB (Bi.coeff 0 / Ai.coeff 0) Ai Bi).coeff i‖
        ≤ η + (1 + M / γc + η) * d
          + (η + 2 * M * d / γc ^ 2) * (2 * M + M ^ 2 / γc)) := by
  have hd0 : 0 ≤ d := le_trans (norm_nonneg _) (hdev 0).1
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hmag 0).1
  have hγmagi : ‖Bi.coeff 0 / Ai.coeff 0‖ ≤ M / γc := by
    rw [norm_div]
    have hdenpos : (0 : ℝ) < ‖Ai.coeff 0‖ := lt_of_lt_of_le hγc hdivI
    rw [div_le_div_iff₀ hdenpos hγc]
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hmag 0).1
    calc ‖Bi.coeff 0‖ * γc ≤ M * γc := mul_le_mul_of_nonneg_right (hmag 0).2.2.2 (le_of_lt hγc)
      _ ≤ M * ‖Ai.coeff 0‖ := mul_le_mul_of_nonneg_left hdivI hM0
  have hγmag : ‖γ‖ ≤ M / γc + η :=
    certRead_norm_le hγc A B γ (hmag 0).2.1 hdivC hread
  have hconv : (M / γc) * M = M ^ 2 / γc := by
    field_simp

  have hphase : ‖γ - Bi.coeff 0 / Ai.coeff 0‖ ≤ η + 2 * M * d / γc ^ 2 := by
    have hsplit : γ - Bi.coeff 0 / Ai.coeff 0
        = (γ - B.coeff 0 / A.coeff 0) + (B.coeff 0 / A.coeff 0 - Bi.coeff 0 / Ai.coeff 0) := by
      ring
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add hread ?_)
    have hA : A.coeff 0 ≠ 0 := by
      intro h0
      rw [h0] at hdivC
      simp at hdivC
      exact absurd hdivC (not_le.mpr hγc)
    have hAi : Ai.coeff 0 ≠ 0 := by
      intro h0
      rw [h0] at hdivI
      simp at hdivI
      exact absurd hdivI (not_le.mpr hγc)
    have hq : B.coeff 0 / A.coeff 0 - Bi.coeff 0 / Ai.coeff 0
        = (B.coeff 0 * Ai.coeff 0 - Bi.coeff 0 * A.coeff 0) / (A.coeff 0 * Ai.coeff 0) := by
      apply mul_right_cancel₀ (mul_ne_zero hA hAi)
      field_simp
    rw [hq, norm_div]
    have hdenpos : (0 : ℝ) < ‖A.coeff 0 * Ai.coeff 0‖ := by
      rw [Complex.norm_mul]
      exact mul_pos (lt_of_lt_of_le hγc hdivC) (lt_of_lt_of_le hγc hdivI)
    have hdenlb : γc ^ 2 ≤ ‖A.coeff 0 * Ai.coeff 0‖ := by
      rw [Complex.norm_mul]
      nlinarith [hdivC, hdivI, sq_nonneg γc]
    have hnum : ‖B.coeff 0 * Ai.coeff 0 - Bi.coeff 0 * A.coeff 0‖ ≤ 2 * M * d := by
      have e : B.coeff 0 * Ai.coeff 0 - Bi.coeff 0 * A.coeff 0
          = B.coeff 0 * (Ai.coeff 0 - A.coeff 0)
            + (B.coeff 0 - Bi.coeff 0) * A.coeff 0 := by
        ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      have hB : ‖B.coeff 0‖ ≤ M := (hmag 0).2.1
      have hA : ‖A.coeff 0‖ ≤ M := (hmag 0).1
      have hdA : ‖Ai.coeff 0 - A.coeff 0‖ ≤ d := by
        rw [norm_sub_rev]
        exact (hdev 0).1
      have hdB : ‖B.coeff 0 - Bi.coeff 0‖ ≤ d := (hdev 0).2
      have h1 : ‖B.coeff 0 * (Ai.coeff 0 - A.coeff 0)‖ ≤ M * d := by
        rw [Complex.norm_mul]
        exact mul_le_mul hB hdA (norm_nonneg _) (le_trans (norm_nonneg _) hB)
      have h2 : ‖(B.coeff 0 - Bi.coeff 0) * A.coeff 0‖ ≤ d * M := by
        rw [Complex.norm_mul]
        exact mul_le_mul hdB hA (norm_nonneg _) (le_trans (norm_nonneg _) hdB)
      have hmd : M * d = d * M := mul_comm _ _
      linarith
    have hgc2pos : (0 : ℝ) < γc ^ 2 := by positivity
    rw [div_le_div_iff₀ hdenpos hgc2pos]
    have h1 : ‖B.coeff 0 * Ai.coeff 0 - Bi.coeff 0 * A.coeff 0‖ * γc ^ 2
        ≤ 2 * M * d * γc ^ 2 :=
      mul_le_mul_of_nonneg_right hnum (sq_nonneg γc)
    have h2 : 2 * M * d * γc ^ 2 ≤ 2 * M * d * ‖A.coeff 0 * Ai.coeff 0‖ := by
      refine mul_le_mul_of_nonneg_left hdenlb ?_
      nlinarith [hM0, hd0]
    linarith
  refine ⟨hphase, ?_, ?_⟩
  · intro i
    rw [certRefA_coeff]
    have hkey : A'.coeff i - layerC (Bi.coeff 0 / Ai.coeff 0)
            * (Ai.coeff i + (starRingEnd ℂ (Bi.coeff 0 / Ai.coeff 0)) * Bi.coeff i)
        = (A'.coeff i - layerC γ * (A.coeff i + (starRingEnd ℂ γ) * B.coeff i))
          + (layerC γ * (A.coeff i + (starRingEnd ℂ γ) * B.coeff i)
            - layerC (Bi.coeff 0 / Ai.coeff 0)
              * (Ai.coeff i + (starRingEnd ℂ (Bi.coeff 0 / Ai.coeff 0)) * Bi.coeff i)) := by
      ring
    have hmid : layerC γ * (A.coeff i + (starRingEnd ℂ γ) * B.coeff i)
            - layerC (Bi.coeff 0 / Ai.coeff 0)
              * (Ai.coeff i + (starRingEnd ℂ (Bi.coeff 0 / Ai.coeff 0)) * Bi.coeff i)
        = layerC γ * ((A.coeff i - Ai.coeff i) + (starRingEnd ℂ γ) * (B.coeff i - Bi.coeff i)
              + (starRingEnd ℂ (γ - Bi.coeff 0 / Ai.coeff 0)) * Bi.coeff i)
          + (layerC γ - layerC (Bi.coeff 0 / Ai.coeff 0))
              * (Ai.coeff i + (starRingEnd ℂ (Bi.coeff 0 / Ai.coeff 0)) * Bi.coeff i) := by
      have hcsub : (starRingEnd ℂ γ) - (starRingEnd ℂ (Bi.coeff 0 / Ai.coeff 0))
          = starRingEnd ℂ (γ - Bi.coeff 0 / Ai.coeff 0) := (map_sub _ _ _).symm
      rw [← hcsub]
      ring
    have hnorm1 : ‖layerC γ * ((A.coeff i - Ai.coeff i) + (starRingEnd ℂ γ) * (B.coeff i - Bi.coeff i)
          + (starRingEnd ℂ (γ - Bi.coeff 0 / Ai.coeff 0)) * Bi.coeff i)‖
        ≤ d + ‖γ‖ * d + ‖γ - Bi.coeff 0 / Ai.coeff 0‖ * M := by
      have hinner : ‖(A.coeff i - Ai.coeff i) + (starRingEnd ℂ γ) * (B.coeff i - Bi.coeff i)
          + (starRingEnd ℂ (γ - Bi.coeff 0 / Ai.coeff 0)) * Bi.coeff i‖
          ≤ d + ‖γ‖ * d + ‖γ - Bi.coeff 0 / Ai.coeff 0‖ * M := by
        have t1 := norm_add_le ((A.coeff i - Ai.coeff i) + (starRingEnd ℂ γ) * (B.coeff i - Bi.coeff i))
          ((starRingEnd ℂ (γ - Bi.coeff 0 / Ai.coeff 0)) * Bi.coeff i)
        have t2 :=
            norm_add_le (A.coeff i - Ai.coeff i) ((starRingEnd ℂ γ) * (B.coeff i - Bi.coeff i))
        have t3 : ‖(starRingEnd ℂ γ) * (B.coeff i - Bi.coeff i)‖ ≤ ‖γ‖ * d := by
          rw [← Complex.norm_conj γ, Complex.norm_mul]
          exact mul_le_mul (le_refl _) (hdev i).2 (norm_nonneg _) (norm_nonneg _)
        have t4 : ‖(starRingEnd ℂ (γ - Bi.coeff 0 / Ai.coeff 0)) * Bi.coeff i‖
            ≤ ‖γ - Bi.coeff 0 / Ai.coeff 0‖ * M := by
          rw [Complex.norm_mul, Complex.norm_conj (γ - Bi.coeff 0 / Ai.coeff 0)]
          exact mul_le_mul (le_refl _) (hmag i).2.2.2 (norm_nonneg _) (norm_nonneg _)
        have t5 : ‖A.coeff i - Ai.coeff i‖ ≤ d := (hdev i).1
        linarith
      calc ‖layerC γ * ((A.coeff i - Ai.coeff i) + (starRingEnd ℂ γ) * (B.coeff i - Bi.coeff i)
              + (starRingEnd ℂ (γ - Bi.coeff 0 / Ai.coeff 0)) * Bi.coeff i)‖
          = ‖layerC γ‖ * ‖(A.coeff i - Ai.coeff i) + (starRingEnd ℂ γ) * (B.coeff i - Bi.coeff i)
              + (starRingEnd ℂ (γ - Bi.coeff 0 / Ai.coeff 0)) * Bi.coeff i‖ := Complex.norm_mul _ _
        _ ≤ 1 * (d + ‖γ‖ * d + ‖γ - Bi.coeff 0 / Ai.coeff 0‖ * M) :=
            mul_le_mul (layerC_norm_le_one γ) hinner (norm_nonneg _)
              (by nlinarith [hd0, norm_nonneg γ, norm_nonneg (γ - Bi.coeff 0 / Ai.coeff 0)])
        _ = d + ‖γ‖ * d + ‖γ - Bi.coeff 0 / Ai.coeff 0‖ * M := one_mul _
    have hnorm2 : ‖(layerC γ - layerC (Bi.coeff 0 / Ai.coeff 0))
          * (Ai.coeff i + (starRingEnd ℂ (Bi.coeff 0 / Ai.coeff 0)) * Bi.coeff i)‖
        ≤ ‖γ - Bi.coeff 0 / Ai.coeff 0‖ * (M + M ^ 2 / γc) := by
      rw [Complex.norm_mul]
      have hinner : ‖Ai.coeff i + (starRingEnd ℂ (Bi.coeff 0 / Ai.coeff 0)) * Bi.coeff i‖
          ≤ M + M ^ 2 / γc := by
        have h11 : ‖Ai.coeff i + (starRingEnd ℂ (Bi.coeff 0 / Ai.coeff 0)) * Bi.coeff i‖
            ≤ M + (M / γc) * M := by
          refine le_trans (norm_add_le _ _) (add_le_add (hmag i).2.2.1 ?_)
          rw [Complex.norm_mul, Complex.norm_conj (Bi.coeff 0 / Ai.coeff 0)]
          exact mul_le_mul hγmagi (hmag i).2.2.2 (norm_nonneg _)
            (div_nonneg hM0 (le_of_lt hγc))
        linarith
      exact mul_le_mul (layerC_lipschitz _ _) hinner (norm_nonneg _) (norm_nonneg _)
    have hcoef : (0 : ℝ) ≤ 2 * M + M ^ 2 / γc := by
      have h1 : (0 : ℝ) ≤ M ^ 2 / γc := div_nonneg (sq_nonneg M) hγc.le
      linarith
    have hpart1 : d + ‖γ‖ * d ≤ (1 + M / γc + η) * d := by
      have hring : (1 + M / γc + η) * d = d + (M / γc + η) * d := by
        ring
      have hprod : ‖γ‖ * d ≤ (M / γc + η) * d := mul_le_mul_of_nonneg_right hγmag hd0
      linarith
    have hpart2 : ‖γ - Bi.coeff 0 / Ai.coeff 0‖ * (2 * M + M ^ 2 / γc)
        ≤ (η + 2 * M * d / γc ^ 2) * (2 * M + M ^ 2 / γc) :=
      mul_le_mul_of_nonneg_right hphase hcoef
    have hring : d + ‖γ‖ * d + ‖γ - Bi.coeff 0 / Ai.coeff 0‖ * M
        + ‖γ - Bi.coeff 0 / Ai.coeff 0‖ * (M + M ^ 2 / γc)
        = (d + ‖γ‖ * d) + ‖γ - Bi.coeff 0 / Ai.coeff 0‖ * (2 * M + M ^ 2 / γc) := by
      ring
    calc ‖A'.coeff i - layerC (Bi.coeff 0 / Ai.coeff 0)
            * (Ai.coeff i + (starRingEnd ℂ (Bi.coeff 0 / Ai.coeff 0)) * Bi.coeff i)‖
        ≤ ‖(A'.coeff i - layerC γ * (A.coeff i + (starRingEnd ℂ γ) * B.coeff i))
            + (layerC γ * (A.coeff i + (starRingEnd ℂ γ) * B.coeff i)
              - layerC (Bi.coeff 0 / Ai.coeff 0)
                * (Ai.coeff i + (starRingEnd ℂ (Bi.coeff 0 / Ai.coeff 0)) * Bi.coeff i))‖ := by
          rw [hkey]
      _ ≤ ‖A'.coeff i - layerC γ * (A.coeff i + (starRingEnd ℂ γ) * B.coeff i)‖
            + ‖layerC γ * (A.coeff i + (starRingEnd ℂ γ) * B.coeff i)
              - layerC (Bi.coeff 0 / Ai.coeff 0)
                * (Ai.coeff i + (starRingEnd ℂ (Bi.coeff 0 / Ai.coeff 0)) * Bi.coeff i)‖ :=
          norm_add_le _ _
      _ ≤ η + (1 + M / γc + η) * d
          + (η + 2 * M * d / γc ^ 2) * (2 * M + M ^ 2 / γc) := by
          have hA : ‖A'.coeff i - layerC γ * (A.coeff i + (starRingEnd ℂ γ) * B.coeff i)‖ ≤ η := by
            have h := hrotA i
            rwa [certRefA_coeff] at h
          have hsplit : ‖layerC γ * (A.coeff i + (starRingEnd ℂ γ) * B.coeff i)
              - layerC (Bi.coeff 0 / Ai.coeff 0)
                * (Ai.coeff i + (starRingEnd ℂ (Bi.coeff 0 / Ai.coeff 0)) * Bi.coeff i)‖
              ≤ (1 + M / γc + η) * d + (η + 2 * M * d / γc ^ 2) * (2 * M + M ^ 2 / γc) := by
            rw [hmid]
            refine le_trans (norm_add_le _ _) ?_
            linarith
          linarith
  · intro i
    rw [certRefB_coeff]
    have hkey : B'.coeff i - layerC (Bi.coeff 0 / Ai.coeff 0)
            * (Bi.coeff (i + 1) - (Bi.coeff 0 / Ai.coeff 0) * Ai.coeff (i + 1))
        = (B'.coeff i - layerC γ * (B.coeff (i + 1) - γ * A.coeff (i + 1)))
          + (layerC γ * (B.coeff (i + 1) - γ * A.coeff (i + 1))
            - layerC (Bi.coeff 0 / Ai.coeff 0)
              * (Bi.coeff (i + 1) - (Bi.coeff 0 / Ai.coeff 0) * Ai.coeff (i + 1))) := by
      ring
    have hmid : layerC γ * (B.coeff (i + 1) - γ * A.coeff (i + 1))
          - layerC (Bi.coeff 0 / Ai.coeff 0)
            * (Bi.coeff (i + 1) - (Bi.coeff 0 / Ai.coeff 0) * Ai.coeff (i + 1))
        = layerC γ * ((B.coeff (i + 1) - Bi.coeff (i + 1))
              - γ * (A.coeff (i + 1) - Ai.coeff (i + 1))
              - (γ - Bi.coeff 0 / Ai.coeff 0) * Ai.coeff (i + 1))
          + (layerC γ - layerC (Bi.coeff 0 / Ai.coeff 0))
              * (Bi.coeff (i + 1) - (Bi.coeff 0 / Ai.coeff 0) * Ai.coeff (i + 1)) := by
      ring
    have hnorm1 : ‖layerC γ * ((B.coeff (i + 1) - Bi.coeff (i + 1))
          - γ * (A.coeff (i + 1) - Ai.coeff (i + 1))
          - (γ - Bi.coeff 0 / Ai.coeff 0) * Ai.coeff (i + 1))‖
        ≤ d + ‖γ‖ * d + ‖γ - Bi.coeff 0 / Ai.coeff 0‖ * M := by
      have hinner : ‖(B.coeff (i + 1) - Bi.coeff (i + 1))
          - γ * (A.coeff (i + 1) - Ai.coeff (i + 1))
          - (γ - Bi.coeff 0 / Ai.coeff 0) * Ai.coeff (i + 1)‖
          ≤ d + ‖γ‖ * d + ‖γ - Bi.coeff 0 / Ai.coeff 0‖ * M := by
        have t1 := norm_sub_le ((B.coeff (i + 1) - Bi.coeff (i + 1))
          - γ * (A.coeff (i + 1) - Ai.coeff (i + 1)))
          ((γ - Bi.coeff 0 / Ai.coeff 0) * Ai.coeff (i + 1))
        have t2 := norm_sub_le (B.coeff (i + 1) - Bi.coeff (i + 1))
          (γ * (A.coeff (i + 1) - Ai.coeff (i + 1)))
        have t3 : ‖γ * (A.coeff (i + 1) - Ai.coeff (i + 1))‖ ≤ ‖γ‖ * d := by
          rw [Complex.norm_mul]
          exact mul_le_mul (le_refl _) (hdev (i + 1)).1 (norm_nonneg _) (norm_nonneg _)
        have t4 : ‖(γ - Bi.coeff 0 / Ai.coeff 0) * Ai.coeff (i + 1)‖
            ≤ ‖γ - Bi.coeff 0 / Ai.coeff 0‖ * M := by
          rw [Complex.norm_mul]
          exact mul_le_mul (le_refl _) (hmag (i + 1)).2.2.1 (norm_nonneg _) (norm_nonneg _)
        have t5 : ‖B.coeff (i + 1) - Bi.coeff (i + 1)‖ ≤ d := (hdev (i + 1)).2
        linarith
      calc ‖layerC γ * ((B.coeff (i + 1) - Bi.coeff (i + 1))
              - γ * (A.coeff (i + 1) - Ai.coeff (i + 1))
              - (γ - Bi.coeff 0 / Ai.coeff 0) * Ai.coeff (i + 1))‖
          = ‖layerC γ‖ * ‖(B.coeff (i + 1) - Bi.coeff (i + 1))
              - γ * (A.coeff (i + 1) - Ai.coeff (i + 1))
              - (γ - Bi.coeff 0 / Ai.coeff 0) * Ai.coeff (i + 1)‖ := Complex.norm_mul _ _
        _ ≤ 1 * (d + ‖γ‖ * d + ‖γ - Bi.coeff 0 / Ai.coeff 0‖ * M) :=
            mul_le_mul (layerC_norm_le_one γ) hinner (norm_nonneg _)
              (by nlinarith [hd0, norm_nonneg γ, norm_nonneg (γ - Bi.coeff 0 / Ai.coeff 0)])
        _ = d + ‖γ‖ * d + ‖γ - Bi.coeff 0 / Ai.coeff 0‖ * M := one_mul _
    have hnorm2 : ‖(layerC γ - layerC (Bi.coeff 0 / Ai.coeff 0))
          * (Bi.coeff (i + 1) - (Bi.coeff 0 / Ai.coeff 0) * Ai.coeff (i + 1))‖
        ≤ ‖γ - Bi.coeff 0 / Ai.coeff 0‖ * (M + M ^ 2 / γc) := by
      rw [Complex.norm_mul]
      have hinner : ‖Bi.coeff (i + 1) - (Bi.coeff 0 / Ai.coeff 0) * Ai.coeff (i + 1)‖
          ≤ M + M ^ 2 / γc := by
        have h11 : ‖Bi.coeff (i + 1) - (Bi.coeff 0 / Ai.coeff 0) * Ai.coeff (i + 1)‖
            ≤ M + (M / γc) * M := by
          refine le_trans (norm_sub_le _ _) (add_le_add (hmag (i + 1)).2.2.2 ?_)
          rw [Complex.norm_mul]
          exact mul_le_mul hγmagi (hmag (i + 1)).2.2.1 (norm_nonneg _)
            (div_nonneg hM0 (le_of_lt hγc))
        linarith
      exact mul_le_mul (layerC_lipschitz _ _) hinner (norm_nonneg _) (norm_nonneg _)
    have hcoef : (0 : ℝ) ≤ 2 * M + M ^ 2 / γc := by
      have h1 : (0 : ℝ) ≤ M ^ 2 / γc := div_nonneg (sq_nonneg M) hγc.le
      linarith
    have hpart1 : d + ‖γ‖ * d ≤ (1 + M / γc + η) * d := by
      have hring : (1 + M / γc + η) * d = d + (M / γc + η) * d := by
        ring
      have hprod : ‖γ‖ * d ≤ (M / γc + η) * d := mul_le_mul_of_nonneg_right hγmag hd0
      linarith
    have hpart2 : ‖γ - Bi.coeff 0 / Ai.coeff 0‖ * (2 * M + M ^ 2 / γc)
        ≤ (η + 2 * M * d / γc ^ 2) * (2 * M + M ^ 2 / γc) :=
      mul_le_mul_of_nonneg_right hphase hcoef
    have hring : d + ‖γ‖ * d + ‖γ - Bi.coeff 0 / Ai.coeff 0‖ * M
        + ‖γ - Bi.coeff 0 / Ai.coeff 0‖ * (M + M ^ 2 / γc)
        = (d + ‖γ‖ * d) + ‖γ - Bi.coeff 0 / Ai.coeff 0‖ * (2 * M + M ^ 2 / γc) := by
      ring
    calc ‖B'.coeff i - layerC (Bi.coeff 0 / Ai.coeff 0)
            * (Bi.coeff (i + 1) - (Bi.coeff 0 / Ai.coeff 0) * Ai.coeff (i + 1))‖
        ≤ ‖(B'.coeff i - layerC γ * (B.coeff (i + 1) - γ * A.coeff (i + 1)))
            + (layerC γ * (B.coeff (i + 1) - γ * A.coeff (i + 1))
              - layerC (Bi.coeff 0 / Ai.coeff 0)
                * (Bi.coeff (i + 1) - (Bi.coeff 0 / Ai.coeff 0) * Ai.coeff (i + 1)))‖ := by
          rw [hkey]
      _ ≤ ‖B'.coeff i - layerC γ * (B.coeff (i + 1) - γ * A.coeff (i + 1))‖
            + ‖layerC γ * (B.coeff (i + 1) - γ * A.coeff (i + 1))
              - layerC (Bi.coeff 0 / Ai.coeff 0)
                * (Bi.coeff (i + 1) - (Bi.coeff 0 / Ai.coeff 0) * Ai.coeff (i + 1))‖ :=
          norm_add_le _ _
      _ ≤ η + (1 + M / γc + η) * d
          + (η + 2 * M * d / γc ^ 2) * (2 * M + M ^ 2 / γc) := by
          have hB : ‖B'.coeff i - layerC γ * (B.coeff (i + 1) - γ * A.coeff (i + 1))‖ ≤ η := by
            have h := hrotB i
            rwa [certRefB_coeff] at h
          have hsplit : ‖layerC γ * (B.coeff (i + 1) - γ * A.coeff (i + 1))
              - layerC (Bi.coeff 0 / Ai.coeff 0)
                * (Bi.coeff (i + 1) - (Bi.coeff 0 / Ai.coeff 0) * Ai.coeff (i + 1))‖
              ≤ (1 + M / γc + η) * d + (η + 2 * M * d / γc ^ 2) * (2 * M + M ^ 2 / γc) := by
            rw [hmid]
            refine le_trans (norm_add_le _ _) ?_
            linarith
          linarith

private theorem certLayerStrip_stability_aux (η γc M : ℝ) (hγc : 0 < γc)
    {A B : Polynomial ℂ} (r : CertLayerStrip η γc A B) :
    ∀ (δ : ℝ) {Ai Bi : Polynomial ℂ},
    LayerStripExact Ai Bi r.certSteps →
    (∀ k < r.certSteps, γc ≤ ‖(idealPair Ai Bi k).1.coeff 0‖) →
    (∀ k ≤ r.certSteps, ∀ i,
      ‖(r.certPairAt k).1.coeff i‖ ≤ M ∧ ‖(r.certPairAt k).2.coeff i‖ ≤ M
        ∧ ‖(idealPair Ai Bi k).1.coeff i‖ ≤ M
        ∧ ‖(idealPair Ai Bi k).2.coeff i‖ ≤ M) →
    (∀ i, ‖A.coeff i - Ai.coeff i‖ ≤ δ ∧ ‖B.coeff i - Bi.coeff i‖ ≤ δ) →
    ∀ k ≤ r.certSteps,
      (∀ i, ‖(r.certPairAt k).1.coeff i - (idealPair Ai Bi k).1.coeff i‖
          ≤ certRespBound η γc M δ k
        ∧ ‖(r.certPairAt k).2.coeff i - (idealPair Ai Bi k).2.coeff i‖
          ≤ certRespBound η γc M δ k)
      ∧ (k < r.certSteps →
        ‖r.certGammas.getD k 0 - idealGamma Ai Bi k‖ ≤ certPhaseBound η γc M δ k) := by
  induction r with
  | stop A B =>
    intro δ Ai Bi _hex _hγcI _hmag hdev k hk
    have h0 : (CertLayerStrip.stop (η := η) (γc := γc) A B).certSteps = 0 := by
      simp [CertLayerStrip.certSteps]
    rw [h0] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    refine ⟨?_, ?_⟩
    · intro i
      have hp0 : (CertLayerStrip.stop (η := η) (γc := γc) A B).certPairAt 0 = (A, B) := rfl
      rw [hp0, idealPair_zero]
      exact hdev i
    · intro hk'
      rw [h0] at hk'
      exact absurd hk' (Nat.not_lt_zero 0)
  | more A B s hdiv rest ih =>
    intro δ Ai0 Bi0 hex hγcI hmag hdev k hk
    have hlen : (CertLayerStrip.more A B s hdiv rest).certSteps = rest.certSteps + 1 := rfl
    rw [hlen] at hk

    obtain ⟨hphase1, hrespA1, hrespB1⟩ := certStep_stability hγc A B Ai0 Bi0 s.γ s.A' s.B'
      (fun i => ⟨(hmag 0 (Nat.zero_le _) i).1, (hmag 0 (Nat.zero_le _) i).2.1,
        (hmag 0 (Nat.zero_le _) i).2.2.1, (hmag 0 (Nat.zero_le _) i).2.2.2⟩)
      hdev hdiv (hγcI 0 (by rw [hlen]; omega)) s.readOK s.rotAOK s.rotBOK
    rw [certRefA_eq_step Ai0 Bi0] at hrespA1
    rw [certRefB_eq_step Ai0 Bi0] at hrespB1
    have hdev1 : ∀ i, ‖s.A'.coeff i - (layerStripStepSU2 Ai0 Bi0).2.1.coeff i‖
        ≤ certRespBound η γc M δ 1
      ∧ ‖s.B'.coeff i - (layerStripStepSU2 Ai0 Bi0).2.2.coeff i‖
        ≤ certRespBound η γc M δ 1 := fun i => ⟨hrespA1 i, hrespB1 i⟩

    obtain ⟨-, hex'⟩ := hex
    have hγcI' : ∀ k < rest.certSteps,
        γc ≤ ‖(idealPair (layerStripStepSU2 Ai0 Bi0).2.1 (layerStripStepSU2 Ai0 Bi0).2.2 k).1.coeff 0‖ := by
      intro k hk'
      rw [idealPair_step]
      exact hγcI (k + 1) (by rw [hlen]; omega)
    have hmag' : ∀ k ≤ rest.certSteps, ∀ i,
      ‖(rest.certPairAt k).1.coeff i‖ ≤ M ∧ ‖(rest.certPairAt k).2.coeff i‖ ≤ M
        ∧ ‖(idealPair (layerStripStepSU2 Ai0 Bi0).2.1 (layerStripStepSU2 Ai0 Bi0).2.2 k).1.coeff i‖ ≤ M
        ∧ ‖(idealPair (layerStripStepSU2 Ai0 Bi0).2.1 (layerStripStepSU2 Ai0 Bi0).2.2 k).2.coeff i‖ ≤ M := by
      intro k hk' i
      rw [idealPair_step,
        show rest.certPairAt k
            = CertLayerStrip.certPairAt (CertLayerStrip.more A B s hdiv rest) (k + 1) from
          (CertLayerStrip.certPairAt_more_succ A B s hdiv rest k).symm]
      exact hmag (k + 1) (by rw [hlen]; omega) i
    have hih := ih (δ := certRespBound η γc M δ 1)
      (Ai := (layerStripStepSU2 Ai0 Bi0).2.1) (Bi := (layerStripStepSU2 Ai0 Bi0).2.2)
      hex' hγcI' hmag' hdev1
    cases k with
    | zero =>
      refine ⟨?_, ?_⟩
      · intro i
        have hp0 : (CertLayerStrip.more A B s hdiv rest).certPairAt 0 = (A, B) := rfl
        rw [hp0, idealPair_zero]
        exact hdev i
      · intro _
        show ‖s.γ - Bi0.coeff 0 / Ai0.coeff 0‖ ≤ certPhaseBound η γc M δ 0
        have hb : certPhaseBound η γc M δ 0 = η + 2 * M * δ / γc ^ 2 := by
          simp only [certPhaseBound]
          rfl
        rw [hb]
        exact hphase1
    | succ k =>
      refine ⟨?_, ?_⟩
      · intro i
        have hrec := (hih k (by omega)).1 i
        rw [CertLayerStrip.certPairAt_more_succ A B s hdiv rest k, ← idealPair_step Ai0 Bi0 k,
          ← certRespBound_shift η γc M δ k]
        exact hrec
      · intro hk'
        have hrec := (hih k (by omega)).2 (by omega)
        rw [CertLayerStrip.certGammas_more_getD_succ A B s hdiv rest k, ← idealGamma_step Ai0 Bi0 k,
          ← certPhaseBound_shift η γc M δ k]
        exact hrec

theorem certLayerStrip_stability (η γc M δ0 : ℝ) (hγc : 0 < γc)
    (A0 B0 : Polynomial ℂ) (r : CertLayerStrip η γc A0 B0)
    {Ai0 Bi0 : Polynomial ℂ}
    (hex : LayerStripExact Ai0 Bi0 r.certSteps)
    (hγcI : ∀ k < r.certSteps, γc ≤ ‖(idealPair Ai0 Bi0 k).1.coeff 0‖)
    (hmag : ∀ k ≤ r.certSteps, ∀ i,
      ‖(r.certPairAt k).1.coeff i‖ ≤ M ∧ ‖(r.certPairAt k).2.coeff i‖ ≤ M
        ∧ ‖(idealPair Ai0 Bi0 k).1.coeff i‖ ≤ M
        ∧ ‖(idealPair Ai0 Bi0 k).2.coeff i‖ ≤ M)
    (hdev0 : ∀ i, ‖A0.coeff i - Ai0.coeff i‖ ≤ δ0
      ∧ ‖B0.coeff i - Bi0.coeff i‖ ≤ δ0) :
    ∀ k ≤ r.certSteps,
      (∀ i, ‖(r.certPairAt k).1.coeff i - (idealPair Ai0 Bi0 k).1.coeff i‖
          ≤ certRespBound η γc M δ0 k
        ∧ ‖(r.certPairAt k).2.coeff i - (idealPair Ai0 Bi0 k).2.coeff i‖
          ≤ certRespBound η γc M δ0 k)
      ∧ (k < r.certSteps →
        ‖r.certGammas.getD k 0 - idealGamma Ai0 Bi0 k‖ ≤ certPhaseBound η γc M δ0 k) :=
  certLayerStrip_stability_aux η γc M hγc r δ0 hex hγcI hmag hdev0

theorem frontier1 (η γc M δ0 : ℝ) (hγc : 0 < γc)
    (A0 B0 Ai0 Bi0 : Polynomial ℂ) (r : CertLayerStrip η γc A0 B0)
    (hex : LayerStripExact Ai0 Bi0 r.certSteps)
    (hγcI : ∀ k < r.certSteps, γc ≤ ‖(idealPair Ai0 Bi0 k).1.coeff 0‖)
    (hmag : ∀ k ≤ r.certSteps, ∀ i,
      ‖(r.certPairAt k).1.coeff i‖ ≤ M ∧ ‖(r.certPairAt k).2.coeff i‖ ≤ M
        ∧ ‖(idealPair Ai0 Bi0 k).1.coeff i‖ ≤ M
        ∧ ‖(idealPair Ai0 Bi0 k).2.coeff i‖ ≤ M)
    (hdev0 : ∀ i, ‖A0.coeff i - Ai0.coeff i‖ ≤ δ0
      ∧ ‖B0.coeff i - Bi0.coeff i‖ ≤ δ0) :
    r.certGammas.length = r.certSteps
      ∧ r.certOps = 4 * r.certSteps ^ 2 + 12 * r.certSteps
      ∧ (∀ k ≤ r.certSteps,
          (∀ i, ‖(r.certPairAt k).1.coeff i - (idealPair Ai0 Bi0 k).1.coeff i‖
              ≤ certRespBound η γc M δ0 k
            ∧ ‖(r.certPairAt k).2.coeff i - (idealPair Ai0 Bi0 k).2.coeff i‖
              ≤ certRespBound η γc M δ0 k)
          ∧ (k < r.certSteps →
            ‖r.certGammas.getD k 0 - idealGamma Ai0 Bi0 k‖ ≤ certPhaseBound η γc M δ0 k)) :=
  ⟨CertLayerStrip.certGammas_length r, CertLayerStrip.certOps_eq r,
    certLayerStrip_stability η γc M δ0 hγc A0 B0 r hex hγcI hmag hdev0⟩

private theorem nlft_fst_coeff_pos_real (γs : List ℂ) :
    ((nlftSU2 γs).1.coeff 0).im = 0 ∧ 0 < ((nlftSU2 γs).1.coeff 0).re := by
  have h := nlftSU2_fst_coeff_zero γs
  have hpos : (0 : ℝ) < (γs.map fun g => (Real.sqrt (1 + Complex.normSq g))⁻¹).prod := by
    apply List.prod_pos
    intro x hx
    obtain ⟨g, -, rfl⟩ := List.mem_map.mp hx
    exact inv_pos.mpr (Real.sqrt_pos.mpr
      (add_pos_of_pos_of_nonneg zero_lt_one (Complex.normSq_nonneg _)))
  rw [h]
  constructor
  · simp
  · simp
    exact hpos

theorem frontier2 (η γc M δ0 : ℝ) (hγc : 0 < γc)
    (γtrue : List ℂ) (n : ℕ) (hn : γtrue.length = n) (hn1 : 1 ≤ n)
    (A0 B0 : Polynomial ℂ) (r : CertLayerStrip η γc A0 B0)
    (hrn : r.certSteps = n)
    (hdev0 : ∀ i, ‖A0.coeff i - (nlftSU2 γtrue).1.coeff i‖ ≤ δ0
      ∧ ‖B0.coeff i - (nlftSU2 γtrue).2.coeff i‖ ≤ δ0)
    (hγcI : ∀ k < r.certSteps,
      γc ≤ ‖(idealPair (nlftSU2 γtrue).1 (nlftSU2 γtrue).2 k).1.coeff 0‖)
    (hmag : ∀ k ≤ r.certSteps, ∀ i,
      ‖(r.certPairAt k).1.coeff i‖ ≤ M ∧ ‖(r.certPairAt k).2.coeff i‖ ≤ M
        ∧ ‖(idealPair (nlftSU2 γtrue).1 (nlftSU2 γtrue).2 k).1.coeff i‖ ≤ M
        ∧ ‖(idealPair (nlftSU2 γtrue).1 (nlftSU2 γtrue).2 k).2.coeff i‖ ≤ M) :
    r.certOps = 4 * n ^ 2 + 12 * n
      ∧ ∀ k < n, ‖r.certGammas.getD k 0 - γtrue.getD k 0‖
        ≤ certPhaseBound η γc M δ0 k := by
  have hdegA : (nlftSU2 γtrue).1.natDegree ≤ n - 1 := by
    have h := nlftSU2_fst_natDegree_le γtrue
    rw [hn] at h
    exact h
  have hdegB : (nlftSU2 γtrue).2.natDegree ≤ n - 1 := by
    have h := nlftSU2_snd_natDegree_le γtrue
    rw [hn] at h
    exact h
  have himage : (nlftSU2 γtrue).1 * conjRevN (n - 1) (nlftSU2 γtrue).1
      + (nlftSU2 γtrue).2 * conjRevN (n - 1) (nlftSU2 γtrue).2 = X ^ (n - 1) := by
    have h := nlftSU2_identity γtrue
    rw [hn] at h
    exact h
  obtain ⟨him0, hre0⟩ := nlft_fst_coeff_pos_real γtrue
  have hex : LayerStripExact (nlftSU2 γtrue).1 (nlftSU2 γtrue).2 n :=
    layerStripExact_of_pos _ _ n him0 hre0
  rw [← hrn] at hex
  have hsn : n - 1 + 1 = n := by omega
  have hrecover : (layerStripSU2 (nlftSU2 γtrue).1 (nlftSU2 γtrue).2 n).gammas = γtrue := by
    obtain ⟨hcorr, -, -⟩ :=
      layerStripSU2_correct (n - 1) _ _ hdegA hdegB himage him0 hre0
    rw [hsn] at hcorr
    have hlen : (layerStripSU2 (nlftSU2 γtrue).1 (nlftSU2 γtrue).2 n).gammas.length
        = γtrue.length := by
      rw [layerStripSU2_gammas_length, hn]
    exact nlftSU2_injective hlen hcorr
  have hmain := certLayerStrip_stability η γc M δ0 hγc A0 B0 r hex hγcI hmag hdev0
  have hops : r.certOps = 4 * n ^ 2 + 12 * n := by
    rw [CertLayerStrip.certOps_eq r, hrn]
  refine ⟨hops, ?_⟩
  intro k hk
  have hkbound := (hmain k (by rw [hrn]; omega)).2 (by rw [hrn]; omega)
  have hget : (layerStripSU2 (nlftSU2 γtrue).1 (nlftSU2 γtrue).2 n).gammas.getD k 0
      = idealGamma (nlftSU2 γtrue).1 (nlftSU2 γtrue).2 k :=
    layerStrip_gammas_getD _ _ n k hk
  have htrue : γtrue.getD k 0 = idealGamma (nlftSU2 γtrue).1 (nlftSU2 γtrue).2 k := by
    have h1 : γtrue.getD k 0
        = (layerStripSU2 (nlftSU2 γtrue).1 (nlftSU2 γtrue).2 n).gammas.getD k 0 := by
      rw [hrecover]
    rw [h1, hget]
  rw [htrue]
  exact hkbound

theorem certRefA_exact_normSq (a b : ℂ) (ha : a ≠ 0) :
    Complex.normSq (layerC (b / a) * (a + (starRingEnd ℂ (b / a)) * b))
      = Complex.normSq a + Complex.normSq b := by
  have hu : (0 : ℝ) ≤ 1 + Complex.normSq (b / a) :=
    add_nonneg zero_le_one (Complex.normSq_nonneg _)
  have hnsa : Complex.normSq a ≠ 0 := fun h => ha (Complex.normSq_eq_zero.mp h)
  have hx : (0 : ℝ) ≤ Complex.normSq b / Complex.normSq a :=
    div_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hden : (0 : ℝ) < 1 + Complex.normSq b / Complex.normSq a := by linarith
  have hden' : 1 + Complex.normSq b / Complex.normSq a ≠ 0 := ne_of_gt hden
  have hlayer : Complex.normSq (layerC (b / a)) = 1 / (1 + Complex.normSq (b / a)) := by
    rw [layerC, Complex.normSq_ofReal, ← mul_inv,
      show Real.sqrt (1 + Complex.normSq (b / a)) * Real.sqrt (1 + Complex.normSq (b / a))
        = (Real.sqrt (1 + Complex.normSq (b / a))) ^ 2 from (pow_two _).symm,
      Real.sq_sqrt hu, one_div]
  have hnsab : Complex.normSq a + Complex.normSq b ≠ 0 := by
    have h1 : (0 : ℝ) < Complex.normSq a := Complex.normSq_pos.mpr ha
    have h2 : (0 : ℝ) ≤ Complex.normSq b := Complex.normSq_nonneg _
    linarith
  have hmid : a * (starRingEnd ℂ ((starRingEnd ℂ (b / a)) * b)) = (Complex.normSq b : ℂ) := by
    rw [map_mul, starRingEnd_self_apply, ← mul_assoc,
      show a * (b / a) = b from by field_simp]
    exact Complex.mul_conj b
  have hsum : Complex.normSq (a + (starRingEnd ℂ (b / a)) * b)
      = Complex.normSq a + Complex.normSq (b / a) * Complex.normSq b
        + 2 * Complex.normSq b := by
    rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_conj, hmid,
      Complex.ofReal_re]
  rw [Complex.normSq_div] at hlayer hsum
  rw [Complex.normSq_mul, hlayer, hsum]
  field_simp [hnsa, hden', hnsab]
  ring

theorem certRefA_exact_normSq' (A B : Polynomial ℂ) (hA : A.coeff 0 ≠ 0) :
    Complex.normSq ((certRefA (B.coeff 0 / A.coeff 0) A B).coeff 0)
      = Complex.normSq (A.coeff 0) + Complex.normSq (B.coeff 0) := by
  rw [certRefA_coeff]
  exact certRefA_exact_normSq _ _ hA

theorem certRefA_exact_norm_ge (A B : Polynomial ℂ) (hA : A.coeff 0 ≠ 0) :
    ‖A.coeff 0‖ ≤ ‖(certRefA (B.coeff 0 / A.coeff 0) A B).coeff 0‖ := by
  have h := certRefA_exact_normSq' A B hA
  have h2 : ‖A.coeff 0‖ ^ 2 ≤ ‖(certRefA (B.coeff 0 / A.coeff 0) A B).coeff 0‖ ^ 2 := by
    have e1 := Complex.sq_norm (A.coeff 0)
    have e2 := Complex.sq_norm ((certRefA (B.coeff 0 / A.coeff 0) A B).coeff 0)
    rw [e1, e2]
    linarith [Complex.normSq_nonneg (B.coeff 0)]
  have hn := norm_nonneg ((certRefA (B.coeff 0 / A.coeff 0) A B).coeff 0)
  have hn' := norm_nonneg (A.coeff 0)
  nlinarith [h2]

end Qatlib.Concepts.FiniteLocc.LOCCProgram.LayerStrippingCertifiedStability
