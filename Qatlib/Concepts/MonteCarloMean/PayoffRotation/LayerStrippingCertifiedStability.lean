/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
import Qatlib.Concepts.FiniteLocc.LOCCProgram.LayerStrippingCertifiedStability
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
set_option warningAsError false
open Qatlib.Concepts.FiniteLocc.LOCCProgram.LayerStrippingCertifiedStability
open Qatlib.Concepts.FiniteLocc.LOCCProgram.LayerStrippingCertifiedStability.CertLayerStrip

set_option autoImplicit false
set_option maxHeartbeats 800000

open Qatlib

namespace Qatlib.Concepts.MonteCarloMean.PayoffRotation

theorem ratApprox (z : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : GaussianRat, ‖gaussianRatComplex g - z‖ ≤ ε := by
  have hpos : (0 : ℝ) < ε / 2 := by positivity
  obtain ⟨q1, hq1⟩ := exists_rat_near z.re hpos
  obtain ⟨q2, hq2⟩ := exists_rat_near z.im hpos
  refine ⟨(q1, q2), ?_⟩
  have hre : (gaussianRatComplex (q1, q2) - z).re = (q1 : ℝ) - z.re := by
    simp only [gaussianRatComplex, Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, mul_zero]
    norm_cast
    push_cast
    ring
  have him : (gaussianRatComplex (q1, q2) - z).im = (q2 : ℝ) - z.im := by
    simp only [gaussianRatComplex, Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero]
    norm_cast
    push_cast
    ring
  have h3 : |(q1 : ℝ) - z.re| + |(q2 : ℝ) - z.im| ≤ ε := by
    rw [abs_sub_comm (↑q1 : ℝ) z.re, abs_sub_comm (↑q2 : ℝ) z.im,
      show ε = ε / 2 + ε / 2 by ring]
    exact add_le_add hq1.le hq2.le
  calc ‖gaussianRatComplex (q1, q2) - z‖
      ≤ |(gaussianRatComplex (q1, q2) - z).re|
          + |(gaussianRatComplex (q1, q2) - z).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |(q1 : ℝ) - z.re| + |(q2 : ℝ) - z.im| := by
          rw [hre, him]
    _ ≤ ε := h3

theorem gaussianRatComplex_zero : gaussianRatComplex 0 = 0 := by
  simp [gaussianRatComplex]

theorem list_getD_default (l : List GaussianRat) (i : ℕ) (h : l.length ≤ i) :
    l.getD i 0 = 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih =>
    cases i with
    | zero => exact absurd h (by simp only [List.length_cons]; omega)
    | succ i => rw [List.getD_cons_succ]; exact ih i (by simp only [List.length_cons] at h; omega)

noncomputable def ratPoly (gs : List GaussianRat) : Polynomial ℂ :=
  ∑ i ∈ Finset.range gs.length,
    Polynomial.C (gaussianRatComplex (gs.getD i 0)) * Polynomial.X ^ i

theorem ratPoly_coeff (gs : List GaussianRat) (i : ℕ) :
    (ratPoly gs).coeff i = gaussianRatComplex (gs.getD i 0) := by
  by_cases hi : i < gs.length
  · have hmem : i ∈ Finset.range gs.length := Finset.mem_range.mpr hi
    rw [ratPoly, Polynomial.finsetSum_coeff,
      Finset.sum_eq_single i
        (fun b _ hb => by rw [Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hb)])
        (fun h => absurd hmem h)]
    rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
  · rw [ratPoly, Polynomial.finsetSum_coeff,
      Finset.sum_eq_zero (fun b hb => by
        rw [Polynomial.coeff_C_mul_X_pow,
          if_neg (fun h => by have h1 := Finset.mem_range.mp hb; omega)])]
    rw [list_getD_default gs i (by omega), gaussianRatComplex_zero]

def approxList (f : ℕ → GaussianRat) : ℕ → List GaussianRat
  | 0 => [f 0]
  | N + 1 => f 0 :: approxList (fun k => f (k + 1)) N

theorem approxList_length (f : ℕ → GaussianRat) (N : ℕ) :
    (approxList f N).length = N + 1 := by
  induction N generalizing f with
  | zero => rfl
  | succ N ih => rw [approxList, List.length_cons, ih (fun k => f (k + 1))]

theorem approxList_getD (f : ℕ → GaussianRat) (N i : ℕ) (hi : i < N + 1) :
    (approxList f N).getD i 0 = f i := by
  induction N generalizing i f with
  | zero =>
    have hi0 : i = 0 := by omega
    subst hi0
    rfl
  | succ N ih =>
    cases i with
    | zero => rfl
    | succ i =>
      rw [approxList, List.getD_cons_succ]
      exact ih (fun k => f (k + 1)) i (by omega)

theorem certRefA_coeff_zero (γ : ℂ) (A B : Polynomial ℂ) {i : ℕ}
    (hA : A.natDegree < i) (hB : B.natDegree < i) :
    (certRefA γ A B).coeff i = 0 := by
  rw [certRefA_coeff,
    Polynomial.coeff_eq_zero_of_natDegree_lt hA,
    Polynomial.coeff_eq_zero_of_natDegree_lt hB]
  ring

theorem certRefB_coeff_zero (γ : ℂ) (A B : Polynomial ℂ) {i : ℕ}
    (hA : A.natDegree < i) (hB : B.natDegree < i) :
    (certRefB γ A B).coeff i = 0 := by
  rw [certRefB_coeff,
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : B.natDegree < i + 1),
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : A.natDegree < i + 1)]
  ring

theorem certSteps_more {η γc : ℝ} {A B : Polynomial ℂ} (s : CertStepData η A B)
    (hdiv : γc ≤ ‖A.coeff 0‖) (r : CertLayerStrip η γc s.A' s.B') :
    (CertLayerStrip.more A B s hdiv r).certSteps = r.certSteps + 1 := rfl

theorem exists_ratRotPair (η : ℝ) (hη : 0 < η) (γ : ℂ) (A B : Polynomial ℂ) :
    ∃ a1 b1 : List GaussianRat,
      (∀ i, ‖(ratPoly a1).coeff i - (certRefA γ A B).coeff i‖ ≤ η) ∧
      (∀ i, ‖(ratPoly b1).coeff i - (certRefB γ A B).coeff i‖ ≤ η) := by
  have hrA : ∀ i : ℕ, ∃ g : GaussianRat,
      ‖gaussianRatComplex g - (certRefA γ A B).coeff i‖ ≤ η :=
    fun i => ratApprox _ η hη
  choose gA hgA using hrA
  have hrB : ∀ i : ℕ, ∃ g : GaussianRat,
      ‖gaussianRatComplex g - (certRefB γ A B).coeff i‖ ≤ η :=
    fun i => ratApprox _ η hη
  choose gB hgB using hrB
  obtain ⟨N, hNA, hNB⟩ : ∃ N : ℕ, A.natDegree ≤ N ∧ B.natDegree ≤ N :=
    ⟨Nat.max A.natDegree B.natDegree, Nat.le_max_left _ _, Nat.le_max_right _ _⟩
  refine ⟨approxList gA N, approxList gB N, ?_, ?_⟩
  · intro i
    rw [ratPoly_coeff]
    by_cases hi : i < N + 1
    · rw [approxList_getD gA N i hi]
      exact hgA i
    · rw [list_getD_default _ i (by rw [approxList_length]; omega),
        gaussianRatComplex_zero, certRefA_coeff_zero _ _ _ (by omega) (by omega),
        sub_zero, norm_zero]
      exact hη.le
  · intro i
    rw [ratPoly_coeff]
    by_cases hi : i < N + 1
    · rw [approxList_getD gB N i hi]
      exact hgB i
    · rw [list_getD_default _ i (by rw [approxList_length]; omega),
        gaussianRatComplex_zero, certRefB_coeff_zero _ _ _ (by omega) (by omega),
        sub_zero, norm_zero]
      exact hη.le

theorem frontier3 (η : ℝ) (hη : 0 < η) (a0 b0 : List GaussianRat) (n : ℕ) :
    ∃ r : CertLayerStrip η 0 (ratPoly a0) (ratPoly b0),
      r.certSteps = n ∧ r.certOps = 4 * n ^ 2 + 12 * n := by
  induction n generalizing a0 b0 with
  | zero =>
    refine ⟨CertLayerStrip.stop (ratPoly a0) (ratPoly b0), ?_, ?_⟩
    · simp [CertLayerStrip.certSteps]
    · simp [CertLayerStrip.certOps]
  | succ n ih =>
    obtain ⟨gγ, hgγ⟩ :=
      ratApprox ((ratPoly b0).coeff 0 / (ratPoly a0).coeff 0) η hη
    obtain ⟨a1, b1, hrotA, hrotB⟩ :=
      exists_ratRotPair η hη (gaussianRatComplex gγ) (ratPoly a0) (ratPoly b0)
    obtain ⟨rest, hrestSteps, hrestOps⟩ := ih a1 b1
    refine ⟨CertLayerStrip.more (ratPoly a0) (ratPoly b0)
      ⟨gaussianRatComplex gγ, ratPoly a1, ratPoly b1, hgγ, hrotA, hrotB⟩
      (norm_nonneg ((ratPoly a0).coeff 0)) rest, ?_, ?_⟩
    · rw [certSteps_more, hrestSteps]
    · rw [CertLayerStrip.certOps_eq, certSteps_more, hrestSteps]

theorem gaussianRatComplex_eq_zero (z : GaussianRat) :
    gaussianRatComplex z = 0 ↔ z = 0 := by
  obtain ⟨q1, q2⟩ := z
  constructor
  · intro h
    have hre := (Complex.ext_iff.mp h).1
    have him := (Complex.ext_iff.mp h).2
    simp only [gaussianRatComplex] at hre him
    norm_num at hre him
    exact Prod.ext_iff.mpr ⟨hre, him⟩
  · intro h
    rw [h]
    simp [gaussianRatComplex_zero]

theorem frontier3_nondeg (η : ℝ) (hη : 0 < η) :
    ∀ (n : ℕ) (γc : ℝ) (a0 b0 : List GaussianRat),
      0 < γc → γc + n * η ≤ ‖(ratPoly a0).coeff 0‖ →
      ∃ r : CertLayerStrip η γc (ratPoly a0) (ratPoly b0),
        r.certSteps = n ∧ r.certOps = 4 * n ^ 2 + 12 * n := by
  intro n
  induction n with
  | zero =>
    intro γc a0 b0 hγc _
    exact ⟨CertLayerStrip.stop (ratPoly a0) (ratPoly b0),
      rfl, rfl⟩
  | succ n ih =>
    intro γc a0 b0 hγc hbudget
    rw [Nat.cast_succ] at hbudget
    have hnpos : (0 : ℝ) ≤ n * η := mul_nonneg (Nat.cast_nonneg n) hη.le
    have hdiv : γc ≤ ‖(ratPoly a0).coeff 0‖ := by linarith
    have ha : (ratPoly a0).coeff 0 ≠ 0 := by
      intro h0
      rw [h0] at hdiv
      simp at hdiv
      exact absurd hdiv (not_le.mpr hγc)
    obtain ⟨a1, b1, hrotA, hrotB⟩ :=
      exists_ratRotPair η hη ((ratPoly b0).coeff 0 / (ratPoly a0).coeff 0)
        (ratPoly a0) (ratPoly b0)
    have hnorm := certRefA_exact_norm_ge (ratPoly a0) (ratPoly b0) ha
    have hrot0' : ‖(certRefA ((ratPoly b0).coeff 0 / (ratPoly a0).coeff 0)
        (ratPoly a0) (ratPoly b0)).coeff 0 - (ratPoly a1).coeff 0‖ ≤ η := by
      rw [norm_sub_rev]
      exact hrotA 0
    have hchain : ‖(certRefA ((ratPoly b0).coeff 0 / (ratPoly a0).coeff 0)
        (ratPoly a0) (ratPoly b0)).coeff 0‖
        ≤ ‖(ratPoly a1).coeff 0‖ + η := by
      have heq : (certRefA ((ratPoly b0).coeff 0 / (ratPoly a0).coeff 0)
          (ratPoly a0) (ratPoly b0)).coeff 0
          = (certRefA ((ratPoly b0).coeff 0 / (ratPoly a0).coeff 0)
              (ratPoly a0) (ratPoly b0)).coeff 0 - (ratPoly a1).coeff 0
            + (ratPoly a1).coeff 0 := by ring
      rw [heq]
      exact le_trans (norm_add_le _ _) (by linarith)
    have hsub : γc + n * η ≤ ‖(ratPoly a1).coeff 0‖ := by linarith
    obtain ⟨rest, hsteps, hops⟩ := ih γc a1 b1 hγc hsub
    refine ⟨CertLayerStrip.more (ratPoly a0) (ratPoly b0)
      ⟨(ratPoly b0).coeff 0 / (ratPoly a0).coeff 0, ratPoly a1, ratPoly b1,
        by simpa using hη.le, hrotA, hrotB⟩
      hdiv rest, ?_, ?_⟩
    · rw [certSteps_more, hsteps]
    · rw [CertLayerStrip.certOps_eq, certSteps_more, hsteps]

theorem exists_divisor_cert_rat (η : ℝ) (hη : 0 < η) (n : ℕ) (a0 : List GaussianRat)
    (hηn : n * η < ‖gaussianRatComplex (a0.getD 0 0)‖) :
    ∃ γ0 : ℚ, n * η < (γ0 : ℝ) ∧ (γ0 : ℝ) ≤ ‖(ratPoly a0).coeff 0‖ := by
  have hnz : (0 : ℝ) ≤ n * η := mul_nonneg (Nat.cast_nonneg n) hη.le
  have hne : gaussianRatComplex (a0.getD 0 0) ≠ 0 := by
    intro h
    have : ‖gaussianRatComplex (a0.getD 0 0)‖ = 0 := by
      rw [h, norm_zero]
    linarith
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hηn
  refine ⟨q, hq1, ?_⟩
  rw [ratPoly_coeff]
  exact le_of_lt hq2

theorem frontier3_nondeg_of_head (η : ℝ) (hη : 0 < η) (n : ℕ)
    (a0 b0 : List GaussianRat)
    (hηn : n * η < ‖gaussianRatComplex (a0.getD 0 0)‖) :
    ∃ γc : ℝ, 0 < γc ∧ ∃ r : CertLayerStrip η γc (ratPoly a0) (ratPoly b0),
      r.certSteps = n ∧ r.certOps = 4 * n ^ 2 + 12 * n := by
  obtain ⟨γ0, hγ1, hγ2⟩ := exists_divisor_cert_rat η hη n a0 hηn
  have h1 : (0 : ℝ) ≤ n * η := mul_nonneg (Nat.cast_nonneg n) hη.le
  have h2 : (γ0 : ℝ) - n * η + n * η = (γ0 : ℝ) := by linarith
  obtain ⟨r, hs, ho⟩ :=
    frontier3_nondeg η hη n ((γ0 : ℝ) - n * η) a0 b0 (by linarith) (by linarith)
  exact ⟨(γ0 : ℝ) - n * η, by linarith, r, hs, ho⟩

end Qatlib.Concepts.MonteCarloMean.PayoffRotation
