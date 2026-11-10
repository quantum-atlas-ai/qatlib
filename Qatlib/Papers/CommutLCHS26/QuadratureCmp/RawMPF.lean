/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.MPFRemainder
import Qatlib.Foundations.OperatorErrors.OperatorError
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.QuadratureCmp.RawMPF

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Papers.CommutLCHS26.MainResults.MPFRemainder

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]

private theorem power_error_succ (C V : Matrix I I ℂ)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (η : ℝ) (he : ‖C - V‖ ≤ η) (n : ℕ) :
    ‖C ^ (n + 1) - V ^ (n + 1)‖ ≤ ((n + 1 : ℕ) : ℝ) * η * (1 + η) ^ n := by
  have hη : 0 ≤ η := (norm_nonneg _).trans he
  have hC : ‖C‖ ≤ 1 + η := by
    have h := norm_add_le (C - V) V
    have hs : C - V + V = C := by abel
    rw [hs] at h
    linarith [l2_norm_unitary_le_one hV]
  induction n with
  | zero => simpa using! he
  | succ n ih =>
    have hs : C ^ (n + 1 + 1) - V ^ (n + 1 + 1) =
        C * (C ^ (n + 1) - V ^ (n + 1)) + (C - V) * V ^ (n + 1) := by
      rw [pow_succ' C (n + 1), pow_succ' V (n + 1)]
      noncomm_ring
    have hpow : 1 ≤ (1 + η) ^ (n + 1) := one_le_pow₀ (by linarith)
    have hfirst := mul_le_mul hC ih (norm_nonneg _) (by positivity :
      0 ≤ 1 + η)
    have hsecond := mul_le_mul he
      (l2_norm_pow_le_one V (l2_norm_unitary_le_one hV) (n + 1))
      (norm_nonneg _) hη
    rw [hs]
    calc
      _ ≤ ‖C‖ * ‖C ^ (n + 1) - V ^ (n + 1)‖ + ‖C - V‖ * ‖V ^ (n + 1)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ (1 + η) * (((n + 1 : ℕ) : ℝ) * η * (1 + η) ^ n) + η := by
        simpa only [mul_one] using! add_le_add hfirst hsecond
      _ ≤ (1 + η) * (((n + 1 : ℕ) : ℝ) * η * (1 + η) ^ n) +
          η * (1 + η) ^ (n + 1) :=
        _root_.add_le_add le_rfl (by simpa using! mul_le_mul_of_nonneg_left hpow hη)
      _ = _ := by push_cast; rw [pow_succ]; ring

theorem power_error (C V : Matrix I I ℂ) (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (η : ℝ) (he : ‖C - V‖ ≤ η) (r : ℕ) :
    ‖C ^ r - V ^ r‖ ≤ (r : ℝ) * η * (1 + η) ^ (r - 1) := by
  cases r with
  | zero => simp
  | succ n => simpa using! power_error_succ C V hV η he n

theorem weighted_power_error (C V : J → Matrix I I ℂ) (v : J → ℂ) (η : J → ℝ)
    (hV : ∀ i, V i ∈ Matrix.unitaryGroup I ℂ)
    (he : ∀ i, ‖C i - V i‖ ≤ η i) (r : ℕ) :
    ‖(∑ i, v i • C i ^ r) - (∑ i, v i • V i ^ r)‖ ≤
      (∑ i, ‖v i‖ * ‖C i ^ r - V i ^ r‖) ∧
    (∑ i, ‖v i‖ * ‖C i ^ r - V i ^ r‖) ≤
      (r : ℝ) * ∑ i, ‖v i‖ * η i * (1 + η i) ^ (r - 1) := by
  constructor
  · rw [← Finset.sum_sub_distrib]
    simp_rw [← smul_sub]
    simpa only [norm_smul] using! norm_sum_le Finset.univ (fun i => v i • (C i ^ r - V i ^ r))
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact (mul_le_mul_of_nonneg_left (power_error (C i) (V i) (hV i) (η i) (he i) r)
      (norm_nonneg _)).trans_eq (by ring)

theorem weighted_power_error_uniform (C V : J → Matrix I I ℂ) (v : J → ℂ)
    (η : J → ℝ) (E : ℝ) (hV : ∀ i, V i ∈ Matrix.unitaryGroup I ℂ)
    (he : ∀ i, ‖C i - V i‖ ≤ η i) (hE : ∀ i, η i ≤ E) (r : ℕ) :
    ‖(∑ i, v i • C i ^ r) - (∑ i, v i • V i ^ r)‖ ≤
      (1 + E) ^ (r - 1) * ((r : ℝ) * ∑ i, ‖v i‖ * η i) := by
  have h := weighted_power_error C V v η hV he r
  refine (h.1.trans h.2).trans ?_
  have hb (i : J) : (1 + η i) ^ (r - 1) ≤ (1 + E) ^ (r - 1) :=
    pow_le_pow_left₀ (by linarith [((norm_nonneg _).trans (he i))])
      (by linarith [hE i]) _
  have hn (i : J) : 0 ≤ η i := (norm_nonneg _).trans (he i)
  calc
    _ ≤ (r : ℝ) * ∑ i, ‖v i‖ * η i * (1 + E) ^ (r - 1) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hb i) (mul_nonneg (norm_nonneg _) (hn i)))
        (Nat.cast_nonneg r)
    _ = _ := by rw [← Finset.sum_mul]; ring

set_option backward.isDefEq.respectTransparency false in

theorem target_power (Z : Matrix I I ℂ) (T : ℝ) (r : ℕ) (hr : 0 < r) :
    NormedSpace.exp ((T / r) • Z) ^ r = NormedSpace.exp (T • Z) := by
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := .restrictScalars ℚ ℝ _
  rw [← NormedSpace.exp_nsmul]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  field_simp

theorem post_quadrature_chain
    (C : ℝ → ℝ → Matrix I I ℂ) (Z : ℝ → Matrix I I ℂ)
    (node : J → ℝ) (v : J → ℂ) (Φ : ℝ → ℝ) (Cm Rm R cap T : ℝ) (m r : ℕ)
    (hZ : ∀ k, (Z k)ᴴ = -Z k) (hr : 0 < r) (hT : 0 < T)
    (hstep : T / r ≤ cap) (hnodes : ∀ i, |node i| ≤ R)
    (hlocal : ∀ k, |k| ≤ R → ∀ s, 0 < s → s ≤ cap →
      ‖C k s - NormedSpace.exp (s • Z k)‖ ≤ Cm * s ^ (2 * m + 1) * Φ k + Rm) :
    let η := fun i => Cm * (T / r) ^ (2 * m + 1) * Φ (node i) + Rm
    ‖(∑ i, v i • (C (node i) (T / r)) ^ r) -
      (∑ i, v i • NormedSpace.exp (T • Z (node i)))‖ ≤
      (∑ i, ‖v i‖ * ‖(C (node i) (T / r)) ^ r - NormedSpace.exp (T • Z (node i))‖) ∧
    (∑ i, ‖v i‖ * ‖(C (node i) (T / r)) ^ r - NormedSpace.exp (T • Z (node i))‖) ≤
      (r : ℝ) * ∑ i, ‖v i‖ * η i * (1 + η i) ^ (r - 1) := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  have h := weighted_power_error (fun i => C (node i) (T / r))
    (fun i => NormedSpace.exp ((T / r) • Z (node i))) v
    (fun i => Cm * (T / r) ^ (2 * m + 1) * Φ (node i) + Rm)
    (fun i => general_trotter_exp_unitary _ _ (hZ (node i)))
    (fun i => hlocal (node i) (hnodes i) (T / r) (div_pos hT hrpos) hstep) r
  simpa only [target_power _ T r hr] using! h

theorem post_quadrature_profile [Nonempty J]
    (C : ℝ → ℝ → Matrix I I ℂ) (Z : ℝ → Matrix I I ℂ)
    (node : J → ℝ) (v : J → ℂ) (Φ : ℝ → ℝ) (Cm Rm R cap T : ℝ) (m r : ℕ)
    (hZ : ∀ k, (Z k)ᴴ = -Z k) (hr : 0 < r) (hT : 0 < T)
    (hstep : T / r ≤ cap) (hnodes : ∀ i, |node i| ≤ R)
    (hlocal : ∀ k, |k| ≤ R → ∀ s, 0 < s → s ≤ cap →
      ‖C k s - NormedSpace.exp (s • Z k)‖ ≤ Cm * s ^ (2 * m + 1) * Φ k + Rm) :
    let η := fun i => Cm * (T / r) ^ (2 * m + 1) * Φ (node i) + Rm
    let E := Finset.univ.sup' Finset.univ_nonempty η
    ‖(∑ i, v i • (C (node i) (T / r)) ^ r) -
      (∑ i, v i • NormedSpace.exp (T • Z (node i)))‖ ≤
      (1 + E) ^ (r - 1) *
        (Cm * T ^ (2 * m + 1) / (r : ℝ) ^ (2 * m) * (∑ i, ‖v i‖ * Φ (node i)) +
          (r : ℝ) * (∑ i, ‖v i‖) * Rm) := by
  classical
  (try dsimp only)
  let η := fun i => Cm * (T / r) ^ (2 * m + 1) * Φ (node i) + Rm
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  have he (i : J) : ‖C (node i) (T / r) - NormedSpace.exp ((T / r) • Z (node i))‖ ≤ η i :=
    hlocal (node i) (hnodes i) (T / r) (div_pos hT hrpos) hstep
  have h := weighted_power_error_uniform (fun i => C (node i) (T / r))
    (fun i => NormedSpace.exp ((T / r) • Z (node i))) v η
    (Finset.univ.sup' Finset.univ_nonempty η)
    (fun i => general_trotter_exp_unitary _ _ (hZ (node i))) he
    (fun i => Finset.le_sup' η (Finset.mem_univ i)) r
  have hscale : (r : ℝ) * (T / r) ^ (2 * m + 1) =
      T ^ (2 * m + 1) / (r : ℝ) ^ (2 * m) := by
    rw [div_pow, pow_succ (r : ℝ)]
    field_simp [ne_of_gt hrpos]
  have hsum : (∑ i, ‖v i‖ * η i) =
      Cm * (T / r) ^ (2 * m + 1) * (∑ i, ‖v i‖ * Φ (node i)) +
        (∑ i, ‖v i‖) * Rm := by
    dsimp only [η]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hrate : (r : ℝ) * (∑ i, ‖v i‖ * η i) =
      Cm * T ^ (2 * m + 1) / (r : ℝ) ^ (2 * m) * (∑ i, ‖v i‖ * Φ (node i)) +
        (r : ℝ) * (∑ i, ‖v i‖) * Rm := by
    rw [hsum]
    calc
      _ = Cm * ((r : ℝ) * (T / r) ^ (2 * m + 1)) *
          (∑ i, ‖v i‖ * Φ (node i)) + (r : ℝ) * (∑ i, ‖v i‖) * Rm := by ring
      _ = _ := by rw [hscale]; ring
  simpa only [target_power _ T r hr, hrate] using! h

theorem quadrature_from_coefficients {K : Type} [Fintype K]
    (ws : J → K → List (Matrix I I ℂ)) (a : K → ℝ) (Z : J → Matrix I I ℂ)
    (v : J → ℂ) (hZ : ∀ i, (Z i)ᴴ = -Z i) (T : ℝ) (d r : ℕ) (hr : 0 < r) :
    ‖(∑ i, v i • (multiProduct (ws i) a (T / r)) ^ r) -
      (∑ i, v i • NormedSpace.exp (T • Z i))‖ ≤
      (r : ℝ) * ∑ i, ‖v i‖ * localCertificate (ws i) a (Z i) (T / r) d *
        (1 + localCertificate (ws i) a (Z i) (T / r) d) ^ (r - 1) := by
  have hlocal (i : J) :
      ‖multiProduct (ws i) a (T / r) - NormedSpace.exp ((T / r) • Z i)‖ ≤
        localCertificate (ws i) a (Z i) (T / r) d :=
    local_error_from_coefficients (ws i) a (Z i) (T / r) d
  have h := weighted_power_error (fun i => multiProduct (ws i) a (T / r))
    (fun i => NormedSpace.exp ((T / r) • Z i)) v
    (fun i => localCertificate (ws i) a (Z i) (T / r) d)
    (fun i => general_trotter_exp_unitary (Z i) (T / r) (hZ i)) hlocal r
  simpa only [target_power _ T r hr] using! h.1.trans h.2

end Qatlib.Papers.CommutLCHS26.QuadratureCmp.RawMPF
