/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.ElementDistinctnessAlgorithmStat
import Qatlib.Concepts.WalkFind.UniqueCollision.SearchReadoutAux
import Qatlib.Concepts.WalkFind.UniqueCollision.WalkStartFixedQuan
import Qatlib.Concepts.WalkFind.UniqueCollision.WalkUnitaryQuan
import Qatlib.Concepts.WalkFind.WalkSpectrum.WalkPhaseGapQuan
import Qatlib.Concepts.WalkFind.GroverInterp.GroverInterpolationQuan
set_option warningAsError false
open Qatlib.Concepts.WalkFind.GroverInterp
open Qatlib.Concepts.WalkFind.WalkSpectrum
open Qatlib.Concepts.WalkFind.UniqueCollision

set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.UniqueCollision
open Matrix Qatlib.Concepts.WalkFind.UniqueCollision

theorem jwGoodTilde_eq_last (k : ℕ) :
    jwGoodTilde k = fun i => if i = Fin.last (2 * k) then 1 else 0 := by
  funext i
  have hc : jwPsiCoord k i = (k, false) ↔ i = Fin.last (2 * k) := by
    have hl : jwPsiCoord k (Fin.last (2 * k)) = (k, false) := by simp [jwPsiCoord]
    exact ⟨fun h => jwPsiCoord_injective k (h.trans hl.symm), fun h => h ▸ hl⟩
  simp [jwGoodTilde, hc]

theorem jwReducedFlip_search_inputs (k : ℕ) :
    star (jwFlipTilde k) * jwFlipTilde k = 1 ∧
      (∑ i, ‖jwGoodTilde k i‖ ^ 2) = 1 ∧
      (∀ i, (jwGoodTilde k i).im = 0) ∧
      jwFlipTilde k *ᵥ jwGoodTilde k = -jwGoodTilde k ∧
      ∀ v : Fin (2 * k + 1) → ℂ,
        (∑ i, star (v i) * jwGoodTilde k i) = 0 → jwFlipTilde k *ᵥ v = v := by
  classical
  have hd := jwFlipTilde_eq_diagonal k
  have hc (i : Fin (2 * k + 1)) : jwPsiCoord k i = (k, false) ↔ i = Fin.last (2 * k) := by
    have hl : jwPsiCoord k (Fin.last (2 * k)) = (k, false) := by simp [jwPsiCoord]
    exact ⟨fun h => jwPsiCoord_injective k (h.trans hl.symm), fun h => h ▸ hl⟩
  rw [hd]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = Fin.last (2 * k) <;>
      simp [hc, h, Matrix.diagonal_apply, Matrix.one_apply]
  · simp [jwGoodTilde_eq_last, apply_ite]
  · intro i
    simp [jwGoodTilde_eq_last, apply_ite]
  · ext i
    simp only [Matrix.mulVec_diagonal, jwGoodTilde_eq_last, hc, Pi.neg_apply]
    split_ifs <;> norm_num
  · intro v hv
    have hvlast : v (Fin.last (2 * k)) = 0 := by
      have hs : star (v (Fin.last (2 * k))) = 0 := by
        simpa [jwGoodTilde_eq_last] using hv
      simpa using congrArg star hs
    ext i
    simp only [Matrix.mulVec_diagonal, hc]
    by_cases hi : i = Fin.last (2 * k)
    · simp [hi, hvlast]
    · simp [hi]

theorem jwSearch_unitary_pow {m : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (hu : star U * U = 1) (t : ℕ) : star (U ^ t) * U ^ t = 1 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', star_mul]
    calc
      star (U ^ t) * star U * (U * U ^ t) =
          star (U ^ t) * (star U * U) * U ^ t := by simp only [mul_assoc]
      _ = 1 := by rw [hu, mul_one, ih]

theorem jwSearch_real_pow {m : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (hU : ∀ i j, (U i j).im = 0) (t : ℕ) : ∀ i j, ((U ^ t) i j).im = 0 := by
  induction t with
  | zero => intro i j; simp [Matrix.one_apply, apply_ite]
  | succ t ih =>
    intro i j
    rw [pow_succ']
    simp [Matrix.mul_apply, Complex.mul_im, hU, ih]

theorem jwNormalizedSearch_inputs (k N r t : ℕ) (hk : 1 ≤ k)
    (hkr : k ≤ r) (hkNr : k < N - r) :
    let start := fun i => jwStart k N r i / (Real.sqrt (jwStartNormSq k N r) : ℂ)
    0 < jwStartNormSq k N r ∧
      (∑ i, ‖start i‖ ^ 2) = 1 ∧
      (∀ i, (start i).im = 0) ∧
      (∑ i, star (jwGoodTilde k i) * start i) = (jwAlpha k N r : ℂ) ∧
      jwWalk k N r ^ t *ᵥ start = start ∧
      star (jwWalk k N r ^ t) * jwWalk k N r ^ t = 1 ∧
      (∀ i j, ((jwWalk k N r ^ t) i j).im = 0) := by
  have hrN : r ≤ N := by omega
  have hNr : 0 < N - r := by omega
  have hcount : 0 < jwStartNormSq k N r := by
    rw [jwStartNormSq_eq k N r hkr hkNr.le hrN, ← Nat.cast_sub hrN]
    exact mul_pos (Nat.cast_pos.mpr (Nat.choose_pos hrN)) (Nat.cast_pos.mpr hNr)
  let start := fun i => jwStart k N r i / (Real.sqrt (jwStartNormSq k N r) : ℂ)
  change 0 < jwStartNormSq k N r ∧ (∑ i, ‖start i‖ ^ 2) = 1 ∧ _
  have heq : start = (Real.sqrt (jwStartNormSq k N r) : ℂ)⁻¹ • jwStart k N r := by
    funext i
    simp [start, div_eq_mul_inv, mul_comm]
  have hfix : jwWalk k N r *ᵥ start = start := by
    rw [heq, Matrix.mulVec_smul, walkStartFixed k N r hk hkr hkNr]
  have hpow : jwWalk k N r ^ t *ᵥ start = start := by
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hfix]
  refine ⟨hcount, jwNormalizedStart_normSq k N r hcount, ?_, ?_, hpow, ?_, ?_⟩
  · intro i
    simp [jwStart]
  · change (∑ i, star (jwGoodTilde k i) *
      (jwStart k N r i / (Real.sqrt (jwStartNormSq k N r) : ℂ))) = _
    simp only [← mul_div_assoc, ← Finset.sum_div, jwGoodTilde_overlap]
    exact_mod_cast (show Real.sqrt (jwCnt k N r k false) /
      Real.sqrt (jwStartNormSq k N r) = jwAlpha k N r from rfl)
  · exact jwSearch_unitary_pow _ ((walkUnitary k N r hkNr.le (by omega)).2.2.1) t
  · exact jwSearch_real_pow _ (jwWalk_real k N r) t

theorem jwElementDistinctnessAlgorithm_from_interpolation
    (hGrover : GroverInterpolation) : ElementDistinctnessAlgorithm := by
  intro k N r hk hkr hr hsize I hI
  have hkNr := jwWalk_size_physical k N r hk hsize
  obtain ⟨hε, hε1⟩ := jwEpsArc_bounds k r hk hkr
  obtain ⟨_, _, _, hα, hα1⟩ := alphaFromInput k N r hk hkr hkNr
  obtain ⟨hcount, hsn, hsreal, hoverlap, hsfix, hU, hUreal⟩ :=
    jwNormalizedSearch_inputs k N r (jwT2 k r) hk hkr hkNr
  obtain ⟨hflipU, hgn, hgreal, hflipgood, hflipfix⟩ := jwReducedFlip_search_inputs k
  let start := fun i => jwStart k N r i / (Real.sqrt (jwStartNormSq k N r) : ℂ)
  have hsqrt : (Real.sqrt (jwStartNormSq k N r) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hcount)
  have hphase : ∀ (ν : ℂ) (v : Fin (2 * k + 1) → ℂ),
      jwWalk k N r ^ jwT2 k r *ᵥ v = ν • v →
      (∑ i, star (v i) * start i) = 0 → v ≠ 0 →
      ∃ θ : ℝ, jwEpsArc k r ≤ θ ∧ θ ≤ 2 * Real.pi - jwEpsArc k r ∧
        θ ≠ Real.pi ∧ ν = Complex.exp (Complex.I * θ) := by
    intro ν v he ho hv
    have ho' : (∑ i, star (v i) * jwStart k N r i) = 0 := by
      change (∑ i, star (v i) * (jwStart k N r i /
        (Real.sqrt (jwStartNormSq k N r) : ℂ))) = 0 at ho
      simp only [← mul_div_assoc, ← Finset.sum_div] at ho
      exact (div_eq_zero_iff.mp ho).resolve_right hsqrt
    exact jwWalk_powered_phase_gap k N r hk hkr hr hsize ν v he ho' hv
  obtain ⟨t1, ht1, hamp⟩ := hGrover (2 * k + 1) (jwEpsArc k r) (jwAlpha k N r)
    hε hε1 hα hα1 (jwFlipTilde k) (jwWalk k N r ^ jwT2 k r) start (jwGoodTilde k)
    hflipU hU hUreal hsreal hgreal hsn hgn hoverlap hflipgood hflipfix hsfix hphase
  refine ⟨t1, ht1, ?_, ?_⟩
  · rw [jwMarkedAmplitude_eq_reduced k N r hkr hkNr I hI t1 (jwT2 k r)]
    exact hamp
  · have h := mul_le_mul_of_nonneg_right ht1
      (by positivity : (0 : ℝ) ≤ 2 * (jwT2 k r : ℝ))
    push_cast
    calc
      (r : ℝ) + 2 * t1 * jwT2 k r = (r : ℝ) + (t1 : ℝ) * (2 * jwT2 k r) := by ring
      _ ≤ (r : ℝ) + (8 / (jwEpsArc k r * jwAlpha k N r)) * (2 * jwT2 k r) :=
        add_le_add (le_refl (r : ℝ)) h
      _ = _ := by ring

theorem elementDistinctnessAlgorithm : ElementDistinctnessAlgorithm :=
  jwElementDistinctnessAlgorithm_from_interpolation groverInterpolation

theorem elementDistinctnessAlgorithm_answer : ElementDistinctnessAlgorithm :=
  elementDistinctnessAlgorithm

end Qatlib.Concepts.WalkFind.UniqueCollision
