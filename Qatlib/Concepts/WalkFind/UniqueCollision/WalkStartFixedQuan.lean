/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.WalkStartFixedStat
import Qatlib.Concepts.WalkFind.WalkSpectrum.AlphaFromInputQuan
import Qatlib.Concepts.WalkFind.WalkSpectrum.JohnsonDiffusionAux
import Qatlib.Concepts.WalkFind.WalkSpectrum.WalkTypeTransportQuan

/-!
# The fixed Johnson-walk starting state

This module proves that the reduced starting vector is fixed by both diffusion steps under the
physical size assumptions. It also identifies the total type population with the cardinality of
the full Johnson basis and decomposes the uniform full starting state into its type vectors
[Ambainis2007ElementDistinctness].

The full search state is the type lift of the reduced evolution, and its marked amplitude equals
the corresponding reduced overlap. These identities connect the full collision-search walk to
its spectral reduction.

## Main statements

* `walkStartFixed`: the starting vector is fixed by the reduced walk.
* `jwStartBig_decompose`: the type decomposition of the uniform full starting state.
* `jwMarkedAmplitude_eq_reduced`: equality of the full and reduced marked amplitudes.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

open Qatlib.Concepts.WalkFind.WalkSpectrum
open Qatlib.Concepts.WalkFind.UniqueCollision

set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.UniqueCollision

open Matrix Qatlib.Concepts.WalkFind.UniqueCollision

/-- The sum of squared norms of the reduced starting amplitudes is `jwStartNormSq`. -/
theorem jwStart_normSq (k N r : ℕ) :
    (∑ i : Fin (2 * k + 1), ‖jwStart k N r i‖ ^ 2) = jwStartNormSq k N r := by
  unfold jwStartNormSq
  apply Finset.sum_congr rfl
  intro i _
  simp only [jwStart, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sq_sqrt (Nat.cast_nonneg _)

/-- If `jwStartNormSq` is positive, dividing the starting vector by its square root gives
squared norm one. -/
theorem jwNormalizedStart_normSq (k N r : ℕ) (h : 0 < jwStartNormSq k N r) :
    (∑ i : Fin (2 * k + 1),
      ‖jwStart k N r i / (Real.sqrt (jwStartNormSq k N r) : ℂ)‖ ^ 2) = 1 := by
  simp only [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [← Finset.sum_div, jwStart_normSq, Real.sq_sqrt (le_of_lt h), div_self (ne_of_gt h)]

/-- Under `k ≤ r` and `k < N-r`, the first reduced diffusion step fixes `jwStart`. -/
theorem jwStep1_start_fixed (k N r : ℕ) (hkr : k ≤ r) (hkNr : k < N-r) :
    jwStep1 k N r *ᵥ jwStart k N r = jwStart k N r := by
  apply jwStep1_fixed_of_pairs
  intro j a
  have hj : j.val ≤ k := Nat.le_of_lt j.isLt
  have hrN : r ≤ N := by omega
  let c : ℝ := (Nat.choose k j.val * Nat.choose (N-k) (r-j.val) : ℕ)
  let A : ℝ := c * (N-r-(k-j.val) : ℕ)
  let B : ℝ := c * (k-j.val : ℕ)
  have hc : 0 < c := by
    dsimp only [c]
    exact_mod_cast Nat.mul_pos (Nat.choose_pos hj) (Nat.choose_pos (by omega : r-j.val ≤ N-k))
  have hA : 0 ≤ A := mul_nonneg (le_of_lt hc) (Nat.cast_nonneg _)
  have hB : 0 ≤ B := mul_nonneg (le_of_lt hc) (Nat.cast_nonneg _)
  have hab : A+B = c * (N-r : ℕ) := by
    dsimp only [A,B]
    rw [← mul_add, ← Nat.cast_add]
    congr 1
    congr 1
    omega
  have hp : 0 < A+B := by rw [hab]; exact mul_pos hc (by exact_mod_cast (by omega : 0 < N-r))
  have he : B/(A+B) = (k-j.val : ℝ)/(N-r) := by
    rw [hab]
    dsimp only [B]
    rw [Nat.cast_sub hj, Nat.cast_sub hrN]
    exact mul_div_mul_left _ _ (ne_of_gt hc)
  have hv (b : Bool) : jwStart k N r (jwPairIndex k b j) =
      if b then (Real.sqrt B : ℂ) else (Real.sqrt A : ℂ) := by
    cases b <;> simp [jwStart, jwPairIndex, jwPsiCoord, Nat.add_div, Nat.add_mod,
      jwCnt, A, B, c, Nat.cast_mul]
  rw [hv false, hv true, hv a, ← he]
  exact jwD2_population_fixed A B hA hB hp a

/-- Under `k ≤ r` and `k < N-r`, the second reduced diffusion step fixes `jwStart`. -/
theorem jwStep2_start_fixed (k N r : ℕ) (hkr : k ≤ r) (hkNr : k < N-r) :
    jwStep2 k r *ᵥ jwStart k N r = jwStart k N r := by
  apply jwStep2_fixed_of_pairs
  intro j a
  let l := k-j.val
  have hj : j.val < k := j.isLt
  have hl : 1 ≤ l := by dsimp [l]; omega
  have hlk : l ≤ k := Nat.sub_le _ _
  have hlr : l ≤ r := le_trans hlk hkr
  let c : ℝ := (Nat.choose k l * Nat.choose (N-k) (r+1-l) : ℕ)
  let A : ℝ := c * (r+1-l : ℕ)
  let B : ℝ := c * (l : ℕ)
  have hc : 0 < c := by
    dsimp only [c]
    exact_mod_cast Nat.mul_pos (Nat.choose_pos hlk) (Nat.choose_pos (by omega : r+1-l ≤ N-k))
  have hA : 0 ≤ A := mul_nonneg (le_of_lt hc) (Nat.cast_nonneg _)
  have hB : 0 ≤ B := mul_nonneg (le_of_lt hc) (Nat.cast_nonneg _)
  have hab : A+B = c * (r+1 : ℕ) := by
    dsimp only [A,B]
    rw [← mul_add, ← Nat.cast_add]
    congr 1
    congr 1
    omega
  have hp : 0 < A+B := by rw [hab]; exact mul_pos hc (by positivity)
  have he : B/(A+B) = (k-j.val : ℝ)/(r+1) := by
    rw [hab]
    dsimp only [B,l]
    rw [Nat.cast_sub (Nat.le_of_lt hj), Nat.cast_add, Nat.cast_one]
    exact mul_div_mul_left _ _ (ne_of_gt hc)
  have coords (b : Bool) : jwPsiCoord k (jwPairIndex k b j).rev =
      (l - if b then 1 else 0, b) := by
    cases b <;> apply Prod.ext
    all_goals simp [jwPairIndex, jwPsiCoord, Fin.val_rev, l]
    all_goals omega
  have hv (b : Bool) : jwStart k N r (jwPairIndex k b j).rev =
      if b then (Real.sqrt B : ℂ) else (Real.sqrt A : ℂ) := by
    cases b
    · simp only [jwStart, coords, Bool.false_eq_true, if_false, Nat.sub_zero]
      rw [jwCnt_inserted_false k N r l hlr hlk (le_of_lt hkNr)]
      simp [A,c,Nat.cast_mul]
    · simp only [jwStart, coords, if_true]
      rw [jwCnt_inserted_true k N r l hl (by omega) hlk]
      simp [B,c,Nat.cast_mul]
  rw [hv false, hv true, hv a, ← he]
  exact jwD2_population_fixed A B hA hB hp a

/-- The reduced Johnson walk fixes the starting vector under the hypotheses of `WalkStartFixed`
[Ambainis2007ElementDistinctness]. -/
theorem walkStartFixed : WalkStartFixed := by
  intro k N r _ hkr hkNr
  rw [jwWalk, ← Matrix.mulVec_mulVec, jwStep1_start_fixed k N r hkr hkNr,
    jwStep2_start_fixed k N r hkr hkNr]

/-- Under the stated subset-size conditions, the total reduced population equals the number of
full Johnson states. -/
theorem jwStartNormSq_eq_basis_card (k N r : ℕ) (hkr : k ≤ r) (hkNr : k ≤ N-r)
    (hrN : r ≤ N) :
    jwStartNormSq k N r = (Fintype.card (JRState N r) : ℝ) := by
  rw [jwStartNormSq_eq k N r hkr hkNr hrN,jrState_card]
  push_cast
  rw [Nat.cast_sub hrN]

/-- For a `k`-element target set, the uniform full starting vector decomposes into type vectors
with normalized `jwStart` coefficients. -/
theorem jwStartBig_decompose (k N r : ℕ) (hkr : k ≤ r) (hkNr : k < N-r)
    (I : Finset (Fin N)) (hI : I.card = k) :
    jwStartBig N r = ∑ i : Fin (2*k+1),
      (jwStart k N r i / (Real.sqrt (jwStartNormSq k N r) : ℂ)) • jwPsiBigAt k N r I i := by
  rw [jwStartNormSq_eq_basis_card k N r hkr (le_of_lt hkNr) (by omega)]
  exact jwStartBig_decompose_card k N r hkr hkNr I hI

/-- For a `k`-element target set under the physical size assumptions, the initial marked
amplitude equals `jwAlpha`. -/
theorem jwMarkedAmplitude_zero_eq_alpha (k N r t2 : ℕ) (hkr : k ≤ r) (hkNr : k < N-r)
    (I : Finset (Fin N)) (hI : I.card = k) :
    jwMarkedAmplitude k N r 0 t2 I = (jwAlpha k N r : ℂ) := by
  rw [jwMarkedAmplitude_zero,jwGoodVec_eq_typeLast k N r I hI,
    jwStartBig_decompose k N r hkr hkNr I hI,
    jwPsiBigAt_inner_sum k N r hkr hkNr I hI]
  simp [jwStart,jwPsiCoord,jwAlpha]

/-- The full search state is the type lift of the reduced walk-and-flip evolution applied to the
normalized reduced starting vector. -/
theorem jwRunState_eq_typeLift (k N r : ℕ) (hkr : k ≤ r) (hkNr : k < N-r)
    (I : Finset (Fin N)) (hI : I.card = k) (t1 t2 : ℕ) :
    jwRunState k N r t1 t2 I = jwTypeLift k N r I
      ((jwWalk k N r ^ t2 * jwFlipTilde k) ^ t1 *ᵥ
        (fun i => jwStart k N r i / (Real.sqrt (jwStartNormSq k N r) : ℂ))) := by
  rw [jwRunState,show jwStartBig N r = jwTypeLift k N r I
      (fun i => jwStart k N r i / (Real.sqrt (jwStartNormSq k N r) : ℂ)) from
        jwStartBig_decompose k N r hkr hkNr I hI,
      jwRunMat_typeLift k N r hkr hkNr I hI]

/-- The full marked amplitude equals the reduced evolved state's overlap with `jwGoodTilde`. -/
theorem jwMarkedAmplitude_eq_reduced (k N r : ℕ) (hkr : k ≤ r) (hkNr : k < N-r)
    (I : Finset (Fin N)) (hI : I.card = k) (t1 t2 : ℕ) :
    jwMarkedAmplitude k N r t1 t2 I =
      ∑ i : Fin (2*k+1), star (jwGoodTilde k i) *
        ((jwWalk k N r ^ t2 * jwFlipTilde k) ^ t1 *ᵥ
          (fun i => jwStart k N r i / (Real.sqrt (jwStartNormSq k N r) : ℂ))) i := by
  rw [jwMarkedAmplitude,jwGoodVec_eq_typeLast k N r I hI,
    jwRunState_eq_typeLift k N r hkr hkNr I hI]
  unfold jwTypeLift
  rw [jwPsiBigAt_inner_sum k N r hkr hkNr I hI]
  have hc (i : Fin (2*k+1)) : jwPsiCoord k i = (k,false) ↔ i = Fin.last (2*k) := by
    have hl : jwPsiCoord k (Fin.last (2*k)) = (k,false) := by simp [jwPsiCoord]
    exact ⟨fun h => jwPsiCoord_injective k (h.trans hl.symm),fun h => h ▸ hl⟩
  simp [jwGoodTilde,hc]

end Qatlib.Concepts.WalkFind.UniqueCollision
