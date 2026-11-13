/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Defs
import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Kraus
import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Tools
import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic

/-!
# An Euler-chain branch calculation and counterexample

This module evaluates the all-false measurement branch of the six-vertex Euler chain when only
the first angle is nonzero. It expands the entangler into local frame and controlled-Z phases,
reduces the resulting finite sums, and computes an entry of the branch applied to the identity.
These calculations concern the concrete real exponential measurement vectors in `mpSVector`,
within the cluster computation framework motivated by [RaussendorfBriegel2000].

The resulting entry is `(1 + exp(-t)^2)^2 / 128`. At `t = log 2`, it contradicts the value
required by a uniformly weighted unitary branch formula, yielding a counterexample to the
assertion that this formula holds for every angle assignment under the present definitions.

## Main statements

* `euler_adaptive` gives the angles on the all-false branch.
* `euler_ent_diag` and `euler_ent_off` identify the diagonal entangler.
* `euler_corePre_val` evaluates the branch core entrywise.
* `euler_channel_I00` computes the branch's `(0,0)` entry on the identity.
* `Basic.clause7_counter_clause2` rules out the universal unitary branch formula for this
  Euler-pattern definition.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000], *Quantum computing via measurements
  only*.
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic

set_option autoImplicit false
set_option maxHeartbeats 800000

open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open scoped BigOperators Classical

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire
open scoped BigOperators Classical
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra

/-- The all-false outcome string for the five measured vertices of the Euler chain. -/
def s0 : Fin 5 → Bool := fun _ => false

/-- The five-angle assignment whose zeroth angle is `t` and whose other angles are zero. -/
def theta (t : ℝ) : Fin 5 → ℝ := fun j => if j = 0 then t else 0

/-- The parity of any selected coordinates of an all-false outcome string is false. -/
theorem mpParity_false {k : ℕ} (S : Finset (Fin k)) :
    mpParity S (fun _ => false) = false := by
  simp [mpParity]

/-- Both adaptive-angle control parities vanish on the all-false Euler-chain outcome string. -/
theorem euler_parities (t : ℝ) (j : Fin 5) :
    mpParity ((mpEulerPattern (theta t)).angleSign j) s0 = false ∧
      mpParity ((mpEulerPattern (theta t)).angleShift j) s0 = false :=
  ⟨mpParity_false _, mpParity_false _⟩

/-- For `theta t` and the all-false outcome string, the adaptive Euler-chain angle is `-t` at
index zero and zero elsewhere. -/
theorem euler_adaptive (t : ℝ) (j : Fin 5) :
    mpAdaptiveAngle (mpEulerPattern (theta t)) s0 j = if j = 0 then -t else 0 := by
  have hp := euler_parities t j
  have hbase : (mpEulerPattern (theta t)).baseAngle j = -(theta t j) := rfl
  unfold mpAdaptiveAngle
  rw [hp.1, hp.2, hbase]
  by_cases hj : j = 0
  · subst hj
    simp [theta]
  · simp [theta, hj]

/-- The five successive directed edges of the six-vertex path from zero to five. -/
def eulerE : Finset (Fin 6 × Fin 6) :=
  {(⟨0, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩),
    (⟨2, by omega⟩, ⟨3, by omega⟩), (⟨3, by omega⟩, ⟨4, by omega⟩),
    (⟨4, by omega⟩, ⟨5, by omega⟩)}

/-- The filtered consecutive-vertex edge set used in `mpEulerPattern` equals the explicit path
edge set `eulerE`. -/
theorem eulerEdges_eq :
    (Finset.univ.filter fun p : Fin 6 × Fin 6 =>
      ∃ k : ℕ, k + 1 < 6 ∧ (p.1 : ℕ) = k ∧ (p.2 : ℕ) = k + 1) = eulerE := by
  have key : ∀ p : Fin 6 × Fin 6,
      (p ∈ (Finset.univ.filter fun p : Fin 6 × Fin 6 =>
        ∃ k : ℕ, k + 1 < 6 ∧ (p.1 : ℕ) = k ∧ (p.2 : ℕ) = k + 1)) ↔ p ∈ eulerE := by
    intro p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨i, j⟩ := p
    constructor
    · rintro ⟨k, hk, h1, h2⟩
      have h1' : (i : ℕ) = k := h1
      have h2' : (j : ℕ) = k + 1 := h2
      have hval : (j : ℕ) = (i : ℕ) + 1 := by omega
      fin_cases i <;> fin_cases j
      all_goals simp [eulerE] at hval ⊢
    · intro h
      fin_cases i <;> fin_cases j
      all_goals simp [eulerE] at h
      all_goals first
        | exact ⟨0, by decide, by decide, by decide⟩
        | exact ⟨1, by decide, by decide, by decide⟩
        | exact ⟨2, by decide, by decide, by decide⟩
        | exact ⟨3, by decide, by decide, by decide⟩
        | exact ⟨4, by decide, by decide, by decide⟩
  exact Finset.ext fun p => key p

/-- The Euler-pattern entangler for `theta t` is the source-pulse matrix on `eulerE`. -/
theorem euler_ent_eq (t : ℝ) :
    (mpEulerPattern (theta t)).entangler = Qatlib.Concepts.MbqcFlow.FlowDecision.sourcePulse eulerE := by
  rw [show (mpEulerPattern (theta t)).entangler
      = Qatlib.Concepts.MbqcFlow.FlowDecision.sourcePulse
          (Finset.univ.filter fun p : Fin 6 × Fin 6 =>
            ∃ k : ℕ, k + 1 < 6 ∧ (p.1 : ℕ) = k ∧ (p.2 : ℕ) = k + 1) from rfl,
    eulerEdges_eq]

/-- A product over `Fin 6` is the ordered product of the six values at indices zero through
five. -/
theorem prod_fin6 (g : Fin 6 → ℂ) :
    (∏ v : Fin 6, g v) = g 0 * g 1 * g 2 * g 3 * g 4 * g 5 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ,
    Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_zero]
  simp only [mul_one]
  show g 0 * (g 1 * (g 2 * (g 3 * (g 4 * g 5)))) = g 0 * g 1 * g 2 * g 3 * g 4 * g 5
  ring

/-- The diagonal frame entry of the Euler path is the product of the single-bit signs at
vertices one through five. -/
theorem euler_frame (x : Reg 6) :
    Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix eulerE x x
      = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 1) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 2)
          * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 3) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 4)
          * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 5) := by
  rw [Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix, Matrix.diagonal_apply,
      if_pos (rfl : x = x)]
  rw [prod_fin6]
  have h0 : Qatlib.Concepts.MbqcFlow.FlowDecision.incomingOdd eulerE 0 = false := by decide
  have h1 : Qatlib.Concepts.MbqcFlow.FlowDecision.incomingOdd eulerE 1 = true := by decide
  have h2 : Qatlib.Concepts.MbqcFlow.FlowDecision.incomingOdd eulerE 2 = true := by decide
  have h3 : Qatlib.Concepts.MbqcFlow.FlowDecision.incomingOdd eulerE 3 = true := by decide
  have h4 : Qatlib.Concepts.MbqcFlow.FlowDecision.incomingOdd eulerE 4 = true := by decide
  have h5 : Qatlib.Concepts.MbqcFlow.FlowDecision.incomingOdd eulerE 5 = true := by decide
  rw [h0, h1, h2, h3, h4, h5]
  simp [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase]

/-- The diagonal controlled-Z entry of the Euler path is the product of the five adjacent-pair
bit phases. -/
theorem euler_cz (x : Reg 6) :
    Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix eulerE x x
      = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 0 && x 1) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 1 && x 2)
          * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 2 && x 3) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 3 && x 4)
          * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 4 && x 5) := by
  rw [Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix, Matrix.diagonal_apply, if_pos (rfl : x = x)]
  show (∏ e ∈ eulerE, if x e.1 && x e.2 then (-1 : ℂ) else 1) = _
  rw [eulerE]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  simp [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase]

/-- The product of the local frame signs at vertices one through five and the controlled-Z signs
on all five Euler-path edges. -/
def eulerPhase (x : Reg 6) : ℂ :=
  (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 1) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 2)
      * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 3) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 4)
      * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 5))
    * (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 0 && x 1) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 1 && x 2)
      * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 2 && x 3) * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 3 && x 4)
      * Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 4 && x 5))

/-- Every diagonal entry of the Euler-pattern entangler equals the corresponding explicit phase
`eulerPhase x`. -/
theorem euler_ent_diag (t : ℝ) (x : Reg 6) :
    (mpEulerPattern (theta t)).entangler x x = eulerPhase x := by
  rw [euler_ent_eq, Qatlib.Concepts.MbqcFlow.FlowDecision.sourcePulse_eq_frame_cz]
  rw [Matrix.mul_apply, Finset.sum_eq_single x]
  · rw [euler_frame, euler_cz]
    rfl
  · intro k _ hk
    rw [Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix, Matrix.diagonal_apply,
        if_neg (Ne.symm hk), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Every off-diagonal entry of the Euler-pattern entangler is zero. -/
theorem euler_ent_off (t : ℝ) (x y : Reg 6) (h : x ≠ y) :
    (mpEulerPattern (theta t)).entangler x y = 0 := by
  rw [euler_ent_eq, Qatlib.Concepts.MbqcFlow.FlowDecision.sourcePulse_eq_frame_cz, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k = x
  · subst hk
    rw [Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix, Matrix.diagonal_apply, if_neg h, mul_zero]
  · rw [Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix, Matrix.diagonal_apply,
      if_neg (Ne.symm hk), zero_mul]

/-- Each amplitude of the uniform five-qubit vector is the inverse of `sqrt 32`. -/
theorem uniform5 (x : Reg 5) : Uniform (Reg 5) x = ((Real.sqrt 32 : ℝ) : ℂ)⁻¹ := by
  show ((Real.sqrt (Fintype.card (Reg 5)) : ℝ) : ℂ)⁻¹ = _
  rw [card_reg]
  norm_num

/-- The Euler-chain loading entry is `1 / sqrt 32` when its zeroth register bit agrees with the
input bit, and zero otherwise. -/
theorem euler_load (t : ℝ) (d : Reg 6) (y : Reg 1) :
    mpLoadMatrix (mpEulerPattern (theta t)) (Uniform (Reg 5)) d y
      = if d 0 = y 0 then ((Real.sqrt 32 : ℝ) : ℂ)⁻¹ else 0 := by
  simp only [mpLoadMatrix, Matrix.of_apply]
  by_cases h : ∀ i : Fin 1, d (Fin.castLE (by omega : (1:ℕ) ≤ 5 + 1) i) = y i
  · rw [if_pos h]
    have h0 : d 0 = y 0 := h ⟨0, by omega⟩
    rw [if_pos h0]
    exact uniform5 _
  · rw [if_neg h]
    have h0 : ¬ d 0 = y 0 := by
      intro hh
      apply h
      intro i
      fin_cases i
      exact hh
    rw [if_neg h0]

/-- Entangling the loaded uniform resource gives `eulerPhase d / sqrt 32` when the first
register bit matches the input, and zero otherwise. -/
theorem euler_EL (t : ℝ) (d : Reg 6) (y : Reg 1) :
    ((mpEulerPattern (theta t)).entangler
        * mpLoadMatrix (mpEulerPattern (theta t)) (Uniform (Reg 5))) d y
      = if d 0 = y 0 then (eulerPhase d * ((Real.sqrt 32 : ℝ) : ℂ)⁻¹) else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single d]
  · rw [euler_ent_diag, euler_load]
    by_cases h : d 0 = y 0
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      exact mul_zero _
  · intro d' _ hdne
    rw [euler_ent_off _ _ _ (Ne.symm hdne), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The Euler chain has no output `X` correction on the all-false outcome string. -/
theorem euler_xCorr (t : ℝ) : (mpEulerPattern (theta t)).xCorr 0 s0 = false := rfl

/-- The Euler chain has no output `Z` correction on the all-false outcome string. -/
theorem euler_zCorr (t : ℝ) : (mpEulerPattern (theta t)).zCorr 0 s0 = false := rfl

/-- On the all-false Euler-chain branch, the corrected output bit is the bit encoded by the
output index `xp`. -/
theorem euler_outBit (t : ℝ) (xp : Fin 2) :
    mpOutBit (mpEulerPattern (theta t)) s0 xp 0 = ((bitVecEquiv 1).symm xp 0) := by
  show xor ((mpEulerPattern (theta t)).xCorr 0 s0) ((bitVecEquiv 1).symm xp 0) = _
  rw [euler_xCorr]
  cases ((bitVecEquiv 1).symm xp 0) <;> rfl

/-- Under the one-qubit index equivalence, zero is the all-false register and one has its unique
bit true. -/
theorem bitVec1_symm : (bitVecEquiv 1).symm 0 = ZeroStr 1 ∧
    ((bitVecEquiv 1).symm 0 : Reg 1) 0 = false ∧
    ((bitVecEquiv 1).symm 1 : Reg 1) 0 = true := by
  refine ⟨bitVecEquiv_symm_zero 1, by decide, by decide⟩

/-- The register summand for the all-false Euler-chain core, combining conjugate measurement
amplitudes, the fixed output-bit constraint, and the entangled loading amplitude with input
bit `y0`. -/
noncomputable def eulerSummand (t : ℝ) (y0 e : Bool) : Reg 6 → ℂ := fun c =>
  (∏ j : Fin 5,
      star (mpSVector (mpAdaptiveAngle (mpEulerPattern (theta t)) s0 j) (s0 j)
        (c (Fin.castLE (by omega : 5 ≤ 5 + 1) j))))
    * (if ∀ v : Fin 1, c (Fin.natAdd 5 v) = e then (1 : ℂ) else 0)
    * (if c 0 = y0 then (eulerPhase c * ((Real.sqrt 32 : ℝ) : ℂ)⁻¹) else 0)

/-- Fixing every bit of the one-qubit output block to `e` is equivalent to fixing register
coordinate five to `e`. -/
theorem euler_delta_iff (c : Reg 6) (e : Bool) :
    (∀ v : Fin 1, c (Fin.natAdd 5 v) = e) ↔ (c 5 = e) := by
  constructor
  · intro h
    simpa using h ⟨0, by omega⟩
  · intro h v
    fin_cases v
    simpa using h

/-- The Euler-chain output constraint on the all-false branch is equivalent to equating register
coordinate five with the bit encoded by `xp`. -/
theorem euler_delta_iff_out (t : ℝ) (c : Reg 6) (xp : Fin 2) :
    (∀ v : Fin 1, c (Fin.natAdd 5 v) = mpOutBit (mpEulerPattern (theta t)) s0 xp v)
      ↔ (c 5 = (bitVecEquiv 1).symm xp 0) := by
  constructor
  · intro h
    exact (h ⟨0, by omega⟩).trans (euler_outBit t xp)
  · intro h v
    fin_cases v
    show c 5 = mpOutBit (mpEulerPattern (theta t)) s0 xp 0
    exact h.trans (euler_outBit t xp).symm

/-- The Euler core summand vanishes if either the input bit at coordinate zero or the output bit
at coordinate five violates its prescribed value. -/
theorem euler_summand_vanish (t : ℝ) (y0 e : Bool) (c : Reg 6) :
    (c 0 ≠ y0 ∨ c 5 ≠ e) → eulerSummand t y0 e c = 0 := by
  intro h
  rcases h with h | h
  · unfold eulerSummand
    rw [if_neg h, mul_zero]
  · unfold eulerSummand
    have h' : ¬ ∀ v : Fin 1, c (Fin.natAdd 5 v) = e :=
      fun hall => h ((euler_delta_iff c e).mp hall)
    rw [if_neg h', mul_zero, zero_mul]

/-- The product of the five conjugate measurement amplitudes on the all-false branch is `exp(-t)
/ (sqrt 2)^5` when the zeroth selected bit is true, and `1 / (sqrt 2)^5` otherwise. -/
theorem euler_sv_prod (t : ℝ) (f : Fin 5 → Bool) :
    (∏ j : Fin 5,
        star (mpSVector (mpAdaptiveAngle (mpEulerPattern (theta t)) s0 j) (s0 j) (f j)))
      = (((if f 0 then Real.exp (-t) else 1) / (Real.sqrt 2) ^ 5 : ℝ) : ℂ) := by
  have hterm : ∀ j : Fin 5,
      star (mpSVector (mpAdaptiveAngle (mpEulerPattern (theta t)) s0 j) (s0 j) (f j))
        = (((if j = 0 then (if f j then Real.exp (-t) else 1) else 1) / Real.sqrt 2 : ℝ) : ℂ) := by
    intro j
    rw [star_sv, euler_adaptive t j]
    by_cases hj : j = 0
    · subst hj
      simp only [if_true]
      rw [sv_eq_ofReal]
      simp [s0]
    · have hz : (if j = 0 then -t else 0) = 0 := by simp [hj]
      rw [hz]
      rw [sv_eq_ofReal]
      by_cases hc : f j
      · simp [s0, Real.exp_zero, hc, hj]
      · simp [s0, Real.exp_zero, hc, hj]
  rw [Finset.prod_congr rfl (fun j _ => hterm j), ← Complex.ofReal_prod]
  congr 1
  have hreal : (∏ j : Fin 5,
        ((if j = 0 then (if f j then Real.exp (-t) else 1) else 1) / Real.sqrt 2 : ℝ))
      = (if f 0 then Real.exp (-t) else 1) / Real.sqrt 2 ^ 5 := by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ,
      Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    rw [if_pos (rfl : (0 : Fin 5) = 0)]
    simp only [Fin.succ_ne_zero, if_false]
    have hne : (Real.sqrt 2 : ℝ) ≠ 0 := (Real.sqrt_ne_zero (by norm_num)).mpr (by norm_num)
    by_cases h : f 0
    · simp only [h, if_true]
      field_simp [hne]
    · simp only [h, if_false]
      field_simp [hne]
  exact hreal

/-- The real normalization factors satisfy `(sqrt 2)^5 * sqrt 32 = 32`. -/
theorem sqrt2_pow5_mul_sqrt32 : (Real.sqrt 2 ^ 5 * Real.sqrt 32 : ℝ) = 32 := by
  have h2 : (Real.sqrt 2 ^ 2 : ℝ) = 2 := Real.sq_sqrt (by norm_num)
  have h5 : (Real.sqrt 2 ^ 5 : ℝ) = 4 * Real.sqrt 2 := by
    rw [show (5:ℕ) = 2 + 2 + 1 by norm_num, pow_add, pow_add, pow_one, h2]
    ring
  have hs : (Real.sqrt 32 : ℝ) = 4 * Real.sqrt 2 := by
    rw [show (32:ℝ) = 16 * 2 by norm_num, Real.sqrt_mul (by norm_num)]
    rw [show Real.sqrt 16 = 4 by
      rw [show (16:ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  rw [h5, hs]
  have h : (4 * Real.sqrt 2) * (4 * Real.sqrt 2) = 16 * (Real.sqrt 2 * Real.sqrt 2) := by ring
  rw [h]
  have h2' : (Real.sqrt 2 * Real.sqrt 2 : ℝ) = 2 := by
    rw [← pow_two]
    exact h2
  rw [h2']
  norm_num

/-- Multiplying the complex image of `X / (sqrt 2)^5` by `1 / sqrt 32` gives the complex image
of `X / 32`. -/
theorem euler_const_prod (X : ℝ) :
    (((X / (Real.sqrt 2) ^ 5 : ℝ) : ℂ) * ((Real.sqrt 32 : ℝ) : ℂ)⁻¹)
      = (((X / 32 : ℝ) : ℂ)) := by
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
  congr 1
  have hreal : X / Real.sqrt 2 ^ 5 * (Real.sqrt 32)⁻¹ = X / 32 := by
    have hne : (Real.sqrt 2 ^ 5 : ℝ) ≠ 0 :=
      pow_ne_zero 5 ((Real.sqrt_ne_zero (by norm_num)).mpr (by norm_num))
    have hne2 : (Real.sqrt 32 : ℝ) ≠ 0 := (Real.sqrt_ne_zero (by norm_num)).mpr (by norm_num)
    field_simp [hne, hne2]
    rw [mul_assoc, sqrt2_pow5_mul_sqrt32]
  exact hreal

/-- Restricting a six-bit pinned register to its first five coordinates gives the corresponding
five-bit pinned register. -/
theorem pin6_castLE (a0 a1 a2 a3 a4 a5 : Bool) (h : 5 ≤ 5 + 1) (j : Fin 5) :
    pin6 a0 a1 a2 a3 a4 a5 (Fin.castLE h j) = pin5 a0 a1 a2 a3 a4 j := by
  fin_cases j <;> rfl

/-- With the input and output coordinates pinned, the Euler summand is `eulerPhase` times
`exp(-t) / 32` for a true input bit and `1 / 32` for a false input bit. -/
theorem euler_summand_pin (t : ℝ) (y0 e : Bool) (b1 b2 b3 b4 : Bool) :
    eulerSummand t y0 e (pin6 y0 b1 b2 b3 b4 e)
      = (((if y0 then Real.exp (-t) else 1) / 32 : ℝ) : ℂ)
          * eulerPhase (pin6 y0 b1 b2 b3 b4 e) := by
  unfold eulerSummand
  have hcast : ∀ (h : 5 ≤ 5 + 1) (j : Fin 5),
      pin6 y0 b1 b2 b3 b4 e (Fin.castLE h j) = pin5 y0 b1 b2 b3 b4 j :=
    fun h j => pin6_castLE y0 b1 b2 b3 b4 e h j
  simp only [hcast]
  have hd : (if ∀ v : Fin 1, pin6 y0 b1 b2 b3 b4 e (Fin.natAdd 5 v) = e
        then (1 : ℂ) else 0) = 1 := by
    apply if_pos
    intro v
    fin_cases v
    rfl
  have hl : (if pin6 y0 b1 b2 b3 b4 e 0 = y0
        then eulerPhase (pin6 y0 b1 b2 b3 b4 e) * ((Real.sqrt 32 : ℝ) : ℂ)⁻¹ else 0)
      = eulerPhase (pin6 y0 b1 b2 b3 b4 e) * ((Real.sqrt 32 : ℝ) : ℂ)⁻¹ :=
    if_pos (rfl : pin6 y0 b1 b2 b3 b4 e 0 = y0)
  rw [hd, hl, mul_one, euler_sv_prod, pin5_0]
  have hre : (eulerPhase (pin6 y0 b1 b2 b3 b4 e) * ((Real.sqrt 32 : ℝ) : ℂ)⁻¹)
      = (((Real.sqrt 32 : ℝ) : ℂ)⁻¹ * eulerPhase (pin6 y0 b1 b2 b3 b4 e)) := by ring
  rw [hre, ← mul_assoc, euler_const_prod]

/-- Summing the Euler-path phase over its four internal bits gives `4` when the output is true
and the input is false, and `-4` in the other cases. -/
theorem euler_phase_sum (y0 e : Bool) :
    ∑ b1, ∑ b2, ∑ b3, ∑ b4, eulerPhase (pin6 y0 b1 b2 b3 b4 e)
      = (if e && !y0 then (4 : ℂ) else -4) := by
  cases y0 <;> cases e
  all_goals simp only [sum_bool_eq]
  all_goals simp [eulerPhase, pin6, Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase, Bool.and, Bool.not]
  all_goals norm_num

/-- The full Euler summand sum is the input-dependent factor `(if y0 then exp(-t) else 1) / 32`
times `4` when `e && !y0` holds and `-4` otherwise. -/
theorem euler_core_sum (t : ℝ) (y0 e : Bool) :
    ∑ c : Reg 6, eulerSummand t y0 e c
      = (((if y0 then Real.exp (-t) else 1) / 32 : ℝ) : ℂ)
          * (if e && !y0 then (4 : ℂ) else -4) := by
  have hpin : ∀ b1 b2 b3 b4 : Bool,
      eulerSummand t y0 e (pin6 y0 b1 b2 b3 b4 e)
        = (((if y0 then Real.exp (-t) else 1) / 32 : ℝ) : ℂ)
            * eulerPhase (pin6 y0 b1 b2 b3 b4 e) :=
    fun b1 b2 b3 b4 => euler_summand_pin t y0 e b1 b2 b3 b4
  rw [sum_reg6_fixed _ y0 e (euler_summand_vanish t y0 e)]
  simp_rw [hpin]
  simp only [← Finset.mul_sum]
  rw [euler_phase_sum]

/-- The Euler-chain `corePre` entry on the all-false branch is the sum of `eulerSummand` with
the input bit and decoded output bit fixed by its indices. -/
theorem euler_corePre_eq (t : ℝ) (xp : Fin 2) (y : Reg 1) :
    corePre (mpEulerPattern (theta t)) (Uniform (Reg 5)) s0 xp y
      = ∑ c : Reg 6, eulerSummand t (y 0) ((bitVecEquiv 1).symm xp 0) c := by
  simp only [corePre, Matrix.of_apply]
  have hsign : (∏ k : Fin 1,
      if (mpEulerPattern (theta t)).zCorr k s0
          && mpOutBit (mpEulerPattern (theta t)) s0 xp k then (-1 : ℂ) else 1) = 1 := by
    rw [Fin.prod_univ_one]
    rw [show (mpEulerPattern (theta t)).zCorr 0 s0 = false from euler_zCorr t]
    simp
  rw [hsign, one_mul]
  apply Finset.sum_congr rfl
  intro c _
  show (∏ j : Fin 5, star (mpSVector (mpAdaptiveAngle (mpEulerPattern (theta t)) s0 j) (s0 j)
          (c (Fin.castLE (by omega : 5 ≤ 5 + 1) j))))
      * (if ∀ v : Fin 1, c (Fin.natAdd 5 v) = mpOutBit (mpEulerPattern (theta t)) s0 xp v
          then (1 : ℂ) else 0)
      * ((mpEulerPattern (theta t)).entangler
          * mpLoadMatrix (mpEulerPattern (theta t)) (Uniform (Reg 5))) c y
    = eulerSummand t (y 0) ((bitVecEquiv 1).symm xp 0) c
  rw [euler_EL]
  have heq : eulerSummand t (y 0) ((bitVecEquiv 1).symm xp 0) c
      = (∏ j : Fin 5, star (mpSVector (mpAdaptiveAngle (mpEulerPattern (theta t)) s0 j) (s0 j)
            (c (Fin.castLE (by omega : 5 ≤ 5 + 1) j))))
          * (if c 5 = (bitVecEquiv 1).symm xp 0 then (1 : ℂ) else 0)
          * (if c 0 = y 0 then eulerPhase c * ((Real.sqrt 32 : ℝ) : ℂ)⁻¹ else 0) := by
    unfold eulerSummand
    simp only [euler_delta_iff]
  simp only [euler_delta_iff_out t c xp]
  rw [heq]

/-- The Euler-chain `corePre` entry is `(if y 0 then exp(-t) else 1) / 32` times the
sign-weighted value `4` or `-4`, with `4` occurring exactly for a true output bit and false
input bit. -/
theorem euler_corePre_val (t : ℝ) (xp : Fin 2) (y : Reg 1) :
    corePre (mpEulerPattern (theta t)) (Uniform (Reg 5)) s0 xp y
      = (((if y 0 then Real.exp (-t) else 1) / 32 : ℝ) : ℂ)
          * (if ((bitVecEquiv 1).symm xp 0) && !(y 0) then (4 : ℂ) else -4) := by
  rw [euler_corePre_eq, euler_core_sum]

/-- An Euler-chain `core` entry is the corresponding `corePre` entry with its input index
decoded by `bitVecEquiv 1`. -/
theorem core_eq (t : ℝ) (xp yp : Fin 2) :
    core (mpEulerPattern (theta t)) (Uniform (Reg 5)) s0 xp yp
      = corePre (mpEulerPattern (theta t)) (Uniform (Reg 5)) s0 xp ((bitVecEquiv 1).symm yp) := by
  simp only [core, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm,
    Equiv.refl_apply]

/-- The `(0,0)` entry of the all-false Euler-chain core is `-1 / 8`, independently of `t`. -/
theorem euler_core00 (t : ℝ) :
    core (mpEulerPattern (theta t)) (Uniform (Reg 5)) s0 0 0 = ((-1 / 8 : ℝ) : ℂ) := by
  rw [core_eq, euler_corePre_val]
  have h0 : ((bitVecEquiv 1).symm 0 : Reg 1) 0 = false := (bitVec1_symm).2.1
  have he : ((bitVecEquiv 1).symm 0 : Reg 1) 0 = false := (bitVec1_symm).2.1
  simp only [h0, he, if_false, if_true, Bool.false_and, Bool.not_false, Bool.and_false]
  push_cast
  norm_num

/-- The `(0,1)` entry of the all-false Euler-chain core is `-exp(-t) / 8`. -/
theorem euler_core01 (t : ℝ) :
    core (mpEulerPattern (theta t)) (Uniform (Reg 5)) s0 0 1
      = ((-Real.exp (-t) / 8 : ℝ) : ℂ) := by
  rw [core_eq, euler_corePre_val]
  have h1 : ((bitVecEquiv 1).symm 1 : Reg 1) 0 = true := (bitVec1_symm).2.2
  have he : ((bitVecEquiv 1).symm 0 : Reg 1) 0 = false := (bitVec1_symm).2.1
  simp only [h1, he, if_true, if_false, Bool.false_and, Bool.not_true, Bool.and_false]
  push_cast
  norm_num
  ring

/-- Summing a function of only the first bit over five Boolean variables gives `16 * (g true + g
false)`. -/
theorem sum5_b0 (g : Bool → ℂ) :
    (∑ b0 : Bool, ∑ b1 : Bool, ∑ b2 : Bool, ∑ b3 : Bool, ∑ b4 : Bool, g b0)
      = 16 * (g true + g false) := by
  have h4 : ∀ b : Bool,
      (∑ b1 : Bool, ∑ b2 : Bool, ∑ b3 : Bool, ∑ b4 : Bool, g b) = 16 * g b := by
    intro b
    simp only [sum_bool_eq]
    ring
  simp only [sum_bool_eq, h4]
  ring

/-- The product of the five measurement amplitudes on the all-false branch equals `(if z 0 then
exp(-t) else 1) / (sqrt 2)^5` as a complex scalar. -/
theorem euler_v (t : ℝ) (z : Fin 5 → Bool) :
    (∏ j : Fin 5, mpSVector (mpAdaptiveAngle (mpEulerPattern (theta t)) s0 j) (s0 j) (z j))
      = (((if z 0 then Real.exp (-t) else 1) / (Real.sqrt 2) ^ 5 : ℝ) : ℂ) := by
  have h : (∏ j : Fin 5, mpSVector (mpAdaptiveAngle (mpEulerPattern (theta t)) s0 j) (s0 j) (z j))
      = (∏ j : Fin 5,
          star (mpSVector (mpAdaptiveAngle (mpEulerPattern (theta t)) s0 j) (s0 j) (z j))) := by
    apply Finset.prod_congr rfl
    intro j _
    exact (star_sv _ _ _).symm
  rw [h]
  exact euler_sv_prod t z

/-- The squared magnitude of the Euler-chain measurement-amplitude product is `(if z 0 then
exp(-t) else 1)^2 / 32`. -/
theorem euler_vsq (t : ℝ) (z : Fin 5 → Bool) :
    (∏ j : Fin 5, mpSVector (mpAdaptiveAngle (mpEulerPattern (theta t)) s0 j) (s0 j) (z j))
        * star (∏ j : Fin 5,
            mpSVector (mpAdaptiveAngle (mpEulerPattern (theta t)) s0 j) (s0 j) (z j))
      = ((((if z 0 then Real.exp (-t) else 1) ^ 2 / 32 : ℝ) : ℂ)) := by
  rw [euler_v]
  have hst : star (((if z 0 then Real.exp (-t) else 1) / (Real.sqrt 2) ^ 5 : ℝ) : ℂ)
      = (((if z 0 then Real.exp (-t) else 1) / (Real.sqrt 2) ^ 5 : ℝ) : ℂ) :=
    Complex.conj_ofReal _
  rw [hst, ← Complex.ofReal_mul]
  congr 1
  rw [div_mul_div_comm]
  have hs : (Real.sqrt 2 ^ 5 * Real.sqrt 2 ^ 5 : ℝ) = 32 := by
    rw [← pow_add, show (5 + 5 : ℕ) = 2 * 5 by norm_num, pow_mul]
    have h2 : (Real.sqrt 2 ^ 2 : ℝ) = 2 := Real.sq_sqrt (by norm_num)
    rw [h2]
    norm_num
  rw [hs, ← pow_two]

/-- The sum of squared magnitudes of the Euler-chain measurement-amplitude products is `(1 +
exp(-t)^2) / 2`. -/
theorem euler_vsum (t : ℝ) :
    ∑ z : Fin 5 → Bool,
        (∏ j : Fin 5, mpSVector (mpAdaptiveAngle (mpEulerPattern (theta t)) s0 j) (s0 j) (z j))
          * star (∏ j : Fin 5,
              mpSVector (mpAdaptiveAngle (mpEulerPattern (theta t)) s0 j) (s0 j) (z j))
      = (((1 + Real.exp (-t) ^ 2) / 2 : ℝ) : ℂ) := by
  have hsum : (∑ z : Fin 5 → Bool,
        (∏ j : Fin 5, mpSVector (mpAdaptiveAngle (mpEulerPattern (theta t)) s0 j) (s0 j) (z j))
          * star (∏ j : Fin 5,
              mpSVector (mpAdaptiveAngle (mpEulerPattern (theta t)) s0 j) (s0 j) (z j)))
      = ∑ z : Fin 5 → Bool, (((if z 0 then Real.exp (-t) else 1) ^ 2 / 32 : ℝ) : ℂ) :=
    Finset.sum_congr rfl (fun z _ => euler_vsq t z)
  rw [hsum]
  have hfold : (∑ z : Fin 5 → Bool, (((if z 0 then Real.exp (-t) else 1) ^ 2 / 32 : ℝ) : ℂ))
      = ∑ b0 : Bool, ∑ b1 : Bool, ∑ b2 : Bool, ∑ b3 : Bool, ∑ b4 : Bool,
          (((if b0 then Real.exp (-t) else 1) ^ 2 / 32 : ℝ) : ℂ) := by
    simp only [sum_reg5_pin, pin5_0]
  rw [hfold, sum5_b0]
  simp only [if_true, if_false, one_pow]
  push_cast
  field_simp
  ring

/-- The all-false Euler-chain branch is conjugation by its core multiplied by the sum of the
squared measurement-amplitude products over discarded-register strings. -/
theorem euler_channel_smul (t : ℝ) (ρ : Operator 2) :
    ∑ z : Fin 5 → Bool,
        (mpPatternKraus (mpEulerPattern (theta t)) (Uniform (Reg 5)) s0 z) * ρ
          * (mpPatternKraus (mpEulerPattern (theta t)) (Uniform (Reg 5)) s0 z).conjTranspose
      = (∑ z : Fin 5 → Bool,
            (∏ j : Fin 5,
                mpSVector (mpAdaptiveAngle (mpEulerPattern (theta t)) s0 j) (s0 j) (z j))
              * star (∏ j : Fin 5,
                  mpSVector (mpAdaptiveAngle (mpEulerPattern (theta t)) s0 j) (s0 j) (z j)))
          • (core (mpEulerPattern (theta t)) (Uniform (Reg 5)) s0 * ρ
              * (core (mpEulerPattern (theta t)) (Uniform (Reg 5)) s0).conjTranspose) := by
  have hkey : ∀ z : Fin 5 → Bool,
      (mpPatternKraus (mpEulerPattern (theta t)) (Uniform (Reg 5)) s0 z) * ρ
          * (mpPatternKraus (mpEulerPattern (theta t)) (Uniform (Reg 5)) s0 z).conjTranspose
        = ((∏ j : Fin 5,
              mpSVector (mpAdaptiveAngle (mpEulerPattern (theta t)) s0 j) (s0 j) (z j))
            * star (∏ j : Fin 5,
                mpSVector (mpAdaptiveAngle (mpEulerPattern (theta t)) s0 j) (s0 j) (z j)))
            • (core (mpEulerPattern (theta t)) (Uniform (Reg 5)) s0 * ρ
                * (core (mpEulerPattern (theta t)) (Uniform (Reg 5)) s0).conjTranspose) := by
    intro z
    rw [kraus_eq_smul_core, Matrix.conjTranspose_smul, smul_mul_assoc, smul_mul_smul]
  simp_rw [hkey]
  rw [← Finset.sum_smul]

/-- A sum over `Fin (2^1)` is the sum of its values at zero and one. -/
theorem sum_fin2p1 (f : Fin (2 ^ 1) → ℂ) :
    (∑ x : Fin (2 ^ 1), f x) = f 0 + f 1 := by
  show (∑ x : Fin 2, f x) = f 0 + f 1
  rw [Fin.sum_univ_two]

/-- The `(0,0)` entry of the Euler core multiplied by its conjugate transpose is `(1 +
exp(-t)^2) / 64`. -/
theorem euler_core_conj00 (t : ℝ) :
    (core (mpEulerPattern (theta t)) (Uniform (Reg 5)) s0
        * (core (mpEulerPattern (theta t)) (Uniform (Reg 5)) s0).conjTranspose) 0 0
      = (((1 + Real.exp (-t) ^ 2) / 64 : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, sum_fin2p1]
  rw [euler_core00, euler_core01]
  have h1 : star (((-1 / 8 : ℝ) : ℂ)) = ((-1 / 8 : ℝ) : ℂ) := Complex.conj_ofReal _
  have h2 : star (((-Real.exp (-t) / 8 : ℝ) : ℂ)) = ((-Real.exp (-t) / 8 : ℝ) : ℂ) :=
    Complex.conj_ofReal _
  rw [h1, h2]
  push_cast
  field_simp
  ring

/-- The `(0,0)` entry of the all-false Euler-chain branch applied to the identity is `(1 +
exp(-t)^2)^2 / 128`. This calculation uses the concrete measurement-vector convention for
the cluster pattern motivated by [RaussendorfBriegel2000]. -/
theorem euler_channel_I00 (t : ℝ) :
    (∑ z : Fin 5 → Bool,
        (mpPatternKraus (mpEulerPattern (theta t)) (Uniform (Reg 5)) s0 z) * (1 : Operator 2)
          * (mpPatternKraus (mpEulerPattern (theta t)) (Uniform (Reg 5)) s0 z).conjTranspose) 0 0
      = (((1 + Real.exp (-t) ^ 2) ^ 2 / 128 : ℝ) : ℂ) := by
  rw [euler_channel_smul, Matrix.smul_apply]
  rw [euler_vsum]
  have hcore : ((core (mpEulerPattern (theta t)) (Uniform (Reg 5)) s0 * (1 : Operator 2)
        * (core (mpEulerPattern (theta t)) (Uniform (Reg 5)) s0).conjTranspose) 0 0)
      = (((1 + Real.exp (-t) ^ 2) / 64 : ℝ) : ℂ) := by
    rw [Matrix.mul_one]
    exact euler_core_conj00 t
  rw [hcore, smul_eq_mul, ← Complex.ofReal_mul]
  congr 1
  field_simp
  ring
end Qatlib.Concepts.ClusterPatterns.CnotPatterns
namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire
open scoped BigOperators Classical
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra

/-- The present Euler-pattern definitions do not give, for every angle assignment, branches
equal to `1 / 32` times conjugation by a common unitary. For the cluster setting motivated
by [RaussendorfBriegel2000], the proof uses only the first angle `log 2`, the all-false
outcome, and the identity input. -/
theorem clause7_counter_clause2 :
    ¬ (∀ θ : Fin 5 → ℝ,
        ∃ V : Matrix (Fin 2) (Fin 2) ℂ,
          V * V.conjTranspose = 1 ∧ V.conjTranspose * V = 1 ∧
          ∀ (s : Fin 5 → Bool) (ρ : Operator 2),
            ∑ z : Fin 5 → Bool,
                (mpPatternKraus (mpEulerPattern θ) (Uniform (Reg 5)) s z) * ρ
                  * (mpPatternKraus (mpEulerPattern θ) (Uniform (Reg 5)) s z).conjTranspose
              = (1 / 32 : ℂ) • (V * ρ * V.conjTranspose)) := by
  intro h
  obtain ⟨V, hV1, _hV2, hV⟩ := h (Qatlib.Concepts.ClusterPatterns.CnotPatterns.theta (Real.log 2))
  have hz := hV Qatlib.Concepts.ClusterPatterns.CnotPatterns.s0 (1 : Operator 2)
  have hent := congrArg (fun M : Operator 2 => M 0 0) hz
  beta_reduce at hent
  rw [Qatlib.Concepts.ClusterPatterns.CnotPatterns.euler_channel_I00] at hent
  have hR : ((1 / 32 : ℂ) • (V * (1 : Operator 2) * V.conjTranspose)) 0 0
      = ((1 / 32 : ℂ)) := by
    rw [Matrix.mul_one, hV1]
    simp [Matrix.smul_apply, Matrix.one_apply]
  rw [hR] at hent
  have he : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    norm_num
  rw [he] at hent
  push_cast at hent
  norm_num at hent
end Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
