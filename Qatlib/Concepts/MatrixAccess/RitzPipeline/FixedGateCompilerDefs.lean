/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.FixedGateEffective
import Qatlib.Concepts.MatrixAccess.RitzPipeline.FixedGateEffectiveDefs
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Controlled-phase error lower bounds

This module bounds the distance between an empty gate word and a dyadic controlled-phase gate,
even after adjusting global phase. The bounds show that `effectiveCompiler` fails the acceptance
condition in the intermediate exponent range, and `ScalarPhaseSynthesizer` specifies the
additional single-wire synthesis data. Background on phase gates and circuit approximation
appears in [NielsenChuang2010].

## Main statements

* `emptyWord_error_lower`: half the controlled-phase angle gives a sine lower bound on the
  error.
* `effectiveCompiler_rejects_middleWindow`: the empty output fails the required tolerance in the
  stated range.
* `ScalarPhaseSynthesizer`: a fixed-primitive synthesis interface for single-wire phases.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedTactic false

noncomputable section

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.GuardedCounter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TableCopy
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TinyTag

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib
open Qatlib

/-- The sine of twice a real angle equals twice its sine times its cosine. -/
theorem sin_two_mul (x : ℝ) : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
  rw [show (2 : ℝ) * x = x + x by ring, Real.sin_add]
  ring

/-- Express `π / 2^e` as twice the next dyadic angle for a positive natural exponent. -/
theorem pi_div_two_pow_succ (e : ℕ) (he : 1 ≤ e) :
    Real.pi / (2 : ℝ) ^ e = 2 * (Real.pi / (2 : ℝ) ^ (e + 1)) := by
  have h2 : (2 : ℝ) ^ (e + 1) = (2 : ℝ) ^ e * 2 := pow_succ _ _
  rw [h2]
  field_simp

/-- Every natural power of the real number two is at least one. -/
theorem one_le_two_pow_nat : ∀ n : ℕ, (1 : ℝ) ≤ (2 : ℝ) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      have hpos : 0 ≤ (2 : ℝ) ^ k := pow_nonneg (by norm_num) _
      nlinarith [ih]

/-- For `e ≥ 2`, the sine of `π / 2^e` is strictly greater than `2⁻¹` raised to `e - 1`. -/
theorem sin_dyadic_lower : ∀ (e : ℕ), 2 ≤ e →
    ((2 : ℝ) ⁻¹) ^ (e - 1) < Real.sin (Real.pi / (2 : ℝ) ^ e) := by
  intro e he
  induction e, he using Nat.le_induction with
  | base =>
      have hsin : Real.sin (Real.pi / (2 : ℝ) ^ 2) = Real.sqrt 2 / 2 := by
        rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
        norm_num [Real.sin_pi_div_four]
      have hsqrt : (1 : ℝ) < Real.sqrt 2 := by
        have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
        have hpos := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
        nlinarith
      have hhalf : ((2 : ℝ) ⁻¹) ^ (2 - 1) = (1 : ℝ) / 2 := by
        norm_num
      rw [hhalf, hsin]
      linarith
  | succ n hn ih =>
      have hcos : Real.cos (Real.pi / (2 : ℝ) ^ (n + 1)) ≤ 1 := by
        have h := Real.abs_cos_le_one (Real.pi / (2 : ℝ) ^ (n + 1))
        exact le_trans (le_abs_self _) h
      have hsin : 0 ≤ Real.sin (Real.pi / (2 : ℝ) ^ (n + 1)) := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi
        · exact (div_pos Real.pi_pos (pow_pos (by norm_num) _)).le
        · have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := one_le_two_pow_nat (n + 1)
          have h2 : 0 < (2 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
          have hdiv : (1 : ℝ) / (2 : ℝ) ^ (n + 1) ≤ 1 := (div_le_one h2).mpr h3
          have hle : Real.pi / (2 : ℝ) ^ (n + 1) ≤ Real.pi := by
            have heq : Real.pi / (2 : ℝ) ^ (n + 1)
                = Real.pi * ((1 : ℝ) / (2 : ℝ) ^ (n + 1)) := by
              rw [div_eq_mul_inv, one_div]
            rw [heq]
            calc Real.pi * ((1 : ℝ) / (2 : ℝ) ^ (n + 1))
                = ((1 : ℝ) / (2 : ℝ) ^ (n + 1)) * Real.pi := by ring
              _ ≤ 1 * Real.pi := mul_le_mul_of_nonneg_right hdiv Real.pi_nonneg
              _ = Real.pi := by norm_num
          exact hle
      have htwo : Real.pi / (2 : ℝ) ^ n
          = 2 * (Real.pi / (2 : ℝ) ^ (n + 1)) := pi_div_two_pow_succ n (by omega)
      have hstep : Real.sin (Real.pi / (2 : ℝ) ^ n)
          ≤ 2 * Real.sin (Real.pi / (2 : ℝ) ^ (n + 1)) := by
        rw [htwo, sin_two_mul]
        nlinarith
      have hlower : ((2 : ℝ) ⁻¹) ^ (n - 1) < Real.sin (Real.pi / (2 : ℝ) ^ n) := ih
      have hpow : ((2 : ℝ) ⁻¹) ^ (n - 1) / 2 = ((2 : ℝ) ⁻¹) ^ n := by
        rw [div_eq_mul_inv, ← pow_succ, show n - 1 + 1 = n by omega]
      have hfinal : ((2 : ℝ) ⁻¹) ^ n < Real.sin (Real.pi / (2 : ℝ) ^ (n + 1)) := by
        rw [← hpow]
        have h3 : Real.sin (Real.pi / (2 : ℝ) ^ n) / 2
            ≤ Real.sin (Real.pi / (2 : ℝ) ^ (n + 1)) := by
          linarith
        linarith
      rw [show (n + 1) - 1 = n by omega]
      exact hfinal

/-- For `e ≥ 4`, the sine of `π / 2^(e - 2)` is strictly greater than `2⁻¹` raised to `e - 3`. -/
theorem sin_dyadic_lower_window {e : ℕ} (he : 4 ≤ e) :
    ((2 : ℝ) ⁻¹) ^ (e - 3) < Real.sin (Real.pi / (2 : ℝ) ^ (e - 2)) :=
  sin_dyadic_lower (e - 2) (by omega)

/-- If `e ≤ k + 1`, the precision tolerance at `k` is at most `2⁻¹` raised to `e - 1`. -/
theorem tolerance_le_two_pow_one_sub_e {e k : ℕ} (hk : e ≤ k + 1) :
    tolerance k ≤ ((2 : ℝ) ⁻¹) ^ (e - 1) := by
  have hk1 : e - 1 ≤ k := by omega
  have hpow : (2 : ℝ) ^ (e - 1) ≤ (2 : ℝ) ^ k := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk1
  have hinv : ((2 : ℝ) ^ k)⁻¹ ≤ ((2 : ℝ) ^ (e - 1))⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hpow
  calc tolerance k = ((2 : ℝ) ^ k)⁻¹ := by rw [tolerance]; simp [inv_pow]
    _ ≤ ((2 : ℝ) ^ (e - 1))⁻¹ := hinv
    _ = ((2 : ℝ) ⁻¹) ^ (e - 1) := by rw [inv_pow]

/-- The constant-false register used to probe the unphased diagonal entry of a controlled-phase
gate. -/
def probeLow {w : ℕ} (a c : Fin w) : Reg w := fun _ => false

/-- The register that is true exactly on the two selected wires, used to probe the phased
diagonal entry of a controlled-phase gate. -/
def probeHigh {w : ℕ} (a c : Fin w) : Reg w :=
  fun i => if i = a then true else if i = c then true else false

/-- Both selected wires of `probeLow` have value `false`. -/
theorem probeLow_false {w : ℕ} (a c : Fin w) :
    probeLow a c a = false ∧ probeLow a c c = false :=
  ⟨rfl, rfl⟩

/-- Both selected wires of `probeHigh` have value `true`. -/
theorem probeHigh_true {w : ℕ} (a c : Fin w) :
    probeHigh a c a = true ∧ probeHigh a c c = true := by
  constructor <;> simp [probeHigh]

/-- The diagonal error between the identity and a controlled-phase gate multiplied by a global
phase. -/
def emptyWordErrorDiag {w : ℕ} (a c : Fin w) (e : ℕ) (neg : Bool) (φ : ℝ) : Reg w → ℂ :=
  fun x => 1 - Complex.exp (φ * Complex.I)
    * (if x a && x c then Complex.exp (dyadicPhaseAngle e neg * Complex.I) else 1)

/-- At `probeLow`, the diagonal error is one minus the global phase factor. -/
theorem emptyWordErrorDiag_low {w : ℕ} (a c : Fin w) (e : ℕ) (neg : Bool) (φ : ℝ) :
    emptyWordErrorDiag a c e neg φ (probeLow a c) = 1 - Complex.exp (φ * Complex.I) := by
  have h1 : probeLow a c a = false := rfl
  have h2 : probeLow a c c = false := rfl
  simp [emptyWordErrorDiag, h1, h2]

/-- At `probeHigh`, the diagonal error is one minus the product of the global and controlled
phase factors. -/
theorem emptyWordErrorDiag_high {w : ℕ} (a c : Fin w) (e : ℕ) (neg : Bool) (φ : ℝ) :
    emptyWordErrorDiag a c e neg φ (probeHigh a c)
      = 1 - Complex.exp (φ * Complex.I) * Complex.exp (dyadicPhaseAngle e neg * Complex.I) := by
  have h1 : probeHigh a c a = true := (probeHigh_true a c).1
  have h2 : probeHigh a c c = true := (probeHigh_true a c).2
  simp [emptyWordErrorDiag, h1, h2]

/-- The difference between the high and low probe errors factors as the global phase times one
minus the controlled phase factor. -/
theorem emptyWordErrorDiag_diff {w : ℕ} (a c : Fin w) (e : ℕ) (neg : Bool) (φ : ℝ) :
    emptyWordErrorDiag a c e neg φ (probeHigh a c)
        - emptyWordErrorDiag a c e neg φ (probeLow a c)
      = Complex.exp (φ * Complex.I)
          * (1 - Complex.exp (Complex.I * (dyadicPhaseAngle e neg : ℝ))) := by
  rw [emptyWordErrorDiag_high, emptyWordErrorDiag_low]
  ring

/-- For any global phase, the operator-norm distance from the identity to the phased
controlled-phase gate is at least the absolute sine of half its angle. -/
theorem emptyWord_error_lower {w : ℕ} (a c : Fin w) (e : ℕ) (neg : Bool) (φ : ℝ) :
    ‖(1 : Matrix (Reg w) (Reg w) ℂ) - (Complex.exp (φ * Complex.I))
        • localGateMatrix (.cp a c e neg)‖
      ≥ |Real.sin (dyadicPhaseAngle e neg / 2)| := by
  have hdiag : (1 : Matrix (Reg w) (Reg w) ℂ) - (Complex.exp (φ * Complex.I))
        • localGateMatrix (.cp a c e neg)
      = Matrix.diagonal (emptyWordErrorDiag a c e neg φ) :=
    one_sub_phase_smul_cp a c e neg φ
  rw [hdiag, Matrix.l2_opNorm_diagonal]
  have hlo : ‖emptyWordErrorDiag a c e neg φ (probeLow a c)‖
      ≤ ‖emptyWordErrorDiag a c e neg φ‖ :=
    norm_le_pi_norm _ _
  have hhi : ‖emptyWordErrorDiag a c e neg φ (probeHigh a c)‖
      ≤ ‖emptyWordErrorDiag a c e neg φ‖ :=
    norm_le_pi_norm _ _
  have htri : ‖emptyWordErrorDiag a c e neg φ (probeHigh a c)
        - emptyWordErrorDiag a c e neg φ (probeLow a c)‖
      ≤ ‖emptyWordErrorDiag a c e neg φ (probeHigh a c)‖
        + ‖emptyWordErrorDiag a c e neg φ (probeLow a c)‖ := by
    have h := dist_triangle (emptyWordErrorDiag a c e neg φ (probeHigh a c)) 0
      (emptyWordErrorDiag a c e neg φ (probeLow a c))
    rw [dist_eq_norm, dist_zero_right, dist_zero_left] at h
    exact h
  have hnorm : ‖1 - Complex.exp (dyadicPhaseAngle e neg * Complex.I)‖
      = 2 * |Real.sin (dyadicPhaseAngle e neg / 2)| := by
    calc ‖1 - Complex.exp (dyadicPhaseAngle e neg * Complex.I)‖
        = ‖Complex.exp (dyadicPhaseAngle e neg * Complex.I) - 1‖ := by
          rw [norm_sub_rev]
      _ = ‖Complex.exp (Complex.I * (dyadicPhaseAngle e neg : ℝ)) - 1‖ := by
          rw [show (dyadicPhaseAngle e neg : ℂ) * Complex.I
              = Complex.I * (dyadicPhaseAngle e neg : ℝ) by push_cast; ring]
      _ = 2 * |Real.sin (dyadicPhaseAngle e neg / 2)| := by
          rw [Complex.norm_exp_I_mul_ofReal_sub_one (dyadicPhaseAngle e neg)]
          simp
  have hdiff : ‖emptyWordErrorDiag a c e neg φ (probeHigh a c)
        - emptyWordErrorDiag a c e neg φ (probeLow a c)‖
      = 2 * |Real.sin (dyadicPhaseAngle e neg / 2)| := by
    calc ‖emptyWordErrorDiag a c e neg φ (probeHigh a c)
          - emptyWordErrorDiag a c e neg φ (probeLow a c)‖
        = ‖Complex.exp (φ * Complex.I)
            * (1 - Complex.exp (Complex.I * (dyadicPhaseAngle e neg : ℝ)))‖ := by
          rw [emptyWordErrorDiag_diff]
      _ = ‖1 - Complex.exp (Complex.I * (dyadicPhaseAngle e neg : ℝ))‖ := by
          rw [Complex.norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      _ = 2 * |Real.sin (dyadicPhaseAngle e neg / 2)| := by
          rw [norm_sub_rev]
          rw [Complex.norm_exp_I_mul_ofReal_sub_one (dyadicPhaseAngle e neg)]
          simp
  have hsum : (‖emptyWordErrorDiag a c e neg φ (probeLow a c)‖
        + ‖emptyWordErrorDiag a c e neg φ (probeHigh a c)‖) / 2
      ≥ |Real.sin (dyadicPhaseAngle e neg / 2)| := by
    calc (‖emptyWordErrorDiag a c e neg φ (probeLow a c)‖
        + ‖emptyWordErrorDiag a c e neg φ (probeHigh a c)‖) / 2
        ≥ ‖emptyWordErrorDiag a c e neg φ (probeHigh a c)
            - emptyWordErrorDiag a c e neg φ (probeLow a c)‖ / 2 := by linarith
      _ = |Real.sin (dyadicPhaseAngle e neg / 2)| := by
          rw [hdiff]
          ring
  have hmax : ‖emptyWordErrorDiag a c e neg φ‖
      ≥ |Real.sin (dyadicPhaseAngle e neg / 2)| := by
    calc ‖emptyWordErrorDiag a c e neg φ‖
        ≥ (‖emptyWordErrorDiag a c e neg φ (probeLow a c)‖
            + ‖emptyWordErrorDiag a c e neg φ (probeHigh a c)‖) / 2 := by
          linarith
      _ ≥ |Real.sin (dyadicPhaseAngle e neg / 2)| := hsum
  exact hmax

/-- For a positive exponent, the absolute value of half a signed dyadic phase angle is `π /
2^e`. -/
theorem abs_half_dyadicPhaseAngle {e : ℕ} (neg : Bool) (he : 1 ≤ e) :
    |dyadicPhaseAngle e neg / 2| = Real.pi / (2 : ℝ) ^ e := by
  rw [abs_div_two]
  exact abs_dyadicPhaseAngle_div_two e neg

/-- If `4 ≤ e ≤ k + 1` and `k ≥ 1`, the empty word's error for the controlled-phase gate exceeds
`tolerance k` for every global phase. -/
theorem middleWindow_empty_far {w : ℕ} {a c : Fin w} (e k : ℕ) (neg : Bool)
    (he : 4 ≤ e) (hk : e ≤ k + 1) (hkk : 1 ≤ k) (φ : ℝ) :
    tolerance k < ‖(1 : Matrix (Reg w) (Reg w) ℂ) -
        (Complex.exp (φ * Complex.I)) • localGateMatrix (.cp a c e neg)‖ := by
  have hlower := emptyWord_error_lower a c e neg φ
  have hhalf : |dyadicPhaseAngle e neg / 2| = Real.pi / (2 : ℝ) ^ e :=
    abs_half_dyadicPhaseAngle neg (by omega)
  have hpi : Real.pi / (2 : ℝ) ^ e ≤ Real.pi := by
    have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ e := one_le_two_pow_nat e
    have h4 : (1 : ℝ) / (2 : ℝ) ^ e ≤ 1 :=
      (div_le_one (pow_pos (by norm_num) e)).mpr h3
    have h5 : Real.pi * ((1 : ℝ) / (2 : ℝ) ^ e) ≤ Real.pi := by
      calc Real.pi * ((1 : ℝ) / (2 : ℝ) ^ e) = ((1 : ℝ) / (2 : ℝ) ^ e) * Real.pi := by ring
        _ ≤ 1 * Real.pi := mul_le_mul_of_nonneg_right h4 Real.pi_nonneg
        _ = Real.pi := by norm_num
    have heq : Real.pi / (2 : ℝ) ^ e = Real.pi * ((1 : ℝ) / (2 : ℝ) ^ e) := by
      rw [div_eq_mul_inv, one_div]
    rw [heq]
    exact h5
  have hsin : |Real.sin (dyadicPhaseAngle e neg / 2)|
      = Real.sin (Real.pi / (2 : ℝ) ^ e) := by
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by rw [hhalf]; exact hpi), hhalf]
  have hdyadic : ((2 : ℝ) ⁻¹) ^ (e - 1)
      < Real.sin (Real.pi / (2 : ℝ) ^ e) := sin_dyadic_lower e (by omega)
  have htol : tolerance k ≤ ((2 : ℝ) ⁻¹) ^ (e - 1) :=
    tolerance_le_two_pow_one_sub_e hk
  have hchain : tolerance k < |Real.sin (dyadicPhaseAngle e neg / 2)| := by
    rw [hsin]
    exact lt_of_le_of_lt htol hdyadic
  exact lt_of_lt_of_le hchain hlower

/-- The effective partial compiler fails `AcceptsAt` for controlled phases with `4 ≤ e ≤ k + 1`
at positive precision. -/
theorem effectiveCompiler_rejects_middleWindow {w : ℕ} {a c : Fin w} (e k : ℕ) (neg : Bool)
    (he : 4 ≤ e) (hk : e ≤ k + 1) (hkk : 1 ≤ k) :
    ¬ AcceptsAt effectiveCompiler w (.cp a c e neg) k := by
  have hnotle : ¬ (e ≤ 3) := by omega
  intro h
  have happ : approxUpToPhase (localProgramMatrix ([] : List (LocalQFTGate w)) * cleanEmbed w w)
      (cleanEmbed w w * localGateMatrix (.cp a c e neg)) (tolerance k) := by
    have h' := h.2.2.2.1
    rw [effectiveCompiler_eq_partial, Compiler.Segment] at h'
    have hemit : partialCompiler.emit w (.cp a c e neg) k = [] :=
      partialCompiler_emit_empty a c e neg k (by omega)
    have hanc : partialCompiler.anc w (.cp a c e neg) k = 0 :=
      partialCompiler_anc_eq w (.cp a c e neg) k
    rw [hemit, hanc] at h'
    exact h'
  rcases happ with ⟨φ, hφ⟩
  have hφ' : ‖(1 : Matrix (Reg w) (Reg w) ℂ) -
        (Complex.exp (φ * Complex.I)) • localGateMatrix (.cp a c e neg)‖ ≤ tolerance k := by
    simpa [localProgramMatrix_nil, cleanEmbed_self, Matrix.one_mul, Matrix.mul_one] using! hφ
  have hcontra : tolerance k < ‖(1 : Matrix (Reg w) (Reg w) ℂ) -
        (Complex.exp (φ * Complex.I)) • localGateMatrix (.cp a c e neg)‖ :=
    middleWindow_empty_far e k neg he hk hkk φ
  exact (not_lt_of_ge hφ') hcontra

/-- Single-wire dyadic phase synthesis data using only fixed primitives. For exponents at least
four and positive precision, the emitted word approximates the target up to global phase and
has polynomial length in exponent plus precision. -/
structure ScalarPhaseSynthesizer where

  emit : (neg : Bool) → (e : ℕ) → (k : ℕ) → List (LocalQFTGate 1)

  legal : ∀ (neg : Bool) (e k : ℕ) (h : LocalQFTGate 1),
    h ∈ emit neg e k → IsFixedPrim h

  correct : ∀ (neg : Bool) (e k : ℕ), 4 ≤ e → 1 ≤ k →
    approxUpToPhase (localProgramMatrix (emit neg e k))
      (oneWirePhaseMatrix 0 (dyadicPhaseAngle e neg)) (tolerance k)

  bounded : ∃ C D : ℕ, ∀ (neg : Bool) (e k : ℕ), 4 ≤ e → 1 ≤ k →
    (emit neg e k).length ≤ C * (e + k) ^ D

end Qatlib.Concepts.MatrixAccess.RitzPipeline
