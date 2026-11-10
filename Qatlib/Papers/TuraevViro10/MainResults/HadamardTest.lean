/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TuraevViro10.MainResults.WrtBridge
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TuraevViro10.MainResults.HadamardTest

open Qatlib.Papers.TuraevViro10.MainResults.WrtBridge
open Qatlib.Papers.TuraevViro10.MainResults.WrtBridge.TuraevViroModel

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def hsqrt : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

theorem hsqrt_mul_self : hsqrt * hsqrt = (2 : ℂ)⁻¹ := by
  unfold hsqrt
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem norm_hsqrt : ‖hsqrt‖ = (Real.sqrt 2)⁻¹ := by
  unfold hsqrt
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]

def ancillaPlus (v : H) : H × H := (hsqrt • v, hsqrt • v)

def ctrl (U : H → H) (φ : H × H) : H × H := (φ.1, U φ.2)

def phaseGate (U : H → H) : H → H := fun y => (-Complex.I) • U y

def hadamardPair (φ : H × H) : H × H :=
  (hsqrt • (φ.1 + φ.2), hsqrt • (φ.1 - φ.2))

theorem hadamardPair_ctrl_ancillaPlus (U : H → H)
    (hUlin : ∀ (c : ℂ) (x : H), U (c • x) = c • U x) (v : H) :
    hadamardPair (ctrl U (ancillaPlus v)) =
      ((2 : ℂ)⁻¹ • (v + U v), (2 : ℂ)⁻¹ • (v - U v)) := by
  have hfst : (hadamardPair (ctrl U (ancillaPlus v))).1 = (2 : ℂ)⁻¹ • (v + U v) := by
    simp only [hadamardPair, ctrl, ancillaPlus, hUlin]
    rw [smul_add, smul_smul, smul_smul, hsqrt_mul_self, ← smul_add]
  have hsnd : (hadamardPair (ctrl U (ancillaPlus v))).2 = (2 : ℂ)⁻¹ • (v - U v) := by
    simp only [hadamardPair, ctrl, ancillaPlus, hUlin]
    rw [smul_sub, smul_smul, smul_smul, hsqrt_mul_self, ← smul_sub]
  exact Prod.ext hfst hsnd

theorem hadamardPair_phaseGate_ctrl_ancillaPlus (U : H → H)
    (hUlin : ∀ (c : ℂ) (x : H), U (c • x) = c • U x) (v : H) :
    hadamardPair (ctrl (phaseGate U) (ancillaPlus v)) =
      ((2 : ℂ)⁻¹ • (v + (-Complex.I) • U v), (2 : ℂ)⁻¹ • (v - (-Complex.I) • U v)) := by
  have hlin' : ∀ (c : ℂ) (y : H), phaseGate U (c • y) = c • phaseGate U y := by
    intro c y
    unfold phaseGate
    rw [hUlin, smul_smul, smul_smul, mul_comm]
  simpa only [phaseGate] using hadamardPair_ctrl_ancillaPlus (phaseGate U) hlin' v

def prob0 (φ : H × H) : ℝ := ‖φ.1‖ ^ 2

def prob1 (φ : H × H) : ℝ := ‖φ.2‖ ^ 2

theorem prob0_real (U : H → H) (hUlin : ∀ (c : ℂ) (x : H), U (c • x) = c • U x)
    (v : H) (hv : ‖v‖ = 1) (hU : ‖U v‖ = ‖v‖) :
    prob0 (hadamardPair (ctrl U (ancillaPlus v))) =
      (1 + (inner ℂ v (U v)).re) / 2 := by
  rw [hadamardPair_ctrl_ancillaPlus U hUlin v]
  unfold prob0
  rw [norm_smul, mul_pow, norm_add_sq (𝕜 := ℂ), hv, hU, hv]
  have hc : ‖(2 : ℂ)⁻¹‖ = 1 / 2 := by norm_num
  rw [hc]
  rw [RCLike.re_to_complex]
  ring

theorem prob1_real (U : H → H) (hUlin : ∀ (c : ℂ) (x : H), U (c • x) = c • U x)
    (v : H) (hv : ‖v‖ = 1) (hU : ‖U v‖ = ‖v‖) :
    prob1 (hadamardPair (ctrl U (ancillaPlus v))) =
      (1 - (inner ℂ v (U v)).re) / 2 := by
  rw [hadamardPair_ctrl_ancillaPlus U hUlin v]
  unfold prob1
  rw [norm_smul, mul_pow, norm_sub_sq (𝕜 := ℂ), hv, hU, hv]
  have hc : ‖(2 : ℂ)⁻¹‖ = 1 / 2 := by norm_num
  rw [hc]
  rw [RCLike.re_to_complex]
  ring

theorem prob0_imag (U : H → H) (hUlin : ∀ (c : ℂ) (x : H), U (c • x) = c • U x)
    (v : H) (hv : ‖v‖ = 1) (hU : ‖U v‖ = ‖v‖) :
    prob0 (hadamardPair (ctrl (phaseGate U) (ancillaPlus v))) =
      (1 + (inner ℂ v (U v)).im) / 2 := by
  have hlin' : ∀ (c : ℂ) (y : H), phaseGate U (c • y) = c • phaseGate U y := by
    intro c y
    unfold phaseGate
    rw [hUlin, smul_smul, smul_smul, mul_comm]
  have hnorm : ‖phaseGate U v‖ = ‖v‖ := by
    unfold phaseGate
    rw [norm_smul, hU, hv]
    simp
  rw [prob0_real (phaseGate U) hlin' v hv hnorm]
  unfold phaseGate
  rw [inner_smul_right]
  have hre : ((-Complex.I) * inner ℂ v (U v)).re = (inner ℂ v (U v)).im := by
    simp [Complex.mul_re]
  rw [hre]

theorem prob1_imag (U : H → H) (hUlin : ∀ (c : ℂ) (x : H), U (c • x) = c • U x)
    (v : H) (hv : ‖v‖ = 1) (hU : ‖U v‖ = ‖v‖) :
    prob1 (hadamardPair (ctrl (phaseGate U) (ancillaPlus v))) =
      (1 - (inner ℂ v (U v)).im) / 2 := by
  have hlin' : ∀ (c : ℂ) (y : H), phaseGate U (c • y) = c • phaseGate U y := by
    intro c y
    unfold phaseGate
    rw [hUlin, smul_smul, smul_smul, mul_comm]
  have hnorm : ‖phaseGate U v‖ = ‖v‖ := by
    unfold phaseGate
    rw [norm_smul, hU, hv]
    simp
  rw [prob1_real (phaseGate U) hlin' v hv hnorm]
  unfold phaseGate
  rw [inner_smul_right]
  have hre : ((-Complex.I) * inner ℂ v (U v)).re = (inner ℂ v (U v)).im := by
    simp [Complex.mul_re]
  rw [hre]

theorem prob_sum_one (U : H → H) (hUlin : ∀ (c : ℂ) (x : H), U (c • x) = c • U x)
    (v : H) (hv : ‖v‖ = 1) (hU : ‖U v‖ = ‖v‖) :
    prob0 (hadamardPair (ctrl U (ancillaPlus v))) +
      prob1 (hadamardPair (ctrl U (ancillaPlus v))) = 1 := by
  rw [prob0_real U hUlin v hv hU, prob1_real U hUlin v hv hU]
  ring

theorem readout_re (U : H → H) (hUlin : ∀ (c : ℂ) (x : H), U (c • x) = c • U x)
    (v : H) (hv : ‖v‖ = 1) (hU : ‖U v‖ = ‖v‖) :
    2 * prob0 (hadamardPair (ctrl U (ancillaPlus v))) - 1 =
      (inner ℂ v (U v)).re := by
  rw [prob0_real U hUlin v hv hU]
  ring

theorem readout_im (U : H → H) (hUlin : ∀ (c : ℂ) (x : H), U (c • x) = c • U x)
    (v : H) (hv : ‖v‖ = 1) (hU : ‖U v‖ = ‖v‖) :
    2 * prob0 (hadamardPair (ctrl (phaseGate U) (ancillaPlus v))) - 1 =
      (inner ℂ v (U v)).im := by
  rw [prob0_imag U hUlin v hv hU]
  ring

theorem prob0_mem_Icc (U : H → H) (hUlin : ∀ (c : ℂ) (x : H), U (c • x) = c • U x)
    (v : H) (hv : ‖v‖ = 1) (hU : ‖U v‖ = ‖v‖) :
    prob0 (hadamardPair (ctrl U (ancillaPlus v))) ∈ Set.Icc (0 : ℝ) 1 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) v (U v)
  rw [hv, hU, hv, mul_one] at h
  have hre : |(inner ℂ v (U v)).re| ≤ 1 :=
    le_trans (Complex.abs_re_le_norm _) h
  rw [prob0_real U hUlin v hv hU]
  constructor <;> nlinarith [hre, abs_le.mp hre]

theorem normSq_eq_readout {a : ℂ} {p q : ℝ}
    (hp : p = (1 + a.re) / 2) (hq : q = (1 + a.im) / 2) :
    ‖a‖ ^ 2 = (2 * p - 1) ^ 2 + (2 * q - 1) ^ 2 := by
  rw [hp, hq, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem normalizedTvInvariant_eq_readout {P ι : Type*} [Fintype P]
    (particles : ParticleData P) (v : ℕ → H) (hv : ∀ g, ‖v g‖ = 1)
    (act : ℕ → ι → H → H) (hact : ∀ g x, ‖act g x (v g)‖ = ‖v g‖)
    (hlin : ∀ g x (c : ℂ) (y : H), act g x (c • y) = c • act g x y)
    {g : ℕ} (hg : 1 ≤ g) (x : ι) :
    (ofUnitaryRepresentation particles v hv act hact).normalizedTvInvariant g x =
      (2 * prob0 (hadamardPair (ctrl (act g x) (ancillaPlus (v g)))) - 1) ^ 2 +
      (2 * prob0 (hadamardPair (ctrl (phaseGate (act g x)) (ancillaPlus (v g)))) - 1) ^ 2 := by
  rw [ofUnitaryRepresentation_normalized_eq particles v hv act hact hg x]
  have hp : prob0 (hadamardPair (ctrl (act g x) (ancillaPlus (v g)))) =
      (1 + (inner ℂ (v g) (act g x (v g))).re) / 2 :=
    prob0_real (act g x) (hlin g x) (v g) (hv g) (hact g x)
  have hq : prob0 (hadamardPair (ctrl (phaseGate (act g x)) (ancillaPlus (v g)))) =
      (1 + (inner ℂ (v g) (act g x (v g))).im) / 2 :=
    prob0_imag (act g x) (hlin g x) (v g) (hv g) (hact g x)
  exact normSq_eq_readout hp hq

theorem wrtScaled_error_le {P ι : Type*} [Fintype P] (M : TuraevViroModel P ι)
    (g : ℕ) (x : ι) (ε : ℝ) {a' : ℂ} (h : ‖a' - M.amplitude g x‖ ≤ ε) :
    ‖((M.D : ℝ) : ℂ) ^ (g - 1) * a' - M.wrtInvariant g x‖ ≤ M.D ^ (g - 1) * ε := by
  have hpos : 0 ≤ M.D ^ (g - 1) := pow_nonneg (le_of_lt M.D_pos) _
  unfold wrtInvariant
  rw [← mul_sub, norm_mul, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (pow_pos M.D_pos _)]
  exact mul_le_mul_of_nonneg_left h hpos

theorem wrtScale_phase_invariant {P ι : Type*} [Fintype P] (M : TuraevViroModel P ι)
    (g : ℕ) (x : ι) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ‖ζ * M.wrtInvariant g x‖ ^ 2 = M.tvInvariant g x := by
  rw [norm_mul, hζ, one_mul]
  rfl

end Qatlib.Papers.TuraevViro10.MainResults.HadamardTest
