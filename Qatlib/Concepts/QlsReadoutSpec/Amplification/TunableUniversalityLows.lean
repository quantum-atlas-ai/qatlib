/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.TunableUniversalityStat
import Qatlib.Concepts.QlsReadoutSpec.ProgramModel.PaidWordSemanticsLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.ProjectorOrderLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.ClockFlagResolutionsLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.StoppedStageTransportLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.ActualNestedAmplificationLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.TightDirichletBoundsLows

/-!
# Forward and reverse bounds for tunable schedules

This module proves `Clause8TunableUniversality_answer`. Forward bounds express minimal round
counts using a natural ceiling and control total loss by the sum of thresholds; reverse bounds
reconstruct thresholds from sufficiently small positive pre-amplitudes and bound their sum by
the negative logarithm of total loss.

The schedule analysis supports variable-time amplitude amplification [Ambainis2012]. For
universality of tunable VTAA, see [LowSu2026].

## Main statements

* `Clause8TunableUniversality_answer`: Proves the forward schedule formulas and reverse
  threshold guarantees.

## References

* [Ambainis, 2012][Ambainis2012]
* [Low and Su, 2026][LowSu2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QlsReadoutSpec.ProgramModel

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QlsReadoutSpec.Amplification

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Qatlib.Concepts.QlsReadoutSpec.Amplification

open Matrix Qatlib.Concepts.QlsReadoutSpec.Amplification
open scoped Classical BigOperators

/-- For `α` in the unit interval, `(5 / 6) ^ α ≤ 1 - α / 6`. -/
private theorem rpow_five_six_le (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    (5 / 6 : ℝ) ^ α ≤ 1 - α / 6 := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := α) (w₂ := 1 - α)
    (p₁ := (5 / 6 : ℝ)) (p₂ := (1 : ℝ)) h0 (by linarith) (by norm_num) (by norm_num) (by ring)
  have hone : ((1 : ℝ) ^ (1 - α)) = 1 := Real.one_rpow _
  have hsum : α * (5 / 6 : ℝ) + (1 - α) * 1 = 1 - α / 6 := by ring
  rw [hone, mul_one] at h
  nlinarith

/-- For a positive real base, a finite product of real powers equals the base raised to the sum
of the exponents. -/
private theorem prod_rpow {ι : Type} [Fintype ι] (b : ℝ) (hb : 0 < b) (f : ι → ℝ) :
    (∏ i, b ^ f i) = b ^ ∑ i, f i := by
  have hdef : ∀ x : ℝ, b ^ x = Real.exp (Real.log b * x) := fun x =>
    Real.rpow_def_of_pos hb x
  calc (∏ i, b ^ f i) = ∏ i, Real.exp (Real.log b * f i) :=
      Finset.prod_congr rfl fun i _ => hdef _
    _ = Real.exp (∑ i, Real.log b * f i) := (Real.exp_sum _ _).symm
    _ = Real.exp (Real.log b * ∑ i, f i) := by rw [← Finset.mul_sum]
    _ = b ^ ∑ i, f i := (hdef _).symm

/-- For real `u < 1`, `u ≤ -Real.log (1 - u)`. -/
private theorem neg_log_one_sub_le (u : ℝ) (_h0 : 0 ≤ u) (h1 : u < 1) :
    u ≤ -Real.log (1 - u) := by
  have hpos : 0 < 1 - u := by linarith
  have h := Real.log_le_sub_one_of_pos hpos
  nlinarith

/-- For a natural factor at least one, a linearized amplitude at most one implies an amplified
arcsine angle at most `Real.pi / 2`. -/
private theorem mul_arcsin_le_pi_div_two (ρ : ℕ) (a : ℝ) (hρ : 1 ≤ ρ)
    (_ha : 0 ≤ a) (hle : (ρ : ℝ) * a ≤ 1) :
    (ρ : ℝ) * Real.arcsin a ≤ Real.pi / 2 := by
  have hρpos : (0:ℝ) < ρ := by
    exact_mod_cast (by omega : (0:ℕ) < ρ)
  have hx0 : 0 ≤ Real.pi / 2 / (ρ:ℝ) := by positivity
  have hx1 : Real.pi / 2 / (ρ:ℝ) ≤ Real.pi / 2 := by
    have h1ρ : (1:ℝ) ≤ ρ := by exact_mod_cast hρ
    rw [div_le_iff₀ hρpos]
    nlinarith [Real.pi_pos]
  have hsin : 1 / (ρ:ℝ) ≤ Real.sin (Real.pi / 2 / (ρ:ℝ)) := by
    have h := Real.mul_le_sin hx0 hx1
    have hsimp : 2 / Real.pi * (Real.pi / 2 / (ρ:ℝ)) = 1 / (ρ:ℝ) := by
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
    linarith
  have hdiv : a ≤ 1 / (ρ:ℝ) := by
    rw [le_div_iff₀ hρpos]
    nlinarith
  have harc : Real.arcsin a ≤ Real.pi / 2 / (ρ:ℝ) := by
    have hmono : Real.arcsin a ≤ Real.arcsin (Real.sin (Real.pi / 2 / (ρ:ℝ))) :=
      Real.arcsin_le_arcsin (by linarith)
    have hneg : -(Real.pi / 2) ≤ Real.pi / 2 / (ρ:ℝ) := by nlinarith [Real.pi_pos]
    rwa [Real.arcsin_sin hneg hx1] at hmono
  have hmul : (ρ:ℝ) * (Real.pi / 2 / (ρ:ℝ)) = Real.pi / 2 := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left harc (le_of_lt hρpos)]

/-- The natural ceiling of a nonpositive real number is zero. -/
private theorem ceil_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : Nat.ceil x = 0 :=
  Nat.ceil_eq_zero.mpr hx

/-- A real number strictly above `n - 1` and at most a nonzero natural `n` has natural ceiling
`n`. -/
private theorem ceil_eq_of_mem {x : ℝ} {n : ℕ} (hn : n ≠ 0)
    (hlo : ((n - 1 : ℕ) : ℝ) < x) (hhi : x ≤ (n : ℝ)) : Nat.ceil x = n :=
  (Nat.ceil_eq_iff hn).mpr ⟨hlo, hhi⟩

/-- The squared vector norm equals the sum of squared coordinate norms. -/
private theorem normVec_sq_eq {H : Type} [Fintype H] (v : QState H) :
    normVec v ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  show ‖toEuclidean_fromVec v‖ ^ 2 = _
  exact norm_toEuclidean_fromVec_sq v

/-- The vector norm is nonnegative. -/
private theorem normVec_nonneg' {H : Type} [Fintype H] (v : QState H) :
    0 ≤ normVec v := norm_nonneg _

/-- Real scalar multiplication scales the vector norm by the scalar's absolute value. -/
private theorem normVec_smul_real {H : Type} [Fintype H] (r : ℝ) (v : QState H) :
    normVec ((r : ℂ) • v) = |r| * normVec v := by
  have hkey : normVec ((r : ℂ) • v) ^ 2 = (|r| * normVec v) ^ 2 := by
    rw [normVec_sq_eq, mul_pow, normVec_sq_eq, Finset.mul_sum]
    simp only [Pi.smul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  refine le_antisymm ?_ ?_
  · exact le_of_sq_le_sq hkey.le (mul_nonneg (abs_nonneg _) (norm_nonneg _))
  · exact le_of_sq_le_sq hkey.ge (norm_nonneg _)

/-- An orthogonal projector cannot increase the vector norm. -/
private theorem normVec_mul_proj_le {H : Type} [Fintype H] [DecidableEq H]
    (G : Matrix H H ℂ) (hG : IsOrthogonalProjector G) (v : QState H) :
    normVec (G *ᵥ v) ≤ normVec v := by
  have h1 : IsOrthogonalProjector (1 : Matrix H H ℂ) :=
    @IsStarProjection.one (Matrix H H ℂ) _ _
  have hG' : (1 : Matrix H H ℂ) * G = G := one_mul G
  have h2 := (Clause2ProjectorOrder_answer H G (1 : Matrix H H ℂ) hG h1).2.2.2.2.2.2
  have h3 := (h2.mp hG') v
  simpa [Matrix.one_mulVec] using! h3

/-- A legal word of unitary oracles sends a normalized input to a clock state of norm one. -/
private theorem normVec_clockState_eq_one {H : Type} [Fintype H] [DecidableEq H]
    {slots : ℕ} (U : ℕ → Matrix H H ℂ) (C : Word H 1) (ω : QState H)
    (hU : ∀ j < slots, U j ∈ Matrix.unitaryGroup H ℂ)
    (hlegal : legal slots C) (hω : Normalized ω) :
    normVec (clockState U C ω) = 1 := by
  have hrun : Normalized (run (by omega : (0:ℕ) < 1) U C ω) :=
    run_normalized (by omega) U C ω hU hlegal hω
  have hsplit : (∑ p : Space H 1, ‖run (by omega : (0:ℕ) < 1) U C ω p‖ ^ 2)
      = ∑ h' : H, ‖run (by omega : (0:ℕ) < 1) U C ω (h', 0)‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun h' _ => by rw [Fin.sum_univ_one]
  have hkey : ∑ h' : H, ‖clockState U C ω h'‖ ^ 2
      = ∑ h' : H, ‖run (by omega : (0:ℕ) < 1) U C ω (h', 0)‖ ^ 2 := by
    rfl
  have h := normVec_sq_eq (clockState U C ω)
  rw [hkey, ← hsplit, hrun] at h
  have hnn : 0 ≤ normVec (clockState U C ω) := norm_nonneg _
  nlinarith

/-- A fully controlled matrix acts on the unique clock slice by its underlying data matrix. -/
private theorem controlled_univ_apply {H : Type} [Fintype H] [DecidableEq H]
    (U : Matrix H H ℂ) (v : QState (Space H 1)) (h : H) :
    (controlled U Finset.univ *ᵥ v) (h, (0 : Fin 1))
      = (U *ᵥ (fun h' : H => v (h', (0 : Fin 1)))) h := by
  have hfin : ∀ h' : H,
      (∑ k' : Fin 1, controlled U Finset.univ (h, (0 : Fin 1)) (h', k') * v (h', k'))
        = U h h' * v (h', (0 : Fin 1)) := by
    intro h'
    rw [Fin.sum_univ_one]
    simp [controlled]
  have hL : (controlled U Finset.univ *ᵥ v) (h, (0 : Fin 1))
      = ∑ t : H × Fin 1, controlled U Finset.univ (h, (0 : Fin 1)) t * v t := rfl
  rw [hL, Fintype.sum_prod_type]
  simp_rw [hfin]
  rfl

/-- Appending a stage word applies its oracle to the current clock state. -/
private theorem clockState_append_call {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (C : Word H 1) (k : ℕ) (ω : QState H) :
    clockState U (C ++ stageWord k) ω = U k *ᵥ clockState U C ω := by
  have hstage : wordMatrix U (stageWord k) = controlled (U k) Finset.univ := by
    unfold wordMatrix stageWord
    simp
  have hwm : wordMatrix U (C ++ stageWord k)
      = controlled (U k) Finset.univ * wordMatrix U C := by
    rw [wordMatrix_append, hstage]
  funext h
  have hL : clockState U (C ++ stageWord k) ω h
      = (controlled (U k) Finset.univ
          *ᵥ (wordMatrix U C *ᵥ clean 1 (by omega) ω)) (h, (0 : Fin 1)) := by
    show (wordMatrix U (C ++ stageWord k) *ᵥ clean 1 (by omega) ω) (h, (0 : Fin 1)) = _
    rw [hwm, Matrix.mulVec_mulVec]
  rw [hL, controlled_univ_apply]
  rfl

/-- The next plain prefix appends the next stage word to the preceding plain prefix. -/
private theorem plainPrefix_succ {H : Type} (k : ℕ) :
    plainPrefix (k + 1) = (plainPrefix k ++ stageWord (k + 1) : Word H 1) := by
  simp [plainPrefix, stageWord, List.range_succ, List.map_append]

/-- The plain prefix at zero is the stage-zero word. -/
private theorem plainPrefix_zero {H : Type} : plainPrefix 0 = (stageWord 0 : Word H 1) := by
  simp [plainPrefix, stageWord, List.range_succ]

/-- The nested word at zero is the stage-zero word. -/
private theorem nestedWord_zero {H : Type} [Fintype H] [DecidableEq H]
    {P : ℕ → Matrix H H ℂ} {bad : Matrix H H ℂ}
    {ω : QState H} {rounds : ℕ → ℕ} :
    nestedWord P bad ω rounds 0 = stageWord 0 := rfl

/-- The next nested word amplifies the current nested word followed by the next stage, using the
next potential and round count. -/
private theorem nestedWord_succ {H : Type} [Fintype H] [DecidableEq H]
    {P : ℕ → Matrix H H ℂ} {bad : Matrix H H ℂ}
    {ω : QState H} {rounds : ℕ → ℕ} (k : ℕ) :
    nestedWord P bad ω rounds (k + 1)
      = aaWord (nestedWord P bad ω rounds k ++ stageWord (k + 1)) ω
          (potential (P (k + 1)) bad) (rounds (k + 1)) := rfl

/-- For amplitudes and thresholds at most one, a minimal round count reaching the square-root
threshold divided by three has linearized amplitude at most one. -/
private theorem schedule_bound (r : ℕ) (a β αk : ℝ)
    (_ha : 0 ≤ a) (ha1 : a ≤ 1) (_hα0 : 0 ≤ αk) (hα1 : αk ≤ 1)
    (hb : β = Real.sqrt αk)
    (hmain : β / 3 ≤ (2 * (r : ℝ) + 1 ) * a)
    (hmin : ∀ s < r, (2 * (s : ℝ) + 1 ) * a < β / 3) :
    (2 * (r : ℝ) + 1 ) * a ≤ 1 := by
  have hβ : β ≤ 1 := by
    rw [hb]
    have h : Real.sqrt αk ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by nlinarith)
    simpa using! h
  by_cases hr0 : r = 0
  · subst hr0
    push_cast at hmain ⊢
    nlinarith
  · have hr1 : 1 ≤ r := by omega
    have hcast : (2 * (r : ℝ) - 1) + 2 = 2 * (r : ℝ) + 1 := by ring
    have hρpos : (0:ℝ) < 2 * (r : ℝ) - 1 := by
      have h1r : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr1
      nlinarith
    have h1 : (2 * (r : ℝ) - 1 ) * a < 1 / 3 := by
      have h := hmin (r - 1) (by omega)
      have heq : (2 * ((r - 1 : ℕ) : ℝ) + 1) = 2 * (r : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
        ring
      rw [heq] at h
      nlinarith
    have ha2 : a < 1 / (3 * (2 * (r : ℝ) - 1 )) := by
      have hden : 0 < 3 * (2 * (r : ℝ) - 1 ) := by nlinarith [hρpos]
      rw [lt_div_iff₀ hden]
      nlinarith
    have hsum : (2 * (r : ℝ) + 1) * a = (2 * (r : ℝ) - 1) * a + 2 * a := by
      rw [← hcast]
      ring
    have hle : 1 / 3 + 2 * (1 / (3 * (2 * (r : ℝ) - 1 ))) ≤ 1 := by
      have hden : 0 < 3 * (2 * (r : ℝ) - 1 ) := by nlinarith [hρpos]
      have hd1 : (1:ℝ) ≤ 2 * (r : ℝ) - 1 := by
        have h1r : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr1
        nlinarith
      have hfrac : 2 * (1 / (3 * (2 * (r : ℝ) - 1 ))) ≤ 2 / 3 := by
        have : 1 / (3 * (2 * (r : ℝ) - 1 )) ≤ 1 / 3 :=
          (div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 3)).mpr (by nlinarith [hd1])
        linarith
      linarith
    nlinarith [ha2, hsum, hle, _ha, hρpos]

/-- For positive amplitude `a`, the minimal round count reaching `β / 3` is `Nat.ceil (β / (6 *
a) - 1 / 2)` when `β` is the square root of the threshold. -/
private theorem schedule_ceil (r : ℕ) (a β αk : ℝ)
    (ha : 0 < a) (_hα0 : 0 ≤ αk)
    (hb : β = Real.sqrt αk)
    (hmain : β / 3 ≤ (2 * (r : ℝ) + 1 ) * a)
    (hmin : ∀ s < r, (2 * (s : ℝ) + 1 ) * a < β / 3) :
    r = Nat.ceil (β / (6 * a) - 1 / 2) := by
  have hβ : 0 ≤ β := by rw [hb]; exact Real.sqrt_nonneg _
  by_cases hr0 : r = 0
  · subst hr0
    push_cast at hmain
    have hba : β / (6 * a) ≤ 1 / 2 := by
      have h6 : 0 < 6 * a := by positivity
      rw [div_le_iff₀ h6]
      nlinarith
    have hx : β / (6 * a) - 1 / 2 ≤ 0 := by linarith
    exact (ceil_eq_zero_of_nonpos hx).symm
  · have hr1 : 1 ≤ r := by omega
    have hcast : (2 * (r : ℝ) - 1) + 2 = 2 * (r : ℝ) + 1 := by ring
    have h1 : (2 * (r : ℝ) - 1 ) * a < β / 3 := by
      have h := hmin (r - 1) (by omega)
      have heq : (2 * ((r - 1 : ℕ) : ℝ) + 1) = 2 * (r : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
        ring
      rw [heq] at h
      exact h
    have h6 : 0 < 6 * a := by positivity
    have hlo : ((r - 1 : ℕ) : ℝ) < β / (6 * a) - 1 / 2 := by
      have hcast1 : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
      rw [hcast1]
      have hmul : (2 * (r : ℝ) - 1 ) * a * 3 < β := by nlinarith
      have hnum : (2 * (r : ℝ) - 1 ) * a * 3 / (6 * a) < β / (6 * a) :=
        (div_lt_div_iff_of_pos_right h6).mpr hmul
      have hcancel : (2 * (r : ℝ) - 1 ) * a * 3 / (6 * a) = (2 * (r : ℝ) - 1 ) / 2 := by
        have hane : a ≠ 0 := by positivity
        field_simp; ring
      rw [hcancel] at hnum
      have hcast2 : (2 * (r : ℝ) - 1) / 2 = (r : ℝ) - 1 / 2 := by
        field_simp
      rw [hcast2] at hnum
      linarith
    have hhi : β / (6 * a) - 1 / 2 ≤ (r : ℝ) := by
      have hmul : β ≤ (2 * (r : ℝ) + 1 ) * a * 3 := by nlinarith
      have hnum : β / (6 * a) ≤ (2 * (r : ℝ) + 1 ) * a * 3 / (6 * a) :=
        (div_le_div_iff_of_pos_right h6).mpr hmul
      have hcancel : (2 * (r : ℝ) + 1 ) * a * 3 / (6 * a) = (2 * (r : ℝ) + 1 ) / 2 := by
        have hane : a ≠ 0 := by positivity
        field_simp; ring
      rw [hcancel] at hnum
      have hcast2 : (2 * (r : ℝ) + 1) / 2 = (r : ℝ) + 1 / 2 := by
        field_simp
      rw [hcast2] at hnum
      linarith
    exact (ceil_eq_of_mem hr0 hlo hhi).symm

/-- For a positive minimal round count, the squared linearized amplitude is strictly below the
threshold used in the stopping criterion. -/
private theorem schedule_sq_lt (r : ℕ) (a β αk : ℝ)
    (_ha : 0 ≤ a) (hα0 : 0 ≤ αk) (hr : 1 ≤ r)
    (hb : β = Real.sqrt αk)
    (hmin : ∀ s < r, (2 * (s : ℝ) + 1 ) * a < β / 3) :
    (2 * (r : ℝ) + 1 ) ^ 2 * a ^ 2 < αk := by
  have h1 : (2 * (r : ℝ) - 1 ) * a < β / 3 := by
    have h := hmin (r - 1) (by omega)
    have heq : (2 * ((r - 1 : ℕ) : ℝ) + 1) = 2 * (r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
      ring
    rw [heq] at h
    exact h
  have hcmp : (2 * r + 1 : ℕ) ≤ 3 * (2 * r - 1) := by omega
  have hcmp' : (2 * (r : ℝ) + 1) ≤ 3 * (2 * (r : ℝ) - 1) := by
    have h1r : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
    nlinarith
  have hnn : 0 ≤ (2 * (r : ℝ) + 1 ) * a := by positivity
  have hlt : (2 * (r : ℝ) + 1 ) * a < β := by nlinarith
  have hsq : ((2 * (r : ℝ) + 1 ) * a) ^ 2 < β ^ 2 := by
    nlinarith [sq_nonneg ((2 * (r : ℝ) + 1 ) * a - β), hlt, hnn]
  have hβsq : β ^ 2 = αk := by
    rw [hb]
    exact Real.sq_sqrt hα0
  nlinarith [hβsq]

/-- Establishes the ceiling formula and loss lower bound for tunable schedules, together with
reverse-threshold tunability and a logarithmic loss bound, as specified by
`Clause8TunableUniversality`. See [Low and Su, Proposition 4][LowSu2026]. -/
theorem Clause8TunableUniversality_answer : Clause8TunableUniversality := by
  intro H _instF _instD m P bad U ω α rs hclock hstage hnorm hplain
  (try dsimp only)
  set E := extendClock m P with hEd
  obtain ⟨hP, hP0, hPm, hpsd, hbad, hcomm⟩ := hclock
  obtain ⟨hUunit, hstagefix⟩ := hstage
  have g3 := Clause3ClockFlagResolutions_answer H m P bad ⟨hP, hP0, hPm, hpsd, hbad, hcomm⟩
  have g4 := Clause4StoppedStageTransport_answer.2 H m P bad U
    ⟨hP, hP0, hPm, hpsd, hbad, hcomm⟩ ⟨hUunit, hstagefix⟩
  have hE_le : ∀ k (hk : k ≤ m), E k = P ⟨k, by omega⟩ := by
    intro k hk
    show (if h : k ≤ m then P ⟨k, by omega⟩ else P ⟨m, by omega⟩) = P ⟨k, by omega⟩
    rw [dif_pos hk]
  have hpot_prod : ∀ (p q : Fin (m + 1)), p.val ≤ q.val →
      potential (P q) bad * potential (P p) bad = potential (P q) bad ∧
      potential (P p) bad * potential (P q) bad = potential (P q) bad := by
    intro p q hpq
    have h := (g3.1 p q hpq).2.2.2.2.2.2
    exact ⟨h.1, h.2.1⟩
  have hpot_proj : ∀ p : Fin (m + 1), IsOrthogonalProjector (potential (P p) bad) := by
    intro p
    exact (g3.1 p p le_rfl).2.2.2.2.2.1
  have hpotE : ∀ k, k ≤ m → IsOrthogonalProjector (potential (E k) bad) := by
    intro k hk
    have hklt : k < m + 1 := by omega
    rw [hE_le k hk]
    exact hpot_proj ⟨k, hklt⟩
  have hpot_absorb : ∀ k, k < m →
      potential (E (k+1)) bad * potential (E k) bad = potential (E (k+1)) bad := by
    intro k hk
    have hk' : k ≤ m := by omega
    have hk1 : k + 1 ≤ m := by omega
    have hklt : k < m + 1 := by omega
    have hk1lt : k + 1 < m + 1 := by omega
    have h := hpot_prod ⟨k, hklt⟩ ⟨k+1, hk1lt⟩ (by omega : (k:ℕ) ≤ k + 1)
    rw [← hE_le k hk', ← hE_le (k+1) hk1] at h
    exact h.1
  have hpot_comm : ∀ (p : Fin (m + 1)) (i : ℕ), p.val < i → i ≤ m →
      U i * potential (P p) bad = potential (P p) bad * U i := by
    intro p i hlt hle
    have hilt : i < m + 1 := by omega
    exact (g4.1 p ⟨i, hilt⟩ (by simpa using! hlt : p.val < (⟨i, hilt⟩ : Fin (m+1)).val)).2.2
  have hcommE : ∀ k, k < m → U (k+1) * potential (E k) bad = potential (E k) bad * U (k+1) := by
    intro k hk
    have hk' : k ≤ m := by omega
    have hklt : k < m + 1 := by omega
    rw [hE_le k hk']
    exact hpot_comm ⟨k, hklt⟩ (k+1) (by simp) (by omega)
  have hplain_mono : ∀ (p q : Fin (m + 1)), p.val ≤ q.val →
      plainAmplitude E bad U ω q.val ≤ plainAmplitude E bad U ω p.val := by
    intro p q hpq
    simpa [hEd] using! g4.2.2 p q ω hpq
  have hUslots : ∀ j < m + 1, U j ∈ Matrix.unitaryGroup H ℂ := by
    intro j hj
    exact hUunit ⟨j, hj⟩
  have hplain_pos : ∀ j : Fin m, 0 < plainAmplitude E bad U ω (j.val+1) := by
    intro j
    have hjlt : j.val < m := j.isLt
    have hj1 : j.val + 1 ≤ m := by omega
    have hj1lt : j.val + 1 < m + 1 := by omega
    have hmlt : m < m + 1 := by omega
    have hmono := hplain_mono ⟨j.val+1, hj1lt⟩ ⟨m, hmlt⟩ hj1
    exact lt_of_lt_of_le hplain hmono
  have hcast21 : ∀ x : ℕ, (2 * (x : ℝ) + 1) = ((2 * x + 1 : ℕ) : ℝ) := by
    intro x
    simp

  have hshift : ∀ k (hk : k < m) (c : ℝ) (φ ψk : QState H),
      Matrix.mulVec (potential (E k) bad) φ
        = (c : ℂ) • (Matrix.mulVec (potential (E k) bad) ψk) →
      Matrix.mulVec (potential (E (k+1)) bad) (Matrix.mulVec (U (k+1)) φ)
        = (c : ℂ) • (Matrix.mulVec (potential (E (k+1)) bad) (Matrix.mulVec (U (k+1)) ψk)) := by
    intro k hk c φ ψk hidk
    have habs : potential (E (k+1)) bad * potential (E k) bad = potential (E (k+1)) bad :=
      hpot_absorb k hk
    have hcommk : U (k+1) * potential (E k) bad = potential (E k) bad * U (k+1) :=
      hcommE k hk
    have habsv : ∀ v : QState H,
        Matrix.mulVec (potential (E (k+1)) bad) (Matrix.mulVec (potential (E k) bad) v)
          = Matrix.mulVec (potential (E (k+1)) bad) v := by
      intro v
      have e1 := Matrix.mulVec_mulVec v (potential (E (k+1)) bad) (potential (E k) bad)
      rw [e1, habs]
    have hcommv : ∀ v : QState H,
        Matrix.mulVec (potential (E k) bad) (Matrix.mulVec (U (k+1)) v)
          = Matrix.mulVec (U (k+1)) (Matrix.mulVec (potential (E k) bad) v) := by
      intro v
      rw [Matrix.mulVec_mulVec v (potential (E k) bad) (U (k+1)),
        Matrix.mulVec_mulVec v (U (k+1)) (potential (E k) bad), hcommk]
    calc Matrix.mulVec (potential (E (k+1)) bad) (Matrix.mulVec (U (k+1)) φ)
        = Matrix.mulVec (potential (E (k+1)) bad)
            (Matrix.mulVec (potential (E k) bad) (Matrix.mulVec (U (k+1)) φ)) :=
          (habsv _).symm
      _ = Matrix.mulVec (potential (E (k+1)) bad)
            (Matrix.mulVec (U (k+1)) (Matrix.mulVec (potential (E k) bad) φ)) := by rw [hcommv]
      _ = Matrix.mulVec (potential (E (k+1)) bad)
            (Matrix.mulVec (U (k+1)) ((c : ℂ) • (Matrix.mulVec (potential (E k) bad) ψk))) := by
          rw [hidk]
      _ = (c : ℂ) • (Matrix.mulVec (potential (E (k+1)) bad)
            (Matrix.mulVec (U (k+1)) (Matrix.mulVec (potential (E k) bad) ψk))) := by
          simp only [Matrix.mulVec_smul]
      _ = (c : ℂ) • (Matrix.mulVec (potential (E (k+1)) bad)
            (Matrix.mulVec (potential (E k) bad) (Matrix.mulVec (U (k+1)) ψk))) := by
          rw [hcommv]
      _ = (c : ℂ) • (Matrix.mulVec (potential (E (k+1)) bad)
            (Matrix.mulVec (U (k+1)) ψk)) := by rw [habsv]
  constructor
  · intro hfwd
    obtain ⟨htun, hall⟩ := hfwd
    have htunj : ∀ j < m, 0 ≤ α (j+1) ∧
        Real.sqrt (α (j+1)) / 3 ≤ (2 * (rs (j+1) : ℝ) + 1) * preAmplitude E bad ω U rs j ∧
        ∀ s < rs (j+1), (2 * (s : ℝ) + 1) * preAmplitude E bad ω U rs j
          < Real.sqrt (α (j+1)) / 3 := fun j hj => htun.2 j hj

    have hcore : ∀ k, k ≤ m → ∃ c : ℝ, 0 < c ∧
        legal (m + 1) (nestedWord E bad ω rs k) ∧
        potential (E k) bad *ᵥ clockState U (nestedWord E bad ω rs k) ω
          = (c : ℂ) • (potential (E k) bad *ᵥ clockState U (plainPrefix k) ω) ∧
        (k < m → preAmplitude E bad ω U rs k ≤ 1 ∧
          (2 * (rs (k+1) : ℝ) + 1) * preAmplitude E bad ω U rs k ≤ 1) := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨1, one_pos, ?_, ?_, ?_⟩
        · intro s hs
          have hs0 : s = .call 0 Finset.univ false := by
            simpa [nestedWord, stageWord] using! hs
          subst hs0
          show (0:ℕ) < m + 1
          omega
        · rw [nestedWord_zero, plainPrefix_zero]
          simp
        · intro hk
          have hB : legal (m + 1) (nestedWord E bad ω rs 0 ++ stageWord 1) := by
            intro s hs
            rw [List.mem_append, nestedWord_zero] at hs
            rcases hs with h | h
            · have hs0 : s = .call 0 Finset.univ false := by simpa [stageWord] using! h
              subst hs0
              show (0:ℕ) < m + 1
              omega
            · have hs1 : s = .call 1 Finset.univ false := by simpa [stageWord] using! h
              subst hs1
              show (1:ℕ) < m + 1
              omega
          have hBv : normVec (clockState U (nestedWord E bad ω rs 0 ++ stageWord 1) ω) = 1 :=
            normVec_clockState_eq_one U _ ω hUslots hB hnorm
          have hle1 : preAmplitude E bad ω U rs 0 ≤ 1 := by
            have h := normVec_mul_proj_le (potential (E 1) bad) (hpotE 1 (by omega))
              (clockState U (nestedWord E bad ω rs 0 ++ stageWord 1) ω)
            rw [hBv] at h
            simpa [preAmplitude] using! h
          refine ⟨hle1, ?_⟩
          obtain ⟨_, hmain, hmin⟩ := htunj 0 hk
          exact schedule_bound (rs 1) (preAmplitude E bad ω U rs 0)
            (Real.sqrt (α 1)) (α 1) (norm_nonneg _) hle1 (htunj 0 hk).1 (hall ⟨0, hk⟩)
            rfl hmain hmin
      | succ k ih =>
        intro hk
        have hkle : k ≤ m := by omega
        have hlt : k < m := by omega
        obtain ⟨c, hcpos, hlegk, hidk, hbndk⟩ := ih hkle
        obtain ⟨hale, hF2⟩ := hbndk hlt
        obtain ⟨hα0, hmain, hmin⟩ := htunj k hlt
        have hα1 : α (k+1) ≤ 1 := hall ⟨k, hlt⟩
        set Bk : Word H 1 := nestedWord E bad ω rs k ++ stageWord (k+1) with hBkd
        set Gk1 : Matrix H H ℂ := potential (E (k+1)) bad with hGk1d
        set aK : ℝ := preAmplitude E bad ω U rs k with haKd
        set r : ℕ := rs (k+1) with hrd
        have hB : legal (m + 1) Bk := by
          intro s hs
          rw [hBkd, List.mem_append] at hs
          rcases hs with h | h
          · exact hlegk s h
          · have hs1 : s = .call (k+1) Finset.univ false := by simpa [stageWord] using! h
            subst hs1
            show (k+1:ℕ) < m + 1
            omega
        have hGk1p : IsOrthogonalProjector Gk1 := by
          rw [hGk1d]
          exact hpotE (k+1) (by omega)
        have hBv : normVec (clockState U Bk ω) = 1 := by
          rw [hBkd]
          exact normVec_clockState_eq_one U _ ω hUslots hB hnorm
        have haK_form : aK = normVec (Gk1 *ᵥ clockState U Bk ω) := by
          rw [haKd, hGk1d, hBkd]
          rfl
        have hF2c : ((2 * r + 1 : ℕ) : ℝ) * aK ≤ 1 := by
          rw [← hcast21 r, hrd, haKd]
          exact hF2
        have hangle : ((2 * r + 1 : ℕ) : ℝ) * Real.arcsin aK ≤ Real.pi / 2 :=
          mul_arcsin_le_pi_div_two (2 * r + 1) aK (by omega) (norm_nonneg _) hF2c
        have hg5 := Clause5ActualNestedAmplification_answer H (m + 1) U Bk ω Gk1 r
          hUslots hB hnorm hGk1p
        have hleg' : legal (m + 1) (aaWord Bk ω Gk1 r) := (hg5 hangle).1
        have hsine : Gk1 *ᵥ clockState U (aaWord Bk ω Gk1 r) ω
            = ((((2 * r + 1 : ℕ) : ℂ)) * ((gainLoss (2 * r + 1)
                (normVec (Gk1 *ᵥ clockState U Bk ω)) : ℝ) : ℂ)) • (Gk1 *ᵥ clockState U Bk ω) :=
          (hg5 hangle).2.1

        have hgain_pos : 0 < ((2 * r + 1 : ℕ) : ℝ) *
            gainLoss (2 * r + 1) (normVec (Gk1 *ᵥ clockState U Bk ω)) := by
          set gN : ℝ := normVec (Gk1 *ᵥ clockState U Bk ω) with hgN
          have hgNpos : 0 ≤ gN := by rw [hgN]; exact norm_nonneg _
          have hangle' : ((2 * r + 1 : ℕ) : ℝ) * Real.arcsin gN ≤ Real.pi / 2 := by
            rw [← haK_form]
            exact hangle
          unfold gainLoss
          split_ifs with hg0
          · have h : (0:ℝ) < ((2 * r + 1 : ℕ) : ℝ) :=
              by exact_mod_cast (by omega : 0 < 2 * r + 1)
            nlinarith
          · have hg0' : 0 < gN := lt_of_le_of_ne hgNpos (Ne.symm hg0)
            have hρpos : (0:ℝ) < ((2 * r + 1 : ℕ) : ℝ) :=
              Nat.cast_pos.mpr (by omega : 0 < 2 * r + 1)
            have hnum : 0 < Real.sin (((2 * r + 1 : ℕ) : ℝ) * Real.arcsin gN) := by
              have hpos : 0 < Real.arcsin gN := Real.arcsin_pos.mpr hg0'
              have hlt2 : ((2 * r + 1 : ℕ) : ℝ) * Real.arcsin gN < Real.pi := by
                linarith [Real.pi_pos]
              exact Real.sin_pos_of_pos_of_lt_pi (mul_pos hρpos hpos) hlt2
            have hden : 0 < ((2 * r + 1 : ℕ) : ℝ) * gN := mul_pos hρpos hg0'
            exact mul_pos hρpos (div_pos hnum hden)

        have hcommk : U (k+1) * potential (E k) bad = potential (E k) bad * U (k+1) :=
          hcommE k hlt
        have habs : potential (E (k+1)) bad * potential (E k) bad = potential (E (k+1)) bad :=
          hpot_absorb k hlt
        have hstep : (Gk1 * U (k+1)) *ᵥ clockState U (nestedWord E bad ω rs k) ω
            = (c : ℂ) • (Gk1 *ᵥ clockState U (plainPrefix (k+1)) ω) := by
          rw [← Matrix.mulVec_mulVec (clockState U (nestedWord E bad ω rs k) ω) Gk1 (U (k+1))]
          have hsh := hshift k hlt c
            (clockState U (nestedWord E bad ω rs k) ω) (clockState U (plainPrefix k) ω) hidk
          rw [← hGk1d] at hsh
          rw [hsh]
          have hplain : clockState U (plainPrefix (k+1)) ω
              = U (k+1) *ᵥ clockState U (plainPrefix k) ω := by
            rw [plainPrefix_succ]
            exact clockState_append_call U _ (k+1) ω
          rw [hplain]
        have hid : ∃ c' : ℝ, 0 < c' ∧
            Gk1 *ᵥ clockState U (nestedWord E bad ω rs (k+1)) ω
              = (c' : ℂ) • (Gk1 *ᵥ clockState U (plainPrefix (k+1)) ω) := by
          have hnest : nestedWord E bad ω rs (k+1) = aaWord Bk ω Gk1 r := by
            rw [nestedWord_succ, ← hBkd, ← hGk1d, ← hrd]
          have hbase : clockState U Bk ω = U (k+1) *ᵥ clockState U (nestedWord E bad ω rs k) ω := by
            rw [hBkd]
            exact clockState_append_call U _ (k+1) ω
          refine ⟨((2 * r + 1 : ℕ) : ℝ) * gainLoss (2 * r + 1) (normVec (Gk1 *ᵥ clockState U Bk ω)) * c,
            mul_pos hgain_pos hcpos, ?_⟩
          have e1 : Gk1 *ᵥ clockState U (nestedWord E bad ω rs (k+1)) ω
              = Gk1 *ᵥ clockState U (aaWord Bk ω Gk1 r) ω := by rw [← hnest]
          have e2 : Gk1 *ᵥ clockState U Bk ω
              = (c : ℂ) • (Gk1 *ᵥ clockState U (plainPrefix (k+1)) ω) := by
            rw [hbase]
            have e2a : Gk1 *ᵥ (U (k+1) *ᵥ clockState U (nestedWord E bad ω rs k) ω)
                = (Gk1 * U (k+1)) *ᵥ clockState U (nestedWord E bad ω rs k) ω :=
              Matrix.mulVec_mulVec (clockState U (nestedWord E bad ω rs k) ω) Gk1 (U (k+1))
            rw [e2a]
            exact hstep
          rw [e1, hsine, e2]
          push_cast
          simp only [← mul_smul]
        obtain ⟨c', hc'pos, hid'⟩ := hid
        refine ⟨c', hc'pos, ?_, hid', ?_⟩
        · rw [nestedWord_succ, ← hBkd, ← hGk1d, ← hrd]
          exact hleg'
        · intro hk2
          have hB2 : legal (m + 1) (nestedWord E bad ω rs (k+1) ++ stageWord (k+2)) := by
            intro s hs
            rw [List.mem_append] at hs
            rcases hs with h | h
            · rw [nestedWord_succ, ← hBkd, ← hGk1d, ← hrd] at h
              exact hleg' s h
            · have hs2 : s = .call (k+2) Finset.univ false := by simpa [stageWord] using! h
              subst hs2
              show (k+2:ℕ) < m + 1
              omega
          have hBv2 : normVec (clockState U (nestedWord E bad ω rs (k+1) ++ stageWord (k+2)) ω) = 1 :=
            normVec_clockState_eq_one U _ ω hUslots hB2 hnorm
          have hale2 : preAmplitude E bad ω U rs (k+1) ≤ 1 := by
            have h := normVec_mul_proj_le (potential (E (k+2)) bad) (hpotE (k+2) (by omega))
              (clockState U (nestedWord E bad ω rs (k+1) ++ stageWord (k+2)) ω)
            rw [hBv2] at h
            simpa [preAmplitude] using! h
          refine ⟨hale2, ?_⟩
          obtain ⟨_, hmain2, hmin2⟩ := htunj (k+1) hk2
          exact schedule_bound (rs (k+2)) (preAmplitude E bad ω U rs (k+1))
            (Real.sqrt (α (k+2))) (α (k+2)) (norm_nonneg _) hale2 (htunj (k+1) hk2).1
            (hall ⟨k+1, hk2⟩) rfl hmain2 hmin2

    have hper : ∀ j : Fin m, 0 < preAmplitude E bad ω U rs j.val ∧
        (2 * (rs (j.val+1) : ℝ) + 1) * preAmplitude E bad ω U rs j.val ≤ 1 ∧
        rs (j.val+1) = Nat.ceil
          (Real.sqrt (α (j.val+1)) / (6 * preAmplitude E bad ω U rs j.val) - 1/2) := by
      intro j
      have hjlt : j.val < m := j.isLt
      obtain ⟨c, hcpos, _, hidj, hbndj⟩ := hcore j.val (by omega)
      obtain ⟨hale, hF2⟩ := hbndj hjlt
      have hmain := (htunj j.val hjlt).2.1
      have hmin := (htunj j.val hjlt).2.2
      have hα0 : 0 ≤ α (j.val+1) := (htunj j.val hjlt).1
      have hpos : 0 < preAmplitude E bad ω U rs j.val := by
        have hGj1 := hpot_absorb j.val hjlt
        have hcommj := hcommE j.val hjlt
        have hsplit : potential (E (j.val+1)) bad *ᵥ
            clockState U (nestedWord E bad ω rs j.val ++ stageWord (j.val+1)) ω
            = (c : ℂ) • (potential (E (j.val+1)) bad *ᵥ clockState U (plainPrefix (j.val+1)) ω) := by
          rw [clockState_append_call]
          have hsh := hshift j.val hjlt c
            (clockState U (nestedWord E bad ω rs j.val) ω) (clockState U (plainPrefix j.val) ω) hidj
          rw [hsh]
          have hplain : clockState U (plainPrefix (j.val+1)) ω
              = U (j.val+1) *ᵥ clockState U (plainPrefix j.val) ω := by
            rw [plainPrefix_succ]
            exact clockState_append_call U _ (j.val+1) ω
          rw [hplain]
        have hnorms : normVec (potential (E (j.val+1)) bad *ᵥ
            clockState U (nestedWord E bad ω rs j.val ++ stageWord (j.val+1)) ω)
            = c * plainAmplitude E bad U ω (j.val+1) := by
          rw [hsplit, normVec_smul_real, abs_of_pos hcpos]
          rfl
        have hplainpos := hplain_pos j
        have hceq : preAmplitude E bad ω U rs j.val
            = normVec (potential (E (j.val+1)) bad *ᵥ
              clockState U (nestedWord E bad ω rs j.val ++ stageWord (j.val+1)) ω) := rfl
        rw [hceq, hnorms]
        exact mul_pos hcpos hplainpos
      have hceil := schedule_ceil (rs (j.val+1)) (preAmplitude E bad ω U rs j.val)
        (Real.sqrt (α (j.val+1))) (α (j.val+1)) hpos hα0 rfl hmain hmin
      exact ⟨hpos, hF2, hceil⟩

    have hloss : ∀ j : Fin m,
        (5/6 : ℝ) ^ α (j.val+1) ≤ gainLoss (2 * rs (j.val+1) + 1) (preAmplitude E bad ω U rs j.val) := by
      intro j
      have hjlt : j.val < m := j.isLt
      obtain ⟨hpos, hF2, _⟩ := hper j
      have hmain := (htunj j.val hjlt).2.1
      have hmin := (htunj j.val hjlt).2.2
      have hα0 : 0 ≤ α (j.val+1) := (htunj j.val hjlt).1
      have hα1 : α (j.val+1) ≤ 1 := hall ⟨j, hjlt⟩
      have ha : 0 ≤ preAmplitude E bad ω U rs j.val := le_of_lt hpos
      by_cases hr0 : rs (j.val+1) = 0
      · have hgl : gainLoss 1 (preAmplitude E bad ω U rs j.val) = 1 := by
          unfold gainLoss
          split_ifs with ha0
          · rfl
          · have ha1 : preAmplitude E bad ω U rs j.val ≤ 1 := by
              have := hF2
              rw [hr0] at this
              push_cast at this
              linarith
            push_cast
            rw [one_mul, one_mul, Real.sin_arcsin (by linarith) ha1]
            have hne : preAmplitude E bad ω U rs j.val ≠ 0 := ha0
            field_simp
        have hgl' : gainLoss (2 * rs (j.val+1) + 1) (preAmplitude E bad ω U rs j.val) = 1 := by
          rw [hr0]; push_cast; exact hgl
        rw [hgl']
        exact Real.rpow_le_one (by norm_num) (by norm_num) hα0
      · have hr1 : 1 ≤ rs (j.val+1) := by omega
        have hgl : gainLoss (2 * rs (j.val+1) + 1) (preAmplitude E bad ω U rs j.val)
            = Real.sin (((2 * rs (j.val+1) + 1 : ℕ) : ℝ) * Real.arcsin
                (preAmplitude E bad ω U rs j.val)) /
              (((2 * rs (j.val+1) + 1 : ℕ) : ℝ) * preAmplitude E bad ω U rs j.val) := by
          unfold gainLoss
          rw [if_neg (by positivity : preAmplitude E bad ω U rs j.val ≠ 0)]
        rw [hgl]
        set θ := Real.arcsin (preAmplitude E bad ω U rs j.val) with hθ
        have hsinθ : Real.sin θ = preAmplitude E bad ω U rs j.val := by
          rw [hθ]
          exact Real.sin_arcsin (by linarith) (by
            have := hF2
            have hρ1 : (1:ℝ) ≤ ((2 * rs (j.val+1) + 1 : ℕ) : ℝ) :=
              by exact_mod_cast (by omega : 1 ≤ 2 * rs (j.val+1) + 1)
            nlinarith [le_mul_of_one_le_left ha hρ1])
        have hθ0 : 0 ≤ θ := by
          rw [hθ]
          exact Real.arcsin_nonneg.mpr ha
        have hθpos : θ ≠ 0 := by
          intro habs
          have : Real.sin θ = 0 := by rw [habs]; exact Real.sin_zero
          rw [hsinθ] at this
          exact ne_of_gt hpos this
        have hF2c : ((2 * rs (j.val+1) + 1 : ℕ) : ℝ) * preAmplitude E bad ω U rs j.val ≤ 1 := by
          rwa [← hcast21 (rs (j.val+1))]
        have hθle : ((2 * rs (j.val+1) + 1 : ℕ) : ℝ) * θ ≤ Real.pi / 2 := by
          rw [hθ]
          exact mul_arcsin_le_pi_div_two (2 * rs (j.val+1) + 1)
            (preAmplitude E bad ω U rs j.val) (by omega) ha hF2c
        have hg7 := Clause7TightDirichletBounds_answer.1 (2 * rs (j.val+1) + 1) θ
          (by omega) hθ0 hθle
        (try dsimp only at hg7)
        rw [if_neg hθpos] at hg7
        have hlo := hg7.1
        rw [hsinθ] at hlo
        have hρa' : (2 * (rs (j.val+1) : ℝ) + 1) ^ 2
            * (preAmplitude E bad ω U rs j.val) ^ 2 < α (j.val+1) :=
          schedule_sq_lt (rs (j.val+1)) (preAmplitude E bad ω U rs j.val)
            (Real.sqrt (α (j.val+1))) (α (j.val+1)) ha hα0 hr1 rfl hmin
        have hρa : ((2 * rs (j.val+1) + 1 : ℕ) : ℝ) ^ 2
            * (preAmplitude E bad ω U rs j.val) ^ 2 < α (j.val+1) := by
          rw [← hcast21 (rs (j.val+1))]
          exact hρa'
        have hchord := rpow_five_six_le (α (j.val+1)) hα0 hα1
        have hlo' : 1 - ((2 * rs (j.val+1) + 1 : ℕ) : ℝ) ^ 2
            * (preAmplitude E bad ω U rs j.val) ^ 2 / 6 ≤
            Real.sin (((2 * rs (j.val+1) + 1 : ℕ) : ℝ) * Real.arcsin
              (preAmplitude E bad ω U rs j.val)) /
            (((2 * rs (j.val+1) + 1 : ℕ) : ℝ) * preAmplitude E bad ω U rs j.val) := by
          rw [hθ] at hlo
          exact hlo
        nlinarith [hlo', hρa, hchord]

    refine ⟨?_, ?_⟩
    · intro j
      exact hper j
    · have hprod : (∏ j : Fin m, (5/6 : ℝ) ^ α (j.val+1))
          = (5/6 : ℝ) ^ ∑ j : Fin m, α (j.val+1) := prod_rpow _ (by norm_num) _
      have hle := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin m)))
        (fun j _ => Real.rpow_nonneg (by norm_num) _) (fun j _ => hloss j)
      have hprod2 : (∏ j : Fin m, (5/6 : ℝ) ^ α (j.val+1))
          = (5/6 : ℝ).rpow (∑ j : Fin m, α (j.val+1)) := hprod
      rw [← hprod2]
      exact hle
  · intro hrev
    have ha_pos : ∀ j : Fin m, 0 < preAmplitude E bad ω U rs j.val := fun j => (hrev j).1
    have ha_le : ∀ j : Fin m,
        preAmplitude E bad ω U rs j.val ≤ 1 / (3 * (2 * (rs (j.val+1) : ℝ) + 1)) :=
      fun j => (hrev j).2

    have hR1 : tunable m E bad U ω (reverseThreshold E bad U ω rs) rs := by
      refine ⟨?_, ?_⟩
      · unfold reverseThreshold
        simp
      · intro j hj
        have hpos := ha_pos ⟨j, hj⟩
        have hle := ha_le ⟨j, hj⟩
        have hne : (j+1 : ℕ) ≠ 0 := by omega
        have hρpos : (0:ℝ) < (2 * (rs (j+1) : ℝ) + 1) := by
          have : (0:ℕ) < 2 * rs (j+1) + 1 := by omega
          exact_mod_cast this
        refine ⟨?_, ?_, ?_⟩
        · unfold reverseThreshold
          rw [if_neg hne]
          split_ifs
          · norm_num
          · nlinarith [sq_nonneg (2 * (rs (j+1) : ℝ) + 1),
              sq_nonneg (preAmplitude E bad ω U rs (j + 1 - 1))]
        · unfold reverseThreshold
          rw [if_neg hne]
          split_ifs with hr0
          · rw [hr0]
            push_cast
            simp
            nlinarith [hpos]
          · rw [Nat.add_sub_cancel, ← hcast21 (rs (j+1))]
            have hsq : (9 : ℝ) * (2 * (rs (j+1) : ℝ) + 1) ^ 2
                * (preAmplitude E bad ω U rs j) ^ 2
                = (3 * (2 * (rs (j+1) : ℝ) + 1) * preAmplitude E bad ω U rs j) ^ 2 := by ring
            rw [hsq]
            have hnn : 0 ≤ 3 * (2 * (rs (j+1) : ℝ) + 1) * preAmplitude E bad ω U rs j := by
              positivity
            rw [Real.sqrt_sq hnn]
            have h3 : 3 * (2 * (rs (j+1) : ℝ) + 1) * preAmplitude E bad ω U rs j / 3
                = (2 * (rs (j+1) : ℝ) + 1) * preAmplitude E bad ω U rs j := by
              field_simp
            rw [h3]
        · intro s hs
          unfold reverseThreshold
          rw [if_neg hne]
          split_ifs with hr0
          · omega
          · rw [Nat.add_sub_cancel, ← hcast21 (rs (j+1))]
            have hsq : (9 : ℝ) * (2 * (rs (j+1) : ℝ) + 1) ^ 2
                * (preAmplitude E bad ω U rs j) ^ 2
                = (3 * (2 * (rs (j+1) : ℝ) + 1) * preAmplitude E bad ω U rs j) ^ 2 := by ring
            rw [hsq]
            have hnn : 0 ≤ 3 * (2 * (rs (j+1) : ℝ) + 1) * preAmplitude E bad ω U rs j := by
              positivity
            rw [Real.sqrt_sq hnn]
            have hcmp : (2 * s + 1 : ℕ) < 2 * rs (j+1) + 1 := by omega
            have hcmp' : (2 * (s : ℝ) + 1) < (2 * (rs (j+1) : ℝ) + 1) := by
              exact_mod_cast hcmp
            have h3 : 3 * (2 * (rs (j+1) : ℝ) + 1) * preAmplitude E bad ω U rs j / 3
                = (2 * (rs (j+1) : ℝ) + 1) * preAmplitude E bad ω U rs j := by
              field_simp
            rw [h3]
            exact mul_lt_mul_of_pos_right hcmp' hpos

    have hR2 : ∀ j : Fin m, reverseThreshold E bad U ω rs (j.val+1) ≤ 1 := by
      intro j
      have hne : (j.val+1 : ℕ) ≠ 0 := by omega
      have hle := ha_le j
      have hρpos : (0:ℝ) < (2 * (rs (j.val+1) : ℝ) + 1) := by
        have : (0:ℕ) < 2 * rs (j.val+1) + 1 := by omega
        exact_mod_cast this
      unfold reverseThreshold
      rw [if_neg hne]
      split_ifs with hr0
      · norm_num
      · rw [Nat.add_sub_cancel, ← hcast21 (rs (j.val+1))]
        have hle' : (2 * (rs (j.val+1) : ℝ) + 1) * preAmplitude E bad ω U rs j.val ≤ 1 / 3 := by
          have := hle
          rw [le_div_iff₀ (by positivity : (0:ℝ) < 3 * (2 * (rs (j.val+1) : ℝ) + 1))] at this
          have hk : 3 * (preAmplitude E bad ω U rs j.val * (2 * (rs (j.val+1) : ℝ) + 1))
              = preAmplitude E bad ω U rs j.val * (3 * (2 * (rs (j.val+1) : ℝ) + 1)) := by ring
          nlinarith [hk]
        have hs : ((2 * (rs (j.val+1) : ℝ) + 1) * preAmplitude E bad ω U rs j.val) ^ 2
            ≤ (1 / 3) ^ 2 := by
          have := mul_self_le_mul_self (by nlinarith [ha_pos j, hρpos]) hle'
          simpa [pow_two] using! this
        have hgoaleq : (9 : ℝ) * (2 * (rs (j.val+1) : ℝ) + 1) ^ 2
            * (preAmplitude E bad ω U rs j.val) ^ 2
            = 9 * (((2 * (rs (j.val+1) : ℝ) + 1) * preAmplitude E bad ω U rs j.val) ^ 2) := by ring
        rw [hgoaleq]
        nlinarith

    have hR3 : (4*Real.pi-8)/(9*Real.pi^3) *
        (∑ j : Fin m, reverseThreshold E bad U ω rs (j.val+1)) ≤
        -Real.log (totalLoss m E bad U ω rs) := by
      have hper : ∀ j : Fin m, (4*Real.pi-8)/(9*Real.pi^3) *
          reverseThreshold E bad U ω rs (j.val+1) ≤
          -Real.log (gainLoss (2 * rs (j.val+1) + 1) (preAmplitude E bad ω U rs j.val)) := by
        intro j
        have hpos := ha_pos j
        have hle := ha_le j
        have hne : (j.val+1 : ℕ) ≠ 0 := by omega
        have hρpos : (0:ℝ) < (2 * (rs (j.val+1) : ℝ) + 1) := by
          have : (0:ℕ) < 2 * rs (j.val+1) + 1 := by omega
          exact_mod_cast this
        by_cases hr0 : rs (j.val+1) = 0
        · have hgl : gainLoss (2 * rs (j.val+1) + 1) (preAmplitude E bad ω U rs j.val) = 1 := by
            rw [hr0]
            push_cast
            unfold gainLoss
            split_ifs with ha0
            · rfl
            · have ha1 : preAmplitude E bad ω U rs j.val ≤ 1 := by
                rw [hr0] at hle
                push_cast at hle
                linarith
              push_cast
              rw [one_mul, one_mul, Real.sin_arcsin (by linarith) ha1]
              have hne' : preAmplitude E bad ω U rs j.val ≠ 0 := ha0
              field_simp
          have hβ : reverseThreshold E bad U ω rs (j.val+1) = 0 := by
            unfold reverseThreshold
            rw [if_neg hne, if_pos hr0]
          rw [hβ, hgl, Real.log_one]
          norm_num
        · have hr1 : 1 ≤ rs (j.val+1) := by omega
          have hβ : reverseThreshold E bad U ω rs (j.val+1)
              = 9 * (2 * (rs (j.val+1) : ℝ) + 1) ^ 2
                  * (preAmplitude E bad ω U rs j.val) ^ 2 := by
            unfold reverseThreshold
            rw [if_neg hne, if_neg hr0]
            rw [Nat.add_sub_cancel, ← hcast21 (rs (j.val+1))]
          have hgl : gainLoss (2 * rs (j.val+1) + 1) (preAmplitude E bad ω U rs j.val)
              = Real.sin (((2 * rs (j.val+1) + 1 : ℕ) : ℝ) * Real.arcsin
                  (preAmplitude E bad ω U rs j.val)) /
                (((2 * rs (j.val+1) + 1 : ℕ) : ℝ) * preAmplitude E bad ω U rs j.val) := by
            unfold gainLoss
            rw [if_neg (by positivity : preAmplitude E bad ω U rs j.val ≠ 0)]
          set θ := Real.arcsin (preAmplitude E bad ω U rs j.val) with hθ
          have hsinθ : Real.sin θ = preAmplitude E bad ω U rs j.val := by
            rw [hθ]
            exact Real.sin_arcsin (by nlinarith [le_of_lt hpos]) (by
              have h3 : (1:ℝ) / (3 * (2 * (rs (j.val+1) : ℝ) + 1)) ≤ 1 / 3 := by
                rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 3 * (2 * (rs (j.val+1) : ℝ) + 1))
                  (by norm_num : (0:ℝ) < 3)]
                nlinarith
              linarith)
          have hθ0 : 0 ≤ θ := by rw [hθ]; exact Real.arcsin_nonneg.mpr (le_of_lt hpos)
          have hθpos : θ ≠ 0 := by
            intro habs
            have : Real.sin θ = 0 := by rw [habs]; exact Real.sin_zero
            rw [hsinθ] at this
            exact ne_of_gt hpos this
          have hF2c : ((2 * rs (j.val+1) + 1 : ℕ) : ℝ) * preAmplitude E bad ω U rs j.val ≤ 1 / 3 := by
            have hρ : (0:ℝ) < (2 * (rs (j.val+1) : ℝ) + 1) := hρpos
            have h3 : (1:ℝ) / (3 * (2 * (rs (j.val+1) : ℝ) + 1)) * (2 * (rs (j.val+1) : ℝ) + 1)
                = 1 / 3 := by
              field_simp
            have hmul : preAmplitude E bad ω U rs j.val * (3 * (2 * (rs (j.val+1) : ℝ) + 1)) ≤ 1 := by
              have := hle
              rw [le_div_iff₀ (by positivity : (0:ℝ) < 3 * (2 * (rs (j.val+1) : ℝ) + 1))] at this
              exact this
            have hF2c' : preAmplitude E bad ω U rs j.val * (2 * (rs (j.val+1) : ℝ) + 1) ≤ 1 / 3 := by
              have hk : 3 * (preAmplitude E bad ω U rs j.val * (2 * (rs (j.val+1) : ℝ) + 1))
                  = preAmplitude E bad ω U rs j.val * (3 * (2 * (rs (j.val+1) : ℝ) + 1)) := by ring
              nlinarith [hk, hmul]
            rwa [← hcast21 (rs (j.val+1)), mul_comm]
          have hθle : ((2 * rs (j.val+1) + 1 : ℕ) : ℝ) * θ ≤ Real.pi / 2 := by
            rw [hθ]
            exact mul_arcsin_le_pi_div_two (2 * rs (j.val+1) + 1)
              (preAmplitude E bad ω U rs j.val) (by omega) (le_of_lt hpos) (by nlinarith)
          have hg7 := Clause7TightDirichletBounds_answer.1 (2 * rs (j.val+1) + 1) θ
            (by omega) hθ0 hθle
          (try dsimp only at hg7)
          rw [if_neg hθpos] at hg7
          have hup := hg7.2
          rw [hsinθ] at hup
          have hglθ : gainLoss (2 * rs (j.val+1) + 1) (preAmplitude E bad ω U rs j.val)
              = Real.sin (((2 * rs (j.val+1) + 1 : ℕ) : ℝ) * θ) /
                (((2 * rs (j.val+1) + 1 : ℕ) : ℝ) * Real.sin θ) := by
            rw [hgl, hθ, hsinθ]
          rw [hβ]
          have hc : (4*Real.pi-8)/(9*Real.pi^3) *
              (9 * (2 * (rs (j.val+1) : ℝ) + 1) ^ 2 * (preAmplitude E bad ω U rs j.val) ^ 2)
              = ((4*Real.pi-8)/Real.pi^3) * (2 * (rs (j.val+1) : ℝ) + 1) ^ 2
                  * (preAmplitude E bad ω U rs j.val) ^ 2 := by
            have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
            field_simp
          rw [hc]
          set u : ℝ := ((4*Real.pi-8)/Real.pi^3) * (2 * (rs (j.val+1) : ℝ) + 1) ^ 2
              * (preAmplitude E bad ω U rs j.val) ^ 2 with hu
          have hcpos : 0 < (4*Real.pi-8)/Real.pi^3 := by
            have hpi3 : 0 < Real.pi ^ 3 := by positivity
            have h4 : (0:ℝ) < 4 * Real.pi - 8 := by
              nlinarith [Real.pi_gt_three]
            exact div_pos h4 hpi3
          have hu0 : 0 ≤ u := by
            rw [hu]
            exact mul_nonneg (mul_nonneg (le_of_lt hcpos) (sq_nonneg _)) (sq_nonneg _)
          have hu1 : u < 1 := by
            rw [hu]
            have hle2 : (2 * (rs (j.val+1) : ℝ) + 1) ^ 2
                * (preAmplitude E bad ω U rs j.val) ^ 2 ≤ 1 / 9 := by
              have h := hF2c
              have hs : ((2 * (rs (j.val+1) : ℝ) + 1) * preAmplitude E bad ω U rs j.val) ^ 2
                  ≤ (1 / 3) ^ 2 := by
                have := mul_self_le_mul_self (by nlinarith [hpos, hρpos]) h
                simpa [pow_two] using! this
              nlinarith
            have hnonneg : (0:ℝ) ≤ (2 * (rs (j.val+1) : ℝ) + 1) ^ 2
                * (preAmplitude E bad ω U rs j.val) ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
            have h4 : (0:ℝ) < 4 * Real.pi - 8 := by nlinarith [Real.pi_gt_three]
            have hcu : ((4*Real.pi-8)/Real.pi^3) * (1 / 9) < 1 := by
              have h4' : 4 * Real.pi - 8 < 8 := by nlinarith [Real.pi_lt_four]
              have hpi3 : (1:ℝ) ≤ Real.pi ^ 3 := by
                have h3 : (3:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
                have hpos : (0:ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
                have hp2 : (3 * 3 : ℝ) ≤ Real.pi * Real.pi := mul_le_mul h3 h3 (by norm_num) hpos
                have hp2n : (0:ℝ) ≤ Real.pi * Real.pi := mul_nonneg hpos hpos
                have hp3 : (3 * 3 * 3 : ℝ) ≤ Real.pi * Real.pi * Real.pi :=
                  mul_le_mul hp2 h3 (by norm_num) hp2n
                have e : Real.pi * Real.pi * Real.pi = Real.pi ^ 3 := by ring
                rw [e] at hp3
                nlinarith
              rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0:ℝ) < Real.pi ^ 3)]
              nlinarith [h4', hpi3]
            have hmul : ((4*Real.pi-8)/Real.pi^3)
                * ((2 * (rs (j.val+1) : ℝ) + 1) ^ 2 * (preAmplitude E bad ω U rs j.val) ^ 2)
                ≤ ((4*Real.pi-8)/Real.pi^3) * (1 / 9) :=
              mul_le_mul_of_nonneg_left hle2 (le_of_lt hcpos)
            nlinarith [hmul, hcu]
          have hgl' : gainLoss (2 * rs (j.val+1) + 1) (preAmplitude E bad ω U rs j.val) ≤ 1 - u := by
            rw [hglθ, hsinθ]
            have hmatch : ((4 * Real.pi - 8) / Real.pi ^ 3)
                * (((2 * rs (j.val+1) + 1 : ℕ) : ℝ)) ^ 2
                  * (preAmplitude E bad ω U rs j.val) ^ 2 = u := by
              rw [hu, ← hcast21 (rs (j.val+1))]
            rw [← hmatch]
            exact hup
          have hlog : u ≤ -Real.log (1 - u) := neg_log_one_sub_le u hu0 hu1
          have h2 : 0 < gainLoss (2 * rs (j.val+1) + 1) (preAmplitude E bad ω U rs j.val) := by
            rw [hglθ]
            have hnum : 0 < Real.sin (((2 * rs (j.val+1) + 1 : ℕ) : ℝ) * θ) := by
              have hposθ : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθpos)
              have hlt : ((2 * rs (j.val+1) + 1 : ℕ) : ℝ) * θ < Real.pi := by
                linarith [Real.pi_pos]
              exact Real.sin_pos_of_pos_of_lt_pi (by positivity) hlt
            exact div_pos hnum (mul_pos (by
              exact_mod_cast (by omega : 0 < 2 * rs (j.val+1) + 1)) (by nlinarith [hsinθ]))
          have h1 : 0 < 1 - u := by linarith
          have hmono := (Real.log_le_log_iff h2 h1).mpr hgl'
          linarith
      have hsum : (4*Real.pi-8)/(9*Real.pi^3) *
          (∑ j : Fin m, reverseThreshold E bad U ω rs (j.val+1))
          = ∑ j : Fin m, ((4*Real.pi-8)/(9*Real.pi^3) * reverseThreshold E bad U ω rs (j.val+1)) := by
        rw [Finset.mul_sum]
      rw [hsum]
      have hsum2 : (∑ j : Fin m, -Real.log
          (gainLoss (2 * rs (j.val+1) + 1) (preAmplitude E bad ω U rs j.val)))
          = -Real.log (∏ j : Fin m, gainLoss (2 * rs (j.val+1) + 1)
            (preAmplitude E bad ω U rs j.val)) := by
        have hprodlog : Real.log (∏ j : Fin m, gainLoss (2 * rs (j.val+1) + 1)
            (preAmplitude E bad ω U rs j.val))
            = ∑ j : Fin m, Real.log (gainLoss (2 * rs (j.val+1) + 1)
              (preAmplitude E bad ω U rs j.val)) := by
          apply Real.log_prod
          intro j _
          have hpos := ha_pos j
          have hne : preAmplitude E bad ω U rs j.val ≠ 0 := by positivity
          by_cases hr0 : rs (j.val+1) = 0
          · rw [hr0]
            push_cast
            unfold gainLoss
            split_ifs with ha0
            · exact one_ne_zero
            · have ha : (0:ℝ) < preAmplitude E bad ω U rs j.val := by
                have h0' : 0 ≤ normVec (potential (E (j.val+1)) bad *ᵥ
                    clockState U (nestedWord E bad ω rs j.val ++ stageWord (j.val+1)) ω) :=
                  norm_nonneg _
                simpa [preAmplitude] using!
                    lt_of_le_of_ne h0' (Ne.symm (by simpa [preAmplitude] using! ha0))
              have ha1 : preAmplitude E bad ω U rs j.val ≤ 1 := by
                have := ha_le j
                rw [le_div_iff₀ (by positivity : (0:ℝ) < 3 * (2 * (rs (j.val+1) : ℝ) + 1))] at this
                nlinarith
              push_cast
              rw [one_mul, one_mul, Real.sin_arcsin (by linarith) ha1]
              have hne2 : preAmplitude E bad ω U rs j.val ≠ 0 := by positivity
              rw [div_self hne2]
              exact one_ne_zero
          · unfold gainLoss
            rw [if_neg hne]
            have hρpos : (0:ℝ) < ((2 * rs (j.val+1) + 1 : ℕ) : ℝ) :=
              Nat.cast_pos.mpr (by omega : 0 < 2 * rs (j.val+1) + 1)
            exact div_ne_zero (by
              intro habs
              have hθ : Real.sin (((2 * rs (j.val+1) + 1 : ℕ) : ℝ) * Real.arcsin
                  (preAmplitude E bad ω U rs j.val)) = 0 := habs
              have hF2c : ((2 * rs (j.val+1) + 1 : ℕ) : ℝ) * preAmplitude E bad ω U rs j.val ≤ 1 / 3 := by
                have hρ : (0:ℝ) < (2 * (rs (j.val+1) : ℝ) + 1) := by
                  have : (0:ℕ) < 2 * rs (j.val+1) + 1 := by omega
                  exact_mod_cast this
                have h3 : (1:ℝ) / (3 * (2 * (rs (j.val+1) : ℝ) + 1)) * (2 * (rs (j.val+1) : ℝ) + 1)
                    = 1 / 3 := by
                  field_simp
                have hmul : preAmplitude E bad ω U rs j.val * (3 * (2 * (rs (j.val+1) : ℝ) + 1)) ≤ 1 := by
                  have := ha_le j
                  rw [le_div_iff₀ (by positivity : (0:ℝ) < 3 * (2 * (rs (j.val+1) : ℝ) + 1))] at this
                  exact this
                have hF2c' : preAmplitude E bad ω U rs j.val * (2 * (rs (j.val+1) : ℝ) + 1) ≤ 1 / 3 := by
                  have hk : 3 * (preAmplitude E bad ω U rs j.val * (2 * (rs (j.val+1) : ℝ) + 1))
                      = preAmplitude E bad ω U rs j.val * (3 * (2 * (rs (j.val+1) : ℝ) + 1)) := by ring
                  nlinarith [hk, hmul]
                rwa [← hcast21 (rs (j.val+1)), mul_comm]
              have hangle := mul_arcsin_le_pi_div_two (2 * rs (j.val+1) + 1)
                (preAmplitude E bad ω U rs j.val) (by omega) (le_of_lt hpos)
                (by nlinarith [hF2c])
              have hposθ : 0 < Real.arcsin (preAmplitude E bad ω U rs j.val) :=
                Real.arcsin_pos.mpr hpos
              have hlt : ((2 * rs (j.val+1) + 1 : ℕ) : ℝ) * Real.arcsin
                  (preAmplitude E bad ω U rs j.val) < Real.pi := by linarith [Real.pi_pos]
              have hsinpos : 0 < Real.sin (((2 * rs (j.val+1) + 1 : ℕ) : ℝ) * Real.arcsin
                  (preAmplitude E bad ω U rs j.val)) :=
                Real.sin_pos_of_pos_of_lt_pi
                  (mul_pos (by exact_mod_cast (by omega : 0 < 2 * rs (j.val+1) + 1))
                    (Real.arcsin_pos.mpr hpos)) hlt
              exact ne_of_gt hsinpos hθ) (by
              exact mul_ne_zero (by
                exact_mod_cast (by omega : (2 * rs (j.val+1) + 1 : ℕ) ≠ 0)) hne)
        rw [Finset.sum_neg_distrib, hprodlog]
      have hle :=
          Finset.sum_le_sum (fun j _ => hper j : ∀ j ∈ (Finset.univ : Finset (Fin m)), _ ≤ _)
      rw [hsum2] at hle
      exact hle
    exact ⟨hR1, hR2, hR3⟩

end Qatlib.Concepts.QlsReadoutSpec.Amplification
