/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.TunableActualQueryComplexityStat
import Qatlib.Concepts.QlsReadoutSpec.ProgramModel.PaidWordSemanticsLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.ProjectorOrderLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.ClockFlagResolutionsLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.ActualNestedAmplificationLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.TightDirichletBoundsLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.TunableUniversalityLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.AmplificationProductsLows

/-!
# Actual query complexity of tunable amplification

This module proves `TunableQueryTunableActualQueryComplexity_answer` for legal tunable nested
words with a positive final plain amplitude and bounded total threshold budget. The result
bounds slot-zero calls, the number of stages with positive round counts, and weighted oracle
cost grouped between increasing markers at amplified stages. The proof expands the exact cost
recurrence and controls gain losses and suffix products.

The estimates formalize cost accounting for variable-time amplitude amplification
[Ambainis2012]. For tunable VTAA query complexity, see [LowSu2026].

## Main statements

* `TunableQueryTunableActualQueryComplexity_answer`: Establishes legality, call-count bounds,
  and the grouped weighted-cost estimate.

## References

* [Ambainis, 2012][Ambainis2012]
* [Low and Su, 2026][LowSu2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QlsReadoutSpec.ProgramModel

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QlsReadoutSpec.Amplification

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Concepts.QlsReadoutSpec.Amplification

open Matrix Qatlib.Concepts.QlsReadoutSpec.Amplification
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The extended clock agrees with the finite clock at every index at most `m`. -/
private theorem extendClock_eq {H : Type} (m : ℕ) (P : Fin (m+1) → Matrix H H ℂ)
    {k : ℕ} (hk : k ≤ m) : extendClock m P k = P ⟨k, by omega⟩ := by
  unfold extendClock
  exact dif_pos hk

/-- A stage word is legal when its oracle index is less than `m + 1`. -/
private theorem legal_stageWord {H : Type} [Fintype H] [DecidableEq H] (m k : ℕ)
    (hk : k < m+1) : legal (m+1) (stageWord (H := H) k) := by
  unfold legal
  intro s hs
  simp only [stageWord, List.mem_singleton] at hs
  subst hs
  exact hk

/-- Concatenation is legal exactly when both constituent words are legal. -/
private theorem legal_append_iff {H : Type} [Fintype H] [DecidableEq H] {slots : ℕ}
    (C D : Word H 1) : legal slots (C ++ D) ↔ legal slots C ∧ legal slots D := by
  constructor
  · intro h
    refine ⟨fun s hs => h s ?_, fun s hs => h s ?_⟩
    · exact List.mem_append_left _ hs
    · exact List.mem_append_right _ hs
  · intro h s hs
    rw [List.mem_append] at hs
    rcases hs with hs | hs
    · exact h.1 s hs
    · exact h.2 s hs

/-- A stage word makes one call to its own slot and no calls to any other slot. -/
private theorem calls_stageWord {H : Type} (k slot : ℕ) :
    calls (stageWord (H := H) k) slot = if k = slot then 1 else 0 := by
  simp [calls, stageWord]

/-- A stage word with nonzero slot makes no calls to slot zero. -/
private theorem calls_stageWord_zero {H : Type} (k : ℕ) (hk : k ≠ 0) :
    calls (stageWord (H := H) k) 0 = 0 := by
  rw [calls_stageWord, if_neg hk]

/-- The weighted cost of concatenation is the sum of the constituent weighted costs. -/
private theorem weightedCost_append {H : Type} (prices : ℕ → ℕ) (C D : Word H 1) :
    weightedCost prices (C ++ D) = weightedCost prices C + weightedCost prices D := by
  show ((C ++ D).map _).sum = (C.map _).sum + (D.map _).sum
  rw [List.map_append, List.sum_append]

/-- The weighted cost of a stage word equals its slot price. -/
private theorem weightedCost_stageWord {H : Type} (prices : ℕ → ℕ) (k : ℕ) :
    weightedCost prices (stageWord (H := H) k) = prices k := by
  simp [weightedCost, stageWord]

/-- The initial plain prefix is the stage-zero word. -/
private theorem plainPrefix_zero {H : Type} :
    plainPrefix (H := H) 0 = stageWord 0 := by
  show (List.range 1).map _ = _
  simp [stageWord]

/-- The next plain prefix appends the next stage word to the preceding prefix. -/
private theorem plainPrefix_succ {H : Type} (j : ℕ) :
    plainPrefix (H := H) (j+1) = plainPrefix j ++ stageWord (j+1) := by
  show (List.range (j+1+1)).map _ = (List.range (j+1)).map _ ++ _
  rw [List.range_succ, List.map_append, List.map_singleton]
  rfl

/-- The clock state is the zero-clock slice of the word matrix applied to the clean input. -/
private theorem clockState_eq_run {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (C : Word H 1) (ω : QState H) :
    clockState U C ω = fun h => (wordMatrix U C *ᵥ clean 1 (Nat.zero_lt_one) ω) (h, (0 : Fin 1)) :=
  rfl

/-- On the unique clock sector, a fully controlled matrix acts on the data slice as the
underlying matrix. -/
private theorem controlled_univ_mulVec_clock {H : Type} [Fintype H] [DecidableEq H]
    (V : Matrix H H ℂ) (Ψ : QState (Space H 1)) (h : H) :
    (controlled V Finset.univ *ᵥ Ψ) (h, (0 : Fin 1)) = (V *ᵥ (fun h' => Ψ (h', 0))) h := by
  show (∑ p : H × Fin 1, controlled V Finset.univ (h, 0) p * Ψ p) = _
  rw [Fintype.sum_prod_type]
  have hinner : ∀ h' : H,
      (∑ k : Fin 1, controlled V Finset.univ (h, 0) (h', k) * Ψ (h', k))
        = V h h' * Ψ (h', 0) := by
    intro h'
    rw [Fin.sum_univ_one]
    show (if (0 : Fin 1) = 0 then (if (0 : Fin 1) ∈ Finset.univ then V h h'
      else if h = h' then (1 : ℂ) else 0) else 0) * Ψ (h', 0) = V h h' * Ψ (h', 0)
    simp
  rw [Finset.sum_congr rfl fun h' _ => hinner h']
  rfl

/-- The stage word's matrix is its oracle controlled on all clock values. -/
private theorem wordMatrix_stageWord {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (i : ℕ) :
    wordMatrix U (stageWord (H := H) i) = controlled (U i) Finset.univ := by
  simp [wordMatrix, stageWord]

/-- Appending a stage word applies its oracle to the current clock state. -/
private theorem clockState_append_stageWord {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (C : Word H 1) (i : ℕ) (ω : QState H) :
    clockState U (C ++ stageWord i) ω = U i *ᵥ clockState U C ω := by
  funext h
  rw [clockState_eq_run]
  have hrun : wordMatrix U (C ++ stageWord i)
      = controlled (U i) Finset.univ * wordMatrix U C := by
    rw [wordMatrix_append, wordMatrix_stageWord]
  rw [hrun, ← Matrix.mulVec_mulVec]
  exact controlled_univ_mulVec_clock (U i) (wordMatrix U C *ᵥ clean 1 (Nat.zero_lt_one) ω) h

/-- The actions of `G` and `1 - G` on a vector sum to that vector. -/
private theorem projector_decomp {H : Type} [Fintype H] [DecidableEq H]
    (G : Matrix H H ℂ) (ψ : QState H) :
    G *ᵥ ψ + (1 - G) *ᵥ ψ = ψ := by
  rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]

/-- Complex scalar multiplication scales `normVec` by the norm of the scalar. -/
private theorem normVec_smul {H : Type} [Fintype H] (c : ℂ) (v : QState H) :
    normVec (c • v) = ‖c‖ * normVec v := by
  show ‖toEuclidean_fromVec (c • v)‖ = ‖c‖ * ‖toEuclidean_fromVec v‖
  have h : toEuclidean_fromVec (c • v) = c • toEuclidean_fromVec v := rfl
  rw [h, norm_smul]

/-- Real scalar multiplication scales `normVec` by the absolute value of the scalar. -/
private theorem normVec_smul_real {H : Type} [Fintype H] (r : ℝ) (v : QState H) :
    normVec (((r : ℝ) : ℂ) • v) = |r| * normVec v := by
  rw [normVec_smul, Complex.norm_real, Real.norm_eq_abs]

/-- The vector norm is nonnegative. -/
private theorem normVec_nonneg {H : Type} [Fintype H] (v : QState H) :
    0 ≤ normVec v := norm_nonneg _

/-- The squared vector norm equals the sum of squared coordinate norms. -/
private theorem normVec_sq_eq {H : Type} [Fintype H] (v : QState H) :
    normVec v ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  show ‖toEuclidean_fromVec v‖ ^ 2 = _
  exact norm_toEuclidean_fromVec_sq v

/-- A vector has zero norm exactly when it is zero. -/
private theorem normVec_eq_zero_iff {H : Type} [Fintype H] (v : QState H) :
    normVec v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h2 : normVec v ^ 2 = ∑ i, ‖v i‖ ^ 2 := normVec_sq_eq v
    rw [h, zero_pow (by norm_num)] at h2
    have hi : ∀ i : H, ‖v i‖ ^ 2 = 0 :=
      fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (‖v j‖))).mp h2.symm i
        (Finset.mem_univ i)
    funext i
    exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp (hi i))
  · intro h
    subst h
    show ‖toEuclidean_fromVec (0 : QState H)‖ = 0
    simp [toEuclidean_fromVec]

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

/-- A legal word of unitary oracles sends a normalized seed to a clock state of norm one. -/
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
  have h2 : normVec (clockState U C ω) ^ 2 = ∑ i, ‖clockState U C ω i‖ ^ 2 :=
    normVec_sq_eq _
  rw [hkey, ← hsplit, hrun] at h2
  have hnn : 0 ≤ normVec (clockState U C ω) := norm_nonneg _
  nlinarith

/-- The complement of `potential Q bad` is `Q * bad`. -/
private theorem potential_one_sub {H : Type} [Fintype H] [DecidableEq H]
    (Q : Matrix H H ℂ) (bad : Matrix H H ℂ) :
    1 - potential Q bad = Q * bad := by
  show (1 : Matrix H H ℂ) - (1 - Q * bad) = Q * bad
  abel

/-- For legal clocks and stages, the next potential annihilates the evolved complement of the
current potential. -/
private theorem collapse {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) {j : ℕ} (hj : j < m) :
    potential (extendClock m P (j+1)) bad * U (j+1) *
      (1 - potential (extendClock m P j) bad) = 0 := by
  obtain ⟨hP, hP0, hPm, hpsd, hbad, hcomm⟩ := hclock
  obtain ⟨hUunit, hstagefix⟩ := hstage
  have g3 := Clause3ClockFlagResolutions_answer H m P bad ⟨hP, hP0, hPm, hpsd, hbad, hcomm⟩
  have hEj : extendClock m P j = P ⟨j, by omega⟩ := extendClock_eq m P (by omega)
  have hEj1 : extendClock m P (j+1) = P ⟨j+1, by omega⟩ := extendClock_eq m P (by omega)
  have hfix : U (j+1) * extendClock m P j = extendClock m P j := by
    have h := hstagefix (⟨j, by omega⟩ : Fin m)
    change U (j+1) * P ⟨j, by omega⟩ = P ⟨j, _⟩ at h
    rw [hEj]
    exact h
  have hcommE : bad * extendClock m P j = extendClock m P j * bad := by
    have h := hcomm ⟨j, by omega⟩
    rw [hEj]
    exact h.symm
  have hprodE : extendClock m P (j+1) * extendClock m P j = extendClock m P j := by
    have h := g3.1 ⟨j, by omega⟩ ⟨j+1, by omega⟩ (by show j ≤ j+1; omega)
    rw [hEj, hEj1]
    exact h.1
  have hbadid : bad * bad = bad := hbad.1
  have h3 : (extendClock m P (j+1) * bad) * (extendClock m P j * bad)
      = extendClock m P j * bad := by
    rw [mul_assoc, ← mul_assoc bad, hcommE, mul_assoc (extendClock m P j), hbadid,
      ← mul_assoc, hprodE]
  rw [potential_one_sub]
  rw [mul_assoc, ← mul_assoc (U (j+1)), hfix]
  rw [show potential (extendClock m P (j+1)) bad = 1 - extendClock m P (j+1) * bad from rfl]
  rw [sub_mul, one_mul, h3]
  abel

/-- For legal clocks and stages, evolving a vector from the current potential's complement and
applying the next potential gives zero. -/
private theorem collapse_apply {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) {j : ℕ} (hj : j < m)
    (v : QState H) :
    (potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ
      ((1 - potential (extendClock m P j) bad) *ᵥ v) = 0 := by
  rw [Matrix.mulVec_mulVec, collapse m P bad U hclock hstage hj, Matrix.zero_mulVec]

/-- For `x` in the unit interval, `Real.arcsin x ≤ (Real.pi / 2) * x`. -/
private theorem arcsin_le_pi_div_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.arcsin x ≤ (Real.pi / 2) * x := by
  have hmem : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, hx1⟩
  have hy : (Real.pi / 2) * x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    have hpi := Real.pi_pos
    refine ⟨?_, ?_⟩ <;> nlinarith
  have h := Real.arcsin_le_iff_le_sin hmem hy
  rw [h]
  exact Real.le_sin_mul hx0 hx1

/-- A tunable schedule with thresholds at most one keeps each amplified pre-amplitude angle at
most `Real.pi / 2`. -/
private theorem noOvershoot {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (htun : tunable m (extendClock m P) bad U ω α rs) (habove : ∀ j : Fin m, α (j.val+1) ≤ 1)
    {j : ℕ} (hj : j < m) :
    ((2*rs (j+1)+1 : ℕ) : ℝ) * Real.arcsin (preAmplitude (extendClock m P) bad ω U rs j)
      ≤ Real.pi / 2 := by
  set a := preAmplitude (extendClock m P) bad ω U rs j with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have hamin : ∀ s < rs (j+1), (2*s+1) * a < Real.sqrt (α (j+1))/3 := (htun.2 j hj).2.2
  have hnonneg : 0 ≤ α (j+1) := (htun.2 j hj).1
  have habovej : α (j+1) ≤ 1 := habove ⟨j, hj⟩
  have hsq : Real.sqrt (α (j+1)) ≤ 1 := Real.sqrt_le_one.mpr habovej
  have hsq3 : Real.sqrt (α (j+1))/3 ≤ 1/3 :=
    div_le_div_of_nonneg_right hsq (by norm_num)
  rcases Nat.eq_zero_or_pos (rs (j+1)) with hz | hpos
  · have : ((2*rs (j+1)+1 : ℕ) : ℝ) * Real.arcsin a = Real.arcsin a := by
      rw [hz]; norm_num
    rw [this]
    exact Real.arcsin_le_pi_div_two a
  · have hσ1 : (1:ℝ) ≤ ((2*rs (j+1)-1 : ℕ) : ℝ) := by
      have : (1:ℕ) ≤ 2*rs (j+1) - 1 := by omega
      exact_mod_cast this
    have hσa : ((2*rs (j+1)-1 : ℕ) : ℝ) * a < 1/3 := by
      have h := hamin (rs (j+1) - 1) (by omega)
      have hkey : (2 * ↑(rs (j+1) - 1) + 1 : ℝ) = ((2*rs (j+1)-1 : ℕ) : ℝ) := by
        have h2 : (2 * (rs (j+1) - 1) + 1 : ℕ) = 2 * rs (j+1) - 1 := by omega
        exact_mod_cast h2
      rw [hkey] at h
      exact lt_of_lt_of_le h hsq3
    have ha_lt : a < 1/3 := by
      have : a ≤ ((2*rs (j+1)-1 : ℕ) : ℝ) * a :=
        le_mul_of_one_le_left ha0 hσ1
      nlinarith
    have hρ : ((2*rs (j+1)+1 : ℕ) : ℝ) = ((2*rs (j+1)-1 : ℕ) : ℝ) + 2 := by
      have h : (2*rs (j+1)+1 : ℕ) = (2*rs (j+1)-1 : ℕ) + 2 := by omega
      exact_mod_cast h
    have hρa : ((2*rs (j+1)+1 : ℕ) : ℝ) * a < 1 := by
      rw [hρ]
      nlinarith
    have hle := arcsin_le_pi_div_two_mul ha0 (by linarith)
    have h2 : (0:ℝ) ≤ (2*rs (j+1)+1 : ℕ) := by
      have : 0 ≤ 2*rs (j+1) + 1 := by omega
      exact_mod_cast this
    have h3 : ((2*rs (j+1)+1 : ℕ) : ℝ) * Real.arcsin a
        ≤ ((2*rs (j+1)+1 : ℕ) : ℝ) * ((Real.pi / 2) * a) :=
      mul_le_mul_of_nonneg_left hle h2
    have h5 : ((2*rs (j+1)+1 : ℕ) : ℝ) * Real.arcsin a < Real.pi / 2 :=
      calc ((2*rs (j+1)+1 : ℕ) : ℝ) * Real.arcsin a
          ≤ ((2*rs (j+1)+1 : ℕ) : ℝ) * ((Real.pi / 2) * a) := h3
        _ = (Real.pi / 2) * (((2*rs (j+1)+1 : ℕ) : ℝ) * a) := by ring
        _ < (Real.pi / 2) * 1 := mul_lt_mul_of_pos_left hρa (by positivity)
        _ = Real.pi / 2 := by ring
    linarith

/-- For legal bounded-threshold tunable amplification, legality of the appended-stage word
implies legality of its amplified word, the projected-state gain identity, and exact
odd-factor recurrences for calls and weighted costs. -/
private theorem clause5_at_stage {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (htun : tunable m (extendClock m P) bad U ω α rs) (habove : ∀ j : Fin m, α (j.val+1) ≤ 1)
    {j : ℕ} (hj : j < m) :
    legal (m+1) (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) →
    legal (m+1) (nestedWord (extendClock m P) bad ω rs (j+1)) ∧
    potential (extendClock m P (j+1)) bad *ᵥ
        clockState U (nestedWord (extendClock m P) bad ω rs (j+1)) ω
      = (((2*rs (j+1)+1 : ℕ) : ℂ)
          * ((gainLoss (2*rs (j+1)+1)
              (preAmplitude (extendClock m P) bad ω U rs j) : ℝ) : ℂ)) •
        (potential (extendClock m P (j+1)) bad *ᵥ
          clockState U (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) ω) ∧
    (∀ slot, calls (nestedWord (extendClock m P) bad ω rs (j+1)) slot
      = (2*rs (j+1)+1) * calls (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) slot) ∧
    (∀ prices, weightedCost prices (nestedWord (extendClock m P) bad ω rs (j+1))
      = (2*rs (j+1)+1) * weightedCost prices
          (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1))) := by
  intro hB
  have hEj1 : extendClock m P (j+1) = P ⟨j+1, by omega⟩ := extendClock_eq m P (by omega)
  have hGproj : IsOrthogonalProjector (potential (extendClock m P (j+1)) bad) := by
    have g3 := Clause3ClockFlagResolutions_answer H m P bad hclock
    have h := (g3.1 ⟨j+1, by omega⟩ ⟨j+1, by omega⟩ le_rfl).2.2.2.2.2.1
    rw [hEj1]
    exact h
  have hUunit : ∀ k < m+1, U k ∈ Matrix.unitaryGroup H ℂ := by
    intro k hk
    exact hstage.1 (⟨k, by omega⟩ : Fin (m+1))
  have hno := noOvershoot m P bad U ω α rs htun habove hj
  have hG5 := Clause5ActualNestedAmplification_answer H (m+1) U
    (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) ω
    (potential (extendClock m P (j+1)) bad) (rs (j+1))
    hUunit hB hnorm hGproj hno
  have hdef : nestedWord (extendClock m P) bad ω rs (j+1)
      = aaWord (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) ω
          (potential (extendClock m P (j+1)) bad) (rs (j+1)) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdef]
    exact hG5.1
  · rw [hdef]
    exact hG5.2.1
  · intro slot
    rw [hdef]
    exact hG5.2.2.1 slot
  · intro prices
    rw [hdef]
    exact hG5.2.2.2.2 prices

/-- A natural-number product indexed by `Fin n` equals the corresponding product over
`Finset.range n`. -/
private theorem fin_prod_eq_range_prod (n : ℕ) (f : ℕ → ℕ) :
    (∏ k : Fin n, f k.val) = ∏ i ∈ Finset.range n, f i :=
  Fin.prod_univ_eq_prod_range f n

/-- The product of odd round factors through stage `j + 1` splits into the previous product and
the new round factor. -/
private theorem prod_split_rs {j : ℕ} {rs : ℕ → ℕ} :
    (∏ k : Fin (j+1), (2*rs (k.val+1)+1))
      = (∏ k : Fin j, (2*rs (k.val+1)+1)) * (2*rs (j+1)+1) := by
  have e : ∀ n : ℕ, (∏ k : Fin n, (2*rs (k.val+1)+1))
      = ∏ k ∈ Finset.range n, (2*rs (k+1)+1) :=
    fun n => Fin.prod_univ_eq_prod_range (fun k => 2*rs (k+1)+1) n
  rw [e (j+1), Finset.prod_range_succ (fun k => 2*rs (k+1)+1) j, ← e j]

/-- Under legal clocks and stages and a bounded-threshold tunable schedule, every nested word
through stage `m` is legal. -/
private theorem legal_nested {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (htun : tunable m (extendClock m P) bad U ω α rs) (habove : ∀ j : Fin m, α (j.val+1) ≤ 1) :
    ∀ j : ℕ, j ≤ m → legal (m+1) (nestedWord (extendClock m P) bad ω rs j) := by
  intro j
  induction j with
  | zero =>
    intro _
    exact legal_stageWord m 0 (by omega)
  | succ j ih =>
    intro hj
    have hjm : j < m := by omega
    have hB : legal (m+1) (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) := by
      rw [legal_append_iff]
      exact ⟨ih (by omega), legal_stageWord m (j+1) (by omega)⟩
    have hg5 := clause5_at_stage m P bad U ω α rs hclock hstage hnorm htun habove hjm hB
    exact hg5.1

/-- Under legal bounded-threshold tunable amplification, appending the next stage to a nested
word before stage `m` gives a legal word. -/
private theorem legal_B {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (htun : tunable m (extendClock m P) bad U ω α rs) (habove : ∀ j : Fin m, α (j.val+1) ≤ 1)
    {j : ℕ} (hj : j < m) :
    legal (m+1) (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) := by
  rw [legal_append_iff]
  exact ⟨legal_nested m P bad U ω α rs hclock hstage hnorm htun habove j (by omega),
    legal_stageWord m (j+1) (by omega)⟩

/-- Under legal bounded-threshold tunable amplification, the number of slot-zero calls through
stage `j` equals the product of odd round factors through that stage. -/
private theorem calls_nested {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (htun : tunable m (extendClock m P) bad U ω α rs) (habove : ∀ j : Fin m, α (j.val+1) ≤ 1) :
    ∀ j : ℕ, j ≤ m →
      calls (nestedWord (extendClock m P) bad ω rs j) 0
        = ∏ k : Fin j, (2*rs (k.val+1)+1) := by
  intro j
  refine Nat.rec (motive := fun k => k ≤ m →
    calls (nestedWord (extendClock m P) bad ω rs k) 0 = ∏ i : Fin k, (2*rs (i.val+1)+1)) ?_ ?_ j
  · intro _
    show calls (stageWord (H := H) 0) 0 = ∏ k : Fin 0, (2*rs (k.val+1)+1)
    simp [calls_stageWord]
  · intro j ih hj
    have hjm : j < m := by omega
    have hleg := legal_B m P bad U ω α rs hclock hstage hnorm htun habove hjm
    have hg5 := clause5_at_stage m P bad U ω α rs hclock hstage hnorm htun habove hjm hleg
    rw [hg5.2.2.1 0, calls_append, calls_stageWord_zero (j+1) (by omega), add_zero,
      ih (by omega), prod_split_rs]
    ring

/-- Under legal bounded-threshold tunable amplification, the next weighted cost equals the odd
round factor times the sum of the previous cost and the new stage price. -/
private theorem cost_nested {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (htun : tunable m (extendClock m P) bad U ω α rs) (habove : ∀ j : Fin m, α (j.val+1) ≤ 1) :
    ∀ j : ℕ, j < m → ∀ prices : ℕ → ℕ,
      weightedCost prices (nestedWord (extendClock m P) bad ω rs (j+1))
        = (2*rs (j+1)+1) *
          (weightedCost prices (nestedWord (extendClock m P) bad ω rs j) + prices (j+1)) := by
  intro j hj prices
  have hleg := legal_B m P bad U ω α rs hclock hstage hnorm htun habove hj
  have hg5 := clause5_at_stage m P bad U ω α rs hclock hstage hnorm htun habove hj hleg
  rw [hg5.2.2.2 prices, weightedCost_append, weightedCost_stageWord]

/-- Every stage gain loss is positive under a tunable schedule with thresholds at most one. -/
private theorem gainLoss_pos {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (htun : tunable m (extendClock m P) bad U ω α rs) (habove : ∀ j : Fin m, α (j.val+1) ≤ 1)
    (j : ℕ) (hj : j < m) :
    0 < gainLoss (2*rs (j+1)+1) (preAmplitude (extendClock m P) bad ω U rs j) := by
  unfold gainLoss
  by_cases ha : preAmplitude (extendClock m P) bad ω U rs j = 0
  · rw [if_pos ha]
    norm_num
  · rw [if_neg ha]
    set a := preAmplitude (extendClock m P) bad ω U rs j with haa
    have ha0 : 0 < a := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ha)
    have hno := noOvershoot m P bad U ω α rs htun habove hj
    have hle : ((2*rs (j+1)+1 : ℕ) : ℝ) * Real.arcsin a ≤ Real.pi / 2 := by
      rw [haa]
      exact hno
    have hρ : 0 < ((2*rs (j+1)+1 : ℕ) : ℝ) := by
      have : 0 < 2*rs (j+1) + 1 := by omega
      exact_mod_cast this
    have harc_pos : 0 < Real.arcsin a := Real.arcsin_pos.mpr ha0
    have hx0 : 0 < ((2*rs (j+1)+1 : ℕ) : ℝ) * Real.arcsin a := mul_pos hρ harc_pos
    have hxπ : ((2*rs (j+1)+1 : ℕ) : ℝ) * Real.arcsin a < Real.pi := by
      have hpi : (0:ℝ) < Real.pi := Real.pi_pos
      nlinarith
    have hsin : 0 < Real.sin (((2*rs (j+1)+1 : ℕ) : ℝ) * Real.arcsin a) :=
      Real.sin_pos_of_pos_of_lt_pi hx0 hxπ
    exact div_pos hsin (mul_pos hρ ha0)

/-- The total gain loss is positive under a tunable schedule with thresholds at most one. -/
private theorem totalLoss_pos {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (htun : tunable m (extendClock m P) bad U ω α rs) (habove : ∀ j : Fin m, α (j.val+1) ≤ 1) :
    0 < totalLoss m (extendClock m P) bad U ω rs := by
  unfold totalLoss
  exact Finset.prod_pos fun j _ => gainLoss_pos m P bad U ω α rs htun habove j.val j.isLt

/-- Under legal bounded-threshold tunable amplification, the pre-amplitude equals the next plain
amplitude multiplied by the preceding gain-multiplier product. -/
private theorem preAmplitude_eq {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (htun : tunable m (extendClock m P) bad U ω α rs) (habove : ∀ j : Fin m, α (j.val+1) ≤ 1)
    {j : ℕ} (hj : j < m) :
    preAmplitude (extendClock m P) bad ω U rs j
      = (∏ k : Fin j, lam (extendClock m P) bad U ω rs k.val)
        *plainAmplitude (extendClock m P) bad U ω (j+1) := by
  have hamp := amplification_products_invariant (H := H) m P bad U ω α rs hclock hstage
    hnorm htun habove j (by omega)
  have hsplit : ∀ v : QState H,
      (potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ v
        = (potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ
            (potential (extendClock m P j) bad *ᵥ v) := by
    intro v
    have hdecomp : v = potential (extendClock m P j) bad *ᵥ v
        + (1 - potential (extendClock m P j) bad) *ᵥ v :=
      (projector_decomp (potential (extendClock m P j) bad) v).symm
    conv_lhs => rw [hdecomp]
    rw [Matrix.mulVec_add, collapse_apply m P bad U hclock hstage hj v, add_zero]
  have hpre : clockState U (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) ω
      = U (j+1) *ᵥ clockState U (nestedWord (extendClock m P) bad ω rs j) ω :=
    clockState_append_stageWord U _ (j+1) ω
  have hprePlain : clockState U (plainPrefix (j+1)) ω
      = U (j+1) *ᵥ clockState U (plainPrefix j) ω := by
    rw [plainPrefix_succ, clockState_append_stageWord]
  have hkey : potential (extendClock m P (j+1)) bad *ᵥ
      clockState U (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) ω
      = (∏ k : Fin j, ((lam (extendClock m P) bad U ω rs k.val : ℝ) : ℂ)) •
        (potential (extendClock m P (j+1)) bad *ᵥ
          clockState U (plainPrefix (j+1)) ω) := by
    rw [hpre, Matrix.mulVec_mulVec, hsplit, hamp, Matrix.mulVec_smul]
    have h2 : (potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ
        (potential (extendClock m P j) bad *ᵥ clockState U (plainPrefix j) ω)
        = potential (extendClock m P (j+1)) bad *ᵥ
            clockState U (plainPrefix (j+1)) ω := by
      calc (potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ
            (potential (extendClock m P j) bad *ᵥ clockState U (plainPrefix j) ω)
          = (potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ
              clockState U (plainPrefix j) ω :=
            (hsplit (clockState U (plainPrefix j) ω)).symm
        _ = potential (extendClock m P (j+1)) bad *ᵥ
              (U (j+1) *ᵥ clockState U (plainPrefix j) ω) := by rw [Matrix.mulVec_mulVec]
        _ = potential (extendClock m P (j+1)) bad *ᵥ
              clockState U (plainPrefix (j+1)) ω := by rw [hprePlain]
    rw [h2]
  have hlamnn : ∀ k : Fin j, 0 ≤ lam (extendClock m P) bad U ω rs k.val := by
    intro k
    exact mul_nonneg (by exact_mod_cast (by omega : 0 ≤ 2*rs (k.val+1)+1))
      (le_of_lt (gainLoss_pos m P bad U ω α rs htun habove k.val
        (lt_of_lt_of_le k.isLt (by omega))))
  show normVec (potential (extendClock m P (j+1)) bad *ᵥ
    clockState U (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) ω) = _
  rw [hkey, normVec_smul]
  have hnp : ‖(∏ k : Fin j, ((lam (extendClock m P) bad U ω rs k.val : ℝ) : ℂ))‖
      = ∏ k : Fin j, lam (extendClock m P) bad U ω rs k.val := by
    rw [norm_prod]
    exact Finset.prod_congr rfl fun k _ => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hlamnn k)]
  rw [hnp]
  rfl

/-- Under legal bounded-threshold tunable amplification, the final post-amplitude equals the
final plain amplitude multiplied by the gain-multiplier product. -/
private theorem postAmplitude_eq {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (htun : tunable m (extendClock m P) bad U ω α rs) (habove : ∀ j : Fin m, α (j.val+1) ≤ 1) :
    postAmplitude (extendClock m P) bad ω U rs m
      = (∏ k : Fin m, lam (extendClock m P) bad U ω rs k.val)
        *plainAmplitude (extendClock m P) bad U ω m := by
  have hamp := amplification_products_invariant (H := H) m P bad U ω α rs hclock hstage
    hnorm htun habove m (le_refl m)
  have hlamnn : ∀ k : Fin m, 0 ≤ lam (extendClock m P) bad U ω rs k.val := by
    intro k
    exact mul_nonneg (by exact_mod_cast (by omega : 0 ≤ 2*rs (k.val+1)+1))
      (le_of_lt (gainLoss_pos m P bad U ω α rs htun habove k.val k.isLt))
  show normVec (potential (extendClock m P m) bad *ᵥ
    clockState U (nestedWord (extendClock m P) bad ω rs m) ω) = _
  rw [hamp, normVec_smul]
  have hnp : ‖(∏ k : Fin m, ((lam (extendClock m P) bad U ω rs k.val : ℝ) : ℂ))‖
      = ∏ k : Fin m, lam (extendClock m P) bad U ω rs k.val := by
    rw [norm_prod]
    exact Finset.prod_congr rfl fun k _ => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hlamnn k)]
  rw [hnp]
  rfl

/-- For legal clocks and stages, a zero plain amplitude remains zero at the next stage. -/
private theorem plainAmplitude_succ_of_zero {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U)
    {k : ℕ} (hk : k < m) :
    plainAmplitude (extendClock m P) bad U ω k = 0 →
      plainAmplitude (extendClock m P) bad U ω (k+1) = 0 := by
  intro hz
  have hsplit : ∀ v : QState H,
      (potential (extendClock m P (k+1)) bad * U (k+1)) *ᵥ v
        = (potential (extendClock m P (k+1)) bad * U (k+1)) *ᵥ
            (potential (extendClock m P k) bad *ᵥ v) := by
    intro v
    have hdecomp : v = potential (extendClock m P k) bad *ᵥ v
        + (1 - potential (extendClock m P k) bad) *ᵥ v :=
      (projector_decomp (potential (extendClock m P k) bad) v).symm
    conv_lhs => rw [hdecomp]
    rw [Matrix.mulVec_add, collapse_apply m P bad U hclock hstage hk v, add_zero]
  have hprePlain : clockState U (plainPrefix (k+1)) ω
      = U (k+1) *ᵥ clockState U (plainPrefix k) ω := by
    rw [plainPrefix_succ, clockState_append_stageWord]
  have hGk : potential (extendClock m P k) bad *ᵥ clockState U (plainPrefix k) ω = 0 := by
    have : normVec (potential (extendClock m P k) bad *ᵥ clockState U (plainPrefix k) ω)
        = 0 := hz
    exact (normVec_eq_zero_iff _).mp this
  have hkey : potential (extendClock m P (k+1)) bad *ᵥ
      clockState U (plainPrefix (k+1)) ω = 0 := by
    rw [hprePlain, Matrix.mulVec_mulVec]
    rw [hsplit (clockState U (plainPrefix k) ω), hGk, Matrix.mulVec_zero]
  have : normVec (potential (extendClock m P (k+1)) bad *ᵥ
      clockState U (plainPrefix (k+1)) ω) = 0 :=
    (normVec_eq_zero_iff _).mpr hkey
  exact this

/-- For legal clocks and stages, a positive final plain amplitude implies positivity of every
earlier plain amplitude. -/
private theorem plainAmplitude_pos {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U)
    (ha : 0 < plainAmplitude (extendClock m P) bad U ω m) :
    ∀ k ≤ m, 0 < plainAmplitude (extendClock m P) bad U ω k := by
  intro k hk
  by_contra hne
  have hz : plainAmplitude (extendClock m P) bad U ω k = 0 :=
    le_antisymm (le_of_not_gt hne) (norm_nonneg _)
  have hprop : ∀ d, k + d ≤ m → plainAmplitude (extendClock m P) bad U ω (k+d) = 0 := by
    intro d
    induction d with
    | zero => exact fun _ => hz
    | succ d ih =>
      intro hd
      have hkm : k + d < m := by omega
      exact plainAmplitude_succ_of_zero m P bad U ω hclock hstage hkm (ih (by omega))
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact absurd (hprop d le_rfl) (ne_of_gt ha)

/-- The final potential amplitude of a legal nested word with legal unitary stages and
normalized seed is at most one. -/
private theorem postAmplitude_le_one {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (hlegal : legal (m+1) (nestedWord (extendClock m P) bad ω rs m)) :
    postAmplitude (extendClock m P) bad ω U rs m ≤ 1 := by
  have hGproj : IsOrthogonalProjector (potential (extendClock m P m) bad) := by
    have g3 := Clause3ClockFlagResolutions_answer H m P bad hclock
    have hE : extendClock m P m = P ⟨m, by omega⟩ := extendClock_eq m P (by omega)
    have h := (g3.1 ⟨m, by omega⟩ ⟨m, by omega⟩ le_rfl).2.2.2.2.2.1
    rw [hE]
    exact h
  have h1 : normVec (potential (extendClock m P m) bad *ᵥ
      clockState U (nestedWord (extendClock m P) bad ω rs m) ω)
      ≤ normVec (clockState U (nestedWord (extendClock m P) bad ω rs m) ω) :=
    normVec_mul_proj_le _ hGproj _
  have hU : ∀ j < m+1, U j ∈ Matrix.unitaryGroup H ℂ := fun j hj =>
    hstage.1 (⟨j, by omega⟩ : Fin (m+1))
  have h2 := normVec_clockState_eq_one U (nestedWord (extendClock m P) bad ω rs m) ω hU
    hlegal hnorm
  show normVec (potential (extendClock m P m) bad *ᵥ
    clockState U (nestedWord (extendClock m P) bad ω rs m) ω) ≤ 1
  linarith

/-- A minimal odd factor reaching the square-root threshold divided by three gives linearized
amplitude at most one when both the amplitude and threshold are at most one. -/
private theorem schedule_bound {r : ℕ} {a β αk : ℝ}
    (_ha : 0 ≤ a) (ha1 : a ≤ 1) (_hα0 : 0 ≤ αk) (hα1 : αk ≤ 1)
    (hb : β = Real.sqrt αk)
    (hmain : β / 3 ≤ (2 * (r : ℝ) + 1) * a)
    (hmin : ∀ s < r, (2 * (s : ℝ) + 1) * a < β / 3) :
    (2 * (r : ℝ) + 1) * a ≤ 1 := by
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
    have h1 : (2 * (r : ℝ) - 1) * a < 1 / 3 := by
      have h := hmin (r - 1) (by omega)
      have heq : (2 * ((r - 1 : ℕ) : ℝ) + 1) = 2 * (r : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
        ring
      rw [heq] at h
      nlinarith
    have ha2 : a < 1 / (3 * (2 * (r : ℝ) - 1)) := by
      have hden : 0 < 3 * (2 * (r : ℝ) - 1) := by nlinarith [hρpos]
      rw [lt_div_iff₀ hden]
      nlinarith
    have hsum : (2 * (r : ℝ) + 1) * a = (2 * (r : ℝ) - 1) * a + 2 * a := by
      rw [← hcast]
      ring
    have hle : 1 / 3 + 2 * (1 / (3 * (2 * (r : ℝ) - 1))) ≤ 1 := by
      have hden : 0 < 3 * (2 * (r : ℝ) - 1) := by nlinarith [hρpos]
      have hd1 : (1:ℝ) ≤ 2 * (r : ℝ) - 1 := by
        have h1r : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr1
        nlinarith
      have hfrac : 2 * (1 / (3 * (2 * (r : ℝ) - 1))) ≤ 2 / 3 := by
        have : 1 / (3 * (2 * (r : ℝ) - 1)) ≤ 1 / 3 :=
          (div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 3)).mpr (by nlinarith [hd1])
        linarith
      linarith
    nlinarith [ha2, hsum, hle, _ha, hρpos]

/-- For a positive minimal round count, the squared linearized amplitude is strictly less than
the threshold whose square root defines the stopping criterion. -/
private theorem schedule_sq_lt (r : ℕ) (a β αk : ℝ)
    (_ha : 0 ≤ a) (_hα0 : 0 ≤ αk) (hr : 1 ≤ r)
    (hb : β = Real.sqrt αk)
    (hmin : ∀ s < r, (2 * (s : ℝ) + 1) * a < β / 3) :
    (2 * (r : ℝ) + 1) ^ 2 * a ^ 2 < αk := by
  have h0 : (2 * ((0:ℕ) : ℝ) + 1) * a < β / 3 := hmin 0 (by omega)
  have h1 : (2 * (((r - 1 : ℕ) : ℝ)) + 1) * a < β / 3 := hmin (r - 1) (by omega)
  have hkey : (2 * (r : ℝ) + 1) * a < β := by
    have heq : (2 * (r : ℝ) + 1) = (2 * (((r - 1 : ℕ) : ℝ)) + 1) + 2 * 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
      ring
    rw [heq, add_mul]
    have h2 : 2 * 1 * a < 2 * (β / 3) := by linarith
    have hsum : ((2 * (((r - 1 : ℕ) : ℝ)) + 1) * a) + (2 * 1 * a)
        < β / 3 + 2 * (β / 3) := by linarith
    have hbeta : β / 3 + 2 * (β / 3) = β := by ring
    linarith
  have hβ0 : 0 ≤ β := by rw [hb]; exact Real.sqrt_nonneg _
  have hxa : 0 ≤ (2 * (r : ℝ) + 1) * a := by positivity
  have hsq : ((2 * (r : ℝ) + 1) * a) ^ 2 < β ^ 2 := by nlinarith
  rw [hb, Real.sq_sqrt _hα0, mul_pow] at hsq
  exact hsq

/-- For `α` in the unit interval, `(5 / 6) ^ α ≤ 1 - α / 6`. -/
private theorem rpow_five_six_le (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    (5 / 6 : ℝ) ^ α ≤ 1 - α / 6 := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := α) (w₂ := 1 - α)
    (p₁ := (5 / 6 : ℝ)) (p₂ := (1 : ℝ)) h0 (by linarith) (by norm_num) (by norm_num) (by ring)
  have hone : ((1 : ℝ) ^ (1 - α)) = 1 := Real.one_rpow _
  have hsum : α * (5 / 6 : ℝ) + (1 - α) * 1 = 1 - α / 6 := by ring
  rw [hone, mul_one] at h
  nlinarith

/-- The absolute sine of a natural multiple of an angle is bounded by that multiple of the
absolute sine. -/
private theorem abs_sin_le (n : ℕ) (θ : ℝ) :
    |Real.sin ((n : ℝ) * θ)| ≤ n * |Real.sin θ| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_cast
    have hsum : Real.sin (((n : ℝ) + 1) * θ)
        = Real.sin ((n : ℝ) * θ) * Real.cos θ + Real.cos ((n : ℝ) * θ) * Real.sin θ := by
      rw [add_mul, Real.sin_add]
      simp only [one_mul]
    rw [hcast, hsum]
    have h1 : |Real.sin ((n : ℝ) * θ) * Real.cos θ + Real.cos ((n : ℝ) * θ) * Real.sin θ|
        ≤ |Real.sin ((n : ℝ) * θ) * Real.cos θ| + |Real.cos ((n : ℝ) * θ) * Real.sin θ| :=
      abs_add_le _ _
    have h2 : |Real.sin ((n : ℝ) * θ) * Real.cos θ| + |Real.cos ((n : ℝ) * θ) * Real.sin θ|
        = |Real.sin ((n : ℝ) * θ)| * |Real.cos θ| + |Real.cos ((n : ℝ) * θ)| * |Real.sin θ| := by
      rw [abs_mul, abs_mul]
    have c1 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
    have c2 : |Real.cos ((n : ℝ) * θ)| ≤ 1 := Real.abs_cos_le_one _
    have h3 : |Real.sin ((n : ℝ) * θ)| * |Real.cos θ| + |Real.cos ((n : ℝ) * θ)| * |Real.sin θ|
        ≤ |Real.sin ((n : ℝ) * θ)| * 1 + 1 * |Real.sin θ| := by
      gcongr
    have h4 : |Real.sin ((n : ℝ) * θ)| * 1 + 1 * |Real.sin θ|
        = |Real.sin ((n : ℝ) * θ)| + |Real.sin θ| := by ring
    have h5 : |Real.sin ((n : ℝ) * θ)| + |Real.sin θ| ≤ (n : ℝ) * |Real.sin θ| + |Real.sin θ| := by
      gcongr
    have h6 : (n : ℝ) * |Real.sin θ| + |Real.sin θ| = ((n : ℝ) + 1) * |Real.sin θ| := by ring
    exact le_trans h1 (le_of_eq h2 |>.trans (le_trans h3 (le_of_eq h4 |>.trans
      (le_trans h5 (le_of_eq h6)))))

/-- For amplitudes in the unit interval, sine amplification is bounded above by linear
amplification. -/
private theorem sin_mul_arcsin_le (ρ : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.sin ((ρ : ℝ) * Real.arcsin a) ≤ (ρ : ℝ) * a := by
  have hsin : Real.sin (Real.arcsin a) = a :=
    Real.sin_arcsin (by linarith) (by linarith)
  have habs : |Real.sin ((ρ : ℝ) * Real.arcsin a)|
      ≤ (ρ : ℝ) * |Real.sin (Real.arcsin a)| := abs_sin_le ρ (Real.arcsin a)
  rw [hsin, abs_of_nonneg ha] at habs
  exact le_trans (le_abs_self _) habs

/-- The gain loss factor is at most one for amplitudes in the unit interval. -/
private theorem gainLoss_le_one {ρ : ℕ} {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    gainLoss ρ a ≤ 1 := by
  have hkey := sin_mul_arcsin_le ρ a ha ha1
  unfold gainLoss
  split_ifs with ha0
  · norm_num
  · by_cases hρ0 : ρ = 0
    · subst hρ0
      norm_num
    · have hρpos : 0 < ρ := Nat.pos_of_ne_zero hρ0
      have hden : 0 < (ρ : ℝ) * a := by positivity
      rw [div_le_iff₀ hden]
      nlinarith

/-- The gain loss factor is nonnegative for nonnegative amplitudes without amplified-angle
overshoot. -/
private theorem gainLoss_nonneg {ρ : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (hang : ((ρ : ℝ) * Real.arcsin a) ≤ Real.pi / 2) :
    0 ≤ gainLoss ρ a := by
  unfold gainLoss
  split_ifs with ha0
  · norm_num
  · by_cases hρ0 : ρ = 0
    · subst hρ0
      norm_num
    · have hx0 : 0 ≤ (ρ : ℝ) * Real.arcsin a := by
        have harc : 0 ≤ Real.arcsin a := (Real.arcsin_nonneg).mpr ha
        positivity
      have hsin : 0 ≤ Real.sin ((ρ : ℝ) * Real.arcsin a) :=
        Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [Real.pi_pos])
      exact div_nonneg hsin (by positivity)

/-- Forming an odd round factor commutes with casting natural numbers to the reals. -/
private theorem cast21 (x : ℕ) : (2 * (x : ℝ) + 1) = ((2 * x + 1 : ℕ) : ℝ) := by
  push_cast
  ring

/-- For a real exponent in the unit interval, `(5 / 6)` raised to that exponent is at least `5 /
6`. -/
private theorem five_six_anti {z : ℝ} (_hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (5/6 : ℝ) ≤ (5/6 : ℝ)^z := by
  have h65 : (6/5 : ℝ)^z ≤ (6/5 : ℝ)^((1:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 6/5) hz1
  have e : (6/5 : ℝ)^z = ((5/6 : ℝ)^z)⁻¹ := by
    rw [show (6/5 : ℝ) = (5/6 : ℝ)⁻¹ from by norm_num]
    exact Real.inv_rpow (by norm_num : (0:ℝ) ≤ 5/6) _
  rw [e, Real.rpow_one] at h65
  have h2 : (5/6 : ℝ) * ((5/6 : ℝ)^z)⁻¹ ≤ 1 := by
    have h3 : (5/6 : ℝ) * ((5/6 : ℝ)^z)⁻¹ ≤ (5/6 : ℝ) * (6/5) :=
      mul_le_mul_of_nonneg_left h65 (by norm_num : (0:ℝ) ≤ 5/6)
    have h4 : (5/6 : ℝ) * (6/5) = 1 := by norm_num
    linarith
  have e5 : ((5/6 : ℝ) * ((5/6 : ℝ)^z)⁻¹) * ((5/6 : ℝ)^z) = 5/6 := by
    rw [mul_assoc, inv_mul_cancel₀
      (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 5/6) z)), mul_one]
  calc (5/6 : ℝ) = ((5/6 : ℝ) * ((5/6 : ℝ)^z)⁻¹) * ((5/6 : ℝ)^z) := e5.symm
    _ ≤ 1 * ((5/6 : ℝ)^z) := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = (5/6 : ℝ)^z := by rw [one_mul]

/-- For legal bounded-threshold tunable amplification with positive final plain amplitude, every
stage gain loss is at least `5 / 6`. -/
private theorem gainLoss_ge_five_six {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (hplain : 0 < plainAmplitude (extendClock m P) bad U ω m)
    (htun : tunable m (extendClock m P) bad U ω α rs) (habove : ∀ j : Fin m, α (j.val+1) ≤ 1)
    (j : ℕ) (hj : j < m) :
    (5/6 : ℝ) ≤ gainLoss (2*rs (j+1)+1) (preAmplitude (extendClock m P) bad ω U rs j) := by
  have g8 := Clause8TunableUniversality_answer (H := H) m P bad U ω α rs hclock hstage hnorm hplain
  obtain ⟨hpos, hF2, _⟩ := (g8.1 ⟨htun, habove⟩).1 ⟨j, hj⟩
  rw [cast21 (rs (j+1))] at hF2
  have hmain := (htun.2 j hj).2.1
  have hmin := (htun.2 j hj).2.2
  have hα0 : 0 ≤ α (j+1) := (htun.2 j hj).1
  have hα1 : α (j+1) ≤ 1 := habove ⟨j, hj⟩
  have ha : 0 ≤ preAmplitude (extendClock m P) bad ω U rs j := le_of_lt hpos
  have hanti := five_six_anti (z := α (j+1)) hα0 hα1
  by_cases hr0 : rs (j+1) = 0
  · have hgl : gainLoss (2*rs (j+1)+1) (preAmplitude (extendClock m P) bad ω U rs j) = 1 := by
      rw [hr0]
      norm_num
      unfold gainLoss
      split_ifs with ha0
      · rfl
      · have ha1 : preAmplitude (extendClock m P) bad ω U rs j ≤ 1 := by
          rw [hr0] at hF2
          push_cast at hF2
          linarith
        push_cast
        rw [one_mul, one_mul,
          Real.sin_arcsin (by linarith : (-1:ℝ) ≤ preAmplitude (extendClock m P) bad ω U rs j) ha1]
        field_simp
    rw [hgl]
    norm_num
  · have hr1 : 1 ≤ rs (j+1) := by omega
    have hgl : gainLoss (2*rs (j+1)+1) (preAmplitude (extendClock m P) bad ω U rs j)
        = Real.sin (((2*rs (j+1)+1 : ℕ) : ℝ) * Real.arcsin
            (preAmplitude (extendClock m P) bad ω U rs j)) /
          (((2*rs (j+1)+1 : ℕ) : ℝ) * preAmplitude (extendClock m P) bad ω U rs j) := by
      unfold gainLoss
      rw [if_neg (by positivity)]
    rw [hgl]
    set θ := Real.arcsin (preAmplitude (extendClock m P) bad ω U rs j) with hθ
    have hsinθ : Real.sin θ = preAmplitude (extendClock m P) bad ω U rs j := by
      rw [hθ]
      refine Real.sin_arcsin (by linarith : (-1:ℝ) ≤ preAmplitude (extendClock m P) bad ω U rs j) ?_
      have hρ1 : (1:ℝ) ≤ ((2*rs (j+1)+1 : ℕ) : ℝ) :=
        by exact_mod_cast (by omega : 1 ≤ 2*rs (j+1)+1)
      nlinarith [hF2, hρ1]
    have hθ0 : 0 ≤ θ := by
      rw [hθ]
      exact Real.arcsin_nonneg.mpr ha
    have hθpos : θ ≠ 0 := by
      intro habs
      have h0 : Real.sin θ = 0 := by rw [habs]; exact Real.sin_zero
      rw [hsinθ] at h0
      exact ne_of_gt hpos h0
    have hθle : ((2*rs (j+1)+1 : ℕ) : ℝ) * θ ≤ Real.pi / 2 := by
      rw [hθ]
      exact noOvershoot m P bad U ω α rs htun habove hj
    have hg7 := Clause7TightDirichletBounds_answer.1 (2*rs (j+1)+1) θ
      (by omega) hθ0 hθle
    (try dsimp only at hg7)
    rw [if_neg hθpos] at hg7
    have hlo := hg7.1
    rw [hsinθ] at hlo
    have hρa : ((2*rs (j+1)+1 : ℕ) : ℝ) ^ 2
        * (preAmplitude (extendClock m P) bad ω U rs j) ^ 2 < α (j+1) := by
      have hρa' : (2 * (rs (j+1) : ℝ) + 1) ^ 2
          * (preAmplitude (extendClock m P) bad ω U rs j) ^ 2 < α (j+1) :=
        schedule_sq_lt (rs (j+1)) (preAmplitude (extendClock m P) bad ω U rs j)
          (Real.sqrt (α (j+1))) (α (j+1)) ha hα0 hr1 rfl hmin
      rw [← cast21 (rs (j+1))]
      exact hρa'
    have hchord := rpow_five_six_le (α (j+1)) hα0 hα1
    nlinarith [hlo, hρa, hchord, hanti]

/-- For legal bounded-threshold tunable amplification with positive final plain amplitude, the
total loss is at least `(5 / 6)` raised to the sum of the stage thresholds. -/
private theorem totalLoss_ge {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (hplain : 0 < plainAmplitude (extendClock m P) bad U ω m)
    (htun : tunable m (extendClock m P) bad U ω α rs) (habove : ∀ j : Fin m, α (j.val+1) ≤ 1) :
    (5/6 : ℝ) ^ (∑ j : Fin m, α (j.val+1)) ≤ totalLoss m (extendClock m P) bad U ω rs :=
  ((Clause8TunableUniversality_answer (H := H) m P bad U ω α rs hclock hstage hnorm hplain).1
    ⟨htun, habove⟩).2

/-- A product over shifted range indices equals the product over the interval starting at one. -/
private theorem prod_range_succ_eq_ico {M : Type} [CommMonoid M] (g : ℕ → M) (m : ℕ) :
    (∏ k ∈ Finset.range m, g (k+1)) = ∏ i ∈ Finset.Ico 1 (m+1), g i := by
  rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
  exact Finset.prod_congr rfl fun k _ => by rw [Nat.add_comm 1 k]

/-- Every odd round factor is at least one as a real number. -/
private theorem rho_ge_one (rs : ℕ → ℕ) (i : ℕ) : (1:ℝ) ≤ ((2*rs i+1 : ℕ) : ℝ) := by
  have : 1 ≤ 2*rs i+1 := by omega
  exact_mod_cast this

/-- Every odd round factor is nonnegative as a real number. -/
private theorem rho_nonneg (rs : ℕ → ℕ) (i : ℕ) : (0:ℝ) ≤ ((2*rs i+1 : ℕ) : ℝ) := by
  have : 0 ≤ 2*rs i+1 := by omega
  exact_mod_cast this

/-- A finite product of real factors each at least one is at least one. -/
private theorem one_le_prod_real {ι : Type} (s : Finset ι) (f : ι → ℝ)
    (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i :=
  Finset.prod_induction f (fun x => 1 ≤ x)
    (fun a b ha hb => by
      have h1 : (1:ℝ)*1 ≤ a*b :=
        mul_le_mul ha hb zero_le_one (le_trans zero_le_one ha)
      simpa using! h1) (le_refl 1) h

/-- Removing an initial segment from an interval product of odd round factors cannot increase
the product. -/
private theorem prod_ico_le_of_le (rs : ℕ → ℕ) {lo hi k : ℕ} (h1 : lo ≤ hi) (h2 : hi ≤ k) :
    ∏ i ∈ Finset.Ico hi k, ((2*rs i+1 : ℕ) : ℝ)
      ≤ ∏ i ∈ Finset.Ico lo k, ((2*rs i+1 : ℕ) : ℝ) := by
  rw [← Finset.prod_Ico_consecutive (fun i => ((2*rs i+1 : ℕ) : ℝ)) h1 h2]
  exact le_mul_of_one_le_left (Finset.prod_nonneg fun i _ => rho_nonneg rs i)
    (one_le_prod_real _ _ (fun i _ => rho_ge_one rs i))

/-- The real suffix product of odd round factors from `max 1 j` through stage `m`. -/
private def suffixProd (m : ℕ) (rs : ℕ → ℕ) (j : ℕ) : ℝ :=
  ∏ i ∈ Finset.Ico (max 1 j) (m+1), ((2*rs i+1 : ℕ) : ℝ)

/-- Casting the natural suffix product of odd round factors to the reals gives `suffixProd`. -/
private theorem suffixProd_cast (m : ℕ) (rs : ℕ → ℕ) (j : ℕ) :
    ((∏ i ∈ Finset.Ico (max 1 j) (m+1), (2*rs i+1) : ℕ) : ℝ) = suffixProd m rs j := by
  rw [suffixProd, Nat.cast_prod]

/-- The suffix product at zero is the full product of odd round factors from stage one through
`m`. -/
private theorem suffixProd_one (m : ℕ) (rs : ℕ → ℕ) :
    suffixProd m rs 0 = ∏ i ∈ Finset.Ico 1 (m+1), ((2*rs i+1 : ℕ) : ℝ) := by
  simp [suffixProd]

/-- The multiplicative weighted-cost recurrence expands into the sum of each stage price
multiplied by its suffix product of odd round factors. -/
private theorem cost_unroll : ∀ (m : ℕ) (W : ℕ → ℕ) (rs prices : ℕ → ℕ),
    W 0 = prices 0 → (∀ j < m, W (j+1) = (2*rs (j+1)+1) * (W j + prices (j+1))) →
    W m = ∑ j ∈ Finset.range (m+1), prices j *
      ∏ i ∈ Finset.Ico (max 1 j) (m+1), (2*rs i+1) := by
  intro m
  induction m with
  | zero =>
    intro W rs prices h0 _
    have h1 : (max 1 0 : ℕ) = 1 := by omega
    rw [h0, Finset.range_one, Finset.sum_singleton]
    simp
  | succ m ih =>
    intro W rs prices h0 hstep
    have hWm := ih W rs prices h0 (fun j hj => hstep j (by omega))
    have hmax : (max 1 (m+1) : ℕ) = m+1 := by omega
    have hsingleton : ∏ i ∈ Finset.Ico (m+1) (m+2), (2*rs i+1)
        = (2*rs (m+1)+1) := by
      have h1 : m + 2 - (m+1) = 1 := by omega
      rw [Finset.prod_Ico_eq_prod_range, h1, Finset.range_one, Finset.prod_singleton]
    have hfactor : ∀ j ∈ Finset.range (m+1),
        prices j * ∏ i ∈ Finset.Ico (max 1 j) (m+2), (2*rs i+1)
          = (prices j * ∏ i ∈ Finset.Ico (max 1 j) (m+1), (2*rs i+1)) * (2*rs (m+1)+1) := by
      intro j hj
      simp only [Finset.mem_range] at hj
      have hIco : Finset.Ico (max 1 j) (m+2)
          = insert (m+1) (Finset.Ico (max 1 j) (m+1)) := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_insert]
        omega
      rw [hIco, Finset.prod_insert (by simp only [Finset.mem_Ico]; omega)]
      ring
    have hRHS : ∑ j ∈ Finset.range (m+1+1),
          prices j * ∏ i ∈ Finset.Ico (max 1 j) (m+2), (2*rs i+1)
        = prices (m+1) * (2*rs (m+1)+1)
          + ∑ j ∈ Finset.range (m+1),
              (prices j * ∏ i ∈ Finset.Ico (max 1 j) (m+1), (2*rs i+1)) * (2*rs (m+1)+1) := by
      rw [Finset.range_add_one, Finset.sum_insert (by simp), hmax, hsingleton,
        Finset.sum_congr rfl (fun j hj => hfactor j hj)]
    have hSmul : ∑ j ∈ Finset.range (m+1), (2*rs (m+1)+1) * (prices j *
          ∏ i ∈ Finset.Ico (max 1 j) (m+1), (2*rs i+1))
        = ∑ j ∈ Finset.range (m+1), (prices j *
          ∏ i ∈ Finset.Ico (max 1 j) (m+1), (2*rs i+1)) * (2*rs (m+1)+1) :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hstep m (by omega), hWm, hRHS, mul_add, Finset.mul_sum, hSmul]
    ring

/-- The block fee is the sum of prices over the natural interval from `a + 1` through `min b m`. -/
private theorem blockFee_eq (prices : ℕ → ℕ) (m a b : ℕ) :
    blockFee prices m a b = ∑ j ∈ Finset.Ico (a+1) (min b m + 1), prices j := by
  unfold blockFee
  rw [Fin.sum_univ_eq_sum_range (fun j => if a < j ∧ j ≤ min b m then prices j else 0) (m+1),
    ← Finset.sum_filter]
  have hset : (Finset.range (m+1)).filter (fun j => a < j ∧ j ≤ min b m)
      = Finset.Ico (a+1) (min b m + 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset]

/-- For a nonnegative function, its sum over a union is at most the sum of its sums over the two
sets. -/
private theorem sum_union_le {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) (A B : Finset ℕ) :
    ∑ j ∈ A ∪ B, f j ≤ ∑ j ∈ A, f j + ∑ j ∈ B, f j := by
  have hEq : A ∪ B = A ∪ (B \ A) := by
    ext x
    simp
  have hdisj : Disjoint A (B \ A) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext x
    simp
  rw [hEq, Finset.sum_union hdisj]
  exact add_le_add_right (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    (fun i _ _ => hf i)) _

/-- For a nonnegative function, its sum over a finite union is at most the sum of its sums over
the constituent sets. -/
private theorem sum_bunion_le : ∀ (l : ℕ) (A : Fin l → Finset ℕ) (f : ℕ → ℝ),
    (∀ j, 0 ≤ f j) → ∑ j ∈ Finset.univ.biUnion A, f j ≤ ∑ v : Fin l, ∑ j ∈ A v, f j := by
  intro l
  induction l with
  | zero => intro A f _; simp
  | succ l ih =>
    intro A f hf
    have hEq : (Finset.univ.biUnion A)
        = A 0 ∪ ((Finset.univ : Finset (Fin l)).biUnion (fun v => A v.succ)) := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_union, Fin.exists_fin_succ,
        true_and]
    rw [hEq, Fin.sum_univ_succ]
    exact le_trans (sum_union_le hf (A 0)
      ((Finset.univ : Finset (Fin l)).biUnion (fun v => A v.succ)))
      (add_le_add_right (ih (fun v => A v.succ) f hf) _)

/-- Under legal bounded-threshold tunable amplification with positive final plain amplitude,
each stage gain multiplier lies between zero and its odd round factor. -/
private theorem lam_le_rho {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (hplain : 0 < plainAmplitude (extendClock m P) bad U ω m)
    (htun : tunable m (extendClock m P) bad U ω α rs) (habove : ∀ j : Fin m, α (j.val+1) ≤ 1)
    {k : ℕ} (hk : k < m) :
    0 ≤ lam (extendClock m P) bad U ω rs k ∧
    lam (extendClock m P) bad U ω rs k ≤ ((2*rs (k+1)+1 : ℕ) : ℝ) := by
  have g8 := Clause8TunableUniversality_answer (H := H) m P bad U ω α rs hclock hstage hnorm hplain
  obtain ⟨hpos, hF2, _⟩ := (g8.1 ⟨htun, habove⟩).1 ⟨k, hk⟩
  have ha : 0 ≤ preAmplitude (extendClock m P) bad ω U rs k := le_of_lt hpos
  have hρ1 : (1:ℝ) ≤ ((2*rs (k+1)+1 : ℕ) : ℝ) :=
    by exact_mod_cast (by omega : 1 ≤ 2*rs (k+1)+1)
  have ha1 : preAmplitude (extendClock m P) bad ω U rs k ≤ 1 := by
    nlinarith [hF2, hρ1]
  have hang := noOvershoot m P bad U ω α rs htun habove hk
  refine ⟨mul_nonneg (rho_nonneg rs (k+1)) (gainLoss_nonneg ha hang), ?_⟩
  have hgl := gainLoss_le_one (ρ := 2*rs (k+1)+1)
    (a := preAmplitude (extendClock m P) bad ω U rs k) ha ha1
  unfold lam
  exact mul_le_of_le_one_right (rho_nonneg rs (k+1)) hgl

/-- Under legal bounded-threshold tunable amplification with positive final plain amplitude,
each prefix round-factor product dominates the square root of its threshold divided by three
times its plain amplitude. -/
private theorem prefix_ge {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (hplain : 0 < plainAmplitude (extendClock m P) bad U ω m)
    (htun : tunable m (extendClock m P) bad U ω α rs) (habove : ∀ j : Fin m, α (j.val+1) ≤ 1)
    {s : ℕ} (hs1 : 1 ≤ s) (hsm : s ≤ m) :
    Real.sqrt (α s)/(3*plainAmplitude (extendClock m P) bad U ω s)
      ≤ ∏ i ∈ Finset.Ico 1 (s+1), ((2*rs i+1 : ℕ) : ℝ) := by
  have hs' : (s-1)+1 = s := by omega
  have hpre := preAmplitude_eq m P bad U ω α rs hclock hstage hnorm htun habove (j := s-1)
    (by omega)
  rw [hs'] at hpre
  have hmain : Real.sqrt (α s)/3 ≤ ((2*rs s+1 : ℕ) : ℝ)
      * preAmplitude (extendClock m P) bad ω U rs (s-1) := by
    have h7 := (htun.2 (s-1) (by omega)).2.1
    rw [hs', cast21 (rs s)] at h7
    exact h7
  have hlams : (∏ k : Fin (s-1), lam (extendClock m P) bad U ω rs k.val)
      ≤ ∏ i ∈ Finset.Ico 1 s, ((2*rs i+1 : ℕ) : ℝ) := by
    have hle : ∏ k : Fin (s-1), lam (extendClock m P) bad U ω rs k.val
        ≤ ∏ k : Fin (s-1), ((2*rs (k.val+1)+1 : ℕ) : ℝ) :=
      Finset.prod_le_prod₀ (fun k _ => (lam_le_rho m P bad U ω α rs hclock hstage hnorm hplain
        htun habove (by omega)).1)
        (fun k _ => (lam_le_rho m P bad U ω α rs hclock hstage hnorm hplain htun habove
          (by omega)).2)
    have hfin : ∏ i ∈ Finset.range (s-1), ((2*rs (i+1)+1 : ℕ) : ℝ)
        = ∏ i ∈ Finset.Ico 1 s, ((2*rs i+1 : ℕ) : ℝ) := by
      rw [prod_range_succ_eq_ico (fun i => ((2*rs i+1 : ℕ) : ℝ)) (s-1), hs']
    exact le_trans hle (le_of_eq (Fin.prod_univ_eq_prod_range
      (fun i => ((2*rs (i+1)+1 : ℕ) : ℝ)) (s-1) |>.trans hfin))
  have hplainpos : 0 < plainAmplitude (extendClock m P) bad U ω s :=
    plainAmplitude_pos m P bad U ω hclock hstage hplain s hsm
  have hsplitIco : (∏ i ∈ Finset.Ico 1 s, ((2*rs i+1 : ℕ) : ℝ))
      * ((2*rs s+1 : ℕ) : ℝ) = ∏ i ∈ Finset.Ico 1 (s+1), ((2*rs i+1 : ℕ) : ℝ) := by
    rw [← Finset.prod_Ico_succ_top hs1 (fun i => ((2*rs i+1 : ℕ) : ℝ))]
  have hkey : Real.sqrt (α s)/3
      ≤ (∏ i ∈ Finset.Ico 1 (s+1), ((2*rs i+1 : ℕ) : ℝ))
        * plainAmplitude (extendClock m P) bad U ω s := by
    rw [← hsplitIco]
    have hstep : ((2*rs s+1 : ℕ) : ℝ) * preAmplitude (extendClock m P) bad ω U rs (s-1)
        ≤ ((∏ i ∈ Finset.Ico 1 s, ((2*rs i+1 : ℕ) : ℝ)) * ((2*rs s+1 : ℕ) : ℝ))
          * plainAmplitude (extendClock m P) bad U ω s := by
      rw [hpre]
      calc ((2*rs s+1 : ℕ) : ℝ) * ((∏ k : Fin (s-1), lam (extendClock m P) bad U ω rs k.val)
            * plainAmplitude (extendClock m P) bad U ω s)
          = (((2*rs s+1 : ℕ) : ℝ) * ∏ k : Fin (s-1), lam (extendClock m P) bad U ω rs k.val)
            * plainAmplitude (extendClock m P) bad U ω s := by ring
        _ ≤ (((2*rs s+1 : ℕ) : ℝ)
            * ∏ i ∈ Finset.Ico 1 s, ((2*rs i+1 : ℕ) : ℝ))
          * plainAmplitude (extendClock m P) bad U ω s :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlams (rho_nonneg rs s)) hplainpos.le
        _ = ((∏ i ∈ Finset.Ico 1 s, ((2*rs i+1 : ℕ) : ℝ)) * ((2*rs s+1 : ℕ) : ℝ))
          * plainAmplitude (extendClock m P) bad U ω s := by ring
    exact le_trans hmain hstep
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 3*plainAmplitude (extendClock m P) bad U ω s)]
  nlinarith [hkey]

/-- A positive lower bound on a prefix round-factor product gives the corresponding upper bound
on the remaining suffix product in terms of the full product. -/
private theorem sigma_split_bound (rs : ℕ → ℕ) {m s : ℕ} (hs1 : 1 ≤ s) (hsm1 : s+1 ≤ m+1)
    {αs ps pf : ℝ} (hps : 0 < ps) (hpf0 : 0 < pf) (hα : 0 < αs)
    (hsq : Real.sqrt αs/(3*ps) ≤ ∏ i ∈ Finset.Ico 1 (s+1), ((2*rs i+1 : ℕ) : ℝ))
    (hpf : ∏ i ∈ Finset.Ico 1 (m+1), ((2*rs i+1 : ℕ) : ℝ) = pf) :
    ∏ i ∈ Finset.Ico (s+1) (m+1), ((2*rs i+1 : ℕ) : ℝ)
      ≤ pf * (3*ps)/Real.sqrt αs := by
  have hPi : (0:ℝ) < ∏ i ∈ Finset.Ico 1 (s+1), ((2*rs i+1 : ℕ) : ℝ) :=
    lt_of_lt_of_le (by norm_num) (one_le_prod_real _ _ (fun i _ => rho_ge_one rs i))
  have hsplit : (∏ i ∈ Finset.Ico 1 (s+1), ((2*rs i+1 : ℕ) : ℝ))
      * ∏ i ∈ Finset.Ico (s+1) (m+1), ((2*rs i+1 : ℕ) : ℝ) = pf := by
    rw [Finset.prod_Ico_consecutive (fun i => ((2*rs i+1 : ℕ) : ℝ))
      (by omega : (1:ℕ) ≤ s+1) hsm1, hpf]
  have hσ : ∏ i ∈ Finset.Ico (s+1) (m+1), ((2*rs i+1 : ℕ) : ℝ)
      = pf / ∏ i ∈ Finset.Ico 1 (s+1), ((2*rs i+1 : ℕ) : ℝ) := by
    rw [eq_div_iff hPi.ne']
    rw [mul_comm]
    exact hsplit
  have hsqrt : (0:ℝ) < Real.sqrt αs := Real.sqrt_pos.mpr hα
  have hkey : Real.sqrt αs ≤ 3*ps * ∏ i ∈ Finset.Ico 1 (s+1), ((2*rs i+1 : ℕ) : ℝ) := by
    rw [mul_comm (3*ps), ← div_le_iff₀ (mul_pos (by norm_num : (0:ℝ) < 3) hps)]
    exact hsq
  rw [hσ, div_le_div_iff₀ hPi hsqrt]
  nlinarith [hkey, hpf0]

/-- The extension of a finite marker sequence to natural indices, taking the value `m + 1`
beyond the finite sequence. -/
private def markerFn {l : ℕ} (s : Fin (l+2) → ℕ) (m : ℕ) : ℕ → ℕ :=
  fun k => if hk : k < l+2 then s ⟨k, hk⟩ else m+1

/-- The extended marker function agrees with the finite marker sequence through index `l + 1`. -/
private theorem markerFn_of {l : ℕ} (s : Fin (l+2) → ℕ) (m : ℕ) {k : ℕ} (hk : k ≤ l+1) :
    markerFn s m k = s ⟨k, by omega⟩ := by
  unfold markerFn
  rw [dif_pos (by omega : k < l+2)]

/-- If markers start at zero and end at `m + 1`, every stage after the first marker and at most
`m` lies between two consecutive extended markers. -/
private theorem marker_lookup {l : ℕ} (s : Fin (l+2) → ℕ) (m j : ℕ)
    (hs0 : s ⟨0, by omega⟩ = 0) (hsT : s ⟨l+1, by omega⟩ = m+1)
    (hjs1 : s ⟨1, by omega⟩ < j) (hjm : j ≤ m) :
    ∃ k : ℕ, 2 ≤ k ∧ k ≤ l+1 ∧ markerFn s m (k-1) < j ∧ j ≤ markerFn s m k := by
  have hex : ∃ k : ℕ, j ≤ markerFn s m k := by
    refine ⟨l+1, ?_⟩
    rw [markerFn_of s m (by omega : l+1 ≤ l+1), hsT]
    omega
  obtain ⟨k, hkq, hkmin⟩ := Nat.findX hex
  have hk2 : 2 ≤ k := by
    by_contra hc
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · rw [markerFn_of s m (by omega), hs0] at hkq
      omega
    · rw [markerFn_of s m (by omega : (1:ℕ) ≤ l+1)] at hkq
      exact absurd hkq (not_le.mpr hjs1)
  have hkle : k ≤ l+1 := by
    by_contra hgt
    have h2 := hkmin (l+1) (by omega)
    rw [markerFn_of s m (by omega : l+1 ≤ l+1), hsT] at h2
    omega
  have hprevm : markerFn s m (k-1) < j :=
    Nat.lt_of_not_ge (hkmin (k-1) (by omega : k-1 < k))
  exact ⟨k, hk2, hkle, hprevm, hkq⟩

/-- Establishes legality, the slot-zero call bound, the logarithmic bound on amplified stages,
and the grouped weighted-cost bound in `TunableQueryTunableActualQueryComplexity`. See [Low
and Su, Proposition 6][LowSu2026] for the tunable VTAA query-complexity bound. -/
theorem TunableQueryTunableActualQueryComplexity_answer : TunableQueryTunableActualQueryComplexity := by
  intro H _instF _instD m P bad U ω α rs prices B hclock hstage hnorm hB0
  (try dsimp only)
  intro hplain htun habove hsumB
  have g8 := Clause8TunableUniversality_answer (H := H) m P bad U ω α rs hclock hstage hnorm hplain
  have g8f := (g8.1 ⟨htun, habove⟩).1
  have hlegalC : legal (m+1) (nestedWord (extendClock m P) bad ω rs m) :=
    legal_nested m P bad U ω α rs hclock hstage hnorm htun habove m (le_refl m)
  have hpostle := postAmplitude_le_one m P bad U ω rs hclock hstage hnorm hlegalC
  have hlossLB := totalLoss_ge m P bad U ω α rs hclock hstage hnorm hplain htun habove
  have hlosspos := totalLoss_pos m P bad U ω α rs htun habove
  have hcallsm := calls_nested m P bad U ω α rs hclock hstage hnorm htun habove m (le_refl m)
  set a := plainAmplitude (extendClock m P) bad U ω m with hdef
  have hPfullIco : (((∏ j : Fin m, (2*rs (j.val+1)+1)) : ℕ) : ℝ)
      = ∏ i ∈ Finset.Ico 1 (m+1), ((2*rs i+1 : ℕ) : ℝ) := by
    rw [Nat.cast_prod]
    exact Fin.prod_univ_eq_prod_range (fun i => ((2*rs (i+1)+1 : ℕ) : ℝ)) m |>.trans
      (prod_range_succ_eq_ico (fun i => ((2*rs i+1 : ℕ) : ℝ)) m)
  have hPfull1 : (1:ℝ) ≤ (((∏ j : Fin m, (2*rs (j.val+1)+1)) : ℕ) : ℝ) := by
    rw [hPfullIco]
    exact one_le_prod_real _ _ (fun i _ => rho_ge_one rs i)

  have h65Sum : ((6/5:ℝ)^(∑ j : Fin m, α (j.val+1)))
      * ((5/6:ℝ)^(∑ j : Fin m, α (j.val+1))) = 1 := by
    rw [show (6/5 : ℝ) = (5/6 : ℝ)⁻¹ from by norm_num, Real.inv_rpow (by norm_num)]
    exact inv_mul_cancel₀ (by positivity :
      ((5/6:ℝ)^(∑ j : Fin m, α (j.val+1))) ≠ 0)
  have hexp : (6/5:ℝ)^(∑ j : Fin m, α (j.val+1)) ≤ (6/5:ℝ)^B :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 6/5) hsumB
  have hfull : (((∏ j : Fin m, (2*rs (j.val+1)+1)) : ℕ) : ℝ) ≤ (6/5:ℝ)^B/a := by
    rw [(amplification_products_intended m P bad U ω α rs hclock hstage hnorm hplain
      htun habove).2.2]
    have hstep1 : postAmplitude (extendClock m P) bad ω U rs m
        / (plainAmplitude (extendClock m P) bad U ω m
            * totalLoss m (extendClock m P) bad U ω rs)
        ≤ ((6/5:ℝ)^(∑ j : Fin m, α (j.val+1)))/plainAmplitude (extendClock m P) bad U ω m := by
      rw [div_le_iff₀ (mul_pos hplain hlosspos), ← mul_assoc,
        div_mul_cancel₀ _ (ne_of_gt hplain)]
      have hXpos2 : (0:ℝ) < (6/5:ℝ)^(∑ j : Fin m, α (j.val+1)) := by positivity
      nlinarith [hpostle, hlossLB, h65Sum, hXpos2]
    have hstep2 : ((6/5:ℝ)^(∑ j : Fin m, α (j.val+1)))/plainAmplitude (extendClock m P) bad U ω m
        ≤ (6/5:ℝ)^B/plainAmplitude (extendClock m P) bad U ω m := by
      rw [div_le_iff₀ hplain, div_mul_cancel₀ _ (ne_of_gt hplain)]
      exact hexp
    exact le_trans hstep1 hstep2
  have hpart2 : ((calls (nestedWord (extendClock m P) bad ω rs m) 0 : ℕ) : ℝ)
      ≤ (6/5:ℝ)^B/a := by
    rw [hcallsm]
    exact hfull

  have hpart3 : (((Finset.univ.filter (fun j : Fin m => 0 < rs (j.val+1))).card : ℕ) : ℝ)
      ≤ (B*Real.log (6/5)+Real.log (1/a))/Real.log 3 := by
    have hT3 : (3:ℝ)^(Finset.univ.filter (fun j : Fin m => 0 < rs (j.val+1))).card
        ≤ (((∏ j : Fin m, (2*rs (j.val+1)+1)) : ℕ) : ℝ) := by
      have hf : ∀ j ∈ Finset.univ.filter (fun j : Fin m => 0 < rs (j.val+1)),
          (3:ℝ) ≤ ((2*rs (j.val+1)+1 : ℕ) : ℝ) := by
        intro j hj
        have hlt : 0 < rs (j.val+1) := (Finset.mem_filter.mp hj).2
        have : (3:ℕ) ≤ 2*rs (j.val+1)+1 := by omega
        exact_mod_cast this
      have h1 : (3:ℝ)^(Finset.univ.filter (fun j : Fin m => 0 < rs (j.val+1))).card
          = ∏ _j ∈ Finset.univ.filter (fun j : Fin m => 0 < rs (j.val+1)), 3 :=
        (Finset.prod_const _).symm
      rw [h1]
      refine le_trans (Finset.prod_le_prod₀ (fun j _ => by norm_num)
        (fun j hj => hf j hj)) ?_
      rw [Nat.cast_prod, ← Finset.prod_mul_prod_compl
        (Finset.univ.filter (fun j : Fin m => 0 < rs (j.val+1)))
        (fun j => ((2*rs (j.val+1)+1 : ℕ) : ℝ))]
      exact le_mul_of_one_le_right (Finset.prod_nonneg fun j _ => rho_nonneg rs (j.val+1))
        (one_le_prod_real _ _ (fun j _ => rho_ge_one rs (j.val+1)))
    have h3pos : (0:ℝ) < (3:ℝ)^(Finset.univ.filter (fun j : Fin m => 0 < rs (j.val+1))).card :=
      pow_pos (by norm_num) _
    have hXpos : (0:ℝ) < (6/5:ℝ)^B/a :=
      div_pos (by positivity : (0:ℝ) < (6/5:ℝ)^B) hplain
    have hlogle : Real.log ((3:ℝ)^(Finset.univ.filter
        (fun j : Fin m => 0 < rs (j.val+1))).card)
        ≤ Real.log ((6/5:ℝ)^B/a) := Real.log_le_log h3pos (le_trans hT3 hfull)
    have hlog3 : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    have hla : Real.log (1/a) = -Real.log a := by rw [one_div, Real.log_inv]
    have hlogR : Real.log ((6/5:ℝ)^B/a) = B*Real.log (6/5) + Real.log (1/a) := by
      have hd : Real.log ((6/5:ℝ)^B/a) = Real.log ((6/5:ℝ)^B) - Real.log a :=
        Real.log_div (ne_of_gt (by positivity : (0:ℝ) < (6/5:ℝ)^B)) (ne_of_gt hplain)
      have hr : Real.log ((6/5:ℝ)^B) = B*Real.log (6/5) :=
        Real.log_rpow (by norm_num : (0:ℝ) < 6/5) B
      rw [hd, hr, hla]
      ring
    rw [hlogR, Real.log_pow 3 _] at hlogle
    rwa [le_div_iff₀ hlog3]

  refine ⟨hlegalC, hpart2, hpart3, ?_⟩
  intro l s hs0 hsT hsmono hiff
  have hs0' : s ⟨0, by omega⟩ = 0 := hs0
  have hsT' : s ⟨l+1, by omega⟩ = m+1 := hsT
  have hsle : ∀ (x y : Fin (l+2)), x.val ≤ y.val → s x ≤ s y := by
    intro x y hxy
    have key : ∀ (k : ℕ) (z : Fin (l+2)), z.val = y.val - k → s z ≤ s y := by
      intro k
      induction k with
      | zero =>
        intro z hz
        have hzy : z = y := Fin.ext (by simpa using! hz)
        rw [hzy]
      | succ k ih =>
        intro z hz
        by_cases hk : y.val ≤ k
        · have hval : z.val = y.val - k := by omega
          have hzz : z = ⟨y.val - k, by omega⟩ := Fin.ext hval
          rw [hzz]
          exact ih ⟨y.val - k, by omega⟩ rfl
        · have hval : z.val + 1 = y.val - k := by omega
          have h4 := ih ⟨y.val - k, by omega⟩ rfl
          have he : s ⟨z.val+1, by omega⟩ = s ⟨y.val - k, by omega⟩ := by
            congr 1
            exact Fin.ext hval
          rw [← he] at h4
          exact le_trans (le_of_lt (hsmono ⟨z.val, by omega⟩)) h4
    exact key (y.val - x.val) x (by omega)
  have hsvle : ∀ v : Fin l, s ⟨v.val+1, by omega⟩ ≤ m := by
    intro v
    have hvl := v.isLt
    have h1 : s ⟨v.val+1, by omega⟩ < s ⟨v.val+2, by omega⟩ := hsmono ⟨v.val+1, by omega⟩
    have hv2 : v.val + 2 ≤ l + 1 := by omega
    have h2 : s ⟨v.val+2, by omega⟩ ≤ s ⟨l+1, by omega⟩ :=
      hsle ⟨v.val+2, by omega⟩ ⟨l+1, by omega⟩ hv2
    rw [hsT'] at h2
    omega
  have hsvge1 : ∀ v : Fin l, 1 ≤ s ⟨v.val+1, by omega⟩ := by
    intro v
    have hvl := v.isLt
    have h1 : s ⟨v.val, by omega⟩ < s ⟨v.val+1, by omega⟩ := hsmono ⟨v.val, by omega⟩
    have hv0 : (0:ℕ) ≤ v.val := by omega
    have h2 : s ⟨0, by omega⟩ ≤ s ⟨v.val, by omega⟩ :=
      hsle ⟨0, by omega⟩ ⟨v.val, by omega⟩ hv0
    rw [hs0'] at h2
    omega
  have hαpos : ∀ v : Fin l, 0 < α (s ⟨v.val+1, by omega⟩) := by
    intro v
    have hvl := v.isLt
    have ht1 : 1 ≤ s ⟨v.val+1, by omega⟩ := hsvge1 v
    have htm : s ⟨v.val+1, by omega⟩ ≤ m := hsvle v
    have hrst : 0 < rs (s ⟨v.val+1, by omega⟩) := by
      have h1 := hiff ⟨s ⟨v.val+1, by omega⟩ - 1, by omega⟩
      have h2 : (s ⟨v.val+1, by omega⟩ - 1) + 1 = s ⟨v.val+1, by omega⟩ := by omega
      rw [h2] at h1
      exact h1.mpr ⟨v, rfl⟩
    have hpos : 0 < preAmplitude (extendClock m P) bad ω U rs
        (s ⟨v.val+1, by omega⟩ - 1) :=
      (g8f ⟨s ⟨v.val+1, by omega⟩ - 1, by omega⟩).1
    have hmin0 : (2*(0:ℕ)+1) * preAmplitude (extendClock m P) bad ω U rs
        (s ⟨v.val+1, by omega⟩ - 1) < Real.sqrt (α (s ⟨v.val+1, by omega⟩))/3 := by
      have h2 : (s ⟨v.val+1, by omega⟩ - 1) + 1 = s ⟨v.val+1, by omega⟩ := by omega
      have hrst' : 0 < rs ((s ⟨v.val+1, by omega⟩ - 1) + 1) := by rw [h2]; exact hrst
      have h3 := (htun.2 (s ⟨v.val+1, by omega⟩ - 1) (by omega)).2.2 0 hrst'
      rwa [h2] at h3
    norm_num at hmin0
    have hsqrt : 0 < Real.sqrt (α (s ⟨v.val+1, by omega⟩)) := by
      nlinarith [hmin0, hpos]
    exact Real.sqrt_pos.mp hsqrt
  have hbnd : ∀ v : Fin l,
      ∏ i ∈ Finset.Ico (s ⟨v.val+1, by omega⟩+1) (m+1), ((2*rs i+1 : ℕ) : ℝ)
        ≤ (((∏ j : Fin m, (2*rs (j.val+1)+1)) : ℕ) : ℝ)
          * (3*plainAmplitude (extendClock m P) bad U ω (s ⟨v.val+1, by omega⟩))
          /Real.sqrt (α (s ⟨v.val+1, by omega⟩)) := by
    intro v
    have hvl := v.isLt
    have ht1 : 1 ≤ s ⟨v.val+1, by omega⟩ := hsvge1 v
    have htm : s ⟨v.val+1, by omega⟩ ≤ m := hsvle v
    have hplainpos : 0 < plainAmplitude (extendClock m P) bad U ω (s ⟨v.val+1, by omega⟩) :=
      plainAmplitude_pos m P bad U ω hclock hstage hplain _ htm
    exact sigma_split_bound rs ht1 (by omega) hplainpos
      (lt_of_lt_of_le zero_lt_one hPfull1) (hαpos v)
      (prefix_ge m P bad U ω α rs hclock hstage hnorm hplain htun habove ht1 htm) hPfullIco.symm
  have hW := cost_unroll m
    (fun j => weightedCost prices (nestedWord (extendClock m P) bad ω rs j)) rs prices
    (weightedCost_stageWord (H := H) prices 0)
    (fun j hj => cost_nested m P bad U ω α rs hclock hstage hnorm htun habove j hj prices)
  have hW' : weightedCost prices (nestedWord (extendClock m P) bad ω rs m)
      = ∑ j ∈ Finset.range (m+1), prices j *
        ∏ i ∈ Finset.Ico (max 1 j) (m+1), (2*rs i+1) := hW
  have hWreal : ((weightedCost prices (nestedWord (extendClock m P) bad ω rs m) : ℕ) : ℝ)
      = ∑ j ∈ Finset.range (m+1), (prices j : ℝ) * suffixProd m rs j := by
    rw [hW', Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.cast_mul, suffixProd_cast]
  have hfnn : ∀ j, 0 ≤ (prices j : ℝ) * suffixProd m rs j := by
    intro j
    rw [suffixProd]
    exact mul_nonneg (by exact_mod_cast (by omega : (0:ℕ) ≤ prices j))
      (Finset.prod_nonneg fun i _ => rho_nonneg rs i)

  have hcover : ∀ j ∈ Finset.range (m+1),
      j ∈ (Finset.Ico 0 (min (s ⟨1, by omega⟩) m + 1)) ∪
        ((Finset.univ.biUnion fun v : Fin l =>
          Finset.Ico (s ⟨v.val+1, by omega⟩+1) (min (s ⟨v.val+2, by omega⟩) m + 1))) := by
    intro j hj
    have hjm : j ≤ m := by simpa using! hj
    by_cases hj1 : j ≤ s ⟨1, by omega⟩
    · rw [Finset.mem_union]
      left
      rw [Finset.mem_Ico]
      omega
    · rw [Finset.mem_union]
      right
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      have hjs1 : s ⟨1, by omega⟩ < j := by omega
      obtain ⟨k, hk2, hkle, hprevm, hkqm⟩ := marker_lookup s m j hs0' hsT' hjs1 hjm
      rw [markerFn_of s m (by omega : k-1 ≤ l+1)] at hprevm
      rw [markerFn_of s m hkle] at hkqm
      have hv : k-2 < l := by omega
      refine ⟨⟨k-2, hv⟩, Finset.mem_Ico.mpr ⟨?_, ?_⟩⟩
      · have hfin1 : (⟨(⟨k-2, hv⟩ : Fin l).val + 1, by omega⟩ : Fin (l+2))
            = ⟨k-1, by omega⟩ := by
          refine Fin.ext ?_
          have hv' : (⟨k-2, hv⟩ : Fin l).val = k - 2 := rfl
          show (⟨k-2, hv⟩ : Fin l).val + 1 = k - 1
          rw [hv']
          omega
        rw [hfin1]
        exact Nat.succ_le_of_lt hprevm
      · have hfin2 : (⟨(⟨k-2, hv⟩ : Fin l).val + 2, by omega⟩ : Fin (l+2))
            = ⟨k, by omega⟩ := by
          refine Fin.ext ?_
          have hv' : (⟨k-2, hv⟩ : Fin l).val = k - 2 := rfl
          show (⟨k-2, hv⟩ : Fin l).val + 2 = k
          rw [hv']
          omega
        rw [hfin2]
        exact Nat.lt_succ_of_le (Nat.le_min.mpr ⟨hkqm, hjm⟩)
  have hB := Finset.sum_le_sum_of_subset_of_nonneg hcover (fun j _ _ => hfnn j)
  have hsplit2 := sum_bunion_le l (fun v : Fin l =>
      Finset.Ico (s ⟨v.val+1, by omega⟩+1) (min (s ⟨v.val+2, by omega⟩) m + 1))
    (fun j => (prices j : ℝ) * suffixProd m rs j) hfnn
  have hsplit1 := sum_union_le hfnn (Finset.Ico 0 (min (s ⟨1, by omega⟩) m + 1))
    ((Finset.univ.biUnion fun v : Fin l =>
      Finset.Ico (s ⟨v.val+1, by omega⟩+1) (min (s ⟨v.val+2, by omega⟩) m + 1)))
  have hsplit3 : ∑ j ∈ Finset.range (m+1), (prices j : ℝ) * suffixProd m rs j
      ≤ ∑ j ∈ Finset.Ico 0 (min (s ⟨1, by omega⟩) m + 1), (prices j : ℝ) * suffixProd m rs j
        + ∑ v : Fin l, ∑ j ∈ Finset.Ico (s ⟨v.val+1, by omega⟩+1)
            (min (s ⟨v.val+2, by omega⟩) m + 1), (prices j : ℝ) * suffixProd m rs j :=
    le_trans (le_trans hB hsplit1) (add_le_add (le_refl _) hsplit2)

  have hA0 : ∑ j ∈ Finset.Ico 0 (min (s ⟨1, by omega⟩) m + 1), (prices j : ℝ) * suffixProd m rs j
      ≤ ((prices 0 + blockFee prices m 0 (s ⟨1, by omega⟩) : ℕ) : ℝ)
        * (((∏ j : Fin m, (2*rs (j.val+1)+1)) : ℕ) : ℝ) := by
    have hle : ∀ j ∈ Finset.Ico 0 (min (s ⟨1, by omega⟩) m + 1),
        suffixProd m rs j ≤ (((∏ j : Fin m, (2*rs (j.val+1)+1)) : ℕ) : ℝ) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · rw [hj0, suffixProd_one]
        exact le_of_eq hPfullIco.symm
      · have hmax : max 1 j = j := Nat.max_eq_right (by omega)
        rw [suffixProd, hmax, hPfullIco]
        exact prod_ico_le_of_le rs (by omega : (1:ℕ) ≤ j) (by omega : j ≤ m+1)
    have hstep1 : ∑ j ∈ Finset.Ico 0 (min (s ⟨1, by omega⟩) m + 1),
          (prices j : ℝ) * suffixProd m rs j
        ≤ (∑ j ∈ Finset.Ico 0 (min (s ⟨1, by omega⟩) m + 1), (prices j : ℝ))
          * (((∏ j : Fin m, (2*rs (j.val+1)+1)) : ℕ) : ℝ) := by
      have hle' : ∑ j ∈ Finset.Ico 0 (min (s ⟨1, by omega⟩) m + 1),
            (prices j : ℝ) * suffixProd m rs j
          ≤ ∑ j ∈ Finset.Ico 0 (min (s ⟨1, by omega⟩) m + 1),
              (prices j : ℝ) * (((∏ j : Fin m, (2*rs (j.val+1)+1)) : ℕ) : ℝ) :=
        Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hle j hj)
          (by exact_mod_cast (by omega : (0:ℕ) ≤ prices j)))
      rw [Finset.sum_mul]
      exact hle'
    have hA0eq : ∑ j ∈ Finset.Ico 0 (min (s ⟨1, by omega⟩) m + 1), (prices j : ℝ)
        = ((prices 0 + blockFee prices m 0 (s ⟨1, by omega⟩) : ℕ) : ℝ) := by
      have hIco : Finset.Ico 0 (min (s ⟨1, by omega⟩) m + 1)
          = insert 0 (Finset.Ico 1 (min (s ⟨1, by omega⟩) m + 1)) := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_insert]
        omega
      rw [hIco, Finset.sum_insert (by simp only [Finset.mem_Ico]; omega),
        blockFee_eq prices m 0 (s ⟨1, by omega⟩), Nat.cast_add, Nat.cast_sum]
    refine le_trans hstep1 (mul_le_mul_of_nonneg_right (le_of_eq hA0eq) ?_)
    exact_mod_cast (by omega : (0:ℕ) ≤ ∏ j : Fin m, (2*rs (j.val+1)+1))

  have hAv : ∀ v : Fin l,
      ∑ j ∈ Finset.Ico (s ⟨v.val+1, by omega⟩+1) (min (s ⟨v.val+2, by omega⟩) m + 1),
          (prices j : ℝ) * suffixProd m rs j
        ≤ (∏ i ∈ Finset.Ico (s ⟨v.val+1, by omega⟩+1) (m+1), ((2*rs i+1 : ℕ) : ℝ))
          * ((blockFee prices m (s ⟨v.val+1, by omega⟩)
            (s ⟨v.val+2, by omega⟩) : ℕ) : ℝ) := by
    intro v
    have hvl := v.isLt
    have hle : ∀ j ∈ Finset.Ico (s ⟨v.val+1, by omega⟩+1)
          (min (s ⟨v.val+2, by omega⟩) m + 1),
        suffixProd m rs j
          ≤ ∏ i ∈ Finset.Ico (s ⟨v.val+1, by omega⟩+1) (m+1), ((2*rs i+1 : ℕ) : ℝ) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hj1 : 1 ≤ j := by omega
      have hmax : max 1 j = j := Nat.max_eq_right hj1
      have hlo : s ⟨v.val+1, by omega⟩+1 ≤ j := by omega
      have hhi : j ≤ m+1 := by omega
      rw [suffixProd, hmax]
      exact prod_ico_le_of_le rs hlo hhi
    have hstep1 : ∑ j ∈ Finset.Ico (s ⟨v.val+1, by omega⟩+1)
            (min (s ⟨v.val+2, by omega⟩) m + 1), (prices j : ℝ) * suffixProd m rs j
        ≤ (∑ j ∈ Finset.Ico (s ⟨v.val+1, by omega⟩+1)
            (min (s ⟨v.val+2, by omega⟩) m + 1), (prices j : ℝ))
          * ∏ i ∈ Finset.Ico (s ⟨v.val+1, by omega⟩+1) (m+1), ((2*rs i+1 : ℕ) : ℝ) := by
      have hle' : ∑ j ∈ Finset.Ico (s ⟨v.val+1, by omega⟩+1)
            (min (s ⟨v.val+2, by omega⟩) m + 1), (prices j : ℝ) * suffixProd m rs j
          ≤ ∑ j ∈ Finset.Ico (s ⟨v.val+1, by omega⟩+1)
              (min (s ⟨v.val+2, by omega⟩) m + 1), (prices j : ℝ)
            * ∏ i ∈ Finset.Ico (s ⟨v.val+1, by omega⟩+1) (m+1), ((2*rs i+1 : ℕ) : ℝ) :=
        Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hle j hj)
          (by exact_mod_cast (by omega : (0:ℕ) ≤ prices j)))
      rw [Finset.sum_mul]
      exact hle'
    refine le_trans hstep1 ((mul_le_mul_of_nonneg_right ?_
      (Finset.prod_nonneg fun i _ => rho_nonneg rs i)).trans_eq (mul_comm _ _))
    rw [blockFee_eq prices m (s ⟨v.val+1, by omega⟩) (s ⟨v.val+2, by omega⟩), Nat.cast_sum]

  have h65B : (0:ℝ) < (6/5:ℝ)^B := by positivity
  have h65B1 : (1:ℝ) ≤ (6/5:ℝ)^B := by
    have h1 : (6/5:ℝ)^((0:ℝ)) ≤ (6/5:ℝ)^B :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 6/5) hB0
    simpa using! h1
  have h2B : (6/5:ℝ)^(2*B) = (6/5:ℝ)^B * (6/5:ℝ)^B := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 6/5)]
    congr 1
    ring
  have hPa : (((∏ j : Fin m, (2*rs (j.val+1)+1)) : ℕ) : ℝ)
      * a ≤ (6/5:ℝ)^B := by
    have h1 := hfull
    rwa [le_div_iff₀ hplain] at h1
  have hPK : (((∏ j : Fin m, (2*rs (j.val+1)+1)) : ℕ) : ℝ)
      ≤ 6*(6/5:ℝ)^(2*B)/a := by
    rw [h2B, le_div_iff₀ hplain]
    nlinarith [hPa, h65B1, h65B]
  have hPK3 : (((∏ j : Fin m, (2*rs (j.val+1)+1)) : ℕ) : ℝ) * 3
      ≤ 6*(6/5:ℝ)^(2*B)/a := by
    rw [h2B, le_div_iff₀ hplain]
    nlinarith [hPa, h65B1, h65B]

  have hblock : ∀ v : Fin l,
      (∏ i ∈ Finset.Ico (s ⟨v.val+1, by omega⟩+1) (m+1), ((2*rs i+1 : ℕ) : ℝ))
        * ((blockFee prices m (s ⟨v.val+1, by omega⟩)
          (s ⟨v.val+2, by omega⟩) : ℕ) : ℝ)
        ≤ 6*(6/5:ℝ)^(2*B)/plainAmplitude (extendClock m P) bad U ω m
          * (plainAmplitude (extendClock m P) bad U ω (s ⟨v.val+1, by omega⟩)
            * ((blockFee prices m (s ⟨v.val+1, by omega⟩)
              (s ⟨v.val+2, by omega⟩) : ℕ) : ℝ)
            /Real.sqrt (α (s ⟨v.val+1, by omega⟩))) := by
    intro v
    have hvl := v.isLt
    have hb := hbnd v
    have hbfnn : (0:ℝ) ≤ ((blockFee prices m (s ⟨v.val+1, by omega⟩)
        (s ⟨v.val+2, by omega⟩) : ℕ) : ℝ) := by
      have h0 : (0:ℕ) ≤ blockFee prices m (s ⟨v.val+1, by omega⟩)
          (s ⟨v.val+2, by omega⟩) := by omega
      exact_mod_cast h0
    have hpnn : (0:ℝ) ≤ plainAmplitude (extendClock m P) bad U ω
        (s ⟨v.val+1, by omega⟩) := norm_nonneg _
    have hsqrt : (0:ℝ) < Real.sqrt (α (s ⟨v.val+1, by omega⟩)) :=
      Real.sqrt_pos.mpr (hαpos v)
    rw [le_div_iff₀ hsqrt] at hb
    have m1 := mul_le_mul_of_nonneg_right hb hbfnn
    have e3 : (((∏ j : Fin m, (2*rs (j.val+1)+1)) : ℕ) : ℝ) * 3
          * plainAmplitude (extendClock m P) bad U ω (s ⟨v.val+1, by omega⟩)
          * ((blockFee prices m (s ⟨v.val+1, by omega⟩)
            (s ⟨v.val+2, by omega⟩) : ℕ) : ℝ)
        ≤ (6*(6/5:ℝ)^(2*B)/plainAmplitude (extendClock m P) bad U ω m)
          * (plainAmplitude (extendClock m P) bad U ω (s ⟨v.val+1, by omega⟩)
            * ((blockFee prices m (s ⟨v.val+1, by omega⟩)
              (s ⟨v.val+2, by omega⟩) : ℕ) : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_right hPK3 (mul_nonneg hpnn hbfnn)
      nlinarith [hmul, hpnn, hbfnn]
    rw [← mul_div_assoc, le_div_iff₀ hsqrt]
    nlinarith [m1, e3]

  have hA0K : ((prices 0 + blockFee prices m 0 (s ⟨1, by omega⟩) : ℕ) : ℝ)
        * (((∏ j : Fin m, (2*rs (j.val+1)+1)) : ℕ) : ℝ)
      ≤ 6*(6/5:ℝ)^(2*B)/plainAmplitude (extendClock m P) bad U ω m
        * ((prices 0 + blockFee prices m 0 (s ⟨1, by omega⟩) : ℕ) : ℝ) := by
    have hx : (0:ℝ) ≤ ((prices 0 + blockFee prices m 0 (s ⟨1, by omega⟩) : ℕ) : ℝ) := by
      have h0 : (0:ℕ) ≤ prices 0 + blockFee prices m 0 (s ⟨1, by omega⟩) := by omega
      exact_mod_cast h0
    nlinarith [hPK, hx]
  rw [hWreal]
  refine le_trans (le_trans hsplit3
    (add_le_add hA0 (Finset.sum_le_sum (fun v _ => hAv v)))) ?_
  refine le_trans (add_le_add hA0K (Finset.sum_le_sum (fun v _ => hblock v))) ?_
  rw [mul_add, Finset.mul_sum]
  rfl

end Qatlib.Concepts.QlsReadoutSpec.Amplification
