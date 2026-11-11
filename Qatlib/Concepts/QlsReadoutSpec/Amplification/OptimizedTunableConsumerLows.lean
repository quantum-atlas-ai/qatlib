/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.OptimizedTunableConsumerStat
import Qatlib.Concepts.QlsReadoutSpec.ProgramModel.PaidWordSemanticsLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.ProjectorOrderLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.ClockFlagResolutionsLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.ActualNestedAmplificationLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.TunableUniversalityLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.OptimalThresholdAllocationLows

/-!
# Optimized tunable amplification with weighted costs

This module proves `OptimizedTunableOptimizedTunableConsumer_answer`, constructing a legal
nested amplification word with final potential amplitude at least 1/10. Its weighted cost is
bounded by a universal constant times the initial fees and a 2/3 quasinorm of intermediate
amplitude-weighted fees, divided by the final plain amplitude. The proof combines minimal round
schedules, an amplitude invariant, accumulated loss bounds, and threshold allocation.

Variable-time amplitude amplification provides the algorithmic background [Ambainis2012]. For
tunable VTAA query bounds, see [LowSu2026].

## Main statements

* `OptimizedTunableOptimizedTunableConsumer_answer`: Establishes the optimized tunable consumer
  specification.

## References

* [Ambainis, 2012][Ambainis2012]
* [Low and Su, 2026][LowSu2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QlsReadoutSpec.ProgramModel

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QlsReadoutSpec.Amplification

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Qatlib.Concepts.QlsReadoutSpec.Amplification

open Matrix Qatlib.Concepts.QlsReadoutSpec.Amplification
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false

/-- The extended clock agrees with the finite clock at every index at most `m`. -/
private theorem extendClock_eq {H : Type} (m : ℕ) (P : Fin (m+1) → Matrix H H ℂ)
    {j : ℕ} (hj : j ≤ m) : extendClock m P j = P ⟨j, by omega⟩ := by
  unfold extendClock
  simp [hj]

/-- A stage word is legal when its oracle index is less than `m + 1`. -/
private theorem legal_stageWord {H : Type} [Fintype H] [DecidableEq H] (m k : ℕ)
    (hk : k < m+1) : legal (m+1) (stageWord (H := H) k) := by
  intro s hs
  have hs2 : s = .call k Finset.univ false := List.eq_of_mem_singleton hs
  subst hs2
  simpa using! hk

/-- A concatenated word is legal exactly when both constituent words are legal. -/
private theorem legal_append_iff {H : Type} [Fintype H] [DecidableEq H] {r : ℕ} {slots : ℕ}
    (C D : Word H r) : legal slots (C ++ D) ↔ legal slots C ∧ legal slots D := by
  constructor
  · intro h
    constructor <;> intro s hs <;> exact h s (by simp_all)
  · intro h s hs
    rw [List.mem_append] at hs
    rcases hs with h' | h'
    · exact h.1 s h'
    · exact h.2 s h'

/-- The weighted cost of concatenating two words is the sum of their weighted costs. -/
private theorem weightedCost_append {H : Type} {r : ℕ}
    (prices : ℕ → ℕ) (C D : Word H r) :
    weightedCost prices (C ++ D) = weightedCost prices C + weightedCost prices D := by
  unfold weightedCost
  rw [List.map_append, List.sum_append]

/-- The weighted cost of a single stage word is the price of its oracle slot. -/
private theorem weightedCost_stageWord {H : Type} (prices : ℕ → ℕ) (k : ℕ) :
    weightedCost prices (stageWord (H := H) k) = prices k := by
  show (([.call k Finset.univ false] : Word H 1).map _).sum = _
  simp

/-- The plain prefix at stage zero consists of the stage-zero word. -/
private theorem plainPrefix_zero {H : Type} :
    plainPrefix 0 = (stageWord 0 : Word H 1) := by
  simp [plainPrefix, stageWord, List.range_succ]

/-- The next plain prefix appends the next stage word to the current prefix. -/
private theorem plainPrefix_succ {H : Type} (j : ℕ) :
    plainPrefix (H := H) (j+1) = plainPrefix j ++ stageWord (j+1) := by
  simp [plainPrefix, stageWord, List.range_succ, List.map_append]

/-- The clock state is the zero-clock slice obtained by applying the word matrix to the clean
input. -/
private theorem clockState_eq_run {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (C : Word H 1) (ω : QState H) :
    clockState U C ω = fun h => (wordMatrix U C *ᵥ clean 1 (Nat.zero_lt_one) ω) (h, (0 : Fin 1)) :=
  rfl

/-- On the unique clock sector, a fully controlled matrix acts as the underlying matrix on the
state slice. -/
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

/-- The matrix of a stage word is the corresponding oracle controlled on all clock values. -/
private theorem wordMatrix_stageWord {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (i : ℕ) :
    wordMatrix U (stageWord (H := H) i) = controlled (U i) Finset.univ := by
  simp [wordMatrix, stageWord]

/-- Appending a stage word applies its oracle matrix to the current clock state. -/
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

/-- The squared vector norm is the sum of the squared norms of its coordinates. -/
private theorem normVec_sq_eq {H : Type} [Fintype H] (v : QState H) :
    normVec v ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  show ‖toEuclidean_fromVec v‖ ^ 2 = _
  exact norm_toEuclidean_fromVec_sq v

/-- The vector norm is nonnegative. -/
private theorem normVec_nonneg {H : Type} [Fintype H] (v : QState H) :
    0 ≤ normVec v := norm_nonneg _

/-- Multiplication by a real scalar scales the vector norm by the scalar's absolute value. -/
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

/-- A vector has zero norm exactly when it is zero. -/
private theorem normVec_zero_iff {H : Type} [Fintype H] (v : QState H) :
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
      = ∑ h' : H, ‖run (by omega : (0:ℕ) < 1) U C ω (h', 0)‖ ^ 2 := rfl
  have h := normVec_sq_eq (clockState U C ω)
  rw [hkey, ← hsplit, hrun] at h
  have hnn : 0 ≤ normVec (clockState U C ω) := norm_nonneg _
  nlinarith

/-- Projecting the clock state of a legal unitary word on a normalized input gives norm at most
one. -/
private theorem normVec_clockState_le_one {H : Type} [Fintype H] [DecidableEq H]
    {slots : ℕ} (U : ℕ → Matrix H H ℂ) (C : Word H 1) (ω : QState H)
    (hU : ∀ j < slots, U j ∈ Matrix.unitaryGroup H ℂ)
    (hlegal : legal slots C) (hω : Normalized ω)
    (G : Matrix H H ℂ) (hG : IsOrthogonalProjector G) :
    normVec (G *ᵥ clockState U C ω) ≤ 1 := by
  have h := normVec_mul_proj_le G hG (clockState U C ω)
  rw [normVec_clockState_eq_one U C ω hU hlegal hω] at h
  exact h

/-- For `x` in the unit interval, `Real.arcsin x` is at most `(Real.pi / 2) * x`. -/
private theorem arcsin_le_pi_div_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.arcsin x ≤ (Real.pi / 2) * x := by
  have hmem : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, hx1⟩
  have hy : (Real.pi / 2) * x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    have hpi := Real.pi_pos
    refine ⟨?_, ?_⟩ <;> nlinarith
  have h := Real.arcsin_le_iff_le_sin hmem hy
  rw [h]
  exact Real.le_sin_mul hx0 hx1

/-- The complement of `potential Q bad` is the product `Q * bad`. -/
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

/-- The next potential applied after a legal stage annihilates every vector in the current
potential's complement. -/
private theorem collapse_apply {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) {j : ℕ} (hj : j < m)
    (v : QState H) :
    (potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ
      ((1 - potential (extendClock m P j) bad) *ᵥ v) = 0 := by
  rw [Matrix.mulVec_mulVec, collapse m P bad U hclock hstage hj, Matrix.zero_mulVec]

/-- The stage gain multiplier is the odd round factor multiplied by the corresponding
`gainLoss`. -/
private def lam {H : Type} [Fintype H] [DecidableEq H]
    (E : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (rs : ℕ → ℕ) (k : ℕ) : ℝ :=
  (2*rs (k+1)+1) * gainLoss (2*rs (k+1)+1) (preAmplitude E bad ω U rs k)

/-- Casting the stage gain multiplier to complex numbers preserves its product expression. -/
private theorem lam_eq {H : Type} [Fintype H] [DecidableEq H]
    (E : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (rs : ℕ → ℕ) (k : ℕ) :
    ((lam E bad U ω rs k : ℝ) : ℂ)
      = (((2*rs (k+1)+1 : ℕ) : ℂ) * ((gainLoss (2*rs (k+1)+1)
          (preAmplitude E bad ω U rs k) : ℝ) : ℂ)) := by
  unfold lam
  rw [Complex.ofReal_mul]
  push_cast
  rfl

/-- A valid schedule chooses at each stage the least round count whose linearized amplitude
reaches `Real.sqrt (α (j + 1)) / 3`, with nonnegative thresholds. -/
private def schedOK {H : Type} [Fintype H] [DecidableEq H]
    (E : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ j < m, 0 ≤ α (j+1) ∧
    Real.sqrt (α (j+1))/3 ≤ (2*rs (j+1)+1)*preAmplitude E bad ω U rs j ∧
    ∀ s < rs (j+1), (2*s+1)*preAmplitude E bad ω U rs j < Real.sqrt (α (j+1))/3

/-- Tunability is equivalent to the initial threshold being one and the remaining schedule
satisfying `schedOK`. -/
private theorem tunable_iff {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (E : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ) :
    tunable m E bad U ω α rs ↔ α 0 = 1 ∧ schedOK E bad U ω α rs m := by
  constructor
  · intro h
    exact ⟨h.1, fun j hj => h.2 j hj⟩
  · intro h
    exact ⟨h.1, fun j hj => h.2 j hj⟩

/-- A valid schedule remains valid when restricted to fewer stages. -/
private theorem schedOK_mono {H : Type} [Fintype H] [DecidableEq H]
    (E : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ) {m' m : ℕ} (h : m' ≤ m)
    (hs : schedOK E bad U ω α rs m) : schedOK E bad U ω α rs m' :=
  fun j hj => hs j (lt_of_lt_of_le hj h)

/-- A minimal odd amplification factor reaching a threshold at most 1/3 has amplified arcsine
angle at most `Real.pi / 2`. -/
private theorem noOvershoot_of {r : ℕ} {a t : ℝ}
    (ha0 : 0 ≤ a) (ht : t ≤ 1/3)
    (hmain : t ≤ ((2*r+1 : ℕ) : ℝ) * a)
    (hmin : ∀ s < r, ((2*s+1 : ℕ) : ℝ) * a < t) :
    ((2*r+1 : ℕ) : ℝ) * Real.arcsin a ≤ Real.pi / 2 := by
  rcases Nat.eq_zero_or_pos r with hz | hpos
  · subst hz
    have h1 : ((2*0+1 : ℕ) : ℝ) = 1 := by norm_num
    rw [h1, one_mul]
    exact Real.arcsin_le_pi_div_two a
  · have hσ1 : (1:ℝ) ≤ ((2*r-1 : ℕ) : ℝ) := by
      have : (1:ℕ) ≤ 2*r - 1 := by omega
      exact_mod_cast this
    have hσa : ((2*r-1 : ℕ) : ℝ) * a < t := by
      have h := hmin (r - 1) (by omega)
      have hkey : ((2 * (r - 1) + 1 : ℕ) : ℝ) = ((2*r-1 : ℕ) : ℝ) := by
        have h2 : (2 * (r - 1) + 1 : ℕ) = 2 * r - 1 := by omega
        exact_mod_cast h2
      rw [hkey] at h
      exact h
    have ha_lt : a < 1/3 := by
      have : a ≤ ((2*r-1 : ℕ) : ℝ) * a :=
        le_mul_of_one_le_left ha0 hσ1
      nlinarith
    have ha1 : a ≤ 1 := by linarith
    have hρ : ((2*r+1 : ℕ) : ℝ) = ((2*r-1 : ℕ) : ℝ) + 2 := by
      have h : (2*r+1 : ℕ) = (2*r-1 : ℕ) + 2 := by omega
      exact_mod_cast h
    have hρa : ((2*r+1 : ℕ) : ℝ) * a < 1 := by
      rw [hρ]
      nlinarith
    have hle := arcsin_le_pi_div_two_mul ha0 ha1
    have h2 : (0:ℝ) ≤ (2*r+1 : ℕ) := by
      have : 0 ≤ 2*r + 1 := by omega
      exact_mod_cast this
    have h3 : ((2*r+1 : ℕ) : ℝ) * Real.arcsin a
        ≤ ((2*r+1 : ℕ) : ℝ) * ((Real.pi / 2) * a) :=
      mul_le_mul_of_nonneg_left hle h2
    have h5 : ((2*r+1 : ℕ) : ℝ) * Real.arcsin a < Real.pi / 2 :=
      calc ((2*r+1 : ℕ) : ℝ) * Real.arcsin a
          ≤ ((2*r+1 : ℕ) : ℝ) * ((Real.pi / 2) * a) := h3
        _ = (Real.pi / 2) * (((2*r+1 : ℕ) : ℝ) * a) := by ring
        _ < (Real.pi / 2) * 1 := mul_lt_mul_of_pos_left hρa (by positivity)
        _ = Real.pi / 2 := by ring
    linarith

/-- A word containing only a known matrix makes no oracle calls. -/
private theorem calls_singleton_known {H : Type} {r : ℕ}
    (V : Matrix (Space H r) (Space H r) ℂ) (slot : ℕ) :
    calls [.known V] slot = 0 := rfl

/-- A word containing only a known matrix has zero weighted oracle cost. -/
private theorem weightedCost_singleton_known {H : Type} {r : ℕ}
    (prices : ℕ → ℕ) (V : Matrix (Space H r) (Space H r) ℂ) :
    weightedCost prices [.known V] = 0 := rfl

/-- A singleton word containing a known unitary matrix is legal. -/
private theorem legal_singleton_known {H : Type} [Fintype H] [DecidableEq H]
    (slots : ℕ) (V : Matrix (Space H 1) (Space H 1) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Space H 1) ℂ) : legal slots [.known V] := by
  intro t ht
  have ht' : t = .known V := List.mem_singleton.mp ht
  subst ht'
  exact hV

/-- Taking the formal adjoint of a word preserves its weighted oracle cost. -/
private theorem weightedCost_wordAdjoint {H : Type} {r : ℕ}
    (prices : ℕ → ℕ) (C : Word H r) :
    weightedCost prices (wordAdjoint C) = weightedCost prices C := by
  have hdef : ∀ D : Word H r, weightedCost prices D =
      ((D.map (fun (s : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H r) => match s with | .call j _ _ => prices j | _ => 0)).sum) :=
    fun _ => rfl
  rw [hdef (wordAdjoint C), hdef C, wordAdjoint_eq, List.map_map, List.map_reverse,
    List.sum_reverse]
  congr 1
  apply List.map_congr_left
  intro s _
  cases s with
  | known V => rfl
  | call i T a =>
    cases a with
    | true => rfl
    | false => rfl

/-- The negative identity matrix is unitary. -/
private theorem neg_one_unitary {n : Type} [Fintype n] [DecidableEq n] :
    (-1 : Matrix n n ℂ) ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  show (-1 : Matrix n n ℂ) * star (-1) = 1
  rw [star_neg, star_one, neg_mul_neg, one_mul]

/-- One amplification round consists of the target reflection, the adjoint word, the seed
reflection, the forward word, and a negative identity gate. -/
private def aaRound {H : Type} [Fintype H] [DecidableEq H]
    (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ) : Word H 1 :=
  ([.known (controlled (ReflectionAbout G) Finset.univ)] ++ wordAdjoint B ++
      [.known (controlled (ReflectionAbout (seedProjector ω)) Finset.univ)] ++ B ++
      [.known (-1)] : Word H 1)

/-- An amplification word consists of the initial word followed by the requested number of
amplification rounds. -/
private theorem aaWord_eq {H : Type} [Fintype H] [DecidableEq H]
    (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ) (s : ℕ) :
    aaWord B ω G s = B ++ (List.replicate s (aaRound B ω G)).flatten := rfl

/-- One amplification round makes twice as many calls to each oracle slot as the underlying
word. -/
private theorem calls_aaRound {H : Type} [Fintype H] [DecidableEq H]
    (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ) (j : ℕ) :
    calls (aaRound B ω G) j = 2 * calls B j := by
  show calls ([.known (controlled (ReflectionAbout G) Finset.univ)] ++ wordAdjoint B ++
      [.known (controlled (ReflectionAbout (seedProjector ω)) Finset.univ)] ++ B ++
      [.known (-1)]) j = _
  rw [calls_append, calls_append, calls_append, calls_append, calls_wordAdjoint,
    calls_singleton_known, calls_singleton_known, calls_singleton_known]
  ring

/-- One amplification round has twice the weighted oracle cost of the underlying word. -/
private theorem weightedCost_aaRound {H : Type} [Fintype H] [DecidableEq H]
    (prices : ℕ → ℕ) (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ) :
    weightedCost prices (aaRound B ω G) = 2 * weightedCost prices B := by
  show weightedCost prices ([.known (controlled (ReflectionAbout G) Finset.univ)] ++
      wordAdjoint B ++
      [.known (controlled (ReflectionAbout (seedProjector ω)) Finset.univ)] ++ B ++
      [.known (-1)]) = _
  rw [weightedCost_append, weightedCost_append, weightedCost_append, weightedCost_append,
    weightedCost_singleton_known, weightedCost_singleton_known, weightedCost_singleton_known,
    weightedCost_wordAdjoint]
  ring

/-- An amplification round is legal for a legal underlying word, an orthogonal target projector,
and a normalized seed. -/
private theorem legal_aaRound {H : Type} [Fintype H] [DecidableEq H]
    (slots : ℕ) (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ)
    (hG : IsOrthogonalProjector G) (hω : Normalized ω) (hB : legal slots B) :
    legal slots (aaRound B ω G) := by
  have hRG : legal slots
      ([.known (controlled (ReflectionAbout G) Finset.univ)] : Word H 1) :=
    legal_singleton_known slots _ (controlled_unitary (reflectionAbout_unitary hG) Finset.univ)
  have hRω : legal slots
      ([.known (controlled (ReflectionAbout (seedProjector ω)) Finset.univ)] : Word H 1) := by
    apply legal_singleton_known
    have hseed : seedProjector ω = outerProduct ω := pureDensity_eq_outerProduct ω
    rw [hseed]
    exact controlled_unitary (outerProduct_reflection_unitary hω) Finset.univ
  have hneg : legal slots [.known (-1 : Matrix (Space H 1) (Space H 1) ℂ)] :=
    legal_singleton_known slots (-1 : Matrix (Space H 1) (Space H 1) ℂ) neg_one_unitary
  have hAdj : legal slots (wordAdjoint B) := legal_wordAdjoint B hB
  intro t ht
  change t ∈ ([.known (controlled (ReflectionAbout G) Finset.univ)] ++ wordAdjoint B ++
      [.known (controlled (ReflectionAbout (seedProjector ω)) Finset.univ)] ++ B ++
      [.known (-1)] : Word H 1) at ht
  rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append] at ht
  simp only [List.mem_singleton] at ht
  simp only [or_assoc] at ht
  rcases ht with h | h | h | h | h
  · subst h
    exact controlled_unitary (reflectionAbout_unitary hG) Finset.univ
  · exact hAdj t h
  · subst h
    have hseed : seedProjector ω = outerProduct ω := pureDensity_eq_outerProduct ω
    rw [hseed]
    exact controlled_unitary (outerProduct_reflection_unitary hω) Finset.univ
  · exact hB t h
  · subst h
    exact neg_one_unitary

/-- Any finite repetition of legal amplification rounds is a legal word. -/
private theorem legal_flatten_replicate {H : Type} [Fintype H] [DecidableEq H]
    (slots : ℕ) (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ) (s : ℕ)
    (hG : IsOrthogonalProjector G) (hω : Normalized ω) (hB : legal slots B) :
    legal slots ((List.replicate s (aaRound B ω G)).flatten) := by
  induction s with
  | zero => intro t ht; simp at ht
  | succ s ih =>
    rw [List.replicate_succ, List.flatten_cons, legal_append_iff]
    exact ⟨legal_aaRound slots B ω G hG hω hB, ih⟩

/-- Repeating an amplification round `s` times multiplies each oracle call count by `s`. -/
private theorem calls_flatten_replicate {H : Type} [Fintype H] [DecidableEq H]
    (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ) (s : ℕ) (j : ℕ) :
    calls ((List.replicate s (aaRound B ω G)).flatten) j = s * calls (aaRound B ω G) j := by
  induction s with
  | zero => simp [calls]
  | succ s ih =>
    rw [List.replicate_succ, List.flatten_cons, calls_append, ih]
    ring

/-- Repeating an amplification round `s` times multiplies its weighted cost by `s`. -/
private theorem weightedCost_flatten_replicate {H : Type} [Fintype H] [DecidableEq H]
    (prices : ℕ → ℕ) (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ) (s : ℕ) :
    weightedCost prices ((List.replicate s (aaRound B ω G)).flatten)
      = s * weightedCost prices (aaRound B ω G) := by
  induction s with
  | zero => simp [weightedCost]
  | succ s ih =>
    rw [List.replicate_succ, List.flatten_cons, weightedCost_append, ih]
    ring

/-- Nested amplification words through stage `m` are legal for a legal clock and normalized
seed. -/
private theorem legal_nested {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ) (_U : ℕ → Matrix H H ℂ)
    (ω : QState H) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hnorm : Normalized ω) :
    ∀ j : ℕ, j ≤ m → legal (m+1) (nestedWord (extendClock m P) bad ω rs j) := by
  intro j
  induction j with
  | zero =>
    intro _
    exact legal_stageWord m 0 (by omega)
  | succ j ih =>
    intro hj
    have hjm : j < m := by omega
    have hEj1 : extendClock m P (j+1) = P ⟨j+1, by omega⟩ := extendClock_eq m P (by omega)
    have hGproj : IsOrthogonalProjector (potential (extendClock m P (j+1)) bad) := by
      have g3 := Clause3ClockFlagResolutions_answer H m P bad hclock
      have h := (g3.1 ⟨j+1, by omega⟩ ⟨j+1, by omega⟩ le_rfl).2.2.2.2.2.1
      rw [hEj1]
      exact h
    have hB : legal (m+1) (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) := by
      rw [legal_append_iff]
      exact ⟨ih (by omega), legal_stageWord m (j+1) (by omega)⟩
    have hleg := legal_flatten_replicate (m+1) (nestedWord (extendClock m P) bad ω rs j
      ++ stageWord (j+1)) ω (potential (extendClock m P (j+1)) bad) (rs (j+1))
      hGproj hnorm hB
    rw [show nestedWord (extendClock m P) bad ω rs (j+1)
        = aaWord (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) ω
            (potential (extendClock m P (j+1)) bad) (rs (j+1)) from rfl,
      aaWord_eq, legal_append_iff]
    exact ⟨hB, hleg⟩

/-- Appending the next stage to a nested amplification word preserves legality before the final
stage. -/
private theorem legal_B {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hnorm : Normalized ω) {j : ℕ} (hj : j < m) :
    legal (m+1) (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) := by
  rw [legal_append_iff]
  exact ⟨legal_nested m P bad U ω rs hclock hnorm j (by omega),
    legal_stageWord m (j+1) (by omega)⟩

/-- Stage legality implies that every oracle with index below `m + 1` is unitary. -/
private theorem stageLegal_units {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (U : ℕ → Matrix H H ℂ) (hstage : stageLegal m P U) :
    ∀ k < m+1, U k ∈ Matrix.unitaryGroup H ℂ := by
  intro k hk
  exact hstage.1 (⟨k, by omega⟩ : Fin (m+1))

/-- For legal clocks and stages and a normalized seed, each pre-amplification amplitude before
stage `m` is at most one. -/
private theorem preAmplitude_le_one {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    {j : ℕ} (hj : j < m) :
    preAmplitude (extendClock m P) bad ω U rs j ≤ 1 := by
  have hleg := legal_B m P bad U ω rs hclock hnorm hj
  have hEj1 : extendClock m P (j+1) = P ⟨j+1, by omega⟩ := extendClock_eq m P (by omega)
  have hGproj : IsOrthogonalProjector (potential (extendClock m P (j+1)) bad) := by
    have g3 := Clause3ClockFlagResolutions_answer H m P bad hclock
    have h := (g3.1 ⟨j+1, by omega⟩ ⟨j+1, by omega⟩ le_rfl).2.2.2.2.2.1
    rw [hEj1]
    exact h
  have h := normVec_clockState_le_one (U) (nestedWord (extendClock m P) bad ω rs j
      ++ stageWord (j+1)) ω (stageLegal_units m P U hstage) hleg hnorm
      (potential (extendClock m P (j+1)) bad) hGproj
  exact h

/-- Under a valid bounded-threshold schedule, the next projected nested state equals the
pre-amplification projected state scaled by the odd round factor and its gain loss. -/
private theorem clause5_at_stage {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    {j : ℕ} (hj : j < m)
    (hsched : schedOK (extendClock m P) bad U ω α rs (j+1)) (habove : ∀ j : Fin m, α (j.val+1) ≤ 1) :
    potential (extendClock m P (j+1)) bad *ᵥ
        clockState U (nestedWord (extendClock m P) bad ω rs (j+1)) ω
      = (((2*rs (j+1)+1 : ℕ) : ℂ)
          * ((gainLoss (2*rs (j+1)+1)
              (preAmplitude (extendClock m P) bad ω U rs j) : ℝ) : ℂ)) •
        (potential (extendClock m P (j+1)) bad *ᵥ
          clockState U (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) ω) := by
  have hEj1 : extendClock m P (j+1) = P ⟨j+1, by omega⟩ := extendClock_eq m P (by omega)
  have hGproj : IsOrthogonalProjector (potential (extendClock m P (j+1)) bad) := by
    have g3 := Clause3ClockFlagResolutions_answer H m P bad hclock
    have h := (g3.1 ⟨j+1, by omega⟩ ⟨j+1, by omega⟩ le_rfl).2.2.2.2.2.1
    rw [hEj1]
    exact h
  have hUunit : ∀ k < m+1, U k ∈ Matrix.unitaryGroup H ℂ := stageLegal_units m P U hstage
  have hsq3 : Real.sqrt (α (j+1))/3 ≤ 1/3 := by
    have hnn : 0 ≤ α (j+1) := (hsched j (by omega)).1
    have hle : α (j+1) ≤ 1 := habove ⟨j, hj⟩
    have hsq : Real.sqrt (α (j+1)) ≤ 1 := Real.sqrt_le_one.mpr hle
    exact div_le_div_of_nonneg_right hsq (by norm_num)
  have hmain : Real.sqrt (α (j+1))/3
      ≤ ((2*rs (j+1)+1 : ℕ) : ℝ) * preAmplitude (extendClock m P) bad ω U rs j := by
    have h := (hsched j (by omega)).2.1
    exact_mod_cast h
  have hmin : ∀ s < rs (j+1),
      ((2*s+1 : ℕ) : ℝ) * preAmplitude (extendClock m P) bad ω U rs j
        < Real.sqrt (α (j+1))/3 := by
    intro s hs
    have h := (hsched j (by omega)).2.2 s hs
    exact_mod_cast h
  have hno := noOvershoot_of (norm_nonneg _) hsq3 hmain hmin
  have hB : legal (m+1) (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) :=
    legal_B m P bad U ω rs hclock hnorm hj
  have hG5 := Clause5ActualNestedAmplification_answer H (m+1) U
    (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) ω
    (potential (extendClock m P (j+1)) bad) (rs (j+1))
    hUunit hB hnorm hGproj hno
  have hdef : nestedWord (extendClock m P) bad ω rs (j+1)
      = aaWord (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) ω
          (potential (extendClock m P (j+1)) bad) (rs (j+1)) := rfl
  rw [hdef]
  exact hG5.2.1

/-- The next nested word has weighted cost equal to its odd round factor times the sum of the
previous cost and the next stage price. -/
private theorem cost_nested {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (_hstage : stageLegal m P U) (hnorm : Normalized ω)
    (_hsched : schedOK (extendClock m P) bad U ω α rs m) (_habove : ∀ j : Fin m, α (j.val+1) ≤ 1)
    (j : ℕ) (hj : j < m) (prices : ℕ → ℕ) :
    weightedCost prices (nestedWord (extendClock m P) bad ω rs (j+1))
      = (2*rs (j+1)+1) *
        (weightedCost prices (nestedWord (extendClock m P) bad ω rs j) + prices (j+1)) := by
  have hleg := legal_B m P bad U ω rs hclock hnorm hj
  have hEj1 : extendClock m P (j+1) = P ⟨j+1, by omega⟩ := extendClock_eq m P (by omega)
  have hGproj : IsOrthogonalProjector (potential (extendClock m P (j+1)) bad) := by
    have g3 := Clause3ClockFlagResolutions_answer H m P bad hclock
    have h := (g3.1 ⟨j+1, by omega⟩ ⟨j+1, by omega⟩ le_rfl).2.2.2.2.2.1
    rw [hEj1]
    exact h
  rw [show nestedWord (extendClock m P) bad ω rs (j+1)
      = aaWord (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) ω
          (potential (extendClock m P (j+1)) bad) (rs (j+1)) from rfl,
    aaWord_eq, weightedCost_append, weightedCost_flatten_replicate,
    weightedCost_aaRound, weightedCost_append, weightedCost_stageWord]
  ring

/-- The absolute sine of a natural multiple of an angle is at most that multiple of the absolute
sine of the angle. -/
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

/-- For an amplitude in the unit interval, the sine of its amplified arcsine is bounded above by
the linear amplification factor. -/
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

/-- The gain loss factor is nonnegative for nonnegative amplitudes whose amplified angle is at
most `Real.pi / 2`. -/
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

/-- For a positive amplification factor and an amplitude in the unit interval without angle
overshoot, the gain loss is at least `2 / Real.pi`. -/
private theorem gainLoss_ge_two_div_pi {ρ : ℕ} {a : ℝ} (hρ : 0 < ρ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hang : ((ρ : ℝ) * Real.arcsin a) ≤ Real.pi / 2) :
    (2 / Real.pi : ℝ) ≤ gainLoss ρ a := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2pi : (2:ℝ) ≤ Real.pi :=
    le_trans (by norm_num : (2:ℝ) ≤ 3) (le_of_lt Real.pi_gt_three)
  unfold gainLoss
  split_ifs with ha0
  · exact (div_le_one₀ hpi).mpr h2pi
  · have hθ0 : 0 ≤ Real.arcsin a := (Real.arcsin_nonneg).mpr ha
    have hsinθ : Real.sin (Real.arcsin a) = a :=
      Real.sin_arcsin (by linarith) (by linarith)
    have harc_ge : a ≤ Real.arcsin a := by
      have h := Real.sin_le (x := Real.arcsin a) hθ0
      nlinarith [hsinθ]
    have hsin_ge : (2 / Real.pi : ℝ) * ((ρ : ℝ) * Real.arcsin a)
        ≤ Real.sin ((ρ : ℝ) * Real.arcsin a) := by
      set y := (ρ : ℝ) * Real.arcsin a with hy0
      have hyA : 0 ≤ (2 / Real.pi : ℝ) * y := by positivity
      have hy2 : y ≤ Real.pi / 2 := by rwa [hy0]
      have hyB : (2 / Real.pi : ℝ) * y ≤ 1 := by
        have h2 : (2 / Real.pi : ℝ) * y ≤ (2 / Real.pi) * (Real.pi / 2) :=
          mul_le_mul_of_nonneg_left hy2 (by positivity)
        have h3 : (2 / Real.pi : ℝ) * (Real.pi / 2) = 1 := by field_simp
        rw [h3] at h2
        exact h2
      have h := Real.le_sin_mul hyA hyB
      have hrew : Real.sin (Real.pi / 2 * ((2 / Real.pi) * y)) = Real.sin y := by
        field_simp
      rw [hrew] at h
      exact h
    have hρa : (ρ : ℝ) * a ≤ (ρ : ℝ) * Real.arcsin a :=
      mul_le_mul_of_nonneg_left harc_ge (Nat.cast_nonneg _)
    have hchain : (2 / Real.pi : ℝ) * ((ρ : ℝ) * a)
        ≤ (2 / Real.pi : ℝ) * ((ρ : ℝ) * Real.arcsin a) :=
      mul_le_mul_of_nonneg_left hρa (by positivity)
    have hden : 0 < (ρ : ℝ) * a := by positivity
    rw [le_div_iff₀ hden]
    exact le_trans hchain hsin_ge

/-- The complex cast of the empty product of stage gain multipliers is one. -/
private theorem prod_lam_zero {H : Type} [Fintype H] [DecidableEq H]
    (E : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (rs : ℕ → ℕ) :
    ((∏ k : Fin 0, lam E bad U ω rs k) : ℂ) = 1 := by
  simp

/-- The complex cast of the gain product through stage `j + 1` is the previous product times the
gain at stage `j`. -/
private theorem prod_lam_succ {j : ℕ} {H : Type} [Fintype H] [DecidableEq H]
    (E : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (rs : ℕ → ℕ) :
    ((∏ k : Fin (j+1), lam E bad U ω rs k) : ℂ)
      = ((∏ k : Fin j, lam E bad U ω rs k) : ℂ) * ((lam E bad U ω rs j : ℝ) : ℂ) := by
  have h := Finset.prod_range_succ (fun m : ℕ => (lam E bad U ω rs m : ℂ)) j
  rw [← Fin.prod_univ_eq_prod_range (fun m : ℕ => (lam E bad U ω rs m : ℂ)) (j+1)] at h
  rw [← Fin.prod_univ_eq_prod_range (fun m : ℕ => (lam E bad U ω rs m : ℂ)) j] at h
  exact h

/-- Under legal clocks and stages and a valid bounded-threshold schedule, the projected nested
state is the projected plain state scaled by the product of stage gain multipliers. -/
private theorem amplitude_invariant {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (habove : ∀ j : Fin m, α (j.val+1) ≤ 1) :
    ∀ j : ℕ, j ≤ m → schedOK (extendClock m P) bad U ω α rs j →
      potential (extendClock m P j) bad *ᵥ
          clockState U (nestedWord (extendClock m P) bad ω rs j) ω
        = ((∏ k : Fin j, lam (extendClock m P) bad U ω rs k) : ℂ) •
          (potential (extendClock m P j) bad *ᵥ clockState U (plainPrefix j) ω) := by
  intro j
  induction j with
  | zero =>
    intro _ _
    have hpot0 : potential (extendClock m P 0) bad = 1 := by
      have g3 := Clause3ClockFlagResolutions_answer H m P bad hclock
      have hE0 : extendClock m P 0 = P ⟨0, by omega⟩ := extendClock_eq m P (by omega)
      rw [hE0]
      exact g3.2.2.2.2.2.1
    rw [hpot0, show nestedWord (extendClock m P) bad ω rs 0 = stageWord 0 from rfl,
      plainPrefix_zero, prod_lam_zero]
    simp
  | succ j ih =>
    intro hj hschedj
    have hjm : j < m := by omega
    have hschedi : schedOK (extendClock m P) bad U ω α rs j :=
      schedOK_mono _ _ _ _ _ _ (by omega) hschedj
    have hg5 := clause5_at_stage m P bad U ω α rs hclock hstage hnorm hjm hschedj habove
    have hpre : clockState U (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) ω
        = U (j+1) *ᵥ clockState U (nestedWord (extendClock m P) bad ω rs j) ω :=
      clockState_append_stageWord U _ (j+1) ω
    have hprePlain : clockState U (plainPrefix (j+1)) ω
        = U (j+1) *ᵥ clockState U (plainPrefix j) ω := by
      rw [plainPrefix_succ, clockState_append_stageWord]
    have hsplit : ∀ v : QState H,
        (potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ v
          = (potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ
              (potential (extendClock m P j) bad *ᵥ v) := by
      intro v
      have hdecomp : v = potential (extendClock m P j) bad *ᵥ v
          + (1 - potential (extendClock m P j) bad) *ᵥ v :=
        (projector_decomp (potential (extendClock m P j) bad) v).symm
      conv_lhs => rw [hdecomp]
      rw [Matrix.mulVec_add, collapse_apply m P bad U hclock hstage hjm v, add_zero]

    have hLHS : potential (extendClock m P (j+1)) bad *ᵥ
        clockState U (nestedWord (extendClock m P) bad ω rs (j+1)) ω
        = ((lam (extendClock m P) bad U ω rs j : ℝ) : ℂ) •
          ((potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ
            clockState U (nestedWord (extendClock m P) bad ω rs j) ω) := by
      rw [hg5]
      have h1 : potential (extendClock m P (j+1)) bad *ᵥ
          clockState U (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) ω
          = (potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ
              clockState U (nestedWord (extendClock m P) bad ω rs j) ω := by
        rw [hpre, Matrix.mulVec_mulVec]
      rw [h1, ← lam_eq]

    have hcore : (potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ
        clockState U (nestedWord (extendClock m P) bad ω rs j) ω
        = ((∏ k : Fin j, lam (extendClock m P) bad U ω rs k) : ℂ) •
          ((potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ
            (potential (extendClock m P j) bad *ᵥ clockState U (plainPrefix j) ω)) := by
      rw [hsplit, ih (by omega) hschedi, Matrix.mulVec_smul]
    have hcollapse : (potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ
        (potential (extendClock m P j) bad *ᵥ clockState U (plainPrefix j) ω)
        = potential (extendClock m P (j+1)) bad *ᵥ clockState U (plainPrefix (j+1)) ω := by
      have h2 : potential (extendClock m P (j+1)) bad *ᵥ clockState U (plainPrefix (j+1)) ω
          = (potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ
              clockState U (plainPrefix j) ω := by
        rw [hprePlain, Matrix.mulVec_mulVec]
      rw [h2]
      exact (hsplit (clockState U (plainPrefix j) ω)).symm
    rw [hLHS, hcore, hcollapse]
    rw [← mul_smul, prod_lam_succ]
    congr 1
    ring

/-- Each stage gain multiplier is nonnegative under a valid schedule whose thresholds are at
most one. -/
private theorem lam_nonneg_all {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    {k : ℕ} (hk : k < m) (hsched : schedOK (extendClock m P) bad U ω α rs (k+1))
    (habove : ∀ j : Fin m, α (j.val+1) ≤ 1) :
    0 ≤ lam (extendClock m P) bad U ω rs k := by
  unfold lam
  have hsq3 : Real.sqrt (α (k+1))/3 ≤ 1/3 := by
    have hle : α (k+1) ≤ 1 := habove ⟨k, hk⟩
    have hsq : Real.sqrt (α (k+1)) ≤ 1 := Real.sqrt_le_one.mpr hle
    exact div_le_div_of_nonneg_right hsq (by norm_num)
  have hmain : Real.sqrt (α (k+1))/3
      ≤ ((2*rs (k+1)+1 : ℕ) : ℝ) * preAmplitude (extendClock m P) bad ω U rs k := by
    have h := (hsched k (by omega)).2.1
    exact_mod_cast h
  have hmin : ∀ s < rs (k+1),
      ((2*s+1 : ℕ) : ℝ) * preAmplitude (extendClock m P) bad ω U rs k
        < Real.sqrt (α (k+1))/3 := by
    intro s hs
    have h := (hsched k (by omega)).2.2 s hs
    exact_mod_cast h
  have hang := noOvershoot_of (norm_nonneg _) hsq3 hmain hmin
  have hg : 0 ≤ gainLoss (2*rs (k+1)+1) (preAmplitude (extendClock m P) bad ω U rs k) :=
    gainLoss_nonneg (norm_nonneg _) (by exact_mod_cast hang)
  positivity

/-- A finite product of nonnegative stage gain multipliers is nonnegative. -/
private theorem prod_lam_nonneg {j : ℕ} {H : Type} [Fintype H] [DecidableEq H]
    (E : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (rs : ℕ → ℕ)
    (h : ∀ k < j, 0 ≤ lam E bad U ω rs k) :
    0 ≤ ∏ k : Fin j, lam E bad U ω rs k :=
  Finset.prod_nonneg fun k _ => h k.val k.isLt

/-- Multiplication by a nonnegative real scalar scales the vector norm by that scalar. -/
private theorem normVec_smul_real_nonneg {H : Type} [Fintype H] (r : ℝ) (v : QState H)
    (hr : 0 ≤ r) : normVec ((r : ℂ) • v) = r * normVec v := by
  rw [normVec_smul_real, abs_of_nonneg hr]

/-- Multiplication by a complex scalar scales the vector norm by the norm of that scalar. -/
private theorem normVec_smul_abs {H : Type} [Fintype H] (c : ℂ) (v : QState H) :
    normVec (c • v) = ‖c‖ * normVec v := by
  show ‖toEuclidean_fromVec (c • v)‖ = ‖c‖ * ‖toEuclidean_fromVec v‖
  have h : toEuclidean_fromVec (c • v) = c • toEuclidean_fromVec v := rfl
  rw [h, norm_smul]

/-- The norm of a product of nonnegative stage gain multipliers cast to complex numbers equals
their real product. -/
private theorem norm_prod_lam {j : ℕ} {H : Type} [Fintype H] [DecidableEq H]
    (E : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (rs : ℕ → ℕ)
    (h : ∀ k < j, 0 ≤ lam E bad U ω rs k) :
    ‖(∏ k : Fin j, (lam E bad U ω rs k : ℂ))‖ = ∏ k : Fin j, lam E bad U ω rs k := by
  have h1 : (‖(∏ k : Fin j, (lam E bad U ω rs k : ℂ))‖ : ℝ)
      = (∏ k : Fin j, ‖(lam E bad U ω rs k : ℂ)‖) := by
    rw [norm_prod]
  have h2 : ∀ k : Fin j, ‖(lam E bad U ω rs k : ℂ)‖ = lam E bad U ω rs k := by
    intro k
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h k.val k.isLt)]
  rw [h1]
  exact Finset.prod_congr rfl fun k _ => h2 k

/-- For a valid bounded-threshold schedule, the pre-amplification amplitude is the next plain
amplitude multiplied by the preceding stage gain product. -/
private theorem preAmplitude_eq {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    {j : ℕ} (hj : j < m) (hsched : schedOK (extendClock m P) bad U ω α rs j)
    (habove : ∀ j : Fin m, α (j.val+1) ≤ 1) :
    preAmplitude (extendClock m P) bad ω U rs j
      = (∏ k : Fin j, lam (extendClock m P) bad U ω rs k)
        * plainAmplitude (extendClock m P) bad U ω (j+1) := by
  have hamp := amplitude_invariant m P bad U ω α rs hclock hstage hnorm habove j (by omega) hsched
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
      = (∏ k : Fin j, (lam (extendClock m P) bad U ω rs k : ℂ)) •
        (potential (extendClock m P (j+1)) bad *ᵥ clockState U (plainPrefix (j+1)) ω) := by
    rw [hpre, Matrix.mulVec_mulVec, hsplit, hamp, Matrix.mulVec_smul]
    have h2 : (potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ
        (potential (extendClock m P j) bad *ᵥ clockState U (plainPrefix j) ω)
        = potential (extendClock m P (j+1)) bad *ᵥ clockState U (plainPrefix (j+1)) ω := by
      have h3 : potential (extendClock m P (j+1)) bad *ᵥ clockState U (plainPrefix (j+1)) ω
          = (potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ
              clockState U (plainPrefix j) ω := by
        rw [hprePlain, Matrix.mulVec_mulVec]
      rw [h3]
      exact (hsplit (clockState U (plainPrefix j) ω)).symm
    rw [h2]
  have hprodf : ∀ k < j, 0 ≤ lam (extendClock m P) bad U ω rs k :=
    fun k hk => lam_nonneg_all m P bad U ω α rs (lt_of_lt_of_le hk (le_of_lt hj))
      (schedOK_mono _ _ _ _ _ _ (by omega) hsched) habove
  show normVec (potential (extendClock m P (j+1)) bad *ᵥ
    clockState U (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) ω) = _
  rw [hkey, normVec_smul_abs, norm_prod_lam _ _ _ _ _ hprodf]
  rfl

/-- For a valid bounded-threshold schedule, the final post-amplification amplitude is the final
plain amplitude multiplied by the stage gain product. -/
private theorem postAmplitude_eq {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (hsched : schedOK (extendClock m P) bad U ω α rs m) (habove : ∀ j : Fin m, α (j.val+1) ≤ 1) :
    postAmplitude (extendClock m P) bad ω U rs m
      = (∏ k : Fin m, lam (extendClock m P) bad U ω rs k)
        * plainAmplitude (extendClock m P) bad U ω m := by
  have hamp :=
      amplitude_invariant m P bad U ω α rs hclock hstage hnorm habove m le_rfl
      (schedOK_mono _ _ _ _ _ _ (by omega) hsched)
  have hprodf : ∀ k < m, 0 ≤ lam (extendClock m P) bad U ω rs k :=
    fun k hk => lam_nonneg_all m P bad U ω α rs hk (schedOK_mono _ _ _ _ _ _ (by omega) hsched) habove
  show normVec (potential (extendClock m P m) bad *ᵥ
    clockState U (nestedWord (extendClock m P) bad ω rs m) ω) = _
  rw [hamp, normVec_smul_abs]
  have hnorm : ‖(∏ k : Fin m, (lam (extendClock m P) bad U ω rs k : ℂ))‖
      = ∏ k : Fin m, lam (extendClock m P) bad U ω rs k :=
    norm_prod_lam _ _ _ _ _ hprodf
  rw [hnorm]
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
  have hGk : potential (extendClock m P k) bad *ᵥ clockState U (plainPrefix k) ω = 0 :=
    (normVec_zero_iff _).mp hz
  have hkey : potential (extendClock m P (k+1)) bad *ᵥ clockState U (plainPrefix (k+1)) ω = 0 := by
    rw [hprePlain, Matrix.mulVec_mulVec]
    rw [hsplit (clockState U (plainPrefix k) ω), hGk, Matrix.mulVec_zero]
  exact (normVec_zero_iff _).mpr hkey

/-- A positive final plain amplitude implies positivity of every preceding plain amplitude for
legal clocks and stages. -/
private theorem plainAmplitude_pos {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U)
    (ha : 0 < plainAmplitude (extendClock m P) bad U ω m) :
    ∀ k ≤ m, 0 < plainAmplitude (extendClock m P) bad U ω k := by
  intro k hk
  by_contra hne
  have hz : plainAmplitude (extendClock m P) bad U ω k = 0 := by
    have hnn : 0 ≤ plainAmplitude (extendClock m P) bad U ω k := norm_nonneg _
    exact le_antisymm (le_of_not_gt hne) hnn
  have hprop : ∀ t, k ≤ t → t ≤ m → plainAmplitude (extendClock m P) bad U ω t = 0 := by
    intro t hkt htm
    rcases Nat.exists_eq_add_of_le hkt with ⟨d, rfl⟩
    induction d with
    | zero => exact hz
    | succ d ih =>
      have hkm : k + d < m := by omega
      exact plainAmplitude_succ_of_zero m P bad U ω hclock hstage hkm (ih (by omega) (by omega))
  have hall : plainAmplitude (extendClock m P) bad U ω m = 0 := hprop m hk le_rfl
  exact lt_irrefl _ (lt_of_lt_of_le ha (le_of_eq hall))

/-- Positive plain amplitudes and a valid preceding schedule with thresholds at most one imply a
positive next pre-amplification amplitude. -/
private theorem preAmplitude_pos_of_sched {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (_hα0 : α 0 = 1) (hα1 : ∀ j : Fin m, α (j.val+1) ≤ 1)
    {j : ℕ} (hj : j < m)
    (hsched : ∀ i, i < j → 0 ≤ α (i+1) ∧
      Real.sqrt (α (i+1))/3 ≤ (2*rs (i+1)+1)*preAmplitude (extendClock m P) bad ω U rs i ∧
      ∀ s < rs (i+1), (2*s+1)*preAmplitude (extendClock m P) bad ω U rs i < Real.sqrt (α (i+1))/3)
    (hpos : ∀ k ≤ m, 0 < plainAmplitude (extendClock m P) bad U ω k) :
    0 < preAmplitude (extendClock m P) bad ω U rs j := by

  have hsq3 : ∀ i < j, Real.sqrt (α (i+1))/3 ≤ 1/3 := by
    intro i hi
    have hle : α (i+1) ≤ 1 := hα1 ⟨i, lt_of_lt_of_le hi (le_of_lt hj)⟩
    have hsq : Real.sqrt (α (i+1)) ≤ 1 := Real.sqrt_le_one.mpr hle
    exact div_le_div_of_nonneg_right hsq (by norm_num)
  have hang : ∀ i < j, ((2*rs (i+1)+1 : ℕ) : ℝ) *
      Real.arcsin (preAmplitude (extendClock m P) bad ω U rs i) ≤ Real.pi / 2 := by
    intro i hi
    have h1 := hsched i hi
    have hmain : Real.sqrt (α (i+1))/3
        ≤ ((2*rs (i+1)+1 : ℕ) : ℝ) * preAmplitude (extendClock m P) bad ω U rs i := by
      exact_mod_cast h1.2.1
    have hmin : ∀ s < rs (i+1),
        ((2*s+1 : ℕ) : ℝ) * preAmplitude (extendClock m P) bad ω U rs i
          < Real.sqrt (α (i+1))/3 := by
      intro s hs
      exact_mod_cast h1.2.2 s hs
    exact noOvershoot_of (norm_nonneg _) (hsq3 i hi) hmain hmin
  have hlam : ∀ i < j, 0 < lam (extendClock m P) bad U ω rs i := by
    intro i hi
    unfold lam
    have hg : 0 < gainLoss (2*rs (i+1)+1) (preAmplitude (extendClock m P) bad ω U rs i) := by
      by_cases ha0 : preAmplitude (extendClock m P) bad ω U rs i = 0
      · rw [ha0]
        show 0 < gainLoss (2*rs (i+1)+1) 0
        unfold gainLoss
        rw [if_pos rfl]
        norm_num
      · have ha : 0 < preAmplitude (extendClock m P) bad ω U rs i :=
          lt_of_le_of_ne (norm_nonneg _) (Ne.symm ha0)
        show 0 < (if preAmplitude (extendClock m P) bad ω U rs i = 0 then 1 else _)
        rw [if_neg ha0]
        have hsin : 0 < Real.sin ((2*rs (i+1)+1 : ℕ) * Real.arcsin
            (preAmplitude (extendClock m P) bad ω U rs i)) := by
          have hx0 : 0 < ((2*rs (i+1)+1 : ℕ) : ℝ) * Real.arcsin
              (preAmplitude (extendClock m P) bad ω U rs i) := by
            have hρ : 0 < ((2*rs (i+1)+1 : ℕ) : ℝ) := by
              have : 0 < 2*rs (i+1) + 1 := by omega
              exact_mod_cast this
            have harc : 0 < Real.arcsin (preAmplitude (extendClock m P) bad ω U rs i) :=
              Real.arcsin_pos.mpr ha
            positivity
          have hxπ : ((2*rs (i+1)+1 : ℕ) : ℝ) * Real.arcsin
              (preAmplitude (extendClock m P) bad ω U rs i) < Real.pi := by
            have hpi : (0:ℝ) < Real.pi := Real.pi_pos
            have h := hang i hi
            nlinarith
          exact Real.sin_pos_of_pos_of_lt_pi hx0 hxπ
        have hden : 0 < ((2*rs (i+1)+1 : ℕ) : ℝ) *
            preAmplitude (extendClock m P) bad ω U rs i := by
          have hρ : 0 < ((2*rs (i+1)+1 : ℕ) : ℝ) := by
            have : 0 < 2*rs (i+1) + 1 := by omega
            exact_mod_cast this
          positivity
        exact div_pos hsin hden
    have hρ : 0 < ((2*rs (i+1)+1 : ℕ) : ℝ) := by
      have : 0 < 2*rs (i+1) + 1 := by omega
      exact_mod_cast this
    positivity
  have hΛ : 0 < ∏ k : Fin j, lam (extendClock m P) bad U ω rs k := by
    exact Finset.prod_pos fun k _ => hlam k.val k.isLt
  have hA : 0 < plainAmplitude (extendClock m P) bad U ω (j+1) := hpos (j+1) (by omega)
  have hA' : 0 ≤ plainAmplitude (extendClock m P) bad U ω (j+1) := le_of_lt hA

  have hidentify : preAmplitude (extendClock m P) bad ω U rs j
      = (∏ k : Fin j, lam (extendClock m P) bad U ω rs k)
        * plainAmplitude (extendClock m P) bad U ω (j+1) := by
    exact preAmplitude_eq m P bad U ω α rs hclock hstage hnorm hj hsched hα1
  rw [hidentify]
  exact mul_pos hΛ hA

/-- Nested words through stage `j` agree when their round schedules agree through that stage. -/
private theorem nestedWord_congr {H : Type} [Fintype H] [DecidableEq H]
    (P : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (ω : QState H) (r r' : ℕ → ℕ) :
    ∀ j : ℕ, (∀ k, k ≤ j → r k = r' k) →
      nestedWord P bad ω r j = nestedWord P bad ω r' j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro h
    simp only [nestedWord, ih (fun k hk => h k (by omega)),
      h (j+1) (le_refl (j+1))]

/-- Pre-amplification amplitudes at stage `j` agree when the round schedules agree through that
stage. -/
private theorem preAmplitude_congr {H : Type} [Fintype H] [DecidableEq H]
    (P : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (r r' : ℕ → ℕ) :
    ∀ j : ℕ, (∀ k, k ≤ j → r k = r' k) →
      preAmplitude P bad ω U r j = preAmplitude P bad ω U r' j := by
  intro j h
  show normVec (potential (P (j+1)) bad *ᵥ
    clockState U (nestedWord P bad ω r j ++ stageWord (j+1)) ω) = _
  rw [nestedWord_congr P bad ω r r' j h]
  rfl

/-- Updating a round schedule at one index leaves its value at every distinct index unchanged. -/
private theorem upd_ne {r : ℕ → ℕ} {c : ℕ} (s : ℕ) {d : ℕ} (h : d ≠ c) :
    Function.update r c s d = r d := Function.update_of_ne h s r

/-- Every real threshold is reached by a least odd multiple of a positive pre-amplification
amplitude. -/
private theorem exists_min_rounds {t pre : ℝ} (hpre : 0 < pre) :
    ∃ s : ℕ, t ≤ (2*(s : ℝ)+1) * pre ∧
      ∀ s' < s, (2*(s' : ℝ)+1) * pre < t := by
  have hex : ∃ n : ℕ, t ≤ (2*(n : ℝ)+1) * pre := by
    obtain ⟨n, hn⟩ := exists_nat_ge (t/pre)
    refine ⟨n, ?_⟩
    have hrew : t = t/pre * pre := (div_mul_cancel₀ _ (ne_of_gt hpre)).symm
    rw [hrew]
    exact mul_le_mul_of_nonneg_right
      (le_trans hn (by nlinarith : ((n : ℝ)) ≤ 2*((n : ℝ))+1)) hpre.le
  obtain ⟨s, hmem, hmin⟩ :=
    Nat.findX (p := fun s : ℕ => t ≤ (2*(s : ℝ)+1) * pre) hex
  exact ⟨s, hmem, fun s' hs' => not_le.mp (hmin s' hs')⟩

/-- Legal clocks and stages, a normalized seed, thresholds in the unit interval, and a positive
final plain amplitude ensure the existence of a valid round schedule. -/
private theorem exists_sched {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (hα01 : α 0 = 1) (hα0 : ∀ j : Fin m, 0 ≤ α (j.val+1))
    (hα1 : ∀ j : Fin m, α (j.val+1) ≤ 1)
    (hplain : 0 < plainAmplitude (extendClock m P) bad U ω m) :
    ∃ rs : ℕ → ℕ, schedOK (extendClock m P) bad U ω α rs m := by
  have hpos : ∀ k ≤ m, 0 < plainAmplitude (extendClock m P) bad U ω k :=
    plainAmplitude_pos m P bad U ω hclock hstage hplain
  have key : ∀ j : ℕ, j ≤ m → ∃ r : ℕ → ℕ, schedOK (extendClock m P) bad U ω α r j := by
    intro j
    induction j with
    | zero => intro _; exact ⟨0, fun i hi => (Nat.not_lt_zero i hi).elim⟩
    | succ j ih =>
      intro hjm
      obtain ⟨r, hr⟩ := ih (by omega)
      have hprepos : 0 < preAmplitude (extendClock m P) bad ω U r j :=
        preAmplitude_pos_of_sched m P bad U ω α r hclock hstage hnorm hα01 hα1 (by omega) hr hpos
      obtain ⟨s, hmain, hmin⟩ := exists_min_rounds hprepos
      refine ⟨Function.update r (j+1) s, ?_⟩
      intro i hi
      rcases Nat.lt_or_ge i j with hlt | hge
      · have hcongr : preAmplitude (extendClock m P) bad ω U (Function.update r (j+1) s) i
            = preAmplitude (extendClock m P) bad ω U r i :=
          preAmplitude_congr (extendClock m P) bad U ω _ r i
            (fun k hk => upd_ne s (by omega))
        rw [show Function.update r (j+1) s (i+1) = r (i+1) from upd_ne s (by omega), hcongr]
        exact hr i hlt
      · have hie : i = j := by omega
        subst hie
        have hcongrj : preAmplitude (extendClock m P) bad ω U (Function.update r (i+1) s) i
            = preAmplitude (extendClock m P) bad ω U r i :=
          preAmplitude_congr (extendClock m P) bad U ω _ r i
            (fun k hk => upd_ne s (by omega))
        rw [hcongrj, Function.update_self]
        exact ⟨hα0 ⟨i, by omega⟩, hmain, hmin⟩
  exact key m (le_refl m)

/-- Casting an odd natural round factor to the reals agrees with forming the odd factor after
casting. -/
private theorem cast21 (x : ℕ) : (2 * (x : ℝ) + 1) = ((2 * x + 1 : ℕ) : ℝ) := by
  push_cast
  ring

/-- A tunable schedule with thresholds at most one keeps every amplified pre-amplitude angle at
most `Real.pi / 2`. -/
private theorem noOvershoot_tun {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (htun : tunable m (extendClock m P) bad U ω α rs)
    (habove : ∀ j : Fin m, α (j.val+1) ≤ 1) {j : ℕ} (hj : j < m) :
    ((2*rs (j+1)+1 : ℕ) : ℝ) * Real.arcsin (preAmplitude (extendClock m P) bad ω U rs j)
      ≤ Real.pi/2 := by
  have h1 := htun.2 j hj
  have hα1 : α (j+1) ≤ 1 := habove ⟨j, hj⟩
  have hsq3 : Real.sqrt (α (j+1))/3 ≤ 1/3 := by
    have hsq : Real.sqrt (α (j+1)) ≤ 1 := Real.sqrt_le_one.mpr hα1
    exact div_le_div_of_nonneg_right hsq (by norm_num)
  have hmain : Real.sqrt (α (j+1))/3 ≤ ((2*rs (j+1)+1 : ℕ) : ℝ)
      * preAmplitude (extendClock m P) bad ω U rs j :=
    by exact_mod_cast h1.2.1
  have hmin : ∀ s < rs (j+1), ((2*s+1 : ℕ) : ℝ)
      * preAmplitude (extendClock m P) bad ω U rs j < Real.sqrt (α (j+1))/3 := by
    intro s hs
    exact_mod_cast h1.2.2 s hs
  exact noOvershoot_of (norm_nonneg _) hsq3 hmain hmin

/-- Each stage gain loss is positive for a tunable schedule with thresholds at most one. -/
private theorem gainLoss_pos {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (htun : tunable m (extendClock m P) bad U ω α rs)
    (habove : ∀ j : Fin m, α (j.val+1) ≤ 1) (j : ℕ) (hj : j < m) :
    0 < gainLoss (2*rs (j+1)+1) (preAmplitude (extendClock m P) bad ω U rs j) := by
  unfold gainLoss
  by_cases ha : preAmplitude (extendClock m P) bad ω U rs j = 0
  · rw [if_pos ha]
    norm_num
  · rw [if_neg ha]
    set a := preAmplitude (extendClock m P) bad ω U rs j with haa
    have ha0 : 0 < a := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ha)
    have hno := noOvershoot_tun m P bad U ω α rs htun habove hj
    have hρ : 0 < ((2*rs (j+1)+1 : ℕ) : ℝ) := by
      have : 0 < 2*rs (j+1) + 1 := by omega
      exact_mod_cast this
    have harc_pos : 0 < Real.arcsin a := Real.arcsin_pos.mpr ha0
    have hx0 : 0 < ((2*rs (j+1)+1 : ℕ) : ℝ) * Real.arcsin a := mul_pos hρ harc_pos
    have hxπ : ((2*rs (j+1)+1 : ℕ) : ℝ) * Real.arcsin a < Real.pi := by
      have hpi : (0:ℝ) < Real.pi := Real.pi_pos
      nlinarith
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi hx0 hxπ) (mul_pos hρ ha0)

/-- The accumulated gain loss is positive for a tunable schedule with thresholds at most one. -/
private theorem totalLoss_pos {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (htun : tunable m (extendClock m P) bad U ω α rs)
    (habove : ∀ j : Fin m, α (j.val+1) ≤ 1) :
    0 < totalLoss m (extendClock m P) bad U ω rs :=
  Finset.prod_pos fun j _ => gainLoss_pos m P bad U ω α rs htun habove j.val j.isLt

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

/-- For legal clocks and stages and a normalized seed with positive final plain amplitude, a
tunable threshold budget of at most one gives total gain loss at least `5 / 6`. -/
private theorem totalLoss_ge_five_six {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (hplain : 0 < plainAmplitude (extendClock m P) bad U ω m)
    (htun : tunable m (extendClock m P) bad U ω α rs)
    (habove : ∀ j : Fin m, α (j.val+1) ≤ 1)
    (hsum : (∑ j : Fin m, α (j.val+1)) ≤ 1) :
    (5/6 : ℝ) ≤ totalLoss m (extendClock m P) bad U ω rs := by
  have hα0 : 0 ≤ ∑ j : Fin m, α (j.val+1) :=
    Finset.sum_nonneg fun j _ => (htun.2 j.val j.isLt).1
  have h8 := (Clause8TunableUniversality_answer (H := H) m P bad U ω α rs hclock hstage hnorm
    hplain).1 ⟨htun, habove⟩
  exact le_trans (five_six_anti hα0 hsum) h8.2

/-- For legal unitary stages and a normalized seed, the potential amplitude of a legal final
nested word is at most one. -/
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

/-- Every odd round factor is at least one as a real number. -/
private theorem rho_ge_one (rs : ℕ → ℕ) (i : ℕ) : (1:ℝ) ≤ ((2*rs i+1 : ℕ) : ℝ) := by
  have : 1 ≤ 2*rs i + 1 := by omega
  exact_mod_cast this

/-- Every odd round factor is nonnegative as a real number. -/
private theorem rho_nonneg (rs : ℕ → ℕ) (i : ℕ) : (0:ℝ) ≤ ((2*rs i+1 : ℕ) : ℝ) := by
  have : 0 ≤ 2*rs i + 1 := by omega
  exact_mod_cast this

/-- A finite product of real factors each at least one is at least one. -/
private theorem one_le_prod_real {ι : Type} (s : Finset ι) (f : ι → ℝ)
    (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i :=
  Finset.prod_induction f (fun x => 1 ≤ x)
    (fun a b ha hb => by
      have h1 : (1:ℝ)*1 ≤ a*b :=
        mul_le_mul ha hb zero_le_one (le_trans zero_le_one ha)
      simpa using! h1) (le_refl 1) h

/-- A product over successor indices of a range equals the product over the corresponding
interval starting at one. -/
private theorem prod_range_succ_eq_ico {M : Type} [CommMonoid M] (g : ℕ → M) (m : ℕ) :
    (∏ k ∈ Finset.range m, g (k+1)) = ∏ i ∈ Finset.Ico 1 (m+1), g i := by
  rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
  exact Finset.prod_congr rfl fun k _ => by rw [Nat.add_comm 1 k]

/-- The product of stage gain multipliers factors into the product of odd round factors and the
total gain loss. -/
private theorem prod_lam_split {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (E : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ) (ω : QState H)
    (rs : ℕ → ℕ) :
    (∏ k : Fin m, lam E bad U ω rs k)
      = (∏ k : Fin m, ((2*rs (k.val+1)+1 : ℕ) : ℝ)) * totalLoss m E bad U ω rs := by
  have h : ∀ k : Fin m, lam E bad U ω rs k
      = ((2*rs (k.val+1)+1 : ℕ) : ℝ)
        * gainLoss (2*rs (k.val+1)+1) (preAmplitude E bad ω U rs k.val) := by
    intro k
    unfold lam
    rw [cast21]
  rw [Finset.prod_congr rfl (fun k _ => h k), Finset.prod_mul_distrib]
  rfl

/-- The product of odd round factors indexed by `Fin m` equals the product over stages from one
through `m`. -/
private theorem prod_rho_ico {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (rs : ℕ → ℕ) :
    (∏ k : Fin m, ((2*rs (k.val+1)+1 : ℕ) : ℝ))
      = ∏ i ∈ Finset.Ico 1 (m+1), ((2*rs i+1 : ℕ) : ℝ) := by
  have h1 : ((∏ j : Fin m, (2*rs (j.val+1)+1) : ℕ) : ℝ)
      = ∏ i ∈ Finset.Ico 1 (m+1), ((2*rs i+1 : ℕ) : ℝ) := by
    rw [Nat.cast_prod]
    exact Fin.prod_univ_eq_prod_range (fun i => ((2*rs (i+1)+1 : ℕ) : ℝ)) m |>.trans
      (prod_range_succ_eq_ico (fun i => ((2*rs i+1 : ℕ) : ℝ)) m)
  exact (Nat.cast_prod (fun j : Fin m => 2*rs (j.val+1)+1) Finset.univ).symm.trans h1

/-- Under legal tunable amplification with threshold sum at most one, the product of odd round
factors is at most `(6 / 5)` divided by the final plain amplitude. -/
private theorem pf_bound {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (hplain : 0 < plainAmplitude (extendClock m P) bad U ω m)
    (htun : tunable m (extendClock m P) bad U ω α rs)
    (habove : ∀ j : Fin m, α (j.val+1) ≤ 1)
    (hsum : (∑ j : Fin m, α (j.val+1)) ≤ 1) :
    ∏ i ∈ Finset.Ico 1 (m+1), ((2*rs i+1 : ℕ) : ℝ)
      ≤ (6/5)/plainAmplitude (extendClock m P) bad U ω m := by
  have hsched : schedOK (extendClock m P) bad U ω α rs m :=
    ((tunable_iff m (extendClock m P) bad U ω α rs).mp htun).2
  have hΛa : (∏ k : Fin m, lam (extendClock m P) bad U ω rs k)
      * plainAmplitude (extendClock m P) bad U ω m ≤ 1 := by
    rw [← postAmplitude_eq m P bad U ω α rs hclock hstage hnorm hsched habove]
    exact postAmplitude_le_one m P bad U ω rs hclock hstage hnorm
      (legal_nested m P bad U ω rs hclock hnorm m (le_refl m))
  have h56 := totalLoss_ge_five_six m P bad U ω α rs hclock hstage hnorm hplain htun habove hsum
  have hTLpos : 0 < totalLoss m (extendClock m P) bad U ω rs :=
    totalLoss_pos m P bad U ω α rs htun habove
  have hicoΛ : (∏ i ∈ Finset.Ico 1 (m+1), ((2*rs i+1 : ℕ) : ℝ))
      = (∏ k : Fin m, lam (extendClock m P) bad U ω rs k)
        / totalLoss m (extendClock m P) bad U ω rs := by
    rw [eq_div_iff hTLpos.ne', ← prod_rho_ico (H := H) m rs,
      ← prod_lam_split m (extendClock m P) bad U ω rs]
  rw [hicoΛ, div_le_div_iff₀ hTLpos hplain]
  have hstep : (6/5 : ℝ)*(5/6)
      ≤ (6/5)*totalLoss m (extendClock m P) bad U ω rs :=
    mul_le_mul_of_nonneg_left h56 (by norm_num)
  have h65 : (6/5 : ℝ)*(5/6) = 1 := by norm_num
  rw [h65] at hstep
  nlinarith [hΛa, hstep]

/-- The suffix product multiplies odd round factors from `max 1 j` through the final stage `m`. -/
private def suffixProd (m : ℕ) (rs : ℕ → ℕ) (j : ℕ) : ℝ :=
  ∏ i ∈ Finset.Ico (max 1 j) (m+1), ((2*rs i+1 : ℕ) : ℝ)

/-- The suffix product at zero equals the full product of round factors from stage one through
`m`. -/
private theorem suffixProd_one (m : ℕ) (rs : ℕ → ℕ) :
    suffixProd m rs 0 = ∏ i ∈ Finset.Ico 1 (m+1), ((2*rs i+1 : ℕ) : ℝ) := by
  simp [suffixProd]

/-- For `j ≥ 1`, the suffix product starts at stage `j`. -/
private theorem suffixProd_succ (m : ℕ) (rs : ℕ → ℕ) (j : ℕ) (hj : 1 ≤ j) :
    suffixProd m rs j = ∏ i ∈ Finset.Ico j (m+1), ((2*rs i+1 : ℕ) : ℝ) := by
  rw [suffixProd, Nat.max_eq_right hj]

/-- A multiplicative cost recurrence expands as the sum of each stage price times its suffix
product of odd round factors. -/
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
  have hang := noOvershoot_tun m P bad U ω α rs htun habove hk
  refine ⟨mul_nonneg (by positivity : (0:ℝ) ≤ 2*((rs (k+1) : ℝ))+1)
    (gainLoss_nonneg ha hang), ?_⟩
  have hgl := gainLoss_le_one (ρ := 2*rs (k+1)+1)
    (a := preAmplitude (extendClock m P) bad ω U rs k) ha ha1
  unfold lam
  rw [cast21]
  exact mul_le_of_le_one_right (rho_nonneg rs (k+1)) hgl

/-- Under legal bounded-threshold tunable amplification, the prefix product of round factors is
at least the square root of the stage threshold divided by three times the stage plain
amplitude. -/
private theorem prefix_ge {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (hplain : 0 < plainAmplitude (extendClock m P) bad U ω m)
    (htun : tunable m (extendClock m P) bad U ω α rs) (habove : ∀ j : Fin m, α (j.val+1) ≤ 1)
    {s : ℕ} (hs1 : 1 ≤ s) (hsm : s ≤ m) :
    Real.sqrt (α s)/(3*plainAmplitude (extendClock m P) bad U ω s)
      ≤ ∏ i ∈ Finset.Ico 1 (s+1), ((2*rs i+1 : ℕ) : ℝ) := by
  have hschedM : schedOK (extendClock m P) bad U ω α rs m :=
    ((tunable_iff m (extendClock m P) bad U ω α rs).mp htun).2
  have hs' : (s-1)+1 = s := by omega
  have hpre := preAmplitude_eq m P bad U ω α rs hclock hstage hnorm (by omega : s-1 < m)
    (schedOK_mono (extendClock m P) bad U ω α rs (by omega : s-1 ≤ m) hschedM) habove
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

/-- A lower bound on a prefix product gives an upper bound on the complementary suffix product
in terms of the full product. -/
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

/-- A nonempty product indexed by `Fin m` splits into its first `m - 1` factors and its last
factor. -/
private theorem prod_fin_succ_last {M : Type} [CommMonoid M] (f : ℕ → M) {m : ℕ} (hm : 0 < m) :
    (∏ k : Fin m, f k.val) = (∏ k : Fin (m-1), f k.val) * f (m-1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n+1 := ⟨m-1, by omega⟩
  exact Fin.prod_univ_castSucc (fun k => f k.val)

/-- Sine is monotone between two ordered angles in the interval from zero to `Real.pi / 2`. -/
private theorem sin_monotone {x y : ℝ} (hxy : x ≤ y) (hx0 : 0 ≤ x) (hy : y ≤ Real.pi/2) :
    Real.sin x ≤ Real.sin y :=
  Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [Real.pi_pos, hx0]) hy hxy

/-- The arcsine of an amplitude in the unit interval is at least that amplitude. -/
private theorem arcsin_ge_self {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) : a ≤ Real.arcsin a := by
  have h := Real.sin_le (x := Real.arcsin a) (Real.arcsin_nonneg.mpr ha)
  rw [Real.sin_arcsin (by linarith) (by linarith)] at h
  exact h

/-- The sine of `Real.sqrt 2 / 6` is at least `1 / 10`. -/
private theorem sin_sqrt2_div_six_ge : 1/10 ≤ Real.sin (Real.sqrt 2/6) := by
  have h2 : (0:ℝ) ≤ 2 := by norm_num
  have hs2 : (6/5 : ℝ) ≤ Real.sqrt 2 := by
    have hsq : (6/5 : ℝ)^2 ≤ 2 := by norm_num
    have hnn : (0:ℝ) ≤ 6/5 := by norm_num
    have hsn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    nlinarith [Real.mul_self_sqrt h2, hsq, hnn, hsn]
  have hc : Real.pi/2 * (Real.sqrt 2/(3*Real.pi)) = Real.sqrt 2/6 := by
    field_simp
    ring
  have hc0 : 0 ≤ Real.sqrt 2/(3*Real.pi) := by positivity
  have hc1 : Real.sqrt 2/(3*Real.pi) ≤ 1 := by
    rw [div_le_one₀ (by positivity : (0:ℝ) < 3*Real.pi)]
    have hs2' : Real.sqrt 2 ≤ 2 := by nlinarith [Real.mul_self_sqrt h2]
    have h3p : (9:ℝ) < 3*Real.pi := by nlinarith [Real.pi_gt_three]
    nlinarith
  have hmain := Real.le_sin_mul hc0 hc1
  rw [hc] at hmain
  have hfinal : 1/10 ≤ Real.sqrt 2/(3*Real.pi) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 3*Real.pi)]
    have hπ4 : Real.pi < 4 := Real.pi_lt_four
    nlinarith [hπ4, hs2]
  linarith

/-- For a positive number of legal tunable stages with thresholds at most one and positive final
plain amplitude, the final post-amplitude is the sine of the final amplified pre-amplitude
angle. -/
private theorem postAmplitude_sin {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (hplain : 0 < plainAmplitude (extendClock m P) bad U ω m)
    (htun : tunable m (extendClock m P) bad U ω α rs) (habove : ∀ j : Fin m, α (j.val+1) ≤ 1)
    (hm : 0 < m) :
    postAmplitude (extendClock m P) bad ω U rs m
      = Real.sin (((2*rs m+1 : ℕ) : ℝ)
          * Real.arcsin (preAmplitude (extendClock m P) bad ω U rs (m-1))) := by
  have hschedM : schedOK (extendClock m P) bad U ω α rs m :=
    ((tunable_iff m (extendClock m P) bad U ω α rs).mp htun).2
  have hidx : (m-1)+1 = m := by omega
  have hlampos : ∀ k : Fin (m-1), 0 < lam (extendClock m P) bad U ω rs k := by
    intro k
    have hgl := gainLoss_pos m P bad U ω α rs htun habove k.val (by omega)
    unfold lam
    rw [cast21]
    exact mul_pos (by exact_mod_cast (by omega : 0 < 2*rs (k.val+1)+1)) hgl
  have hΛpos : 0 < ∏ k : Fin (m-1), lam (extendClock m P) bad U ω rs k :=
    Finset.prod_pos fun k _ => hlampos k
  have hprepos : 0 < preAmplitude (extendClock m P) bad ω U rs (m-1) :=
    ((Clause8TunableUniversality_answer (H := H) m P bad U ω α rs hclock hstage hnorm hplain).1
      ⟨htun, habove⟩).1 ⟨m-1, by omega⟩ |>.1
  have hρpos : 0 < ((2*rs ((m-1)+1)+1 : ℕ) : ℝ) :=
    by exact_mod_cast (by omega : 0 < 2*rs ((m-1)+1)+1)
  have hlamlast : lam (extendClock m P) bad U ω rs (m-1)
      = Real.sin (((2*rs ((m-1)+1)+1 : ℕ) : ℝ)
          * Real.arcsin (preAmplitude (extendClock m P) bad ω U rs (m-1)))
        / preAmplitude (extendClock m P) bad ω U rs (m-1) := by
    unfold lam gainLoss
    rw [if_neg (ne_of_gt hprepos), cast21]
    field_simp
  have hpre : preAmplitude (extendClock m P) bad ω U rs (m-1)
      = (∏ k : Fin (m-1), lam (extendClock m P) bad U ω rs k)
        * plainAmplitude (extendClock m P) bad U ω m := by
    have h := preAmplitude_eq m P bad U ω α rs hclock hstage hnorm (by omega : m-1 < m)
      (schedOK_mono (extendClock m P) bad U ω α rs (by omega : m-1 ≤ m) hschedM) habove
    rwa [hidx] at h
  rw [postAmplitude_eq m P bad U ω α rs hclock hstage hnorm hschedM habove,
    prod_fin_succ_last (f := fun k => lam (extendClock m P) bad U ω rs k) hm, hlamlast,
    show ((2*rs m+1 : ℕ) : ℝ) = ((2*rs ((m-1)+1)+1 : ℕ) : ℝ) from by rw [hidx]]
  obtain ⟨θ, hθ⟩ : ∃ θ, Real.arcsin (preAmplitude (extendClock m P) bad ω U rs (m-1)) = θ :=
    ⟨_, rfl⟩
  rw [hθ, hpre]
  have hΛne := ne_of_gt hΛpos
  have hane := ne_of_gt hplain
  field_simp

/-- For legal bounded-threshold tunable amplification with positive final plain amplitude and
final threshold `1 / 2`, the final post-amplitude is at least `1 / 10`. -/
private theorem postAmplitude_ge {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (hplain : 0 < plainAmplitude (extendClock m P) bad U ω m)
    (htun : tunable m (extendClock m P) bad U ω α rs) (habove : ∀ j : Fin m, α (j.val+1) ≤ 1)
    (hm : 0 < m) (hαm : α m = 1/2) :
    1/10 ≤ postAmplitude (extendClock m P) bad ω U rs m := by
  rw [postAmplitude_sin m P bad U ω α rs hclock hstage hnorm hplain htun habove hm]
  set θ := ((2*rs m+1 : ℕ) : ℝ)
      * Real.arcsin (preAmplitude (extendClock m P) bad ω U rs (m-1)) with hθdef
  have hprele : preAmplitude (extendClock m P) bad ω U rs (m-1) ≤ 1 :=
    preAmplitude_le_one m P bad U ω rs hclock hstage hnorm (by omega)
  have harcge : preAmplitude (extendClock m P) bad ω U rs (m-1)
      ≤ Real.arcsin (preAmplitude (extendClock m P) bad ω U rs (m-1)) :=
    arcsin_ge_self (norm_nonneg _) hprele
  have hmain : Real.sqrt (1/2)/3 ≤ ((2*rs m+1 : ℕ) : ℝ)
      * preAmplitude (extendClock m P) bad ω U rs (m-1) := by
    have h7 := (htun.2 (m-1) (by omega)).2.1
    rw [show (m-1)+1 = m from by omega, cast21 (rs m), hαm] at h7
    exact h7
  have hsqrt : Real.sqrt 2/6 = Real.sqrt (1/2)/3 := by
    have h2 : (0:ℝ) ≤ 2 := by norm_num
    have hkey : Real.sqrt (1/2)*Real.sqrt 2 = 1 := by
      rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 1/2) 2,
        show (1/2 : ℝ)*2 = 1 from by norm_num, Real.sqrt_one]
    rw [div_eq_div_iff (by norm_num : (6:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0)]
    nlinarith [hkey, Real.mul_self_sqrt h2, Real.sqrt_nonneg 2, Real.sqrt_nonneg (1/2)]
  have hθlo : Real.sqrt 2/6 ≤ θ := by
    rw [hθdef]
    exact le_trans (le_trans (le_of_eq hsqrt) hmain) (mul_le_mul_of_nonneg_left harcge
      (by exact_mod_cast (by omega : (0:ℕ) ≤ 2*rs m+1)))
  have hθhi : θ ≤ Real.pi/2 := by
    have h := noOvershoot_tun m P bad U ω α rs htun habove (j := m-1) (by omega)
    rw [show (m-1)+1 = m from by omega] at h
    exact h
  exact le_trans sin_sqrt2_div_six_ge (sin_monotone hθlo (by positivity) hθhi)

/-- For nonnegative `x`, division by `Real.sqrt ((1 / 2) * x)` equals `Real.sqrt 2` times
division by `Real.sqrt x`. -/
private theorem div_sqrt_half {w x : ℝ} (hx : 0 ≤ x) :
    w/Real.sqrt ((1/2)*x) = Real.sqrt 2 * (w/Real.sqrt x) := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · subst h0
    simp
  · have hx2 : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
    have hs2 : Real.sqrt 2 ≠ 0 := by positivity
    have hh : Real.sqrt ((1/2)*x) = Real.sqrt x/Real.sqrt 2 := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 1/2) x,
        Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1) 2, Real.sqrt_one]
      ring
    rw [hh]
    field_simp

/-- The real cast of the natural suffix product of odd round factors equals `suffixProd`. -/
private theorem suffixProd_cast (m : ℕ) (rs : ℕ → ℕ) (j : ℕ) :
    ((∏ i ∈ Finset.Ico (max 1 j) (m+1), (2*rs i+1) : ℕ) : ℝ) = suffixProd m rs j := by
  rw [suffixProd, Nat.cast_prod]

/-- Establishes a universal weighted-cost bound for legal tunable nested amplification with
final amplitude at least `1 / 10`, as specified by
`OptimizedTunableOptimizedTunableConsumer`. The cost analysis develops the tunable VTAA
bound of [Low and Su, Proposition 6][LowSu2026]. -/
theorem OptimizedTunableOptimizedTunableConsumer_answer : OptimizedTunableOptimizedTunableConsumer := by
  refine ⟨6, by norm_num, ?_⟩
  intro H _instF _instD m P bad U ω prices hm hclock hstage hnorm
  (try dsimp only)
  intro ha
  set a := plainAmplitude (extendClock m P) bad U ω m with ha_def
  have hposAll : ∀ k ≤ m, 0 < plainAmplitude (extendClock m P) bad U ω k :=
    plainAmplitude_pos m P bad U ω hclock hstage ha
  obtain ⟨w, hw⟩ : ∃ w : Fin (m-1) → ℝ, ∀ j, w j =
      plainAmplitude (extendClock m P) bad U ω (j.val+1)*(prices (j.val+2) : ℝ) :=
    ⟨_, fun _ => rfl⟩
  have hw_nn : ∀ j, 0 ≤ w j := by
    intro j
    rw [hw]
    exact mul_nonneg (le_of_lt (hposAll _ (by omega)))
      (by exact_mod_cast (by omega : (0:ℕ) ≤ prices _))
  obtain ⟨α, hα_def⟩ : ∃ α : ℕ → ℝ, ∀ k, α k = if k = 0 then 1 else
      if k = m then 1/2 else
      if h : k-1 < m-1 then (1/2)*(w ⟨k-1, h⟩).rpow (2/3)
        /(∑ i : Fin (m-1), (w i).rpow (2/3)) else 0 := ⟨_, fun _ => rfl⟩
  have hα0eq : α 0 = 1 := by rw [hα_def, if_pos rfl]
  have hαm : α m = 1/2 := by
    rw [hα_def, if_neg (by omega : ¬(m = 0)), if_pos rfl]
  have hαint : ∀ j : Fin (m-1), α (j.val+1)
      = (1/2)*(w j).rpow (2/3)/(∑ i : Fin (m-1), (w i).rpow (2/3)) := by
    intro j
    have hkey : α (j.val+1)
        = (1/2)*(w ⟨j.val, by omega⟩).rpow (2/3)
          /(∑ i : Fin (m-1), (w i).rpow (2/3)) := by
      rw [hα_def, if_neg (by omega : ¬(j.val+1 = 0)),
        if_neg (by omega : ¬(j.val+1 = m)), dif_pos (show j.val+1-1 < m-1 by omega)]
      rfl
    exact hkey
  have hWnn : (0:ℝ) ≤ ∑ i : Fin (m-1), (w i).rpow (2/3) :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hw_nn i) _
  have hαnn : ∀ j : Fin m, 0 ≤ α (j.val+1) := by
    intro j
    rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt j.isLt) with h | h
    · rw [show j.val+1 = m from h, hαm]
      norm_num
    · rw [hαint ⟨j.val, by omega⟩]
      exact div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (hw_nn _) _)) hWnn
  have hαnnAll : ∀ k' : ℕ, 0 ≤ α k' := by
    intro k'
    rw [hα_def]
    split
    · norm_num
    · split
      · norm_num
      · split
        · exact div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (hw_nn _) _)) hWnn
        · norm_num
  have hα1 : ∀ j : Fin m, α (j.val+1) ≤ 1 := by
    intro j
    rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt j.isLt) with h | h
    · rw [show j.val+1 = m from h, hαm]
      norm_num
    · have hj : j.val < m-1 := by omega
      rw [hαint ⟨j.val, by omega⟩]
      by_cases hW : (∑ i : Fin (m-1), (w i).rpow (2/3)) = 0
      · have hz : (1/2)*(w ⟨j.val, by omega⟩).rpow (2/3)
            /(∑ i : Fin (m-1), (w i).rpow (2/3)) = 0 :=
          div_eq_zero_iff.mpr (Or.inr hW)
        rw [hz]
        norm_num
      · have hWpos : 0 < ∑ i : Fin (m-1), (w i).rpow (2/3) :=
          lt_of_le_of_ne hWnn (Ne.symm hW)
        have hle : (w ⟨j.val, by omega⟩).rpow (2/3) ≤ ∑ i : Fin (m-1), (w i).rpow (2/3) :=
          Finset.single_le_sum (fun i _ => Real.rpow_nonneg (hw_nn i) _) (Finset.mem_univ _)
        have hdiv : (w ⟨j.val, by omega⟩).rpow (2/3)
            /(∑ i : Fin (m-1), (w i).rpow (2/3)) ≤ 1 := (div_le_one hWpos).mpr hle
        have hstep : ((1/2 : ℝ)*(w ⟨j.val, by omega⟩).rpow (2/3))
            /(∑ i : Fin (m-1), (w i).rpow (2/3)) ≤ (1/2)*1 := by
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hdiv (by norm_num)
        exact le_trans hstep (by norm_num : ((1/2 : ℝ)*1) ≤ 1)
  have hsumα : (∑ j : Fin m, α (j.val+1)) ≤ 1 := by
    have hintbound : ∑ j : Fin (m-1), ((w j).rpow (2/3)
        /(∑ i : Fin (m-1), (w i).rpow (2/3))) ≤ 1 := by
      by_cases hW : (∑ i : Fin (m-1), (w i).rpow (2/3)) = 0
      · have hz : ∀ j : Fin (m-1), (w j).rpow (2/3) = 0 :=
          fun j => Finset.sum_eq_zero_iff_of_nonneg
            (fun i _ => Real.rpow_nonneg (hw_nn i) _) |>.mp hW j (Finset.mem_univ j)
        have hzero : ∑ j : Fin (m-1), ((w j).rpow (2/3)
            /(∑ i : Fin (m-1), (w i).rpow (2/3))) = 0 :=
          Finset.sum_eq_zero fun j _ => by rw [hz j, zero_div]
        rw [hzero]
        norm_num
      · have hEq : ∑ j : Fin (m-1), ((w j).rpow (2/3)
          /(∑ i : Fin (m-1), (w i).rpow (2/3))) = 1 := by
          rw [Finset.sum_congr rfl (fun j _ => div_eq_mul_inv _ _), ← Finset.sum_mul,
            mul_inv_cancel₀ (ne_of_gt (lt_of_le_of_ne hWnn (Ne.symm hW)))]
        rw [hEq]
    have hint3 : ∑ j : Fin (m-1), α (j.val+1)
        = (1/2)*∑ j : Fin (m-1), ((w j).rpow (2/3)
            /(∑ i : Fin (m-1), (w i).rpow (2/3))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hαint j, mul_div_assoc]
    have hint2 : ∑ j ∈ Finset.range (m-1), α (j+1) = ∑ j : Fin (m-1), α (j.val+1) :=
      (Fin.sum_univ_eq_sum_range (fun j => α (j+1)) (m-1)).symm
    have hconv : ∑ j : Fin m, α (j.val+1) = ∑ j ∈ Finset.range m, α (j+1) :=
      Fin.sum_univ_eq_sum_range (fun j => α (j+1)) m
    have hgen : ∑ j ∈ Finset.range m, α (j+1)
        = ∑ j ∈ Finset.range (m-1), α (j+1) + α m := by
      have h := Finset.sum_range_succ (fun j => α (j+1)) (m-1)
      rwa [show (m-1)+1 = m from by omega] at h
    rw [hconv, hgen, hαm, hint2, hint3]
    nlinarith [hintbound]
  obtain ⟨rs, hsched⟩ := exists_sched m P bad U ω α hclock hstage hnorm hα0eq hαnn hα1 ha
  have htun : tunable m (extendClock m P) bad U ω α rs :=
    (tunable_iff m (extendClock m P) bad U ω α rs).mpr ⟨hα0eq, hsched⟩
  refine ⟨α, rs, htun, hα1, hsumα, ?_, ?_, ?_⟩
  · exact legal_nested m P bad U ω rs hclock hnorm m (le_refl m)
  · exact postAmplitude_ge m P bad U ω α rs hclock hstage hnorm ha htun hα1 hm hαm

  have hpfK : suffixProd m rs 0 ≤ (6/5)/a :=
    pf_bound m P bad U ω α rs hclock hstage hnorm ha htun hα1 hsumα
  have hprnn : ∀ j, 0 ≤ (prices j : ℝ) := fun j =>
    by exact_mod_cast (by omega : (0:ℕ) ≤ prices j)
  have hW := cost_unroll m (fun j => weightedCost prices (nestedWord (extendClock m P) bad ω rs j))
    rs prices (weightedCost_stageWord (H := H) prices 0)
    (fun j hj => cost_nested m P bad U ω α rs hclock hstage hnorm hsched hα1 j hj prices)
  have hWreal : ((weightedCost prices (nestedWord (extendClock m P) bad ω rs m) : ℕ) : ℝ)
      = ∑ j ∈ Finset.range (m+1), (prices j : ℝ) * suffixProd m rs j := by
    have hbeta : (fun j => weightedCost prices (nestedWord (extendClock m P) bad ω rs j)) m
        = weightedCost prices (nestedWord (extendClock m P) bad ω rs m) := rfl
    rw [hW, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.cast_mul, suffixProd_cast]
  have hsplit : ∑ j ∈ Finset.range (m+1), (prices j : ℝ) * suffixProd m rs j
      = (prices 0 : ℝ) * suffixProd m rs 0 + ((prices 1 : ℝ) * suffixProd m rs 0
        + ∑ k ∈ Finset.Ico 2 (m+1), (prices k : ℝ) * suffixProd m rs k) := by
    have hset : Finset.range (m+1) = insert 0 (insert 1 (Finset.Ico 2 (m+1))) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    have hs1 : suffixProd m rs 1 = suffixProd m rs 0 := by simp [suffixProd]
    rw [hset, Finset.sum_insert (by simp), Finset.sum_insert (by simp), hs1]
  have hpfpos : 0 < suffixProd m rs 0 := by
    rw [suffixProd_one]
    exact lt_of_lt_of_le (by norm_num) (one_le_prod_real _ _ (fun i _ => rho_ge_one rs i))
  have hTerm : ∀ k ∈ Finset.Ico 2 (m+1), (prices k : ℝ) * suffixProd m rs k
      ≤ suffixProd m rs 0 * 3 * (plainAmplitude (extendClock m P) bad U ω (k-1)
          *(prices k : ℝ))/Real.sqrt (α (k-1)) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk1 : 1 ≤ k := by omega
    by_cases hαpos : 0 < α (k-1)
    · have hσ' := sigma_split_bound (s := k-1) rs (by omega : 1 ≤ k-1) (by omega)
        (hposAll (k-1) (by omega)) hpfpos hαpos
        (prefix_ge m P bad U ω α rs hclock hstage hnorm ha htun hα1
          (by omega : 1 ≤ k-1) (by omega : k-1 ≤ m))
        (suffixProd_one m rs).symm
      rw [show (k-1)+1 = k from by omega, ← suffixProd_succ m rs k hk1] at hσ'
      calc (prices k : ℝ) * suffixProd m rs k
          ≤ (prices k : ℝ) * (suffixProd m rs 0
              * (3*plainAmplitude (extendClock m P) bad U ω (k-1))/Real.sqrt (α (k-1))) :=
            mul_le_mul_of_nonneg_left hσ' (hprnn k)
        _ = suffixProd m rs 0 * 3 * (plainAmplitude (extendClock m P) bad U ω (k-1)
              *(prices k : ℝ))/Real.sqrt (α (k-1)) := by ring
    · have hαz : α (k-1) = 0 :=
        le_antisymm (le_of_not_gt hαpos) (hαnnAll (k-1))
      have hprk0 : (prices k : ℝ) = 0 := by
        have hjm : k-2 < m-1 := by omega
        have hαk : α ((k-2)+1)
            = (1/2)*(w ⟨k-2, hjm⟩).rpow (2/3)/(∑ i : Fin (m-1), (w i).rpow (2/3)) :=
          hαint ⟨k-2, hjm⟩
        rw [show (k-2)+1 = k-1 from by omega, hαz] at hαk
        have hwj0 : w ⟨k-2, hjm⟩ = 0 := by
          by_cases hW : (∑ i : Fin (m-1), (w i).rpow (2/3)) = 0
          · have hz : (w ⟨k-2, hjm⟩).rpow (2/3) = 0 :=
              Finset.sum_eq_zero_iff_of_nonneg
                (fun i _ => Real.rpow_nonneg (hw_nn i) _) |>.mp hW ⟨k-2, hjm⟩ (Finset.mem_univ _)
            exact ((Real.rpow_eq_zero_iff_of_nonneg (hw_nn ⟨k-2, hjm⟩)).mp hz).1
          · have hWpos : 0 < ∑ i : Fin (m-1), (w i).rpow (2/3) :=
              lt_of_le_of_ne hWnn (Ne.symm hW)
            have hrw0 : (w ⟨k-2, hjm⟩).rpow (2/3) = 0 := by
              have hval : (1/2)*(w ⟨k-2, hjm⟩).rpow (2/3)
                  /(∑ i : Fin (m-1), (w i).rpow (2/3)) = 0 := hαk.symm
              rw [div_eq_zero_iff] at hval
              rcases hval with h | h
              · exact (mul_eq_zero.mp h).resolve_left (by norm_num)
              · exact absurd h hW
            exact ((Real.rpow_eq_zero_iff_of_nonneg (hw_nn ⟨k-2, hjm⟩)).mp hrw0).1
        have hwk : plainAmplitude (extendClock m P) bad U ω (k-1)*(prices k : ℝ) = 0 := by
          have hthis : w ⟨k-2, hjm⟩ = plainAmplitude (extendClock m P) bad U ω ((k-2)+1)
              *(prices ((k-2)+2) : ℝ) := hw ⟨k-2, hjm⟩
          rw [show (k-2)+1 = k-1 from by omega, show (k-2)+2 = k from by omega] at hthis
          rw [← hthis, hwj0]
        exact (mul_eq_zero.mp hwk).resolve_left (ne_of_gt (hposAll (k-1) (by omega)))
      rw [hprk0, hαz]
      simp
  have hicoFin : ∑ k ∈ Finset.Ico 2 (m+1), (prices k : ℝ) * suffixProd m rs k
      = ∑ j : Fin (m-1), (prices (j.val+2) : ℝ) * suffixProd m rs (j.val+2) := by
    have hfin : ∑ j ∈ Finset.range (m-1), (prices (2+j) : ℝ) * suffixProd m rs (2+j)
        = ∑ j : Fin (m-1), (prices (j.val+2) : ℝ) * suffixProd m rs (j.val+2) := by
      rw [Fin.sum_univ_eq_sum_range
        (fun j => (prices (j+2) : ℝ) * suffixProd m rs (j+2)) (m-1)]
      exact Finset.sum_congr rfl fun j _ => by rw [Nat.add_comm 2 j]
    rw [Finset.sum_Ico_eq_sum_range _ 2 (m+1), show m+1-2 = m-1 from by omega]
    exact hfin
  have hSumInt : ∑ j : Fin (m-1), (prices (j.val+2) : ℝ) * suffixProd m rs (j.val+2)
      ≤ suffixProd m rs 0 * 3 * (∑ j : Fin (m-1), w j/Real.sqrt (α (j.val+1))) := by
    have h1 : ∀ j : Fin (m-1), (prices (j.val+2) : ℝ) * suffixProd m rs (j.val+2)
        ≤ suffixProd m rs 0 * 3 * (w j/Real.sqrt (α (j.val+1))) := by
      intro j
      have h2 := hTerm (j.val+2) (by simp only [Finset.mem_Ico]; omega)
      rw [show (j.val+2)-1 = j.val+1 from by omega] at h2
      rw [← mul_div_assoc, hw j]
      exact h2
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => h1 j
  have hqnn : (0:ℝ) ≤ quasinorm23 w := by
    unfold quasinorm23
    exact Real.rpow_nonneg
      (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (le_max_left 0 (w j)) _) _
  have hq23 : ∑ j : Fin (m-1), w j/Real.sqrt (α (j.val+1)) ≤ Real.sqrt 2 * quasinorm23 w := by
    rcases eq_or_lt_of_le (Finset.sum_nonneg (fun j _ => hw_nn j)) with hsum0 | hsumpos
    · have hw0 : ∀ j : Fin (m-1), w j = 0 := fun j =>
        Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hw_nn j) |>.mp hsum0.symm j
          (Finset.mem_univ j)
      have hsumz : ∑ j : Fin (m-1), w j/Real.sqrt (α (j.val+1)) = 0 := by
        rw [Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ => div_nonneg (hw_nn j) (Real.sqrt_nonneg _))]
        intro j _
        rw [hw0 j, zero_div]
      rw [hsumz]
      exact mul_nonneg (by positivity) hqnn
    · have hg10 := ThresholdOptimalThresholdAllocation_answer (m-1) w hw_nn hsumpos
      have hg := hg10.2.2.1
      (try dsimp only at hg)
      have hiden : ∀ j : Fin (m-1), w j/Real.sqrt (α (j.val+1))
          = Real.sqrt 2 * (w j/Real.sqrt ((w j).rpow (2/3)
              /(∑ i : Fin (m-1), (w i).rpow (2/3)))) := by
        intro j
        rw [hαint j, mul_div_assoc]
        exact div_sqrt_half (div_nonneg (Real.rpow_nonneg (hw_nn j) _) hWnn)
      rw [← hg, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => (hiden j).le
  have hs52 : Real.sqrt 2 ≤ 5/3 := by
    have h3 : (3*Real.sqrt 2)^2 ≤ (5:ℝ)^2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    have hnn : (0:ℝ) ≤ 3*Real.sqrt 2 := by positivity
    have h5 : (0:ℝ) ≤ (5:ℝ) := by norm_num
    nlinarith [h3, hnn, h5]
  have h186 : (6/5 : ℝ)*3*Real.sqrt 2 ≤ 6 := by nlinarith [hs52]
  have h665 : ((6/5)/a) ≤ 6/a := by
    rw [div_le_div_iff₀ ha ha]
    nlinarith [ha]
  have hint0' : ∑ k ∈ Finset.Ico 2 (m+1), (prices k : ℝ) * suffixProd m rs k
      ≤ ((6/5)/a)*(3*Real.sqrt 2*quasinorm23 w) := by
    have h1 : ∑ k ∈ Finset.Ico 2 (m+1), (prices k : ℝ) * suffixProd m rs k
        ≤ suffixProd m rs 0 * 3 * (∑ j : Fin (m-1), w j/Real.sqrt (α (j.val+1))) := by
      rw [hicoFin]
      exact hSumInt
    have h2 : suffixProd m rs 0 * 3 * (∑ j : Fin (m-1), w j/Real.sqrt (α (j.val+1)))
        ≤ suffixProd m rs 0 * 3 * (Real.sqrt 2 * quasinorm23 w) :=
      mul_le_mul_of_nonneg_left hq23 (by positivity)
    have h3 : suffixProd m rs 0 * 3 * (Real.sqrt 2 * quasinorm23 w)
        ≤ ((6/5)/a) * (3*Real.sqrt 2*quasinorm23 w) := by
      calc suffixProd m rs 0 * 3 * (Real.sqrt 2 * quasinorm23 w)
          = (suffixProd m rs 0) * (3*(Real.sqrt 2*quasinorm23 w)) := by ring
        _ ≤ ((6/5)/a) * (3*(Real.sqrt 2*quasinorm23 w)) :=
          mul_le_mul_of_nonneg_right hpfK (mul_nonneg (by norm_num)
            (mul_nonneg (by positivity) hqnn))
        _ = ((6/5)/a) * (3*Real.sqrt 2*quasinorm23 w) := by ring
    exact le_trans (le_trans h1 h2) h3
  have hq23' : ((6/5)/a)*(3*Real.sqrt 2*quasinorm23 w) ≤ 6/a*quasinorm23 w := by
    have hc : ((6/5)/a)*(3*Real.sqrt 2) ≤ 6/a := by
      rw [show ((6/5)/a)*(3*Real.sqrt 2) = ((6/5)*3*Real.sqrt 2)/a from by field_simp]
      rw [div_le_div_iff₀ ha ha]
      nlinarith [h186]
    have hstep := mul_le_mul_of_nonneg_right hc hqnn
    linarith
  have hp0 : (prices 0 : ℝ) * suffixProd m rs 0 ≤ ((6/5)/a)*(prices 0 : ℝ) := by
    calc (prices 0 : ℝ) * suffixProd m rs 0
        ≤ (prices 0 : ℝ) * ((6/5)/a) := mul_le_mul_of_nonneg_left hpfK (hprnn 0)
      _ = ((6/5)/a)*(prices 0 : ℝ) := by ring
  have hp1 : (prices 1 : ℝ) * suffixProd m rs 0 ≤ ((6/5)/a)*(prices 1 : ℝ) := by
    calc (prices 1 : ℝ) * suffixProd m rs 0
        ≤ (prices 1 : ℝ) * ((6/5)/a) := mul_le_mul_of_nonneg_left hpfK (hprnn 1)
      _ = ((6/5)/a)*(prices 1 : ℝ) := by ring
  have hpp : ((6/5)/a)*((prices 0 : ℝ)+(prices 1 : ℝ))
      ≤ 6/a*((prices 0 : ℝ)+(prices 1 : ℝ)) :=
    mul_le_mul_of_nonneg_right h665 (by exact_mod_cast (by omega : (0:ℕ) ≤ prices 0 + prices 1))
  rw [hWreal, hsplit]
  rw [show (((prices 0+prices 1 : ℕ) : ℝ) + quasinorm23 (fun j : Fin (m-1) =>
      plainAmplitude (extendClock m P) bad U ω (j.val+1)*(prices (j.val+2) : ℝ)))
      = ((prices 0 : ℝ)+(prices 1 : ℝ)) + quasinorm23 w from by
    rw [Nat.cast_add]
    congr 1
    rw [show (fun j : Fin (m-1) => plainAmplitude (extendClock m P) bad U ω (j.val+1)
        *(prices (j.val+2) : ℝ)) = w from funext fun j => (hw j).symm]]
  calc (prices 0 : ℝ) * suffixProd m rs 0 + ((prices 1 : ℝ) * suffixProd m rs 0
        + ∑ k ∈ Finset.Ico 2 (m+1), (prices k : ℝ) * suffixProd m rs k)
      ≤ ((6/5)/a)*((prices 0 : ℝ)+(prices 1 : ℝ))
        + ((6/5)/a)*(3*Real.sqrt 2*quasinorm23 w) := by
        have hsplit' : ((6/5)/a)*((prices 0 : ℝ)+(prices 1 : ℝ))
            = ((6/5)/a)*(prices 0 : ℝ) + ((6/5)/a)*(prices 1 : ℝ) := by ring
        rw [hsplit']
        linarith [hp0, hp1, hint0']
    _ ≤ 6/a*((prices 0 : ℝ)+(prices 1 : ℝ)) + 6/a*quasinorm23 w := by
        linarith [hpp, hq23']
    _ = 6/a*(((prices 0 : ℝ)+(prices 1 : ℝ)) + quasinorm23 w) := by ring

end Qatlib.Concepts.QlsReadoutSpec.Amplification
