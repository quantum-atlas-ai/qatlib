/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.AmplificationProductsStat
import Qatlib.Concepts.QlsReadoutSpec.Amplification.ClockFlagResolutionsLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.ActualNestedAmplificationLows
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Products of nested amplification gains

Proves the stagewise invariant relating the projected state of a nested amplification word to
the corresponding plain prefix. The scalar multiplier is the product of `lam`, whose factors
combine the odd amplification counts with their gain losses.

The final theorems give the initial-oracle call product, the weighted cost recurrence, and the
amplitude-ratio identity used in [LowSu2026].

## Main statements

* `amplification_products_invariant`: relates nested and plain projected states through the
  product of stage gains.
* `amplification_products_intended`: proves call, cost, and amplitude-product identities.
* `Clause9AmplificationProducts_answer`: packages these identities as the amplification product
  contract.

## References

* [Low and Su, 2026][LowSu2026]
-/

set_option warningAsError false
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

/-- The extended clock agrees with the original clock projector at every index at most `m`. -/
private theorem extendClock_eq {H : Type} (m : ℕ) (P : Fin (m+1) → Matrix H H ℂ)
    {k : ℕ} (hk : k ≤ m) : extendClock m P k = P ⟨k, by omega⟩ := by
  unfold extendClock
  exact dif_pos hk

/-- The single-stage word at slot `k` is legal when `k < m + 1`. -/
private theorem legal_stageWord {H : Type} [Fintype H] [DecidableEq H] (m k : ℕ)
    (hk : k < m+1) : legal (m+1) (stageWord (H := H) k) := by
  unfold legal
  intro s hs
  simp only [stageWord, List.mem_singleton] at hs
  subst hs
  exact hk

/-- A concatenation of words is legal exactly when each component is legal. -/
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

/-- A stage word calls its own slot once and every other slot zero times. -/
private theorem calls_stageWord {H : Type} (k slot : ℕ) :
    calls (stageWord (H := H) k) slot = if k = slot then 1 else 0 := by
  simp [calls, stageWord]

/-- A stage word with nonzero slot index makes no calls to slot zero. -/
private theorem calls_stageWord_zero {H : Type} (k : ℕ) (hk : k ≠ 0) :
    calls (stageWord (H := H) k) 0 = 0 := by
  rw [calls_stageWord, if_neg hk]

/-- Weighted oracle cost is additive under concatenation. -/
private theorem weightedCost_append {H : Type} (prices : ℕ → ℕ) (C D : Word H 1) :
    weightedCost prices (C ++ D) = weightedCost prices C + weightedCost prices D := by
  show ((C ++ D).map _).sum = (C.map _).sum + (D.map _).sum
  rw [List.map_append, List.sum_append]

/-- The weighted oracle cost of a stage word is the price of its slot. -/
private theorem weightedCost_stageWord {H : Type} (prices : ℕ → ℕ) (k : ℕ) :
    weightedCost prices (stageWord (H := H) k) = prices k := by
  simp [weightedCost, stageWord]

/-- The zero-index plain prefix consists of the stage word at slot zero. -/
private theorem plainPrefix_zero {H : Type} :
    plainPrefix (H := H) 0 = stageWord 0 := by
  show (List.range 1).map _ = _
  simp [stageWord]

/-- The next plain prefix appends the next stage word to the current prefix. -/
private theorem plainPrefix_succ {H : Type} (j : ℕ) :
    plainPrefix (H := H) (j+1) = plainPrefix j ++ stageWord (j+1) := by
  show (List.range (j+1+1)).map _ = (List.range (j+1)).map _ ++ _
  rw [List.range_succ, List.map_append, List.map_singleton]
  rfl

/-- The clock state is the zero-clock slice of the word matrix acting on the clean seed
embedding. -/
private theorem clockState_eq_run {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (C : Word H 1) (ω : QState H) :
    clockState U C ω = fun h => (wordMatrix U C *ᵥ clean 1 (Nat.zero_lt_one) ω) (h, (0 : Fin 1)) :=
  rfl

/-- An operator controlled on the entire singleton clock acts on the zero-clock slice by the
original operator. -/
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

/-- The matrix of a stage word is its oracle matrix controlled on the full singleton clock. -/
private theorem wordMatrix_stageWord {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (i : ℕ) :
    wordMatrix U (stageWord (H := H) i) = controlled (U i) Finset.univ := by
  simp [wordMatrix, stageWord]

/-- Appending stage word `i` applies `U i` to the current clock state. -/
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

/-- For any matrix `G`, the vectors `G *ᵥ ψ` and `(1 - G) *ᵥ ψ` sum to `ψ`. -/
private theorem projector_decomp {H : Type} [Fintype H] [DecidableEq H]
    (G : Matrix H H ℂ) (ψ : QState H) :
    G *ᵥ ψ + (1 - G) *ᵥ ψ = ψ := by
  rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]

/-- For `x` in the unit interval, `arcsin x` is at most `(π / 2) * x`. -/
private theorem arcsin_le_pi_div_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.arcsin x ≤ (Real.pi / 2) * x := by
  have hmem : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, hx1⟩
  have hy : (Real.pi / 2) * x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    have hpi := Real.pi_pos
    refine ⟨?_, ?_⟩ <;> nlinarith
  have h := Real.arcsin_le_iff_le_sin hmem hy
  rw [h]
  exact Real.le_sin_mul hx0 hx1

/-- The complement of `potential Q bad` equals `Q * bad`. -/
private theorem potential_one_sub {H : Type} [Fintype H] [DecidableEq H]
    (Q : Matrix H H ℂ) (bad : Matrix H H ℂ) :
    1 - potential Q bad = Q * bad := by
  show (1 : Matrix H H ℂ) - (1 - Q * bad) = Q * bad
  abel

/-- Under clock and stage legality, the next potential followed by the next stage annihilates
the complement of the current potential. -/
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

/-- The operator collapse identity sends every vector from the complement of the current
potential to zero after the next stage and potential. -/
private theorem collapse_apply {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) {j : ℕ} (hj : j < m)
    (v : QState H) :
    (potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ
      ((1 - potential (extendClock m P j) bad) *ᵥ v) = 0 := by
  rw [Matrix.mulVec_mulVec, collapse m P bad U hclock hstage hj, Matrix.zero_mulVec]

/-- The real amplification multiplier at stage `k + 1`, equal to its odd iteration factor times
the corresponding `gainLoss`. -/
def lam {H : Type} [Fintype H] [DecidableEq H]
    (E : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (rs : ℕ → ℕ) (k : ℕ) : ℝ :=
  (((2*rs (k+1)+1) : ℕ) : ℝ) * gainLoss (2*rs (k+1)+1) (preAmplitude E bad ω U rs k)

/-- Tunability and thresholds at most one imply the no-overshoot angle bound for every
amplification stage before `m`. -/
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

/-- For a legal pre-amplification stage word, proves legality of the next nested word, its
projected amplification law, and its oracle-call and weighted-cost multipliers under the
clock, stage, and tuning hypotheses. -/
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

/-- Multiplying a state by a complex scalar multiplies its vector norm by the scalar norm. -/
private theorem normVec_smul {H : Type} [Fintype H] (c : ℂ) (v : QState H) :
    normVec (c • v) = ‖c‖ * normVec v := by
  show ‖toEuclidean_fromVec (c • v)‖ = ‖c‖ * ‖toEuclidean_fromVec v‖
  have h : toEuclidean_fromVec (c • v) = c • toEuclidean_fromVec v := rfl
  rw [h, norm_smul]

/-- Multiplying a state by a real scalar multiplies its vector norm by the scalar's absolute
value. -/
private theorem normVec_real_smul {H : Type} [Fintype H] (r : ℝ) (v : QState H) :
    normVec (((r : ℝ) : ℂ) • v) = |r| * normVec v := by
  rw [normVec_smul, Complex.norm_real, Real.norm_eq_abs]

/-- Scalar multiplication by a product is successive scalar multiplication. -/
private theorem smul_mul_split {H : Type} (a b : ℂ) (v : QState H) :
    ((a * b : ℂ)) • v = a • (b • v) := mul_smul a b v

/-- Splits the product of the first `j + 1` odd amplification factors into the product of the
first `j` factors and the final factor. -/
private theorem prod_split_rs {j : ℕ} {rs : ℕ → ℕ} :
    (∏ k : Fin (j+1), (2*rs (k.val+1)+1))
      = (∏ k : Fin j, (2*rs (k.val+1)+1)) * (2*rs (j+1)+1) := by
  have e : ∀ n : ℕ, (∏ k : Fin n, (2*rs (k.val+1)+1))
      = ∏ k ∈ Finset.range n, (2*rs (k+1)+1) :=
    fun n => Fin.prod_univ_eq_prod_range (fun k => 2*rs (k+1)+1) n
  rw [e (j+1), Finset.prod_range_succ (fun k => 2*rs (k+1)+1) j, ← e j]

/-- Under clock and stage legality, normalized seed, tunability, and thresholds at most one,
every nested word through stage `m` is legal. -/
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
    have hEj1 : extendClock m P (j+1) = P ⟨j+1, by omega⟩ := extendClock_eq m P (by omega)
    have hGproj : IsOrthogonalProjector (potential (extendClock m P (j+1)) bad) := by
      have g3 := Clause3ClockFlagResolutions_answer H m P bad hclock
      have h := (g3.1 ⟨j+1, by omega⟩ ⟨j+1, by omega⟩ le_rfl).2.2.2.2.2.1
      rw [hEj1]
      exact h
    have hUunit : ∀ k < m+1, U k ∈ Matrix.unitaryGroup H ℂ := by
      intro k hk
      exact hstage.1 (⟨k, by omega⟩ : Fin (m+1))
    have hB : legal (m+1) (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) := by
      rw [legal_append_iff]
      exact ⟨ih (by omega), legal_stageWord m (j+1) (by omega)⟩
    have hno := noOvershoot m P bad U ω α rs htun habove hjm
    have hG5 := Clause5ActualNestedAmplification_answer H (m+1) U
      (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) ω
      (potential (extendClock m P (j+1)) bad) (rs (j+1))
      hUunit hB hnorm hGproj hno
    rw [show nestedWord (extendClock m P) bad ω rs (j+1)
        = aaWord (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) ω
            (potential (extendClock m P (j+1)) bad) (rs (j+1)) from rfl]
    exact hG5.1

/-- Under the amplification hypotheses, appending the next stage to the current nested word
gives a legal pre-amplification word. -/
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

/-- Under the amplification hypotheses, the slot-zero call count through stage `j ≤ m` is the
product of the first `j` odd amplification factors. -/
private theorem calls_nested {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (htun : tunable m (extendClock m P) bad U ω α rs) (habove : ∀ j : Fin m, α (j.val+1) ≤ 1) :
    ∀ j : ℕ, j ≤ m →
      calls (nestedWord (extendClock m P) bad ω rs j) 0
        = ∏ k : Fin j, (2*rs (k.val+1)+1) := by
  intro j
  induction j with
  | zero =>
    intro _
    show calls (stageWord (H := H) 0) 0 = ∏ k : Fin 0, (2*rs (k.val+1)+1)
    simp [calls_stageWord]
  | succ j ih =>
    intro hj
    have hjm : j < m := by omega
    have hleg := legal_B m P bad U ω α rs hclock hstage hnorm htun habove hjm
    have hg5 := clause5_at_stage m P bad U ω α rs hclock hstage hnorm htun habove hjm hleg
    rw [hg5.2.2.1 0, calls_append, calls_stageWord_zero (j+1) (by omega), add_zero,
      ih (by omega), prod_split_rs]
    ring

/-- Under the amplification hypotheses, the next nested weighted cost is the next odd
amplification factor times the sum of the current cost and the next slot price. -/
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

/-- Tunability and thresholds at most one make every stage gain-loss factor strictly positive. -/
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
    have hle : ((2*rs (j+1)+1 : ℕ) : ℝ) * Real.arcsin a ≤ Real.pi / 2 := hno
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

/-- Under the tuning hypotheses and thresholds at most one, the total gain loss through all `m`
stages is strictly positive. -/
private theorem totalLoss_pos {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (htun : tunable m (extendClock m P) bad U ω α rs) (habove : ∀ j : Fin m, α (j.val+1) ≤ 1) :
    0 < totalLoss m (extendClock m P) bad U ω rs := by
  unfold totalLoss
  exact Finset.prod_pos fun j _ => gainLoss_pos m P bad U ω α rs htun habove j.val j.isLt

/-- Splits the complex product of stage multipliers through `j + 1` into the last multiplier and
the product through `j`. -/
private theorem prod_split_lam_coe {H : Type} [Fintype H] [DecidableEq H] (j : ℕ)
    (E : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (rs : ℕ → ℕ) :
    (∏ k : Fin (j+1), ((lam E bad U ω rs k.val : ℝ) : ℂ))
      = ((lam E bad U ω rs j : ℝ) : ℂ)
        * (∏ k : Fin j, ((lam E bad U ω rs k.val : ℝ) : ℂ)) := by
  have e : ∀ n : ℕ, (∏ k : Fin n, ((lam E bad U ω rs k.val : ℝ) : ℂ))
      = ∏ k ∈ Finset.range n, ((lam E bad U ω rs k : ℝ) : ℂ) :=
    fun n => Fin.prod_univ_eq_prod_range (fun k => ((lam E bad U ω rs k : ℝ) : ℂ)) n
  rw [e (j+1), Finset.prod_range_succ (fun k => ((lam E bad U ω rs k : ℝ) : ℂ)) j, ← e j,
    mul_comm]

/-- Under the clock, stage, normalization, and tuning hypotheses, each projected nested state is
the corresponding projected plain-prefix state multiplied by the product of its stage
multipliers. -/
theorem amplification_products_invariant {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (htun : tunable m (extendClock m P) bad U ω α rs) (habove : ∀ j : Fin m, α (j.val+1) ≤ 1) :
    ∀ j : ℕ, j ≤ m →
      potential (extendClock m P j) bad *ᵥ
          clockState U (nestedWord (extendClock m P) bad ω rs j) ω
        = ((∏ k : Fin j, lam (extendClock m P) bad U ω rs k.val) : ℂ) •
          (potential (extendClock m P j) bad *ᵥ clockState U (plainPrefix j) ω) := by
  intro j
  induction j with
  | zero =>
    intro _
    have hpot0 : potential (extendClock m P 0) bad = 1 := by
      have g3 := Clause3ClockFlagResolutions_answer H m P bad hclock
      have hE0 : extendClock m P 0 = P ⟨0, by omega⟩ := extendClock_eq m P (by omega)
      rw [hE0]
      exact g3.2.2.2.2.2.1
    rw [hpot0, show nestedWord (extendClock m P) bad ω rs 0 = stageWord 0 from rfl,
      plainPrefix_zero]
    simp
  | succ j ih =>
    intro hj
    have hjm : j < m := by omega
    have hleg := legal_B m P bad U ω α rs hclock hstage hnorm htun habove hjm
    have hg5 := clause5_at_stage m P bad U ω α rs hclock hstage hnorm htun habove hjm hleg
    have hEj : extendClock m P j = P ⟨j, by omega⟩ := extendClock_eq m P (by omega)
    have hEj1 : extendClock m P (j+1) = P ⟨j+1, by omega⟩ := extendClock_eq m P (by omega)

    have hscalar : (((2*rs (j+1)+1 : ℕ) : ℂ) *
        ((gainLoss (2*rs (j+1)+1) (preAmplitude (extendClock m P) bad ω U rs j) : ℝ) : ℂ))
        = ((lam (extendClock m P) bad U ω rs j : ℝ) : ℂ) := by
      have hlam : (lam (extendClock m P) bad U ω rs j : ℝ)
          = ((2*rs (j+1)+1 : ℕ) : ℝ)
            * gainLoss (2*rs (j+1)+1) (preAmplitude (extendClock m P) bad ω U rs j) := rfl
      rw [hlam, Complex.ofReal_mul, Complex.ofReal_natCast]

    have hamp : potential (extendClock m P (j+1)) bad *ᵥ
        clockState U (nestedWord (extendClock m P) bad ω rs (j+1)) ω
        = ((lam (extendClock m P) bad U ω rs j : ℝ) : ℂ) •
          (potential (extendClock m P (j+1)) bad *ᵥ
            clockState U (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) ω) := by
      rw [hg5.2.1, hscalar]

    have hsplit : ∀ v : QState H,
        (potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ v
          = (potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ
              (potential (extendClock m P j) bad *ᵥ v) := by
      intro v
      have hdecomp : v = potential (extendClock m P j) bad *ᵥ v
          + (1 - potential (extendClock m P j) bad) *ᵥ v :=
        (projector_decomp (potential (extendClock m P j) bad) v).symm
      conv_lhs => rw [hdecomp, Matrix.mulVec_add]
      rw [collapse_apply m P bad U hclock hstage hjm v]
      simp

    have hpre : clockState U (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) ω
        = U (j+1) *ᵥ clockState U (nestedWord (extendClock m P) bad ω rs j) ω :=
      clockState_append_stageWord U _ (j+1) ω
    have hprePlain : clockState U (plainPrefix (j+1)) ω
        = U (j+1) *ᵥ clockState U (plainPrefix j) ω := by
      rw [plainPrefix_succ, clockState_append_stageWord]

    have hLHS : (potential (extendClock m P (j+1)) bad *ᵥ
        clockState U (nestedWord (extendClock m P) bad ω rs (j+1)) ω : QState H)
        = ((lam (extendClock m P) bad U ω rs j : ℝ) : ℂ) •
          (((∏ k : Fin j, lam (extendClock m P) bad U ω rs k.val) : ℂ) •
            (potential (extendClock m P (j+1)) bad *ᵥ clockState U (plainPrefix (j+1)) ω :
              QState H)) := by
      rw [hamp]
      have h1 : potential (extendClock m P (j+1)) bad *ᵥ
          clockState U (nestedWord (extendClock m P) bad ω rs j ++ stageWord (j+1)) ω
          = (potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ
              clockState U (nestedWord (extendClock m P) bad ω rs j) ω := by
        rw [hpre, Matrix.mulVec_mulVec]
      rw [h1, hsplit]
      have h2 : (potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ
          (potential (extendClock m P j) bad *ᵥ clockState U (nestedWord (extendClock m P) bad ω rs j) ω)
          = (potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ
              (((∏ k : Fin j, lam (extendClock m P) bad U ω rs k.val) : ℂ) •
                (potential (extendClock m P j) bad *ᵥ clockState U (plainPrefix j) ω)) := by
        rw [ih (by omega)]
      rw [h2, Matrix.mulVec_smul]
      have h3 : (potential (extendClock m P (j+1)) bad * U (j+1)) *ᵥ
          (potential (extendClock m P j) bad *ᵥ clockState U (plainPrefix j) ω)
          = potential (extendClock m P (j+1)) bad *ᵥ clockState U (plainPrefix (j+1)) ω := by
        rw [← hsplit (clockState U (plainPrefix j) ω), ← Matrix.mulVec_mulVec,
          ← hprePlain]
      rw [h3]

    rw [prod_split_lam_coe j (extendClock m P) bad U ω rs,
      smul_mul_split ((lam (extendClock m P) bad U ω rs j : ℝ) : ℂ)
        ((∏ k : Fin j, ((lam (extendClock m P) bad U ω rs k.val : ℝ) : ℂ)))
        (potential (extendClock m P (j+1)) bad *ᵥ clockState U (plainPrefix (j+1)) ω)]
    rw [← hLHS]

/-- Under the amplification hypotheses and positive final plain amplitude, proves the slot-zero
call product, weighted cost recurrence, and equality of the odd-factor product with the
final amplitude ratio. -/
theorem amplification_products_intended {H : Type} [Fintype H] [DecidableEq H]
    (m : ℕ) (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ)
    (hclock : clockLegal m P bad) (hstage : stageLegal m P U) (hnorm : Normalized ω)
    (hplain : 0 < plainAmplitude (extendClock m P) bad U ω m)
    (htun : tunable m (extendClock m P) bad U ω α rs)
    (habove : ∀ j : Fin m, α (j.val+1) ≤ 1) :
    (∀ j : Fin (m+1),
      calls (nestedWord (extendClock m P) bad ω rs j.val) 0
        = ∏ k : Fin j.val, (2*rs (k.val+1)+1)) ∧
    (∀ j : Fin m, ∀ prices,
      weightedCost prices (nestedWord (extendClock m P) bad ω rs (j.val+1))
        = (2*rs (j.val+1)+1)*
          (weightedCost prices (nestedWord (extendClock m P) bad ω rs j.val)
            +prices (j.val+1))) ∧
    (((∏ j : Fin m, (2*rs (j.val+1)+1)) : ℕ) : ℝ) =
      postAmplitude (extendClock m P) bad ω U rs m/
        (plainAmplitude (extendClock m P) bad U ω m
          *totalLoss m (extendClock m P) bad U ω rs) := by
  refine ⟨fun j => calls_nested (H := H) m P bad U ω α rs hclock hstage hnorm htun habove
      j.val (Nat.le_of_lt_succ j.isLt), fun j prices => cost_nested (H := H) m P bad U ω α rs hclock hstage
      hnorm htun habove j.val j.isLt prices, ?_⟩
  have hinv := amplification_products_invariant (H := H) m P bad U ω α rs hclock hstage hnorm htun habove m
    (le_refl m)
  have hlams_nonneg : ∀ k : Fin m, 0 ≤ lam (extendClock m P) bad U ω rs k.val := by
    intro k
    exact mul_nonneg (by exact_mod_cast (by omega : 0 ≤ 2*rs (k.val+1)+1))
      (le_of_lt (gainLoss_pos (H := H) m P bad U ω α rs htun habove k.val k.isLt))
  have hprodnn : 0 ≤ ∏ k : Fin m, lam (extendClock m P) bad U ω rs k.val :=
    Finset.prod_nonneg (fun k _ => hlams_nonneg k)
  have hprod_form : (∏ k : Fin m, ((lam (extendClock m P) bad U ω rs k.val : ℝ) : ℂ))
      = ((∏ k : Fin m, lam (extendClock m P) bad U ω rs k.val) : ℝ) := by
    rw [Complex.ofReal_prod]
  have hampEq : postAmplitude (extendClock m P) bad ω U rs m
      = (∏ k : Fin m, lam (extendClock m P) bad U ω rs k.val)
        *plainAmplitude (extendClock m P) bad U ω m := by
    show normVec (potential (extendClock m P m) bad *ᵥ
        clockState U (nestedWord (extendClock m P) bad ω rs m) ω) = _
    rw [hinv, hprod_form, normVec_real_smul, abs_of_nonneg hprodnn]
    rfl
  have hloss := totalLoss_pos (H := H) m P bad U ω α rs htun habove
  have hprod2 : (∏ k : Fin m, lam (extendClock m P) bad U ω rs k.val)
      = (((∏ j : Fin m, (2*rs (j.val+1)+1)) : ℕ) : ℝ)
        *totalLoss m (extendClock m P) bad U ω rs := by
    have hlam : ∀ k : Fin m, lam (extendClock m P) bad U ω rs k.val
        = (((2*rs (k.val+1)+1) : ℕ) : ℝ)
          *gainLoss (2*rs (k.val+1)+1)
            (preAmplitude (extendClock m P) bad ω U rs k.val) := fun k => rfl
    rw [Finset.prod_congr rfl (fun k _ => hlam k), Finset.prod_mul_distrib, ← Nat.cast_prod]
    rfl
  rw [hampEq, hprod2]
  have hne : plainAmplitude (extendClock m P) bad U ω m
      *totalLoss m (extendClock m P) bad U ω rs ≠ 0 :=
    mul_ne_zero (ne_of_gt hplain) (ne_of_gt hloss)
  field_simp

/-- Proves the nested amplification call-product, weighted-cost, and amplitude-ratio contract
corresponding to [Low and Su, Lemma 5][LowSu2026]. -/
theorem Clause9AmplificationProducts_answer : Clause9AmplificationProducts := by
  intro H _ _ m P bad U ω α rs hclock hstage hnorm hplain htun habove
  exact amplification_products_intended m P bad U ω α rs
    hclock hstage hnorm hplain htun habove

end Qatlib.Concepts.QlsReadoutSpec.Amplification
