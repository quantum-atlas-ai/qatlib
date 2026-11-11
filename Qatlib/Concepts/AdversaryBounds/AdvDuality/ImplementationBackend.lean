/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ImplementationBackendDefs

/-!
# Dyadic Preparation and Resource Accounting Laws

This file proves the elementary dyadic and unitary-preparation facts used by the implementation
backend. The square-root estimate `thresholdGoal_sqrt_transport` feeds coordinatewise error
transport and accumulation in supremum distance, while
`thresholdGoal_coeffDomainCheck_true_premises` connects the finite coefficient check to its
mathematical premises. Unitary preparation and linear combinations of controlled operations use
the finite-dimensional circuit setting described in [NielsenChuang2010].

The memory-event results establish composition and peak-space laws, keep forward, controlled,
and inverse query budgets separate, and bind resource accounting to an initial state and event
trace. They establish the core contracts packaged below; the additional preparation and
generation requirements remain separate propositions in the definitions module.

## Main statements

- `thresholdGoal_prepare_normalized` derives weight normalization from unitary preparation.
* `thresholdGoal_phaseInverseCore`, `thresholdGoal_prepareTransport`, and
  `thresholdGoal_unitPrepareConsumer` establish the dyadic-angle and basic preparation
  contracts.
- `clause11_memoryCore` establishes memory-transition and peak-space laws.
* `clause11_oraclePayment` and `clause11_oneRunBinding` establish query-budget and
  trace-accounting laws.

## References

- [Nielsen and Chuang, 2010][NielsenChuang2010], Quantum Computation and Quantum Information.
-/

set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ResourceBounds.AsymBounds
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.BlockEncoding.LinearCombination

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open scoped BigOperators
open Qatlib.Foundations.IntervalArith.IntervalOps
  (Valid Contains unit roundDown rounded width)

/-- For nonnegative reals with `y ≤ x`, the squared difference of their square roots is at most
`x - y`. -/
private theorem sq_sqrt_sub_le_of_nonneg (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : y ≤ x) :
    (Real.sqrt x - Real.sqrt y) ^ 2 ≤ x - y := by
  have hsq : (Real.sqrt x - Real.sqrt y) ^ 2 = x + y - 2 * (Real.sqrt x * Real.sqrt y) := by
    rw [sub_sq, Real.sq_sqrt hx, Real.sq_sqrt hy]
    ring
  rw [hsq]
  have key : y ≤ Real.sqrt x * Real.sqrt y := by
    rcases eq_or_lt_of_le hy with h0 | hpos
    · rw [← h0]
      simp
    · have hxy : Real.sqrt y ≤ Real.sqrt x := Real.sqrt_le_sqrt h
      have h2 : Real.sqrt y * Real.sqrt y ≤ Real.sqrt x * Real.sqrt y :=
        mul_le_mul_of_nonneg_right hxy (Real.sqrt_nonneg y)
      rw [Real.mul_self_sqrt hy] at h2
      exact h2
  linarith

/-- The square-root map on nonnegative reals satisfies the bound `|sqrt x - sqrt y| ≤ sqrt |x -
y|`. -/
theorem thresholdGoal_sqrt_transport (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ Real.sqrt |x - y| := by
  apply Real.abs_le_sqrt
  rcases le_total x y with h | h
  · have h' := sq_sqrt_sub_le_of_nonneg y x hy hx h
    have heq : (Real.sqrt x - Real.sqrt y) ^ 2 = (Real.sqrt y - Real.sqrt x) ^ 2 := by ring
    rw [heq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)]
    exact h'
  · have h' := sq_sqrt_sub_le_of_nonneg x y hx hy h
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact h'

/-- A uniform coordinatewise bound by `sqrt d` bounds the finite-product distance between two
state vectors by the same quantity. -/
theorem thresholdGoal_fiber_error_one_layer {m : ℕ} (a b : QState (Fin m)) (d : ℝ)
    (h : ∀ j, ‖a j - b j‖ ≤ Real.sqrt d) : fiberDist a b ≤ Real.sqrt d := by
  show dist a b ≤ Real.sqrt d
  rw [dist_pi_le_iff (Real.sqrt_nonneg d)]
  intro j
  rw [dist_eq_norm]
  exact h j

/-- The distance between the first and final state vectors is bounded by the sum of the
prescribed square-root bounds on successive distances. -/
theorem thresholdGoal_fiber_error_accumulate (m L : ℕ) (f : ℕ → QState (Fin m)) (δ : ℕ → ℝ)
    (h : ∀ i, fiberDist (f (i + 1)) (f i) ≤ Real.sqrt (δ i)) :
    fiberDist (f L) (f 0) ≤ errorBudget L δ := by
  have key : dist (f L) (f 0) ≤ ∑ i ∈ Finset.range L, dist (f (i + 1)) (f i) := by
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Finset.sum_range_succ]
      have h2 : dist (f (L + 1)) (f L) + dist (f L) (f 0)
          ≤ dist (f (L + 1)) (f L) + (∑ i ∈ Finset.range L, dist (f (i + 1)) (f i)) :=
        add_le_add_right ih _
      exact le_trans (dist_triangle (f (L + 1)) (f L) (f 0)) (h2.trans_eq (add_comm _ _))
  refine le_trans key ?_
  show (∑ i ∈ Finset.range L, dist (f (i + 1)) (f i)) ≤ errorBudget L δ
  simp only [errorBudget]
  exact Finset.sum_le_sum fun i _ => h i

/-- Nonnegative weights prepared from a basis vector by a unitary matrix sum to one. -/
theorem thresholdGoal_prepare_normalized {J : Type*} [Fintype J] [DecidableEq J] {w : J → ℝ}
    (hw : ∀ j, 0 ≤ w j) {P : Matrix J J ℂ} {j₀ : J} (hP : IsPrepare P w j₀) :
    ∑ j, w j = 1 := by
  have hcol : ∀ j : J, P j j₀ = ((Real.sqrt (w j) : ℂ)) := by
    intro j
    rw [← mulVec_ket_apply P j₀ j]
    exact congrFun hP.2 j
  have hsq : ∀ j : J, star (P j j₀) * P j j₀ = ((w j : ℝ) : ℂ) := by
    intro j
    rw [hcol j]
    show (starRingEnd ℂ) ((Real.sqrt (w j) : ℝ) : ℂ) * ((Real.sqrt (w j) : ℝ) : ℂ) = _
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hw j)]
  have hunit : (Pᴴ * P) j₀ j₀ = (1 : ℂ) := by
    have h1 : star P * P = (1 : Matrix J J ℂ) :=
      (Matrix.mem_unitaryGroup_iff' (A := P)).mp hP.1
    rw [Matrix.star_eq_conjTranspose] at h1
    rw [h1]
    simp
  have hexpand : (Pᴴ * P) j₀ j₀ = ((∑ j, w j : ℝ) : ℂ) := by
    rw [Matrix.mul_apply]
    have hconj : ∀ k : J, (Pᴴ) j₀ k = star (P k j₀) := by
      intro k
      simp [Matrix.conjTranspose_apply]
    simp only [hconj, hsq]
    rw [← Complex.ofReal_sum]
  rw [hexpand] at hunit
  exact Complex.ofReal_eq_one.mp hunit

/-- No unitary preparation from a basis vector can have every weight equal to zero. -/
theorem thresholdGoal_zero_weights_not_prepare {J : Type*} [Fintype J] [DecidableEq J]
    (P : Matrix J J ℂ) (j₀ : J) : ¬ IsPrepare P (fun _ => (0:ℝ)) j₀ := by
  intro h
  have hnorm := thresholdGoal_prepare_normalized (fun _ => le_rfl) h
  simp at hnorm

/-- The identity matrix prepares the weight distribution concentrated at the chosen basis label. -/
theorem thresholdGoal_unit_prepare {J : Type*} [Fintype J] [DecidableEq J] (j₀ : J) :
    IsPrepare (1 : Matrix J J ℂ) (fun j => if j = j₀ then (1:ℝ) else 0) j₀ := by
  constructor
  · exact one_mem _
  · funext j
    simp [Ket]
    split_ifs with h <;> simp

/-- With identity preparation and a basis-state control register, the selected corner of the LCU
workspace applies the corresponding matrix `U j₀`. -/
theorem thresholdGoal_unit_prepare_lcu {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
    [DecidableEq I] (U : J → Matrix I I ℂ) (j₀ : J) (ψ : QState I) :
    (fun i' => (LCUWorkspace U (1 : Matrix J J ℂ) *ᵥ TensorState (Ket j₀) ψ) (j₀, i'))
      = U j₀ *ᵥ ψ := by
  have hw : ∀ j : J, 0 ≤ (if j = j₀ then (1:ℝ) else 0) := by
    intro j
    by_cases h : j = j₀ <;> simp [h]
  have hP : IsPrepare (1 : Matrix J J ℂ) (fun j => if j = j₀ then (1:ℝ) else 0) j₀ :=
    thresholdGoal_unit_prepare j₀
  have h := lcu_corner_apply U hw hP ψ
  rw [h]
  congr 1
  rw [Finset.sum_eq_single j₀]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hcon
    exact absurd (Finset.mem_univ j₀) hcon

/-- The dyadic-angle range check returns `none` exactly when the numerator is at least its
power-of-two denominator. -/
theorem thresholdGoal_admitAngle_none_iff (num k : ℕ) : admitAngle num k = none ↔ 2 ^ k ≤ num := by
  rw [admitAngle]
  by_cases h : num < 2 ^ k
  · simp [h]
  · have h' : 2 ^ k ≤ num := Nat.le_of_not_lt h
    simp [h, h']

/-- Rounding a rational downward to a dyadic grid never increases it. -/
private theorem roundDown_le (q : ℚ) (k : ℕ) : roundDown q k ≤ q := by
  have h := Int.floor_le (α := ℚ) (q * (2:ℚ)^k)
  have hpow : (0:ℚ) < 2^k := by positivity
  simp only [roundDown]
  rw [div_le_iff₀ hpow]
  exact_mod_cast h

/-- A rational lies strictly below its downward dyadic rounding plus one grid unit. -/
private theorem lt_roundDown_add_unit (q : ℚ) (k : ℕ) : q < roundDown q k + unit k := by
  have h := Int.lt_floor_add_one (q * (2:ℚ)^k)
  have hpow : (0:ℚ) < 2^k := by positivity
  simp only [roundDown, unit]
  rw [← add_div, lt_div_iff₀ hpow]
  exact_mod_cast h

/-- Dyadic-angle evaluation produces a valid interval containing the decoded real angle, with
width exactly `unit p`. -/
theorem thresholdGoal_evalAngle_sound (a : DyadicAngle) (p : ℕ) :
    Valid (evalAngle a p) ∧ Contains (evalAngle a p) a.decode ∧ width (evalAngle a p) = unit p := by
  have hvalid : Valid (evalAngle a p) := by
    simp only [Valid, evalAngle, rounded]
    have h : (0:ℚ) ≤ unit p := by
      show (0:ℚ) ≤ 1/(2:ℚ)^p
      positivity
    exact le_add_of_nonneg_right h
  have hcontains : Contains (evalAngle a p) a.decode := by
    simp only [evalAngle, DyadicAngle.decode]
    refine ⟨?_, ?_⟩
    · exact_mod_cast roundDown_le a.decodeQ p
    · have h := lt_roundDown_add_unit a.decodeQ p
      simp only [rounded]
      exact_mod_cast le_of_lt h
  have hwidth : width (evalAngle a p) = unit p := by
    simp [width, evalAngle, rounded]
  exact ⟨hvalid, hcontains, hwidth⟩

/-- For a numerator strictly below its denominator, the rational decoding of the complementary
angle is one minus the original decoding. -/
theorem thresholdGoal_invAngle_decode (a : DyadicAngle) (h : a.num < 2 ^ a.k) :
    DyadicAngle.decodeQ (invAngle a) = 1 - DyadicAngle.decodeQ a := by
  simp only [invAngle, DyadicAngle.decodeQ]
  rw [Nat.cast_sub (le_of_lt h)]
  have h2 : ((2 ^ a.k : ℕ) : ℚ) = (2:ℚ) ^ a.k := by
    norm_cast
  rw [h2, sub_div]
  rw [div_self (pow_ne_zero _ (by norm_num : (2:ℚ) ≠ 0))]

/-- The angle-evaluation cost covers the length of the concatenated self-delimiting numerator
and exponent encodings. -/
theorem thresholdGoal_evalAngleCost_reads (a : DyadicAngle) (p : ℕ) :
    (selfDelimitBits a.num ++ selfDelimitBits a.k).length ≤ evalAngleCost a p := by
  unfold evalAngleCost
  omega

/-- The self-delimiting encoding of a natural number has length twice its binary digit count
plus one. -/
theorem thresholdGoal_selfDelimit_cost (n : ℕ) :
    (selfDelimitBits n).length = 2 * n.bits.length + 1 := by
  simp [selfDelimitBits]; omega

/-- Summing the numerator list over its finite index type equals the list sum. -/
private theorem sum_get_nat (w : DyadicWeights) :
    (∑ j : Fin w.num.length, (w.num.get j : ℕ)) = w.num.sum := by
  rw [← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_get w.num)

/-- The sum of the rational dyadic coefficients equals the numerator-list sum divided by their
common denominator. -/
private theorem sum_get_cast (w : DyadicWeights) :
    (∑ j : Fin w.num.length, ((w.num.get j : ℚ) / (2:ℚ)^w.bits))
      = (((w.num.sum : ℕ) : ℚ) / (2:ℚ)^w.bits) := by
  rw [← Finset.sum_div]
  have hsum : (∑ j : Fin w.num.length, (w.num.get j : ℚ)) = ((w.num.sum : ℕ) : ℚ) := by
    exact_mod_cast sum_get_nat w
  rw [hsum]

/-- Integer normalization of dyadic weights implies that their decoded real coefficients sum to
one. -/
theorem thresholdGoal_normalizedReal {w : DyadicWeights} (h : w.num.sum = 2 ^ w.bits) :
    ∑ j : Fin w.num.length, w.decode j = 1 := by
  have hq : (∑ j : Fin w.num.length, (w.decodeQ j : ℚ)) = 1 := by
    simp only [DyadicWeights.decodeQ]
    rw [sum_get_cast, h]
    have h2 : ((2 ^ w.bits : ℕ) : ℚ) = (2:ℚ) ^ w.bits := by
      norm_cast
    rw [h2]
    exact div_self (pow_ne_zero _ (by norm_num : (2:ℚ) ≠ 0))
  simp only [DyadicWeights.decode]
  exact_mod_cast hq

/-- A successful coefficient-domain check supplies all positivity, normalization, gap, and
conditioning premises. -/
theorem thresholdGoal_coeffDomainCheck_true_premises {w : DyadicWeights} {γ κ : ℚ}
    (h : coeffDomainCheck w γ κ = true) : CoeffPremises w γ κ := by
  simp only [coeffDomainCheck] at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hγ, hκ⟩, hsum⟩, hgap⟩, hcond⟩ := h
  have hγ' : 0 < γ := of_decide_eq_true hγ
  have hκ' : 0 < κ := of_decide_eq_true hκ
  have hsum' : w.num.sum = 2 ^ w.bits := of_decide_eq_true hsum
  have hgap' : ∀ z ∈ w.num, z = 0 ∨ (γ : ℚ) ≤ (z:ℚ) / 2 ^ w.bits := by
    intro z hz
    have hall := List.all_eq_true.mp hgap
    have hz' := hall z hz
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hz'
    exact hz'
  have hcond' : ∀ z ∈ w.num, (z:ℚ) / 2 ^ w.bits ≤ κ * γ := by
    intro z hz
    have hall := List.all_eq_true.mp hcond
    exact of_decide_eq_true (hall z hz)
  refine ⟨hγ', hκ', hsum', thresholdGoal_normalizedReal hsum', ?_, ?_⟩
  · intro j
    have hj := hgap' (w.num.get j) (List.get_mem _ _)
    rcases hj with hj | hj
    · left
      simp only [DyadicWeights.decode, DyadicWeights.decodeQ]
      rw [hj]
      simp
    · right
      simp only [DyadicWeights.decode, DyadicWeights.decodeQ]
      exact_mod_cast hj
  · intro j
    have hj := hcond' (w.num.get j) (List.get_mem _ _)
    simp only [DyadicWeights.decode, DyadicWeights.decodeQ]
    exact_mod_cast hj

/-- The coefficient-domain checker either rejects its input or yields the full coefficient
premises. -/
theorem thresholdGoal_finiteDigitCore : ThresholdFiniteDigitCore := by
  intro w γ κ
  have hcases : coeffDomainCheck w γ κ = true ∨ coeffDomainCheck w γ κ = false := by
    cases coeffDomainCheck w γ κ <;> simp
  rcases hcases with h | h
  · exact Or.inr (thresholdGoal_coeffDomainCheck_true_premises h)
  · exact Or.inl h

/-- The coefficient-domain checker rejects every all-zero weight list, for all gap and
conditioning parameters. -/
theorem thresholdGoal_zeroWeights_rejected (m bits : ℕ) (γ κ : ℚ) :
    coeffDomainCheck (zeroWeights m bits) γ κ = false := by
  have hsum : ((zeroWeights m bits).num.sum : ℕ) = 0 := by
    simp [zeroWeights, List.sum_replicate]
  have hne : ¬(((zeroWeights m bits).num.sum : ℕ) = 2 ^ (zeroWeights m bits).bits) := by
    have hb : (zeroWeights m bits).bits = bits := rfl
    rw [hsum, hb]
    have hpos : (0:ℕ) < 2 ^ bits := pow_pos (by norm_num) bits
    omega
  have key : decide (((zeroWeights m bits).num.sum : ℕ) = 2 ^ (zeroWeights m bits).bits) = false :=
    decide_eq_false_iff_not.mpr hne
  simp only [coeffDomainCheck]
  rw [key]
  simp

/-- The sum of a list containing `n` copies of a natural number `a` is `n * a`. -/
private theorem sum_replicate_mul (n a : ℕ) : (List.replicate n a).sum = n * a := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul]; omega

/-- Equal dyadic weights satisfy integer normalization whenever their count divides the
power-of-two denominator. -/
theorem thresholdGoal_equalWeights_sum (m bits : ℕ) (hd : m ∣ 2 ^ bits) :
    (equalWeights m bits).num.sum = 2 ^ (equalWeights m bits).bits := by
  simp only [equalWeights]
  rw [sum_replicate_mul]
  exact (Nat.mul_comm m (2 ^ bits / m)).trans (Nat.div_mul_cancel hd)

/-- The dyadic-angle range check, interval evaluation, reading-cost bound, and
complementary-angle decoding satisfy the phase-inverse core contract. -/
theorem thresholdGoal_phaseInverseCore : ThresholdPhaseInverseCore := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro num k
    exact thresholdGoal_admitAngle_none_iff num k
  · intro a p
    exact thresholdGoal_evalAngle_sound a p
  · intro a p
    exact thresholdGoal_evalAngleCost_reads a p
  · intro a h
    exact thresholdGoal_invAngle_decode a h

/-- Square-root stability, uniform coordinate bounds, and accumulation of successive distances
satisfy the preparation-error transport contract. -/
theorem thresholdGoal_prepareTransport : ThresholdPrepareTransport := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hx hy
    exact thresholdGoal_sqrt_transport x y hx hy
  · intro m a b d _ h
    exact thresholdGoal_fiber_error_one_layer a b d h
  · intro m L f δ h
    exact thresholdGoal_fiber_error_accumulate m L f δ h

/-- Identity preparation and its selected LCU corner satisfy the unit-weight preparation
consumer contract. -/
theorem thresholdGoal_unitPrepareConsumer : ThresholdUnitPrepareConsumer := by
  refine ⟨?_, ?_⟩
  · intro J _ _ j₀
    exact thresholdGoal_unit_prepare j₀
  · intro J I _ _ _ _ U j₀ ψ
    exact thresholdGoal_unit_prepare_lcu U j₀ ψ

/-- Running concatenated memory-event lists equals running the first list and then the second. -/
theorem clause11_runMem_append (s : MemState) (a b : List MemEvent) :
    runMem s (a ++ b) = runMem (runMem s a) b := by
  simp only [runMem]
  exact List.foldl_append

/-- The initial live-memory count is at most the peak memory of any event trace. -/
theorem clause11_live_le_peak (s : MemState) (es : List MemEvent) : s.live ≤ peak s es := by
  induction es with
  | nil => exact le_refl _
  | cons e es _ => exact le_max_left _ _

/-- The final live-memory count is at most the peak memory of the event trace. -/
theorem clause11_run_live_le_peak (s : MemState) (es : List MemEvent) :
    (runMem s es).live ≤ peak s es := by
  induction es generalizing s with
  | nil => exact le_refl _
  | cons e es ih =>
    have hrun : runMem s (e :: es) = runMem (step s e) es := rfl
    rw [hrun]
    exact le_trans (ih (step s e)) (le_max_right _ _)

/-- The peak of a concatenated trace is the maximum of the first peak and the second peak
measured from the intermediate state. -/
theorem clause11_peak_append (s : MemState) (a b : List MemEvent) :
    peak s (a ++ b) = max (peak s a) (peak (runMem s a) b) := by
  induction a generalizing s with
  | nil =>
    simp only [List.nil_append, runMem, List.foldl_nil]
    exact (Nat.max_eq_right (clause11_live_le_peak s b)).symm
  | cons e a ih =>
    simp only [List.cons_append, peak]
    rw [ih (step s e)]
    have hrun : runMem s (e :: a) = runMem (step s e) a := rfl
    rw [hrun]
    omega

/-- Allocating a register that is not already live increases the live-memory count by its
declared size. -/
theorem clause11_live_alloc (s : MemState) (r : RegId) (sz : ℕ) (h : r ∉ s.liveSet) :
    (step s (.alloc r sz)).live = s.live + sz := by
  simp only [step, MemState.live]
  have hsum : ∑ x ∈ insert r s.liveSet, Function.update s.sizes r sz x
      = sz + ∑ x ∈ s.liveSet, s.sizes x := by
    rw [Finset.sum_insert h]
    have hupd : ∀ x ∈ s.liveSet, Function.update s.sizes r sz x = s.sizes x := by
      intro x hx
      have hne : x ≠ r := by
        rintro rfl
        exact h hx
      exact Function.update_of_ne hne _ _
    rw [Function.update_self, Finset.sum_congr rfl hupd]
  rw [hsum]
  omega

/-- Releasing a live register decreases the live-memory count by its stored size. -/
theorem clause11_live_release (s : MemState) (r : RegId) (h : r ∈ s.liveSet) :
    (step s (.release r)).live = s.live - s.sizes r := by
  have hadd : s.sizes r + ∑ x ∈ s.liveSet.erase r, s.sizes x = ∑ x ∈ s.liveSet, s.sizes x :=
    Finset.add_sum_erase (s := s.liveSet) (f := s.sizes) (a := r) h
  have hsum : ∑ x ∈ s.liveSet.erase r, s.sizes x
      = (∑ x ∈ s.liveSet, s.sizes x) - s.sizes r := by
    omega
  show s.persistent + ∑ x ∈ s.liveSet.erase r, s.sizes x
      = (s.persistent + ∑ x ∈ s.liveSet, s.sizes x) - s.sizes r
  rw [hsum]
  omega

/-- An uncompute event leaves the live-memory count unchanged. -/
theorem clause11_live_uncompute (s : MemState) (r : RegId) :
    (step s (.uncompute r)).live = s.live := rfl

/-- The number of oracle events of a fixed capability is additive under trace concatenation. -/
theorem clause11_countCap_append (cap : OracleCap) (a b : List MemEvent) :
    countCap cap (a ++ b) = countCap cap a + countCap cap b := by
  induction a with
  | nil => simp [countCap]
  | cons e a ih => simp [countCap, ih]; omega

/-- A budget containing only forward queries cannot cover one controlled query. -/
theorem clause11_forward_cannot_pay_controlled (q : ℕ) :
    ¬((⟨q, 0, 0⟩ : PaidQueries).covers ⟨0, 1, 0⟩) := by
  intro h
  simp only [PaidQueries.covers] at h
  omega

/-- A budget covering a trace bounds its controlled-query and inverse-query counts separately. -/
theorem clause11_usage_bounded (es : List MemEvent) (p : PaidQueries)
    (h : p.covers (usage es)) :
    countCap .controlled es ≤ p.controlled ∧ countCap .inverse es ≤ p.inverse := by
  simpa [usage, PaidQueries.covers] using And.intro h.2.1 h.2.2

/-- The sum of recorded approximation errors is additive under trace concatenation. -/
theorem clause11_errOf_append (a b : List MemEvent) : errOf (a ++ b) = errOf a + errOf b := by
  induction a with
  | nil => simp [errOf]
  | cons e a ih =>
    rcases e <;> simp [errOf, ih, add_assoc]

/-- The accounted time of a concatenated trace is the sum of the times of its two parts. -/
theorem clause11_account_time_append (s : MemState) (a b : List MemEvent) :
    (account s (a ++ b)).time = (account s a).time + (account (runMem s a) b).time := by
  simp [account, List.map_append, List.sum_append]

/-- Reading an entry with `b` addresses records exactly `b` read events. -/
theorem clause11_readEntry_count (r : RegId) (b : ℕ) :
    (List.range b).length
      = countEvent (fun e => if e matches .read _ _ then true else false) (readEntry r b) := by
  have key : ∀ l : List ℕ,
      countEvent (fun e => if e matches .read _ _ then true else false)
          (l.map fun i => .read r i) = l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih =>
      have htrue : (fun e => if e matches .read _ _ then true else false)
          (MemEvent.read r i) = true := rfl
      have hstep : countEvent (fun e => if e matches .read _ _ then true else false)
            ((i :: l).map fun i => MemEvent.read r i)
          = (if (fun e => if e matches .read _ _ then true else false) (MemEvent.read r i)
              then 1 else 0) +
            countEvent (fun e => if e matches .read _ _ then true else false)
              (l.map fun i => MemEvent.read r i) := rfl
      rw [hstep, htrue, ih]
      show 1 + l.length = l.length + 1
      exact Nat.add_comm _ _
  rw [readEntry, key, List.length_range]

/-- The memory-event semantics satisfies the composition, allocation, release, uncompute, and
peak-space laws in the memory core contract. -/
theorem clause11_memoryCore : Clause11MemoryCore := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s a b
    exact clause11_runMem_append s a b
  · intro s a b
    exact clause11_peak_append s a b
  · intro s r sz h
    exact clause11_live_alloc s r sz h
  · intro s r h
    exact clause11_live_release s r h
  · intro s r
    exact clause11_live_uncompute s r
  · intro s es
    exact ⟨clause11_live_le_peak s es, clause11_run_live_le_peak s es⟩

/-- Separate oracle-capability counts and componentwise budgets satisfy the oracle-payment
contract. -/
theorem clause11_oraclePayment : Clause11OraclePayment := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p u h
    exact h.2.1
  · intro q
    exact clause11_forward_cannot_pay_controlled q
  · intro es p h
    exact clause11_usage_bounded es p h
  · intro cap a b
    exact clause11_countCap_append cap a b

/-- Error and time add under concatenation, identical initial states and traces determine
identical resource data, and entry reads have the prescribed count. -/
theorem clause11_oneRunBinding : Clause11OneRunBinding := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b
    exact clause11_errOf_append a b
  · intro s a b
    exact clause11_account_time_append s a b
  · intro r r' hinit hev
    simp [ImplRun.state, ImplRun.peak, ImplRun.resources, hinit, hev]
  · intro r b
    exact clause11_readEntry_count r b

end Qatlib.Concepts.AdversaryBounds.AdvDuality
