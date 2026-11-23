/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem.LatticeDecode
public import Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Theorem11Quan
public import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

@[expose] public section

/-!
# Counted phase queries for compressed weight recovery

The circular phase law avoids identifying real angles that differ by a full
turn. Independent readouts have a derived joint success bound. Every phase
readout uses the actual counted circuit with `M - 1` oracle invocations; the
controlled powers are not counted as single invocations. This is a query
reduction, not an assertion of the paper's full bit-operation runtime.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem

open scoped BigOperators
open Qatlib.Concepts.AmplitudeCore.PhaseEstimation
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.SpectralFilter.PhaseReadout

/-- The two existing Fourier conventions define the same matrix. -/
theorem qft_bhmt (M : ℕ) : QFTMatrix M = bhmt11QFT M := by
  ext x y
  simp only [QFTMatrix, Matrix.of_apply, primRoot, bhmt11QFT,
    ← Complex.exp_int_mul]
  congr 1
  congr 1
  push_cast
  ring

/-- The counted readout kernel agrees with the proven BHMT probability kernel. -/
theorem kernel_bhmt (M : ℕ) (phase : ℝ) :
    qpeKernel M phase = (bhmt11QFT M).conjTranspose.mulVec (bhmt11PhaseState M phase) := by
  have hv : offGridPhase M phase = bhmt11PhaseState M phase := by
    ext y
    simp only [offGridPhase, bhmt11PhaseState]
    congr 1
    congr 1
    push_cast
    ring
  change (QFTMatrix M).conjTranspose.mulVec (offGridPhase M phase) = _
  rw [qft_bhmt, hv]

/-- The actual counted circuit realizes the eigenphase kernel with a clean flag. -/
theorem phase_execution {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 0 < M) (U : Matrix I I ℂ) (state : QState I) (phase : ℝ)
    (heigen : ApplyGate U state = Complex.exp (2 * Real.pi * Complex.I * phase) • state) :
    Run (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ)
      (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle U))
      (countedPhaseCircuit M)
      (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, hM⟩ : Fin M))
        (TensorState (Qatlib.Foundations.PureStateMath.Ket false) state)) =
      (fun p => if p.2.1 then 0 else
        TensorState ((bhmt11QFT M).conjTranspose.mulVec (bhmt11PhaseState M phase)) state
          (p.1, p.2.2)) := by
  rw [(counted_offgrid_qpe_clean_flag M hM U state).1,
    (offgrid_qpe_eigen_and_spectral_law M U state phase hM).1 heigen,
    kernel_bhmt]

/-- A normalized eigenstate's actual measurement marginal is the BHMT label law. -/
theorem phase_mass {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 0 < M) (U : Matrix I I ℂ) (state : QState I) (phase : ℝ)
    (hn : Normalized state)
    (heigen : ApplyGate U state = Complex.exp (2 * Real.pi * Complex.I * phase) • state)
    (label : Fin M) :
    (∑ i : I, ‖Run (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ)
      (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle U))
      (countedPhaseCircuit M)
      (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, hM⟩ : Fin M))
        (TensorState (Qatlib.Foundations.PureStateMath.Ket false) state))
      (label, false, i)‖ ^ 2) = bhmt11OutcomeMass M phase label := by
  rw [phase_execution M hM U state phase heigen]
  simp only [Bool.false_eq_true, ite_false, TensorState, norm_mul, mul_pow]
  rw [← Finset.mul_sum]
  change ‖((bhmt11QFT M).conjTranspose.mulVec (bhmt11PhaseState M phase)) label‖ ^ 2 *
    (∑ i : I, ‖state i‖ ^ 2) = _
  rw [show (∑ i : I, ‖state i‖ ^ 2) = 1 from hn, mul_one]
  rfl

/-- The unit complex number associated with a phase measured in turns. -/
def unitPhase (phase : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * phase : ℝ) : ℂ) * Complex.I)

/-- Integer turns leave the actual complex phase unchanged. -/
theorem unitPhase_shift (phase : ℝ) (turns : ℤ) :
    unitPhase (phase + turns) = unitPhase phase := by
  have he : (((2 * Real.pi * (phase + turns) : ℝ) : ℂ) * Complex.I) =
      (((2 * Real.pi * phase : ℝ) : ℂ) * Complex.I) +
        (turns : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  simp only [unitPhase, he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The chord error is bounded by the circular phase error, including wraparound. -/
theorem phase_chord (phase estimate : ℝ) :
    ‖unitPhase phase - unitPhase estimate‖ ≤
      2 * Real.pi * bhmt11CircleDist phase estimate := by
  let turns : ℤ := round (estimate - phase)
  have he := Qatlib.Papers.PottsPartEval07.ExactRecovery.complex_exp_lipschitz
    (2 * Real.pi * (phase + turns)) (2 * Real.pi * estimate)
  change ‖unitPhase (phase + turns) - unitPhase estimate‖ ≤ _ at he
  rw [unitPhase_shift] at he
  have habs : |2 * Real.pi * (phase + turns) - 2 * Real.pi * estimate| =
      2 * Real.pi * |estimate - phase - (turns : ℝ)| := by
    have hid : 2 * Real.pi * (phase + turns) - 2 * Real.pi * estimate =
        -(2 * Real.pi * (estimate - phase - (turns : ℝ))) := by ring
    rw [hid, abs_neg, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  rw [habs] at he
  simpa only [bhmt_phase_estimation_theorem11_distance_round, turns] using he

/-- The source weight expression evaluated on phases measured in turns. -/
def turnWeight {terms : ℕ} (base scale : ℝ) (coefficient : Fin terms → ℂ)
    (phase : Fin terms → ℝ) : ℝ :=
  base - scale * (∑ a, coefficient a * unitPhase (phase a)).re

/-- Circular phase accuracy propagates to the computed weight without choosing angle lifts. -/
theorem turnWeight_error {terms : ℕ} (base scale : ℝ) (hs : 0 ≤ scale)
    (coefficient : Fin terms → ℂ) (hc : ∀ a, ‖coefficient a‖ ≤ 1)
    (phase estimate : Fin terms → ℝ) (radius : ℝ)
    (he : ∀ a, bhmt11CircleDist (phase a) (estimate a) ≤ radius) :
    |turnWeight base scale coefficient phase - turnWeight base scale coefficient estimate| ≤
      scale * (terms * (2 * Real.pi * radius)) := by
  have hsum : ‖∑ a, coefficient a * (unitPhase (phase a) - unitPhase (estimate a))‖ ≤
      terms * (2 * Real.pi * radius) := by
    calc _ ≤ ∑ a, ‖coefficient a * (unitPhase (phase a) - unitPhase (estimate a))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _a : Fin terms, 2 * Real.pi * radius := by
        apply Finset.sum_le_sum
        intro a _
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _)
          (hc a) |>.trans ((phase_chord (phase a) (estimate a)).trans
            (mul_le_mul_of_nonneg_left (he a) (by positivity)))
      _ = _ := by simp
  have hreal := Complex.abs_re_le_norm
    (∑ a, coefficient a * (unitPhase (phase a) - unitPhase (estimate a)))
  have hid : turnWeight base scale coefficient phase - turnWeight base scale coefficient estimate =
      -(scale * (∑ a, coefficient a * (unitPhase (phase a) - unitPhase (estimate a))).re) := by
    simp only [turnWeight, mul_sub, Finset.sum_sub_distrib, Complex.sub_re]
    ring
  rw [hid, abs_neg, abs_mul, abs_of_nonneg hs]
  exact mul_le_mul_of_nonneg_left (hreal.trans hsum) hs

/-- Recover a natural weight from the observed phase list and integer spacing. -/
def observedWeight {terms : ℕ} (spacing : ℕ) (base scale : ℝ)
    (coefficient : Fin terms → ℂ) (estimate : Fin terms → ℝ) : ℕ :=
  spacing * (latticeDecode spacing (turnWeight base scale coefficient estimate)).toNat

/-- The computed weight equals the true Hamming weight when the source lattice formula holds. -/
theorem observedWeight_eq {terms : ℕ} (spacing : ℕ) (hspacing : 0 < spacing)
    (base scale : ℝ) (hs : 0 ≤ scale) (coefficient : Fin terms → ℂ)
    (hc : ∀ a, ‖coefficient a‖ ≤ 1) (phase estimate : Fin terms → ℝ)
    (radius : ℝ) (he : ∀ a, bhmt11CircleDist (phase a) (estimate a) ≤ radius)
    (hp : scale * (terms * (2 * Real.pi * radius)) < spacing / 2)
    (weight : ℕ) (hdiv : spacing ∣ weight)
    (hformula : turnWeight base scale coefficient phase = weight) :
    observedWeight spacing base scale coefficient estimate = weight := by
  obtain ⟨index, rfl⟩ := hdiv
  have hspacingR : (0 : ℝ) < spacing := by exact_mod_cast hspacing
  have hindex : turnWeight base scale coefficient phase = (index : ℝ) * spacing := by
    rw [hformula, Nat.cast_mul]
    ring
  have herror : |turnWeight base scale coefficient estimate - (index : ℝ) * spacing| <
      spacing / 2 := by
    rw [← hindex, abs_sub_comm]
    exact (turnWeight_error base scale hs coefficient hc phase estimate radius he).trans_lt hp
  have hdecode := latticeDecode_eq hspacingR (index : ℤ) herror
  simp only [observedWeight, hdecode, Int.toNat_natCast]

/-- The product Born mass of independently observed finite QPE labels. -/
def batchMass {terms : ℕ} (M : ℕ) (phase : Fin terms → ℝ)
    (record : Fin terms → Fin M) : ℝ :=
  ∏ a, bhmt11OutcomeMass M (phase a) (record a)

/-- The probability that every recorded phase lies in the stated circular window. -/
def batchGoodMass {terms : ℕ} (M : ℕ) (phase : Fin terms → ℝ) (radius : ℝ) : ℝ :=
  ∑ record : Fin terms → Fin M,
    if ∀ a, bhmt11CircleDist ((record a).val / (M : ℝ)) (phase a) ≤ radius
    then batchMass M phase record else 0

/-- Independent finite QPE masses sum to one. -/
theorem batchMass_sum {terms : ℕ} (M : ℕ) (hM : 0 < M) (phase : Fin terms → ℝ) :
    (∑ record : Fin terms → Fin M, batchMass M phase record) = 1 := by
  simp only [batchMass]
  rw [← Fintype.prod_sum]
  simp only [bhmt_phase_estimation_theorem11_normalization M _ hM, Finset.prod_const_one]

/-- The all-good event factors into the individual circular-window masses. -/
theorem batchGoodMass_prod {terms : ℕ} (M : ℕ) (phase : Fin terms → ℝ) (radius : ℝ) :
    batchGoodMass M phase radius = ∏ a, bhmt11WindowMass M (phase a) radius := by
  classical
  unfold batchGoodMass bhmt11WindowMass
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro record _
  by_cases hg : ∀ a, bhmt11CircleDist ((record a).val / (M : ℝ)) (phase a) ≤ radius
  · simp [hg, batchMass]
  · simp only [hg, ite_false]
    obtain ⟨a, ha⟩ := not_forall.mp hg
    exact (Finset.prod_eq_zero (Finset.mem_univ a) (ite_eq_right ha)).symm

/-- A finite product of nonnegative success masses loses at most the sum of failures. -/
theorem product_failure {A : Type*} (set : Finset A) (mass : A → ℝ) (failure : ℝ)
    (hf : 0 ≤ failure) (hm : ∀ a ∈ set, 0 ≤ mass a)
    (hb : ∀ a ∈ set, 1 - failure ≤ mass a) :
    1 - set.card * failure ≤ ∏ a ∈ set, mass a := by
  classical
  induction set using Finset.induction with
  | empty => simp
  | @insert a set ha ih =>
    have hrest := ih (fun b h => hm b (Finset.mem_insert_of_mem h))
      (fun b h => hb b (Finset.mem_insert_of_mem h))
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
    have hprod : 0 ≤ ∏ b ∈ set, mass b :=
      Finset.prod_nonneg (fun b h => hm b (Finset.mem_insert_of_mem h))
    have hma := hm a (Finset.mem_insert_self a set)
    have hba := hb a (Finset.mem_insert_self a set)
    by_cases hneg : 1 - set.card * failure < 0
    · have htarget : 1 - ((set.card : ℝ) + 1) * failure ≤ 0 := by nlinarith
      exact htarget.trans (mul_nonneg hma hprod)
    · have hmul := mul_le_mul hba hrest (by linarith : 0 ≤ 1 - set.card * failure) hma
      have hc : 0 ≤ (set.card : ℝ) * failure ^ 2 := by positivity
      nlinarith

/-- A union bound derived from the QPE tail controls all phases at once. -/
theorem batchGoodMass_bound {terms : ℕ} (M : ℕ) (hM : 0 < M)
    (phase : Fin terms → ℝ) (window : ℝ) (hw : 1 < window) :
    1 - terms / (2 * (window - 1)) ≤ batchGoodMass M phase (window / (M : ℝ)) := by
  rw [batchGoodMass_prod]
  have hp := product_failure (Finset.univ : Finset (Fin terms))
    (fun a => bhmt11WindowMass M (phase a) (window / (M : ℝ)))
    (1 / (2 * (window - 1))) (by positivity)
    (fun a _ => by
      unfold bhmt11WindowMass
      apply Finset.sum_nonneg
      intro z _
      split_ifs
      · exact sq_nonneg _
      · exact le_rfl)
    (fun a _ => bhmt_phase_estimation_theorem11_tail M (phase a) hM window hw)
  simpa only [Finset.card_univ, Fintype.card_fin, div_eq_mul_inv, one_mul] using hp

/-- The query ledger is computed from every actual QPE word in the batch. -/
def batchQueries (terms M : ℕ) : ℕ :=
  ∑ _a : Fin terms, QueryCount (countedPhaseCircuit (I := Unit) M)

/-- The actual batch uses exactly `terms * (M - 1)` oracle calls. -/
theorem batchQueries_eq (terms M : ℕ) (hM : 0 < M) :
    batchQueries terms M = terms * (M - 1) := by
  unfold batchQueries
  have hc := (counted_offgrid_qpe_clean_flag M hM
    (1 : Matrix Unit Unit ℂ) (fun _ => (1 : ℂ))).2.1
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- The batch has a positive query count when it has a phase and at least two labels. -/
theorem batchQueries_pos {terms M : ℕ} (hd : 0 < terms) (hM : 1 < M) :
    0 < batchQueries terms M := by
  rw [batchQueries_eq terms M (by omega)]
  exact Nat.mul_pos hd (by omega)

/-- The label count chosen from the requested circular tolerance and batch size. -/
def sampleSize (terms : ℕ) (radius : ℝ) : ℕ :=
  ⌈((2 : ℝ) * terms + 1) / radius⌉₊

/-- The chosen precision makes the derived joint success probability at least three quarters. -/
theorem batch_three_quarters {terms : ℕ} (hd : 0 < terms) (phase : Fin terms → ℝ)
    (radius : ℝ) (hr : 0 < radius) :
    3 / 4 ≤ batchGoodMass (sampleSize terms radius) phase radius := by
  let M := sampleSize terms radius
  have hdR : (0 : ℝ) < terms := by exact_mod_cast hd
  have hM : 0 < M := Nat.ceil_pos.mpr (by positivity)
  have hceil : ((2 : ℝ) * terms + 1) / radius ≤ M := Nat.le_ceil _
  have hwindow : 2 * (terms : ℝ) + 1 ≤ (M : ℝ) * radius :=
    (div_le_iff₀ hr).mp hceil
  have hw : 1 < (M : ℝ) * radius := by linarith
  have hb := batchGoodMass_bound M hM phase ((M : ℝ) * radius) hw
  have hden : 0 < 2 * ((M : ℝ) * radius - 1) := by linarith
  have hfail : (terms : ℝ) / (2 * ((M : ℝ) * radius - 1)) ≤ 1 / 4 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have he : (M : ℝ) * radius / (M : ℝ) = radius := by
    have hm : (M : ℝ) ≠ 0 := by positivity
    field_simp
  rw [he] at hb
  linarith

/-- The chosen label count gives a uniform quadratic batch query bound. -/
theorem batch_query_bound {terms : ℕ} (hd : 0 < terms) (radius : ℝ) (hr : 0 < radius) :
    (batchQueries terms (sampleSize terms radius) : ℝ) ≤
      3 * (terms : ℝ) ^ 2 / radius := by
  let M := sampleSize terms radius
  have hdR : (1 : ℝ) ≤ terms := by exact_mod_cast hd
  have hx : 0 < ((2 : ℝ) * terms + 1) / radius := by positivity
  have hM : 0 < M := Nat.ceil_pos.mpr hx
  have hceil : (M : ℝ) < ((2 : ℝ) * terms + 1) / radius + 1 :=
    Nat.ceil_lt_add_one hx.le
  rw [batchQueries_eq terms M hM, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ M),
    Nat.cast_one]
  have hq : (M : ℝ) - 1 ≤ ((2 : ℝ) * terms + 1) / radius := by linarith
  calc (terms : ℝ) * ((M : ℝ) - 1)
      ≤ (terms : ℝ) * (((2 : ℝ) * terms + 1) / radius) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
    _ ≤ 3 * (terms : ℝ) ^ 2 / radius := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff_of_pos_right hr).mpr
      nlinarith

/-- Fixed coefficients and exponent bound an entire family of phase counts uniformly. -/
theorem batch_query_family (count : ℕ → ℕ) (coefficient exponent : ℕ)
    (hfamily : ∀ k, count k ≤ coefficient * k ^ exponent)
    (radius : ℝ) (hr : 0 < radius) (k : ℕ) (hd : 0 < count k) :
    (batchQueries (count k) (sampleSize (count k) radius) : ℝ) ≤
      3 * (coefficient : ℝ) ^ 2 * (k : ℝ) ^ (2 * exponent) / radius := by
  have hb := batch_query_bound hd radius hr
  have hcount : (count k : ℝ) ≤ (coefficient : ℝ) * (k : ℝ) ^ exponent := by
    exact_mod_cast hfamily k
  have hsq : (count k : ℝ) ^ 2 ≤ ((coefficient : ℝ) * (k : ℝ) ^ exponent) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hcount 2
  calc _ ≤ 3 * (count k : ℝ) ^ 2 / radius := hb
    _ ≤ 3 * ((coefficient : ℝ) * (k : ℝ) ^ exponent) ^ 2 / radius := by gcongr
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem
