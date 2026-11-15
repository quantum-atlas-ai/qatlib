/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
public import Qatlib.Concepts.SpectralReadout.PhaseReadout.BornPerturbation
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Tactic.LinearCombination

@[expose] public section
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

namespace Qatlib.Concepts.MatrixAccess.CircuitPipeline

open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate

set_option linter.unusedSectionVars false

noncomputable def cayleyPairWord (p : ℚ × ℕ) : Circuit Bool :=
  [Step.gate Hadamard, Step.gate (rationalPhaseGate (countedCayleyPhase p.1 p.2).1)]

noncomputable def idealPairWord (p : ℚ × ℕ) : Circuit Bool :=
  [Step.gate Hadamard, Step.gate (Rz (p.1 : ℝ))]

noncomputable def cayleyPhaseWord (xs : List (ℚ × ℕ)) : Circuit Bool :=
  xs.flatMap cayleyPairWord

noncomputable def idealPhaseWord (xs : List (ℚ × ℕ)) : Circuit Bool :=
  xs.flatMap idealPairWord

noncomputable def cayleyHadamardTest (x : ℚ) (k : ℕ) : Circuit Bool :=
  [Step.gate Hadamard, Step.gate (rationalPhaseGate (countedCayleyPhase x k).1),
    Step.gate Hadamard]

/-- The Cayley pair word contains exactly two gates. -/
theorem cayleyPairWord_gateCount (p : ℚ × ℕ) : GateCount (cayleyPairWord p) = 2 := by
  simp [cayleyPairWord]

/-- The Cayley pair word makes no oracle queries. -/
theorem cayleyPairWord_queryCount (p : ℚ × ℕ) : QueryCount (cayleyPairWord p) = 0 := by
  simp [cayleyPairWord]

/-- The ideal pair word contains exactly two gates. -/
theorem idealPairWord_gateCount (p : ℚ × ℕ) : GateCount (idealPairWord p) = 2 := by
  simp [idealPairWord]

/-- The ideal pair word makes no oracle queries. -/
theorem idealPairWord_queryCount (p : ℚ × ℕ) : QueryCount (idealPairWord p) = 0 := by
  simp [idealPairWord]

/-- The identity matrix on `Bool` is unitary. -/
theorem one_mem_unitaryGroup :
    (1 : Matrix Bool Bool ℂ) ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  simp

/-- The Cayley pair word is a unitary circuit. -/
theorem cayleyPairWord_unitary (p : ℚ × ℕ) : IsUnitaryCircuit (cayleyPairWord p) := by
  rw [cayleyPairWord, isUnitaryCircuit_gate, isUnitaryCircuit_gate]
  exact ⟨hadamard_unitary, ⟨rationalPhaseGate_mem_unitaryGroup
    (gaussianRatComplex_countedCayleyPhase_norm p.1 p.2), isUnitaryCircuit_nil⟩⟩

/-- The ideal pair word is a unitary circuit. -/
theorem idealPairWord_unitary (p : ℚ × ℕ) : IsUnitaryCircuit (idealPairWord p) := by
  rw [idealPairWord, isUnitaryCircuit_gate, isUnitaryCircuit_gate]
  exact ⟨hadamard_unitary, ⟨rz_unitary _, isUnitaryCircuit_nil⟩⟩

/-- The Cayley phase word contains twice as many gates as input pairs. -/
theorem cayleyPhaseWord_gateCount (xs : List (ℚ × ℕ)) :
    GateCount (cayleyPhaseWord xs) = 2 * xs.length := by
  induction xs with
  | nil => simp [cayleyPhaseWord]
  | cons p xs ih =>
    have h1 : cayleyPhaseWord (p :: xs) = cayleyPairWord p ++ cayleyPhaseWord xs := rfl
    rw [h1, gateCount_append, cayleyPairWord_gateCount, ih, List.length_cons]
    ring

/-- The Cayley phase word makes no oracle queries. -/
theorem cayleyPhaseWord_queryCount (xs : List (ℚ × ℕ)) :
    QueryCount (cayleyPhaseWord xs) = 0 := by
  induction xs with
  | nil => simp [cayleyPhaseWord]
  | cons p xs ih =>
    have h1 : cayleyPhaseWord (p :: xs) = cayleyPairWord p ++ cayleyPhaseWord xs := rfl
    rw [h1, queryCount_append, cayleyPairWord_queryCount, ih]

/-- The Cayley phase word is a unitary circuit. -/
theorem cayleyPhaseWord_unitary (xs : List (ℚ × ℕ)) :
    IsUnitaryCircuit (cayleyPhaseWord xs) := by
  induction xs with
  | nil => exact isUnitaryCircuit_nil
  | cons p xs ih =>
    have h1 : cayleyPhaseWord (p :: xs) = cayleyPairWord p ++ cayleyPhaseWord xs := rfl
    rw [h1, isUnitaryCircuit_append]
    exact ⟨cayleyPairWord_unitary p, ih⟩

/-- The ideal phase word is a unitary circuit. -/
theorem idealPhaseWord_unitary (xs : List (ℚ × ℕ)) :
    IsUnitaryCircuit (idealPhaseWord xs) := by
  induction xs with
  | nil => exact isUnitaryCircuit_nil
  | cons p xs ih =>
    have h : idealPhaseWord (p :: xs) = idealPairWord p ++ idealPhaseWord xs := rfl
    rw [h, isUnitaryCircuit_append]
    exact ⟨idealPairWord_unitary p, ih⟩

/-- The rational phase gate multiplies the true amplitude by `gaussianRatComplex z` and leaves
the false amplitude unchanged. -/
theorem applyGate_rationalPhaseGate (z : GaussianRat) (ψ : QState Bool) :
    ApplyGate (rationalPhaseGate z) ψ
      = fun b => (if b then gaussianRatComplex z else 1) * ψ b := by
  funext b
  simp only [rationalPhaseGate, ApplyGate, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single_of_mem b (Finset.mem_univ b)
    (fun c _ hc => by rw [ite_eq_right (Ne.symm hc), zero_mul])]
  simp

/-- The true amplitude of the Cayley Hadamard test is half of one minus its approximated phase. -/
theorem cayleyHadamardTest_true_amp (x : ℚ) (k : ℕ) :
    (Run 1 (cayleyHadamardTest x k) (Ket false)) true
      = (1 - gaussianRatComplex (countedCayleyPhase x k).1) / 2 := by
  have h1 : ApplyGate (rationalPhaseGate (countedCayleyPhase x k).1)
      (ApplyGate Hadamard (Ket false))
      = fun b => (if b then gaussianRatComplex (countedCayleyPhase x k).1 else 1)
          * ((Real.sqrt 2 : ℂ)⁻¹) := by
    funext b
    rw [applyGate_hadamard_ket_false, applyGate_rationalPhaseGate]
    (try dsimp only)
    rw [show Plus b = (Real.sqrt 2 : ℂ)⁻¹ from hadamard_apply_false b]
  show (Hadamard.mulVec
    (ApplyGate (rationalPhaseGate (countedCayleyPhase x k).1)
      (ApplyGate Hadamard (Ket false)))) true = _
  rw [h1]
  show (∑ c : Bool, Hadamard true c *
      ((if c then gaussianRatComplex (countedCayleyPhase x k).1 else 1)
        * ((Real.sqrt 2 : ℂ)⁻¹))) = _
  have hsplit : ∑ c : Bool, Hadamard true c *
        ((if c then gaussianRatComplex (countedCayleyPhase x k).1 else 1)
          * ((Real.sqrt 2 : ℂ)⁻¹))
      = Hadamard true true
          * (gaussianRatComplex (countedCayleyPhase x k).1 * ((Real.sqrt 2 : ℂ)⁻¹))
        + Hadamard true false * ((Real.sqrt 2 : ℂ)⁻¹) := by
    simp
  rw [hsplit, hadamard_apply_false]
  have hh : Hadamard true true = -((Real.sqrt 2 : ℂ)⁻¹) := by
    simp [Hadamard]
  rw [hh, inv_sqrt2_mul_self]
  linear_combination (gaussianRatComplex (countedCayleyPhase x k).1)
    * (inv_sqrt2_mul_self.symm)

/-- Conversion to the Euclidean representation preserves addition of Boolean states. -/
theorem toEuclidean_fromVec_add (ψ φ : QState Bool) :
    toEuclidean_fromVec (ψ + φ) = toEuclidean_fromVec ψ + toEuclidean_fromVec φ := rfl

/-- The state error between two phase gates is bounded by the phase difference norm times the
input state norm. -/
theorem norm_applyGate_phasePair_sub (z w : ℂ) (χ : QState Bool) :
    ‖toEuclidean_fromVec (ApplyGate (Matrix.diagonal fun a => if a then z else 1) χ
      - ApplyGate (Matrix.diagonal fun a => if a then w else 1) χ)‖
      ≤ ‖z - w‖ * ‖toEuclidean_fromVec χ‖ := by
  have hfun : (ApplyGate (Matrix.diagonal fun a => if a then z else 1) χ
      - ApplyGate (Matrix.diagonal fun a => if a then w else 1) χ)
      = fun b => (if b then z - w else 0) * χ b := by
    funext b
    simp only [Pi.sub_apply, ApplyGate, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
    have hz : (∑ c : Bool, (if b = c then (if b then z else 1) else 0) * χ c)
        = (if b then z else 1) * χ b := by
      rw [Finset.sum_eq_single_of_mem b (Finset.mem_univ b)
        (fun c _ hc => by rw [ite_eq_right (Ne.symm hc), zero_mul])]
      simp
    have hw : (∑ c : Bool, (if b = c then (if b then w else 1) else 0) * χ c)
        = (if b then w else 1) * χ b := by
      rw [Finset.sum_eq_single_of_mem b (Finset.mem_univ b)
        (fun c _ hc => by rw [ite_eq_right (Ne.symm hc), zero_mul])]
      simp
    rw [hz, hw]
    split_ifs
    · ring
    · simp
  rw [hfun]
  have hχ : ‖χ true‖ ^ 2 ≤ ‖toEuclidean_fromVec χ‖ ^ 2 := by
    have h2 : ‖toEuclidean_fromVec χ‖ ^ 2 = ‖χ true‖ ^ 2 + ‖χ false‖ ^ 2 := by
      rw [norm_toEuclidean_fromVec_sq]
      simp
    linarith [sq_nonneg ‖χ false‖]
  have hm : ∀ c : Bool, ‖(if c then z - w else 0) * χ c‖ ^ 2
      = (if c then ‖z - w‖ ^ 2 else 0) * ‖χ c‖ ^ 2 := by
    intro c
    cases c <;> simp [mul_pow]
  have hsplitSum : (∑ c : Bool, ‖(if c then z - w else 0) * χ c‖ ^ 2)
      = ‖z - w‖ ^ 2 * ‖χ true‖ ^ 2 := by
    rw [Finset.sum_eq_single_of_mem true (Finset.mem_univ true)
      (fun c _ hc => by rw [ite_eq_right hc, zero_mul, norm_zero,
        zero_pow (by norm_num : (2:ℕ) ≠ 0)])]
    rw [hm true]
    simp
  have hb : (0:ℝ) ≤ ‖z - w‖ * ‖toEuclidean_fromVec χ‖ :=
    mul_nonneg (norm_nonneg (z - w)) (norm_nonneg (toEuclidean_fromVec χ))
  have hkey := (sq_le_sq₀ (norm_nonneg (toEuclidean_fromVec
      (fun b => (if b then z - w else 0) * χ b))) hb).mp
    (by
      rw [norm_toEuclidean_fromVec_sq, hsplitSum, mul_pow]
      exact mul_le_mul_of_nonneg_left hχ (sq_nonneg ‖z - w‖))
  exact hkey

noncomputable def pairErrSum : List (ℚ × ℕ) → ℝ
  | [] => 0
  | p :: xs => ((2:ℝ) ⁻¹) ^ p.2 + pairErrSum xs

/-- For bounded phase parameters, the Cayley and ideal word state error is bounded by the
accumulated pair error plus a nonnegative slack, times the input norm. -/
theorem norm_run_cayleyWord_sub_idealWord_acc :
    ∀ (xs : List (ℚ × ℕ)) (a : ℝ), (0:ℝ) ≤ a → ∀ (ψ : QState Bool), (∀ p ∈ xs, |(p.1:ℝ)| ≤ 1) →
      ‖toEuclidean_fromVec (Run 1 (cayleyPhaseWord xs) ψ - Run 1 (idealPhaseWord xs) ψ)‖
        ≤ (a + pairErrSum xs) * ‖toEuclidean_fromVec ψ‖ := by
  intro xs
  induction xs with
  | nil =>
    intro a ha ψ _
    simp only [cayleyPhaseWord, idealPhaseWord, List.flatMap_nil, run_nil, sub_self,
      pairErrSum, add_zero]
    have h0 : toEuclidean_fromVec (0 : QState Bool) = 0 := rfl
    rw [h0, norm_zero]
    exact mul_nonneg ha (norm_nonneg _)
  | cons p xs ih =>
    intro a ha ψ hmem
    have hprem : ∀ q ∈ xs, |(q.1:ℝ)| ≤ 1 :=
      fun q hq => hmem q (List.mem_cons_of_mem _ hq)
    have ihv := ih a ha (ApplyGate (Rz (p.1:ℝ)) (ApplyGate Hadamard ψ)) hprem
    rw [norm_applyGate_of_mem_unitaryGroup (rz_unitary (p.1:ℝ)),
      norm_applyGate_of_mem_unitaryGroup hadamard_unitary] at ihv

    rw [cayleyPhaseWord, idealPhaseWord, List.flatMap_cons, run_append]
    simp only [cayleyPairWord, run_gate, run_nil]
    show ‖toEuclidean_fromVec
        (Run 1 (cayleyPhaseWord xs)
          (ApplyGate (rationalPhaseGate (countedCayleyPhase p.1 p.2).1)
            (ApplyGate Hadamard ψ))
        - Run 1 (idealPhaseWord xs)
          (ApplyGate (Rz (p.1:ℝ)) (ApplyGate Hadamard ψ)))‖ ≤ _

    have hsplit :
        (Run 1 (cayleyPhaseWord xs)
            (ApplyGate (rationalPhaseGate (countedCayleyPhase p.1 p.2).1)
              (ApplyGate Hadamard ψ))
          - Run 1 (idealPhaseWord xs)
            (ApplyGate (Rz (p.1:ℝ)) (ApplyGate Hadamard ψ)))
        = (Run 1 (cayleyPhaseWord xs)
            (ApplyGate (rationalPhaseGate (countedCayleyPhase p.1 p.2).1)
              (ApplyGate Hadamard ψ))
          - Run 1 (cayleyPhaseWord xs)
            (ApplyGate (Rz (p.1:ℝ)) (ApplyGate Hadamard ψ)))
          + (Run 1 (cayleyPhaseWord xs)
            (ApplyGate (Rz (p.1:ℝ)) (ApplyGate Hadamard ψ))
          - Run 1 (idealPhaseWord xs)
            (ApplyGate (Rz (p.1:ℝ)) (ApplyGate Hadamard ψ))) := by
      abel
    rw [hsplit, toEuclidean_fromVec_add]

    have hterm1 : ‖toEuclidean_fromVec
          (Run 1 (cayleyPhaseWord xs)
            (ApplyGate (rationalPhaseGate (countedCayleyPhase p.1 p.2).1)
              (ApplyGate Hadamard ψ))
          - Run 1 (cayleyPhaseWord xs)
            (ApplyGate (Rz (p.1:ℝ)) (ApplyGate Hadamard ψ)))‖
        ≤ ((2:ℝ) ⁻¹) ^ p.2 * ‖toEuclidean_fromVec ψ‖ := by
      rw [← run_sub]
      refine le_trans (norm_run_le 1 one_mem_unitaryGroup (cayleyPhaseWord_unitary xs) _) ?_
      refine le_trans (norm_applyGate_phasePair_sub _ _ _) ?_
      rw [norm_applyGate_of_mem_unitaryGroup hadamard_unitary]
      exact mul_le_mul_of_nonneg_right
        (rational_cayley_explicit_precision p.1 p.2 (hmem p List.mem_cons_self)).2
        (norm_nonneg (toEuclidean_fromVec ψ))
    refine le_trans (norm_add_le
      (toEuclidean_fromVec (Run 1 (cayleyPhaseWord xs)
        (ApplyGate (rationalPhaseGate (countedCayleyPhase p.1 p.2).1)
          (ApplyGate Hadamard ψ))
        - Run 1 (cayleyPhaseWord xs) (ApplyGate (Rz (p.1:ℝ)) (ApplyGate Hadamard ψ))))
      (toEuclidean_fromVec (Run 1 (cayleyPhaseWord xs)
        (ApplyGate (Rz (p.1:ℝ)) (ApplyGate Hadamard ψ))
        - Run 1 (idealPhaseWord xs)
          (ApplyGate (Rz (p.1:ℝ)) (ApplyGate Hadamard ψ))))) ?_
    rw [pairErrSum]
    have hbound := add_le_add hterm1 ihv
    ring_nf at hbound ⊢
    linarith

/-- Folding the pair error increments from `c` gives `c + pairErrSum xs`. -/
theorem foldl_pairErrSum_start (xs : List (ℚ × ℕ)) (c : ℝ) :
    xs.foldl (fun q p => q + ((2:ℝ) ⁻¹) ^ p.2) c = c + pairErrSum xs := by
  induction xs generalizing c with
  | nil => simp [pairErrSum]
  | cons p xs ih =>
    show xs.foldl (fun q p => q + ((2:ℝ) ⁻¹) ^ p.2) (c + ((2:ℝ) ⁻¹) ^ p.2) = _
    rw [ih (c + ((2:ℝ) ⁻¹) ^ p.2)]
    simp only [pairErrSum]
    ring

/-- For a normalized input and bounded phase parameters, the Cayley word is unitary, uses two
gates per pair and no queries, and has squared state error bounded by the squared
accumulated pair error. -/
theorem rational_cayley_actual_word_error_and_cost (xs : List (ℚ × ℕ)) (ψ : QState Bool)
    (hmem : ∀ p ∈ xs, |(p.1:ℝ)| ≤ 1) (hψ : Normalized ψ) :
    IsUnitaryCircuit (cayleyPhaseWord xs) ∧ GateCount (cayleyPhaseWord xs) = 2 * xs.length ∧
    QueryCount (cayleyPhaseWord xs) = 0 ∧
    MeasureProb (Run (1:Matrix Bool Bool ℂ) (cayleyPhaseWord xs) ψ
        - Run (1:Matrix Bool Bool ℂ) (idealPhaseWord xs) ψ) Finset.univ ≤
      (xs.foldl (fun q p => q + ((2:ℝ) ⁻¹) ^ p.2) 0) ^ 2 := by
  refine ⟨cayleyPhaseWord_unitary xs, cayleyPhaseWord_gateCount xs,
    cayleyPhaseWord_queryCount xs, ?_⟩
  have hprob : MeasureProb (Run (1:Matrix Bool Bool ℂ) (cayleyPhaseWord xs) ψ
        - Run (1:Matrix Bool Bool ℂ) (idealPhaseWord xs) ψ) Finset.univ
      = ‖toEuclidean_fromVec (Run (1:Matrix Bool Bool ℂ) (cayleyPhaseWord xs) ψ
          - Run (1:Matrix Bool Bool ℂ) (idealPhaseWord xs) ψ)‖ ^ 2 := by
    rw [MeasureProb]
    exact (norm_toEuclidean_fromVec_sq (Run (1:Matrix Bool Bool ℂ) (cayleyPhaseWord xs) ψ
        - Run (1:Matrix Bool Bool ℂ) (idealPhaseWord xs) ψ)).symm
  rw [hprob]
  have htel := norm_run_cayleyWord_sub_idealWord_acc xs 0 (by norm_num) ψ hmem
  rw [(normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ, mul_one] at htel
  simp only [zero_add] at htel
  calc ‖toEuclidean_fromVec (Run (1:Matrix Bool Bool ℂ) (cayleyPhaseWord xs) ψ
          - Run (1:Matrix Bool Bool ℂ) (idealPhaseWord xs) ψ)‖ ^ 2
      ≤ (pairErrSum xs) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htel 2
    _ = (xs.foldl (fun q p => q + ((2:ℝ) ⁻¹) ^ p.2) 0) ^ 2 := by
        rw [foldl_pairErrSum_start xs 0]
        ring

/-- For a normalized input and bounded phase parameters, any event probability changes by at
most `2 * pairErrSum xs` between the Cayley and ideal words. -/
theorem rational_cayley_actual_word_event_error (xs : List (ℚ × ℕ))
    (ψ : QState Bool) (S : Finset Bool)
    (hmem : ∀ p ∈ xs, |(p.1 : ℝ)| ≤ 1) (hψ : Normalized ψ) :
    |MeasureProb (Run (1 : Matrix Bool Bool ℂ) (cayleyPhaseWord xs) ψ) S -
      MeasureProb (Run (1 : Matrix Bool Bool ℂ) (idealPhaseWord xs) ψ) S| ≤
      2 * pairErrSum xs := by
  have hnorm := norm_run_cayleyWord_sub_idealWord_acc xs 0 (by norm_num) ψ hmem
  rw [(normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ, mul_one] at hnorm
  simp only [zero_add] at hnorm
  have hborn := measureProb_sub_le_two_mul_l2
    (Run (1 : Matrix Bool Bool ℂ) (cayleyPhaseWord xs) ψ)
    (Run (1 : Matrix Bool Bool ℂ) (idealPhaseWord xs) ψ) S
    ((cayleyPhaseWord_unitary xs).normalized_run one_mem_unitaryGroup hψ)
    ((idealPhaseWord_unitary xs).normalized_run one_mem_unitaryGroup hψ)
  exact hborn.trans (mul_le_mul_of_nonneg_left hnorm (by norm_num))

/-- The concrete Cayley phase readout approximates its cosine probability within one eighth,
using three gates, no queries, and a counted phase cost of sixteen. -/
theorem rational_cayley_actual_phase_readout_consumer :
    |MeasureProb (Run (1:Matrix Bool Bool ℂ) (cayleyHadamardTest (1/2) 4) (Ket false)) {true}
        - (1 - Real.cos (1/2))/2| ≤ 1/8 ∧
    GateCount (cayleyHadamardTest (1/2) 4) = 3 ∧
    QueryCount (cayleyHadamardTest (1/2) 4) = 0 ∧
    (countedCayleyPhase (1/2) 4).2.1 = 16 := by
  refine ⟨?_, by simp [cayleyHadamardTest], by simp [cayleyHadamardTest], ?_⟩
  · set z : ℂ := gaussianRatComplex (countedCayleyPhase (1/2) 4).1 with hzdef
    have hz1 : ‖z‖ = 1 := gaussianRatComplex_countedCayleyPhase_norm (1/2) 4

    have hprob : MeasureProb (Run (1:Matrix Bool Bool ℂ) (cayleyHadamardTest (1/2) 4)
        (Ket false)) {true} = (1 - z.re)/2 := by
      rw [MeasureProb, Finset.sum_singleton]
      simp only [BornProb, cayleyHadamardTest_true_amp]
      have hzc : z * conj z = 1 := by
        have h1 : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
        rw [Complex.mul_conj, h1, hz1]
        norm_num
      have hzz : z + conj z = 2 * (z.re : ℂ) := by
        have h1 := Complex.re_eq_add_conj z
        rw [eq_div_iff (by norm_num : (2:ℂ) ≠ 0)] at h1
        exact h1.symm.trans (mul_comm _ _)
      have hnormsq : ‖(1:ℂ) - z‖ ^ 2 = 2 - 2 * z.re := by
        have hzre : z.re ≤ 1 := by
          have h := Complex.abs_re_le_norm z
          rw [hz1, abs_le] at h
          linarith
        have hc : conj (1 - z) = 1 - conj z := by
          rw [map_sub]; simp
        have h2 : ‖1 - z‖ * ‖1 - z‖ = ‖(1 - z) * conj (1 - z)‖ := by
          rw [norm_mul, Complex.norm_conj]
        have h3 : ‖(1 - z) * conj (1 - z)‖ = 2 - 2 * z.re := by
          have h4 : (1 - z) * conj (1 - z) = ((2 - 2 * z.re : ℝ) : ℂ) := by
            have hzz2 : ((2 - 2 * z.re : ℝ) : ℂ) = 2 - (z + conj z) := by
              rw [hzz]
              push_cast
              ring
            have hex : (1 - z) * (1 - conj z) = 2 - (z + conj z) := by
              linear_combination hzc
            rw [hc, hex, ← hzz2]
          rw [h4, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 - 2 * z.re)]
        rw [pow_two, h2, h3]
      rw [norm_div, div_pow, hnormsq]
      norm_num
      ring

    have hprec' : ‖z - Complex.exp ((1/2:ℂ) * Complex.I)‖ ≤ ((2:ℝ) ⁻¹) ^ 4 := by
      have h := (rational_cayley_explicit_precision (1/2) 4 (by push_cast; norm_num)).2
      rw [show (↑(1/2 : ℚ) : ℂ) = (1/2:ℂ) from by norm_num] at h
      exact h
    rw [hprob]

    have hcosre : Real.cos (1/2) = (Complex.exp ((1/2:ℂ) * Complex.I)).re := by
      have h1 : (1/2:ℂ) = ((1/2:ℝ):ℂ) := by norm_num
      rw [h1]
      exact (Complex.exp_ofReal_mul_I_re (1/2:ℝ)).symm
    have hre : |(Complex.exp ((1/2:ℂ) * Complex.I)).re - z.re|
        ≤ ‖Complex.exp ((1/2:ℂ) * Complex.I) - z‖ :=
      Complex.abs_re_le_norm (Complex.exp ((1/2:ℂ) * Complex.I) - z)
    have hflip : ‖Complex.exp ((1/2:ℂ) * Complex.I) - z‖
        = ‖z - Complex.exp ((1/2:ℂ) * Complex.I)‖ := by rw [norm_sub_rev]
    rw [hflip] at hre
    have hbound1 : |(Complex.exp ((1/2:ℂ) * Complex.I)).re - z.re| ≤ ((2:ℝ) ⁻¹) ^ 4 :=
      hre.trans hprec'
    rw [show ((2:ℝ) ⁻¹) ^ 4 = 1 / 16 from by norm_num] at hbound1
    have hcalc : ((1:ℝ) - z.re)/2 - (1 - Real.cos (1/2))/2
        = ((Complex.exp ((1/2:ℂ) * Complex.I)).re - z.re)/2 := by
      rw [hcosre]
      field_simp
      ring
    rw [hcalc, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith
  · have h3 := rational_cayley_actual_squaring_counts (1/2) 4
    rw [h3.2.1]

end Qatlib.Concepts.MatrixAccess.CircuitPipeline
