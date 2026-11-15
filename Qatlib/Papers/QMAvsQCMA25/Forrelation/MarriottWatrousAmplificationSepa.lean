/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.QMAvsQCMA25.Forrelation.MarriottWatrousAmplificationStat
public import Qatlib.Concepts.WalshMoment.Forrelation.QmaVerifierSpectralForrelationSepa
public import Qatlib.Concepts.CoherentSim.CoherentOAA.QSVT
public import Qatlib.Concepts.WalshMoment.Forrelation.CountedThresholdQSVT
public import Qatlib.Concepts.QsvtCore.LinearSystems.RealPolynomialCompletionClosed
public import Qatlib.Concepts.WalshMoment.Forrelation.ThresholdApproximation
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Qatlib.Concepts.SketchArith.SketchBuild.FiniteBoundedDifferences
public import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QmaCompleteness.WitnessSampler Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025 Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Concepts.WalshMoment.Forrelation.QmaVerifierSpectralForrelationSepa Qatlib.Concepts.WalshMoment.Forrelation.SpectralForrelationBasicsSepa Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.CopyEvolution.Discriminate Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Papers.QMAvsQCMA25.Forrelation Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.WalshMoment.Forrelation.SpectralForrelationBasicsSepa
open Qatlib.Concepts.QmaCompleteness.WitnessSampler

namespace Qatlib.Papers.QMAvsQCMA25.Forrelation.MarriottWatrousAmplificationSepa

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Matrix Polynomial
open scoped Matrix.Norms.L2Operator

section G1

variable {n : ℕ}

private def isInitConfig (p : ForrSpace n (Reg n × Bool)) : Bool :=
  (p.1.1 = ZeroStr n) && (p.1.2 = false)
    && (p.2.1.1 = ZeroStr n) && (p.2.1.2 = false) && (p.2.2.2 = false)

private def isAcceptConfig (p : ForrSpace n (Reg n × Bool)) : Bool :=
  p.1.2 && p.2.1.2

private noncomputable def diagReflect {I : Type} [DecidableEq I]
    (pred : I → Bool) : Matrix I I ℂ :=
  Matrix.of fun p q => if p = q then (if pred p then (1 : ℂ) else -1) else 0

/-- The diagonal reflection defined by any Boolean predicate is unitary. -/
private theorem diagReflect_unitary {I : Type} [Fintype I] [DecidableEq I]
    (pred : I → Bool) : diagReflect pred ∈ Matrix.unitaryGroup I ℂ := by
  classical
  set M : Matrix I I ℂ := diagReflect pred with hMdef
  set d : I → ℂ := (fun p => if pred p then (1 : ℂ) else -1) with hd
  have hM : ∀ i j : I, M i j = if i = j then d i else 0 := by
    intro i j
    rw [hMdef, hd]
    rfl
  have hdval : ∀ i : I, d i = 1 ∨ d i = -1 := by
    intro i
    by_cases h : pred i <;> simp [hd, h]
  have hd1 : ∀ i : I, d i * star (d i) = 1 := by
    intro i
    rcases hdval i with h | h <;> rw [h] <;> simp
  have hd1' : ∀ i : I, star (d i) * d i = 1 := fun i => by rw [mul_comm]; exact hd1 i
  have hcentry : ∀ i j : I, (star M) i j = if j = i then star (d j) else 0 := by
    intro i j
    rw [Matrix.star_apply, hM j i]
    by_cases h : j = i
    · simp [h]
    · rw [ite_eq_right h, ite_eq_right h, star_zero]
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  simp only [Matrix.mul_apply, hcentry, hM, ite_mul, mul_ite, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.one_apply]
  by_cases h : i = j
  · rw [ite_eq_left h, ite_eq_left h.symm]
    exact hd1' _
  · rw [ite_eq_right h, ite_eq_right (fun hh => h hh.symm)]

private noncomputable def initReflect (n : ℕ) :
    Matrix (ForrSpace n (Reg n × Bool)) (ForrSpace n (Reg n × Bool)) ℂ :=
  diagReflect (isInitConfig : ForrSpace n (Reg n × Bool) → Bool)

private noncomputable def acceptReflect (n : ℕ) :
    Matrix (ForrSpace n (Reg n × Bool)) (ForrSpace n (Reg n × Bool)) ℂ :=
  diagReflect (isAcceptConfig : ForrSpace n (Reg n × Bool) → Bool)

/-- The initial-subspace reflection is unitary. -/
private theorem initReflect_unitary (n : ℕ) :
    initReflect n ∈ Matrix.unitaryGroup (ForrSpace n (Reg n × Bool)) ℂ :=
  diagReflect_unitary _

/-- The acceptance-subspace reflection is unitary. -/
private theorem acceptReflect_unitary (n : ℕ) :
    acceptReflect n ∈ Matrix.unitaryGroup (ForrSpace n (Reg n × Bool)) ℂ :=
  diagReflect_unitary _

private def swapXW (n : ℕ) : ForrSpace n (Reg n × Bool) ≃ ForrSpace n (Reg n × Bool) where
  toFun p := ((p.2.2.1, p.1.2), (p.2.1.1, p.2.1.2), (p.1.1, p.2.2.2))
  invFun p := ((p.2.2.1, p.1.2), (p.2.1.1, p.2.1.2), (p.1.1, p.2.2.2))
  left_inv p := rfl
  right_inv p := rfl

private def swapXY (n : ℕ) : ForrSpace n (Reg n × Bool) ≃ ForrSpace n (Reg n × Bool) where
  toFun p := ((p.2.1.1, p.1.2), (p.1.1, p.2.1.2), p.2.2)
  invFun p := ((p.2.1.1, p.1.2), (p.1.1, p.2.1.2), p.2.2)
  left_inv p := rfl
  right_inv p := rfl

private noncomputable def permGate {I : Type} [DecidableEq I] (e : I ≃ I) : Matrix I I ℂ :=
  Matrix.of fun p q => if e p = q then (1 : ℂ) else 0

private noncomputable def verifierDataH (n : ℕ) :
    Matrix (ForrSpace n (Reg n × Bool)) (ForrSpace n (Reg n × Bool)) ℂ :=
  TensorGate (TensorGate (HadamardN n) (1 : Matrix Bool Bool ℂ)) 1

/-- A gate induced by a permutation is unitary. -/
private theorem permGate_unitary {I : Type} [Fintype I] [DecidableEq I] (e : I ≃ I) :
    permGate e ∈ Matrix.unitaryGroup I ℂ := by
  classical
  have hsum : ∀ p q : I,
      (∑ r, (if e r = p then (1 : ℂ) else 0) * (if e r = q then (1 : ℂ) else 0))
        = (if p = q then (1 : ℂ) else 0) := by
    intro p q
    rw [Finset.sum_eq_single (e.symm p)]
    · rw [e.apply_symm_apply p]
      by_cases hpq : p = q <;> simp [hpq]
    · intro r _ hr
      have h1 : e r ≠ p := fun hc =>
        hr (e.symm_apply_apply r ▸ by rw [hc])
      rw [ite_eq_right h1]
      ring
    · intro hc
      exact absurd (Finset.mem_univ (e.symm p)) hc
  have key : (Matrix.of fun p q => if e p = q then (1 : ℂ) else 0)
      ∈ Matrix.unitaryGroup I ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    ext p q
    have hconv : (∑ x, (starRingEnd ℂ) (if e x = p then (1 : ℂ) else 0) *
          (if e x = q then (1 : ℂ) else 0))
        = (∑ r, (if e r = p then (1 : ℂ) else 0) * (if e r = q then (1 : ℂ) else 0)) :=
      Finset.sum_congr rfl fun r _ => by
        by_cases hr : e r = p <;> simp [hr]
    exact hconv.trans (hsum p q)
  exact key

/-- The verifier's data Hadamard gate is unitary. -/
private theorem verifierDataH_unitary (n : ℕ) :
    verifierDataH n ∈ Matrix.unitaryGroup (ForrSpace n (Reg n × Bool)) ℂ :=
  tensorGate_unitary (tensorGate_unitary (hadamardN_unitary n) (Submonoid.one_mem _))
    (Submonoid.one_mem _)

private noncomputable def baseVerifier (n : ℕ) : TOCircuit (ForrSpace n (Reg n × Bool)) :=
  [.gate (permGate (swapXW n)), .queryS, .gate (verifierDataH n),
    .gate (permGate (swapXY n)), .queryU]

private noncomputable def baseVerifierInv (n : ℕ) : TOCircuit (ForrSpace n (Reg n × Bool)) :=
  [.queryU, .gate (permGate (swapXY n)), .gate (verifierDataH n),
    .queryS, .gate (permGate (swapXW n))]

/-- The base verifier is a unitary two-oracle circuit. -/
private theorem baseVerifier_unitary (n : ℕ) : IsUnitaryTOCircuit (baseVerifier n) := by
  intro G hG
  have h : G = permGate (swapXW n) ∨ G = verifierDataH n ∨ G = permGate (swapXY n) := by
    simpa [baseVerifier] using! hG
  rcases h with rfl | rfl | rfl
  · exact permGate_unitary _
  · exact verifierDataH_unitary n
  · exact permGate_unitary _

/-- The inverse base verifier is a unitary two-oracle circuit. -/
private theorem baseVerifierInv_unitary (n : ℕ) : IsUnitaryTOCircuit (baseVerifierInv n) := by
  intro G hG
  have h : G = permGate (swapXY n) ∨ G = verifierDataH n ∨ G = permGate (swapXW n) := by
    simpa [baseVerifierInv] using! hG
  rcases h with rfl | rfl | rfl
  · exact permGate_unitary _
  · exact verifierDataH_unitary n
  · exact permGate_unitary _

/-- The base verifier makes exactly one query to each oracle. -/
private theorem baseVerifier_queries (n : ℕ) :
    TOQueryCountS (baseVerifier n) = 1 ∧ TOQueryCountU (baseVerifier n) = 1 :=
  ⟨rfl, rfl⟩

/-- The inverse base verifier makes exactly one query to each oracle. -/
private theorem baseVerifierInv_queries (n : ℕ) :
    TOQueryCountS (baseVerifierInv n) = 1 ∧ TOQueryCountU (baseVerifierInv n) = 1 :=
  ⟨rfl, rfl⟩

private noncomputable def groverStep (n : ℕ) : TOCircuit (ForrSpace n (Reg n × Bool)) :=
  baseVerifier n ++ [.gate (acceptReflect n)] ++ baseVerifierInv n ++ [.gate (initReflect n)]

private noncomputable def ampCircuit (n : ℕ) (k : ℕ) : TOCircuit (ForrSpace n (Reg n × Bool)) :=
  (List.replicate k (groverStep n)).flatten ++ baseVerifier n

private def acceptEvent (n : ℕ) : Finset (ForrSpace n (Reg n × Bool)) :=
  Finset.univ.filter fun p : ForrSpace n (Reg n × Bool) => p.1.2 = true ∧ p.2.1.2 = true

/-- The Grover step is a unitary two-oracle circuit. -/
private theorem groverStep_unitary (n : ℕ) : IsUnitaryTOCircuit (groverStep n) := by
  intro G hG

  have hmem : TOStep.gate G ∈
      ((baseVerifier n ++ [TOStep.gate (acceptReflect n)]) ++ baseVerifierInv n)
        ++ [TOStep.gate (initReflect n)] := by
    simpa [groverStep] using! hG
  rcases List.mem_append.mp hmem with h1 | h2
  · rcases List.mem_append.mp h1 with h11 | h12
    · rcases List.mem_append.mp h11 with h111 | h112
      · exact baseVerifier_unitary n G h111
      · have h : G = acceptReflect n := by
          have h' : TOStep.gate G = TOStep.gate (acceptReflect n) := List.mem_singleton.mp h112
          injection h'
        rw [h]
        exact acceptReflect_unitary n
    · exact baseVerifierInv_unitary n G h12
  · have h : G = initReflect n := by
      have h' : TOStep.gate G = TOStep.gate (initReflect n) := List.mem_singleton.mp h2
      injection h'
    rw [h]
    exact initReflect_unitary n

/-- The empty two-oracle circuit makes zero `S` queries. -/
private theorem toQueryCountS_nil {I : Type} : TOQueryCountS ([] : TOCircuit I) = 0 := rfl

/-- The empty two-oracle circuit makes zero `U` queries. -/
private theorem toQueryCountU_nil {I : Type} : TOQueryCountU ([] : TOCircuit I) = 0 := rfl

/-- The `S`-query count of concatenated circuits is the sum of their query counts. -/
private theorem toQueryCountS_append {I : Type} (C D : TOCircuit I) :
    TOQueryCountS (C ++ D) = TOQueryCountS C + TOQueryCountS D := by
  induction C with
  | nil => rw [List.nil_append, toQueryCountS_nil, zero_add]
  | cons s C ih =>
    cases s <;> simp only [List.cons_append, TOQueryCountS, ih, Nat.add_left_comm, Nat.add_comm]

/-- The `U`-query count of concatenated circuits is the sum of their query counts. -/
private theorem toQueryCountU_append {I : Type} (C D : TOCircuit I) :
    TOQueryCountU (C ++ D) = TOQueryCountU C + TOQueryCountU D := by
  induction C with
  | nil => rw [List.nil_append, toQueryCountU_nil, zero_add]
  | cons s C ih =>
    cases s <;> simp only [List.cons_append, TOQueryCountU, ih, Nat.add_left_comm, Nat.add_comm]

/-- Repeating a circuit `k` times multiplies its `S`-query count by `k`. -/
private theorem toQueryCountS_flatten_replicate {I : Type} (C : TOCircuit I) (k : ℕ) :
    TOQueryCountS ((List.replicate k C).flatten) = k * TOQueryCountS C := by
  induction k with
  | zero => rw [List.replicate_zero, List.flatten_nil, toQueryCountS_nil, Nat.zero_mul]
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, toQueryCountS_append, ih, Nat.succ_mul,
      Nat.add_comm]

/-- Repeating a circuit `k` times multiplies its `U`-query count by `k`. -/
private theorem toQueryCountU_flatten_replicate {I : Type} (C : TOCircuit I) (k : ℕ) :
    TOQueryCountU ((List.replicate k C).flatten) = k * TOQueryCountU C := by
  induction k with
  | zero => rw [List.replicate_zero, List.flatten_nil, toQueryCountU_nil, Nat.zero_mul]
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, toQueryCountU_append, ih, Nat.succ_mul,
      Nat.add_comm]

/-- Each Grover step makes exactly two `S` queries. -/
private theorem groverStep_queryS (n : ℕ) : TOQueryCountS (groverStep n) = 2 := by
  simp only [groverStep, toQueryCountS_append]
  have h1 := (baseVerifier_queries n).1
  have h2 := (baseVerifierInv_queries n).1
  simp only [TOQueryCountS]
  omega

/-- Each Grover step makes exactly two `U` queries. -/
private theorem groverStep_queryU (n : ℕ) : TOQueryCountU (groverStep n) = 2 := by
  simp only [groverStep, toQueryCountU_append]
  have h1 := (baseVerifier_queries n).2
  have h2 := (baseVerifierInv_queries n).2
  simp only [TOQueryCountU]
  omega

/-- The amplification circuit is unitary for every iteration count. -/
private theorem ampCircuit_unitary (n : ℕ) (k : ℕ) : IsUnitaryTOCircuit (ampCircuit n k) := by
  intro G hG
  have hmem : TOStep.gate G ∈ (List.replicate k (groverStep n)).flatten ++ baseVerifier n := by
    simpa [ampCircuit] using! hG
  rcases List.mem_append.mp hmem with h1 | h2
  · have hin : ∀ m : ℕ, TOStep.gate G ∈ (List.replicate m (groverStep n)).flatten →
        G ∈ Matrix.unitaryGroup _ ℂ := by
      intro m
      induction m with
      | zero => intro h; cases h
      | succ m ih =>
        intro h
        simp only [List.replicate_succ, List.flatten_cons, List.mem_append] at h
        rcases h with h | h
        · exact groverStep_unitary n G h
        · exact ih h
    exact hin k h1
  · exact baseVerifier_unitary n G h2

/-- The amplification circuit makes twice its iteration count plus one `S` queries. -/
private theorem ampCircuit_queryS (n : ℕ) (k : ℕ) :
    TOQueryCountS (ampCircuit n k) = 2 * k + 1 := by
  rw [ampCircuit, toQueryCountS_append, toQueryCountS_flatten_replicate, groverStep_queryS]
  have hb : TOQueryCountS (baseVerifier n) = 1 := rfl
  omega

/-- The amplification circuit makes twice its iteration count plus one `U` queries. -/
private theorem ampCircuit_queryU (n : ℕ) (k : ℕ) :
    TOQueryCountU (ampCircuit n k) = 2 * k + 1 := by
  rw [ampCircuit, toQueryCountU_append, toQueryCountU_flatten_replicate,
    groverStep_queryU]
  have hb : TOQueryCountU (baseVerifier n) = 1 := rfl
  omega

private noncomputable def binomialTail (m j0 : ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), if j0 ≤ j then
    (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) else 0

/-- A binomial tail is nonnegative when its success parameter lies between zero and one. -/
private theorem binomialTail_nonneg (m j0 : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ binomialTail m j0 p := by
  unfold binomialTail
  apply Finset.sum_nonneg
  intro j _
  by_cases h : j0 ≤ j
  · simp only [ite_eq_left h]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _))
      (pow_nonneg (by linarith) _)
  · simp only [ite_eq_right h]
    exact le_refl _

/-- A binomial tail is at most one when its success parameter lies between zero and one. -/
private theorem binomialTail_le_one (m j0 : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) : binomialTail m j0 p ≤ 1 := by
  classical
  have hsum : (∑ j ∈ Finset.range (m + 1),
      (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j)) = 1 := by
    have h := add_pow (p : ℝ) (1 - p) m
    have h1 : p + (1 - p) = (1 : ℝ) := by ring
    rw [h1, one_pow] at h
    have h2 : (∑ i ∈ Finset.range (m + 1), p ^ i * (1 - p) ^ (m - i) * (m.choose i : ℝ)) = 1 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using! h.symm
    have h3 : (∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j))
        = (∑ i ∈ Finset.range (m + 1), p ^ i * (1 - p) ^ (m - i) * (m.choose i : ℝ)) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h3, h2]
  unfold binomialTail
  have hle : (∑ j ∈ Finset.range (m + 1), if j0 ≤ j then
      (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) else 0)
      ≤ (∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j)) := by
    apply Finset.sum_le_sum
    intro j _
    by_cases h : j0 ≤ j
    · simp [h]
    · simp only [ite_eq_right h]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _))
        (pow_nonneg (by linarith) _)
  linarith

private noncomputable def binomialTailPolynomial (m j0 : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (m + 1), if j0 ≤ j then
    Polynomial.C (m.choose j : ℝ) * Polynomial.X ^ j *
      (1 - Polynomial.X) ^ (m - j) else 0

/-- Evaluating the binomial tail polynomial gives the corresponding binomial tail. -/
private theorem binomialTailPolynomial_eval (m j0 : ℕ) (p : ℝ) :
    (binomialTailPolynomial m j0).eval p = binomialTail m j0 p := by
  unfold binomialTailPolynomial binomialTail
  simp only [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : j0 ≤ j <;> simp [h]

/-- The natural degree of the binomial tail polynomial is at most the trial count. -/
private theorem binomialTailPolynomial_natDegree_le (m j0 : ℕ) :
    (binomialTailPolynomial m j0).natDegree ≤ m := by
  unfold binomialTailPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  by_cases h : j0 ≤ j
  · simp only [ite_eq_left h]
    have hsub : (1 - Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
      have h := Polynomial.natDegree_sub_le (1 : Polynomial ℝ) Polynomial.X
      simpa using! h
    have hlast : ((1 - Polynomial.X : Polynomial ℝ) ^ (m - j)).natDegree ≤ m - j :=
      (Polynomial.natDegree_pow_le).trans (by simpa using! Nat.mul_le_mul_left (m - j) hsub)
    have hfirst :
        (Polynomial.C (m.choose j : ℝ) * Polynomial.X ^ j).natDegree ≤ j := by
      calc
        _ ≤ (Polynomial.C (m.choose j : ℝ)).natDegree +
            (Polynomial.X ^ j).natDegree := Polynomial.natDegree_mul_le
        _ ≤ 0 + j := by
          rw [Polynomial.natDegree_C]
          exact Nat.add_le_add_left (Polynomial.natDegree_X_pow_le j) _
        _ = j := by simp
    have hjm : j ≤ m := by
      have hmem := Finset.mem_range.mp hj
      omega
    calc
      _ ≤ (Polynomial.C (m.choose j : ℝ) * Polynomial.X ^ j).natDegree +
          ((1 - Polynomial.X : Polynomial ℝ) ^ (m - j)).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ j + (m - j) := Nat.add_le_add hfirst hlast
      _ ≤ m := by omega
  · simp [h]

private noncomputable def binomialTailSignalPolynomial (m j0 : ℕ) : Polynomial ℝ :=
  (binomialTailPolynomial m j0).comp (Polynomial.X ^ 2)

/-- The degree of the binomial tail signal polynomial is at most twice the trial count. -/
private theorem binomialTailSignalPolynomial_degree_le (m j0 : ℕ) :
    (binomialTailSignalPolynomial m j0).degree ≤ (2 * m : WithBot ℕ) := by
  apply Polynomial.degree_le_of_natDegree_le
  unfold binomialTailSignalPolynomial
  calc
    _ ≤ (binomialTailPolynomial m j0).natDegree * (Polynomial.X ^ 2 : Polynomial ℝ).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ m * 2 := by
      rw [Polynomial.natDegree_X_pow]
      exact Nat.mul_le_mul_right 2 (binomialTailPolynomial_natDegree_le m j0)
    _ = 2 * m := Nat.mul_comm _ _

/-- The binomial tail signal polynomial has real parity corresponding to twice the trial count. -/
private theorem binomialTailSignalPolynomial_parity (m j0 : ℕ) :
    Qatlib.Concepts.QspSimulation.Achievability.HasRealParity
      (2 * m) (binomialTailSignalPolynomial m j0) := by
  simp [Qatlib.Concepts.QspSimulation.Achievability.HasRealParity,
    binomialTailSignalPolynomial, Polynomial.comp_assoc, Polynomial.pow_comp, pow_mul]

/-- The absolute value of the binomial tail signal polynomial is at most one on the interval
from minus one to one. -/
private theorem binomialTailSignalPolynomial_bounded (m j0 : ℕ) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, |(binomialTailSignalPolynomial m j0).eval x| ≤ 1 := by
  intro x hx
  have hxabs : |x| ≤ 1 := abs_le.mpr hx
  have hx' : x ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
    rcases abs_le.mp hxabs with ⟨hlo, hhi⟩
    constructor <;> nlinarith [sq_nonneg x]
  have hp := binomialTailPolynomial_eval m j0 (x ^ 2)
  have heval : (binomialTailSignalPolynomial m j0).eval x =
      (binomialTailPolynomial m j0).eval (x ^ 2) := by
    simp [binomialTailSignalPolynomial]
  rw [heval, hp]
  have htail := binomialTail_nonneg m j0 hx'.1 hx'.2
  have htail1 := binomialTail_le_one m j0 hx'.1 hx'.2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- There exist a base phase and twice the trial count many phases whose response has real part
equal to the binomial tail evaluated at the squared input. -/
private theorem exists_binomialTail_phases (m j0 : ℕ) :
    ∃ base : ℂ, ∃ zs : List ℂ,
      Qatlib.Concepts.PhaseGeometry.Phase.IsPhase base ∧
      (∀ z ∈ zs, Qatlib.Concepts.PhaseGeometry.Phase.IsPhase z) ∧
      zs.length = 2 * m ∧
      ∀ x : ℝ, ((Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseP base zs).eval (x : ℂ)).re =
        binomialTail m j0 (x ^ 2) := by
  obtain ⟨base, zs, hb, hzs, hlen, _, hre⟩ :=
    Qatlib.Concepts.QsvtCore.LinearSystems.exists_phases_of_bounded
      (binomialTailSignalPolynomial_degree_le m j0)
      (binomialTailSignalPolynomial_parity m j0)
      (binomialTailSignalPolynomial_bounded m j0)
  refine ⟨base, zs, hb, hzs, hlen, ?_⟩
  intro x
  rw [hre x, binomialTailSignalPolynomial, Polynomial.eval_comp,
    Polynomial.eval_pow, Polynomial.eval_X, binomialTailPolynomial_eval]

private noncomputable def binomialTailBase (m j0 : ℕ) : ℂ :=
  Classical.choose (exists_binomialTail_phases m j0)

private noncomputable def binomialTailPhases (m j0 : ℕ) : List ℂ :=
  Classical.choose (Classical.choose_spec (exists_binomialTail_phases m j0))

/-- The chosen binomial tail base and phase list are phases of the prescribed length and realize
the binomial tail at the squared input through the real response. -/
private theorem binomialTail_phase_word_response (m j0 : ℕ) :
    Qatlib.Concepts.PhaseGeometry.Phase.IsPhase (binomialTailBase m j0) ∧
      (∀ z ∈ binomialTailPhases m j0, Qatlib.Concepts.PhaseGeometry.Phase.IsPhase z) ∧
      (binomialTailPhases m j0).length = 2 * m ∧
      ∀ x : ℝ,
        ((Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseP (binomialTailBase m j0)
          (binomialTailPhases m j0)).eval (x : ℂ)).re = binomialTail m j0 (x ^ 2) := by
  simpa only [binomialTailBase, binomialTailPhases] using!
    Classical.choose_spec (Classical.choose_spec (exists_binomialTail_phases m j0))

private noncomputable def binomialTailWord {H I O : Type}
    [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O]
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (m j0 : ℕ) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Bool × H)) :=
  Qatlib.Concepts.CopyEvolution.Discriminate.compileRealPartQSVT
    (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector L)
    (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector R)
    (binomialTailBase m j0) (binomialTailPhases m j0)

/-- A projected unitary encoding yields an exact encoding of the binomial tail polynomial
evaluated at the encoded matrix's Gram matrix using `binomialTailWord` and average frames. -/
private theorem binomialTailWord_exact_gram_encoding
    {H I O : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
    (m j0 : ℕ) (h : Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding A U L R) :
    Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
      (Polynomial.aeval (Aᴴ * A)
        ((binomialTailPolynomial m j0).map Complex.ofRealHom))
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate
        (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle Uᴴ)
        (binomialTailWord L R m j0))
      (Qatlib.Concepts.QspSimulation.Achievability.averageFrame R)
      (Qatlib.Concepts.QspSimulation.Achievability.averageFrame R) := by
  obtain ⟨hb, hzs, hlen, hre⟩ := binomialTail_phase_word_response m j0
  have heven : (binomialTailPhases m j0).length % 2 = 0 := by rw [hlen]; omega
  have hex := Qatlib.Concepts.QspSimulation.Achievability.realPartQSVT_even_right_projectedEncoding
    h hb (binomialTailPhases m j0) hzs heven
  rw [Qatlib.Concepts.QspSimulation.Achievability.realPartResponse_even_right_eq_singularTransform
    h (binomialTailBase m j0) (binomialTailPhases m j0) heven] at hex
  have ht : Qatlib.Concepts.WalkSearch.Spectral.rightSingularTransform A
      (fun x => (((Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseP (binomialTailBase m j0)
        (binomialTailPhases m j0)).eval (x : ℂ)).re : ℂ)) =
      Polynomial.aeval (Aᴴ * A)
        ((binomialTailPolynomial m j0).map Complex.ofRealHom) := by
    rw [Qatlib.Concepts.WalkSearch.Spectral.gram_aeval_eq_rightSingularTransform]
    congr 1
    funext x
    rw [hre x]
    have hreal : (binomialTail m j0 (x ^ 2) : ℂ) =
        ((binomialTailPolynomial m j0).map Complex.ofRealHom).eval ((x : ℂ) ^ 2) := by
      calc
        _ = (((binomialTailPolynomial m j0).eval (x ^ 2) : ℝ) : ℂ) := by
          rw [binomialTailPolynomial_eval]
        _ = ((binomialTailPolynomial m j0).map Complex.ofRealHom).eval ((x : ℂ) ^ 2) := by
          rw [← Complex.ofReal_pow]
          exact (Polynomial.eval_map_apply (f := Complex.ofRealHom) (x ^ 2)).symm
    exact hreal
  rw [ht] at hex
  simpa only [binomialTailWord,
      Qatlib.Concepts.CopyEvolution.Discriminate.evaluate_compileRealPartQSVT] using! hex

/-- For `x` greater than minus one, the logarithm of one plus `x` is at most `x`. -/
private theorem log_one_add_le {x : ℝ} (hx : -1 < x) : Real.log (1 + x) ≤ x := by
  have hy : 0 < 1 + x := by linarith
  have h := Real.add_one_le_exp (Real.log (1 + x))
  rw [Real.exp_log hy] at h
  linarith

/-- For a Bernoulli parameter between zero and one, its exponential moment is bounded by the
exponential of the mean term plus half the squared argument. -/
private theorem bernoulli_mgf_le (p t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    1 - p + p * Real.exp t ≤ Real.exp (p * t + t ^ 2 / 2) := by
  let dist : FinDist Bool := {
    prob := fun b => if b then p else 1 - p
    nonneg := by intro b; cases b <;> simp <;> linarith
    sum_one := by rw [Fintype.univ_bool]; simp
  }
  have hmgf := finite_hoeffding_centered_mgf Bool dist
    (fun b => if b then (1:ℝ) else 0) 0 1 t (by norm_num)
    (by intro b; cases b <;> simp)
  simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect] at hmgf
  rw [Fintype.univ_bool] at hmgf
  simp [dist] at hmgf
  have hin : (1 - p) * Real.exp (t * (0 - p)) + p * Real.exp (t * (1 - p))
      ≤ Real.exp (t ^ 2 / 8) := by
    have e1 : t * (0 - p) = -(t * p) := by ring
    rw [e1, add_comm]
    exact hmgf
  have key : 1 - p + p * Real.exp t
      = Real.exp (p * t) * ((1 - p) * Real.exp (t * (0 - p)) + p * Real.exp (t * (1 - p))) := by
    have e1 : Real.exp (t * (0 - p)) = Real.exp (-(p * t)) := by
      congr 1; ring
    have e2 : Real.exp (t * (1 - p)) = Real.exp (t - p * t) := by
      congr 1; ring
    have e3 : Real.exp (t - p * t) = Real.exp t * Real.exp (-(p * t)) := by
      rw [← Real.exp_add]
      congr 1
    rw [e1, e2, e3]
    have hcancel : Real.exp (p * t) * Real.exp (-(p * t)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc 1 - p + p * Real.exp t
        = (1 - p + p * Real.exp t) * 1 := by ring
      _ = (1 - p + p * Real.exp t) * (Real.exp (p * t) * Real.exp (-(p * t))) := by
        rw [hcancel]
      _ = (1 - p + p * Real.exp t) * Real.exp (p * t) * Real.exp (-(p * t)) := by
        ring
      _ = Real.exp (p * t) * ((1 - p) * Real.exp (-(p * t)) + p * (Real.exp t * Real.exp (-(p * t)))) := by
        have h : Real.exp (p * t) * Real.exp (-(p * t)) = 1 := hcancel
        have hrhs : Real.exp (p * t) * ((1 - p) * Real.exp (-(p * t)) + p * (Real.exp t * Real.exp (-(p * t))))
            = (1 - p) + p * Real.exp t := by
          calc Real.exp (p * t) * ((1 - p) * Real.exp (-(p * t)) + p * (Real.exp t * Real.exp (-(p * t))))
              = Real.exp (p * t) * (1 - p) * Real.exp (-(p * t)) + Real.exp (p * t) * p * (Real.exp t * Real.exp (-(p * t))) := by
                ring
            _ = (1 - p) * (Real.exp (p * t) * Real.exp (-(p * t))) + p * Real.exp t * (Real.exp (p * t) * Real.exp (-(p * t))) := by
              ring
            _ = (1 - p) * 1 + p * Real.exp t * 1 := by rw [h]
            _ = 1 - p + p * Real.exp t := by ring
        have hlhs : (1 - p + p * Real.exp t) * Real.exp (p * t) * Real.exp (-(p * t))
            = 1 - p + p * Real.exp t := by
          calc (1 - p + p * Real.exp t) * Real.exp (p * t) * Real.exp (-(p * t))
              = (1 - p + p * Real.exp t) * (Real.exp (p * t) * Real.exp (-(p * t))) := by
                ring
            _ = (1 - p + p * Real.exp t) * 1 := by rw [h]
            _ = 1 - p + p * Real.exp t := by ring
        linarith
  rw [key]
  have hmul : Real.exp (p * t) * ((1 - p) * Real.exp (t * (0 - p)) + p * Real.exp (t * (1 - p)))
      ≤ Real.exp (p * t) * Real.exp (t ^ 2 / 8) :=
    mul_le_mul_of_nonneg_left hin (le_of_lt (Real.exp_pos _))
  have hsum : Real.exp (p * t) * Real.exp (t ^ 2 / 8) = Real.exp (p * t + t ^ 2 / 8) := by
    rw [← Real.exp_add]
  have hle : Real.exp (p * t + t ^ 2 / 8) ≤ Real.exp (p * t + t ^ 2 / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg t]
  linarith

/-- For a Bernoulli parameter between zero and one, its exponential moment is bounded by the
exponential of the mean term plus one eighth of the squared argument. -/
private theorem bernoulli_mgf_le_sharp (p t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    1 - p + p * Real.exp t ≤ Real.exp (p * t + t ^ 2 / 8) := by
  let dist : FinDist Bool := {
    prob := fun b => if b then p else 1 - p
    nonneg := by intro b; cases b <;> simp <;> linarith
    sum_one := by rw [Fintype.univ_bool]; simp
  }
  have hmgf := finite_hoeffding_centered_mgf Bool dist
    (fun b => if b then (1:ℝ) else 0) 0 1 t (by norm_num)
    (by intro b; cases b <;> simp)
  simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect] at hmgf
  rw [Fintype.univ_bool] at hmgf
  simp [dist] at hmgf
  have hin : (1 - p) * Real.exp (t * (0 - p)) + p * Real.exp (t * (1 - p))
      ≤ Real.exp (t ^ 2 / 8) := by
    have e1 : t * (0 - p) = -(t * p) := by ring
    rw [e1, add_comm]
    exact hmgf
  have key : 1 - p + p * Real.exp t
      = Real.exp (p * t) * ((1 - p) * Real.exp (t * (0 - p)) + p * Real.exp (t * (1 - p))) := by
    have e1 : Real.exp (t * (0 - p)) = Real.exp (-(p * t)) := by
      congr 1; ring
    have e2 : Real.exp (t * (1 - p)) = Real.exp (t - p * t) := by
      congr 1; ring
    have e3 : Real.exp (t - p * t) = Real.exp t * Real.exp (-(p * t)) := by
      rw [← Real.exp_add]
      congr 1
    rw [e1, e2, e3]
    have hcancel : Real.exp (p * t) * Real.exp (-(p * t)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc 1 - p + p * Real.exp t
        = (1 - p + p * Real.exp t) * 1 := by ring
      _ = (1 - p + p * Real.exp t) * (Real.exp (p * t) * Real.exp (-(p * t))) := by
        rw [hcancel]
      _ = (1 - p + p * Real.exp t) * Real.exp (p * t) * Real.exp (-(p * t)) := by
        ring
      _ = Real.exp (p * t) * ((1 - p) * Real.exp (-(p * t)) + p * (Real.exp t * Real.exp (-(p * t)))) := by
        have h : Real.exp (p * t) * Real.exp (-(p * t)) = 1 := hcancel
        have hrhs : Real.exp (p * t) * ((1 - p) * Real.exp (-(p * t)) + p * (Real.exp t * Real.exp (-(p * t))))
            = (1 - p) + p * Real.exp t := by
          calc Real.exp (p * t) * ((1 - p) * Real.exp (-(p * t)) + p * (Real.exp t * Real.exp (-(p * t))))
              = Real.exp (p * t) * (1 - p) * Real.exp (-(p * t)) + Real.exp (p * t) * p * (Real.exp t * Real.exp (-(p * t))) := by
                ring
            _ = (1 - p) * (Real.exp (p * t) * Real.exp (-(p * t))) + p * Real.exp t * (Real.exp (p * t) * Real.exp (-(p * t))) := by
              ring
            _ = (1 - p) * 1 + p * Real.exp t * 1 := by rw [h]
            _ = 1 - p + p * Real.exp t := by ring
        have hlhs : (1 - p + p * Real.exp t) * Real.exp (p * t) * Real.exp (-(p * t))
            = 1 - p + p * Real.exp t := by
          calc (1 - p + p * Real.exp t) * Real.exp (p * t) * Real.exp (-(p * t))
              = (1 - p + p * Real.exp t) * (Real.exp (p * t) * Real.exp (-(p * t))) := by
                ring
            _ = (1 - p + p * Real.exp t) * 1 := by rw [h]
            _ = 1 - p + p * Real.exp t := by ring
        linarith
  rw [key]
  have hmul : Real.exp (p * t) * ((1 - p) * Real.exp (t * (0 - p)) + p * Real.exp (t * (1 - p)))
      ≤ Real.exp (p * t) * Real.exp (t ^ 2 / 8) :=
    mul_le_mul_of_nonneg_left hin (le_of_lt (Real.exp_pos _))
  have hsum : Real.exp (p * t) * Real.exp (t ^ 2 / 8) = Real.exp (p * t + t ^ 2 / 8) := by
    rw [← Real.exp_add]
  linarith [hmul, hsum]

/-- The binomial exponential-moment sum equals the Bernoulli exponential moment raised to the
trial count. -/
private theorem binomial_mgf_eq (m : ℕ) (p t : ℝ) :
    (∑ j ∈ Finset.range (m + 1),
      (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) * Real.exp (t * j))
      = (1 - p + p * Real.exp t) ^ m := by
  have hsum : (∑ j ∈ Finset.range (m + 1),
      (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) * Real.exp (t * j))
      = (∑ j ∈ Finset.range (m + 1),
          (m.choose j : ℝ) * (p * Real.exp t) ^ j * (1 - p) ^ (m - j)) := by
    apply Finset.sum_congr rfl
    intro j _
    have he : Real.exp (t * j) = (Real.exp t) ^ (j : ℕ) := by
      rw [← Real.exp_nat_mul]
      simp [mul_comm]
    rw [he, mul_pow]
    ring
  rw [hsum]
  have h := add_pow ((p : ℝ) * Real.exp t) (1 - p) m

  have h' : (p * Real.exp t + (1 - p)) ^ m
      = (∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * (p * Real.exp t) ^ i * (1 - p) ^ (m - i)) := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hcomm : 1 - p + p * Real.exp t = p * Real.exp t + (1 - p) := by ring
  rw [hcomm, h']

/-- The binomial upper tail at the natural ceiling of a nonnegative threshold satisfies the
exponential Markov bound for every positive exponential parameter. -/
private theorem markov_exp_ge (m : ℕ) (p t a : ℝ)
    (ht : 0 < t) (hp : 0 ≤ p) (hp1 : p ≤ 1) (ha : 0 ≤ a) :
    binomialTail m ⌈a⌉₊ p
      ≤ Real.exp (-t * a) *
        (∑ j ∈ Finset.range (m + 1),
          (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) * Real.exp (t * j)) := by
  unfold binomialTail
  have hmul : Real.exp (-t * a) *
      (∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) * Real.exp (t * j))
      = (∑ j ∈ Finset.range (m + 1),
          (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) *
            (Real.exp (-t * a) * Real.exp (t * j))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hmul]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : ⌈a⌉₊ ≤ j
  · simp only [ite_eq_left hj]
    have hnonneg : 0 ≤ (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) := by
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _))
        (pow_nonneg (by linarith) _)
    have hceil : (a : ℝ) ≤ (j : ℝ) := by
      have h1 : (a : ℝ) ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
      have h2 : (⌈a⌉₊ : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hj
      linarith
    have hge : 1 ≤ Real.exp (t * ((j : ℝ) - a)) := by
      have hx : 0 ≤ t * ((j : ℝ) - a) := by nlinarith
      have h1 : t * ((j : ℝ) - a) + 1 ≤ Real.exp (t * ((j : ℝ) - a)) :=
        Real.add_one_le_exp (t * ((j : ℝ) - a))
      nlinarith [Real.exp_pos (t * ((j : ℝ) - a))]
    have he : Real.exp (-t * a) * Real.exp (t * j) = Real.exp (t * ((j : ℝ) - a)) := by
      rw [← Real.exp_add]
      ring_nf
    rw [he]
    nlinarith [mul_nonneg hnonneg (le_of_lt (Real.exp_pos (t * ((j : ℝ) - a))))]
  · simp only [ite_eq_right hj]
    have hnonneg : 0 ≤ (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) *
        (Real.exp (-t * a) * Real.exp (t * j)) := by
      refine mul_nonneg ?_ (mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _)))
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _))
        (pow_nonneg (by linarith) _)
    exact hnonneg

/-- For a threshold at least the success parameter, the binomial upper tail is bounded by the
exponential of minus half the trial count times the squared gap. -/
private theorem binomialTail_le_exp_half (m : ℕ) {p τ : ℝ}
    (hm : 0 < m) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hpt : p ≤ τ) :
    binomialTail m ⌈m * τ⌉₊ p ≤ Real.exp (- (m : ℝ) * (τ - p) ^ 2 / 2) := by
  by_cases heq : p = τ
  · have h1 : binomialTail m ⌈(m : ℝ) * τ⌉₊ p ≤ 1 := binomialTail_le_one m _ hp hp1
    have h2 : Real.exp (- (m : ℝ) * (τ - p) ^ 2 / 2) = 1 := by
      rw [heq]
      have : (τ - τ : ℝ) ^ 2 = 0 := by ring
      rw [this, mul_zero]
      simp
    rw [h2]
    linarith
  have hlt : p < τ := lt_of_le_of_ne hpt heq
  have hpos : 0 < τ - p := by linarith
  set t : ℝ := τ - p with htdef
  have ht : 0 < t := by rw [htdef]; linarith
  have hnonneg_a : 0 ≤ (m : ℝ) * τ := mul_nonneg (Nat.cast_nonneg m) hτ
  have hmarkov : binomialTail m ⌈(m : ℝ) * τ⌉₊ p
      ≤ Real.exp (-t * ((m : ℝ) * τ)) *
        (∑ j ∈ Finset.range (m + 1),
          (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) * Real.exp (t * j)) :=
    markov_exp_ge m p t ((m : ℝ) * τ) ht hp hp1 hnonneg_a
  have hmgf : (∑ j ∈ Finset.range (m + 1),
      (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) * Real.exp (t * j))
      = (1 - p + p * Real.exp t) ^ m := binomial_mgf_eq m p t
  have hh : 1 - p + p * Real.exp t ≤ Real.exp (p * t + t ^ 2 / 2) :=
    bernoulli_mgf_le p t hp hp1
  have hbase : 0 ≤ 1 - p + p * Real.exp t := by
    have h1 : 0 < Real.exp t := Real.exp_pos t
    nlinarith [mul_nonneg hp (le_of_lt h1), sub_nonneg.mpr hp1]
  have hpow : (1 - p + p * Real.exp t) ^ m ≤ Real.exp ((m : ℝ) * (p * t + t ^ 2 / 2)) := by
    have h : (1 - p + p * Real.exp t) ^ m
        ≤ (Real.exp (p * t + t ^ 2 / 2)) ^ m :=
      pow_le_pow_left₀ hbase hh m
    have hexp : (Real.exp (p * t + t ^ 2 / 2)) ^ m
        = Real.exp ((m : ℝ) * (p * t + t ^ 2 / 2)) := by
      rw [← Real.exp_nat_mul]
    rw [hexp] at h
    exact h
  rw [hmgf] at hmarkov
  have hmul_le : Real.exp (-t * ((m : ℝ) * τ)) * (1 - p + p * Real.exp t) ^ m
      ≤ Real.exp (-t * ((m : ℝ) * τ)) * Real.exp ((m : ℝ) * (p * t + t ^ 2 / 2)) :=
    mul_le_mul_of_nonneg_left hpow (le_of_lt (Real.exp_pos _))
  have hsum : Real.exp (-t * ((m : ℝ) * τ)) * Real.exp ((m : ℝ) * (p * t + t ^ 2 / 2))
      = Real.exp ((m : ℝ) * (t * (p - τ) + t ^ 2 / 2)) := by
    rw [← Real.exp_add]
    congr 1
    nlinarith
  have htval : t * (p - τ) + t ^ 2 / 2 = - (τ - p) ^ 2 / 2 := by
    rw [htdef]
    ring
  rw [hsum, htval] at hmul_le
  have hfinal : Real.exp ((m : ℝ) * (- (τ - p) ^ 2 / 2))
      = Real.exp (- (m : ℝ) * (τ - p) ^ 2 / 2) := by
    congr 1
    ring
  calc binomialTail m ⌈(m : ℝ) * τ⌉₊ p
      ≤ Real.exp (-t * ((m : ℝ) * τ)) * (1 - p + p * Real.exp t) ^ m := hmarkov
    _ ≤ Real.exp ((m : ℝ) * (- (τ - p) ^ 2 / 2)) := hmul_le
    _ = Real.exp (- (m : ℝ) * (τ - p) ^ 2 / 2) := hfinal

/-- The binomial mass below a floored nonnegative threshold satisfies the exponential Markov
bound using the negative exponential moment. -/
private theorem markov_exp_le (m : ℕ) (p t a : ℝ)
    (ht : 0 < t) (hp : 0 ≤ p) (hp1 : p ≤ 1) (ha : 0 ≤ a) :
    (∑ j ∈ Finset.range (m + 1), if j ≤ ⌊a⌋₊ then
      (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) else 0)
      ≤ Real.exp (t * a) *
        (∑ j ∈ Finset.range (m + 1),
          (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) * Real.exp (-t * j)) := by
  have hmul : Real.exp (t * a) *
      (∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) * Real.exp (-t * j))
      = (∑ j ∈ Finset.range (m + 1),
          (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) *
            (Real.exp (t * a) * Real.exp (-t * j))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hmul]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j ≤ ⌊a⌋₊
  · simp only [ite_eq_left hj]
    have hnonneg : 0 ≤ (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) := by
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _))
        (pow_nonneg (by linarith) _)
    have hfloor : (j : ℝ) ≤ a := by
      have h1 : (j : ℝ) ≤ (⌊a⌋₊ : ℝ) := Nat.cast_le.mpr hj
      have h2 : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha
      linarith
    have hge : 1 ≤ Real.exp (t * (a - (j : ℝ))) := by
      have hx : 0 ≤ t * (a - (j : ℝ)) := by nlinarith
      have h1 : t * (a - (j : ℝ)) + 1 ≤ Real.exp (t * (a - (j : ℝ))) :=
        Real.add_one_le_exp _
      nlinarith
    have he : Real.exp (t * a) * Real.exp (-t * (j : ℝ)) = Real.exp (t * (a - (j : ℝ))) := by
      rw [← Real.exp_add]
      ring_nf
    rw [he]
    nlinarith [mul_nonneg hnonneg (le_of_lt (Real.exp_pos (t * (a - (j : ℝ)))))]
  · simp only [ite_eq_right hj]
    have hnonneg : 0 ≤ (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) *
        (Real.exp (t * a) * Real.exp (-t * (j : ℝ))) := by
      refine mul_nonneg ?_ (mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _)))
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _))
        (pow_nonneg (by linarith) _)
    exact hnonneg

/-- The natural ceiling of a real number minus one is at most its natural floor. -/
private theorem ceil_sub_one_le_floor (a : ℝ) : (⌈a⌉₊ : ℕ) - 1 ≤ ⌊a⌋₊ := by
  have h : ⌈a⌉₊ ≤ ⌊a⌋₊ + 1 := by
    apply Nat.ceil_le.mpr
    have := Nat.lt_floor_add_one a
    exact_mod_cast le_of_lt this
  omega

/-- The binomial weights sum to one for every real parameter. -/
private theorem binomial_total (m : ℕ) (p : ℝ) :
    (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j)) = 1 := by
  have h := add_pow (p : ℝ) (1 - p) m
  have h1 : (p + (1 - p)) ^ m = (1 : ℝ) ^ m := by ring_nf
  rw [h1, one_pow] at h
  have h2 : (∑ i ∈ Finset.range (m + 1), p ^ i * (1 - p) ^ (m - i) * (m.choose i : ℝ)) = 1 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using! h.symm
  have h3 : (∑ j ∈ Finset.range (m + 1),
      (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j))
      = (∑ i ∈ Finset.range (m + 1), p ^ i * (1 - p) ^ (m - i) * (m.choose i : ℝ)) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h3, h2]

/-- For a threshold at most the success parameter, the binomial tail is at least one minus the
exponential of minus half the trial count times the squared gap. -/
private theorem binomialTail_ge_one_sub_exp_half (m : ℕ) {p τ : ℝ}
    (hm : 0 < m) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hpt : τ ≤ p) :
    1 - Real.exp (- (m : ℝ) * (p - τ) ^ 2 / 2) ≤ binomialTail m ⌈m * τ⌉₊ p := by
  by_cases heq : p = τ
  · have h1 : binomialTail m ⌈(m : ℝ) * τ⌉₊ p ≥ 0 := binomialTail_nonneg m _ hp hp1
    have h2 : Real.exp (- (m : ℝ) * (p - τ) ^ 2 / 2) = 1 := by
      rw [heq]
      have : (τ - τ : ℝ) ^ 2 = 0 := by ring
      rw [this, mul_zero]
      simp
    rw [h2]
    linarith
  have hlt : τ < p := lt_of_le_of_ne hpt (fun h => heq h.symm)
  have hpos : 0 < p - τ := by linarith
  set t : ℝ := p - τ with htdef
  have ht : 0 < t := by rw [htdef]; linarith

  have hmarkov : (∑ j ∈ Finset.range (m + 1), if j ≤ ⌊(m : ℝ) * τ⌋₊ then
      (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) else 0)
      ≤ Real.exp (t * ((m : ℝ) * τ)) *
        (∑ j ∈ Finset.range (m + 1),
          (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) * Real.exp (-t * j)) :=
    markov_exp_le m p t ((m : ℝ) * τ) ht hp hp1 (mul_nonneg (Nat.cast_nonneg m) hτ)
  have hmgf : (∑ j ∈ Finset.range (m + 1),
      (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) * Real.exp (-t * j))
      = (1 - p + p * Real.exp (-t)) ^ m := binomial_mgf_eq m p (-t)
  have hh : 1 - p + p * Real.exp (-t) ≤ Real.exp (p * (-t) + (-t) ^ 2 / 2) :=
    bernoulli_mgf_le p (-t) hp hp1
  have hbase : 0 ≤ 1 - p + p * Real.exp (-t) := by
    have h1 : 0 < Real.exp (-t) := Real.exp_pos _
    nlinarith [mul_nonneg hp (le_of_lt h1), sub_nonneg.mpr hp1]
  have hpow : (1 - p + p * Real.exp (-t)) ^ m ≤ Real.exp ((m : ℝ) * (p * (-t) + (-t) ^ 2 / 2)) := by
    have h : (1 - p + p * Real.exp (-t)) ^ m
        ≤ (Real.exp (p * (-t) + (-t) ^ 2 / 2)) ^ m :=
      pow_le_pow_left₀ hbase hh m
    have hexp : (Real.exp (p * (-t) + (-t) ^ 2 / 2)) ^ m
        = Real.exp ((m : ℝ) * (p * (-t) + (-t) ^ 2 / 2)) := by
      rw [← Real.exp_nat_mul]
    rw [hexp] at h
    exact h
  rw [hmgf] at hmarkov
  have hmul_le : Real.exp (t * ((m : ℝ) * τ)) * (1 - p + p * Real.exp (-t)) ^ m
      ≤ Real.exp (t * ((m : ℝ) * τ)) * Real.exp ((m : ℝ) * (p * (-t) + (-t) ^ 2 / 2)) :=
    mul_le_mul_of_nonneg_left hpow (le_of_lt (Real.exp_pos _))
  have hsum : Real.exp (t * ((m : ℝ) * τ)) * Real.exp ((m : ℝ) * (p * (-t) + (-t) ^ 2 / 2))
      = Real.exp ((m : ℝ) * (t * (τ - p) + t ^ 2 / 2)) := by
    rw [← Real.exp_add]
    congr 1
    nlinarith
  have htval : t * (τ - p) + t ^ 2 / 2 = - (p - τ) ^ 2 / 2 := by
    rw [htdef]
    ring
  rw [hsum, htval] at hmul_le
  have hfinal : Real.exp ((m : ℝ) * (- (p - τ) ^ 2 / 2))
      = Real.exp (- (m : ℝ) * (p - τ) ^ 2 / 2) := by
    congr 1
    ring

  have hcomp : 1 - binomialTail m ⌈(m : ℝ) * τ⌉₊ p
      ≤ (∑ j ∈ Finset.range (m + 1), if j ≤ ⌊(m : ℝ) * τ⌋₊ then
        (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) else 0) := by
    have htotal := binomial_total m p
    have hsplit : (∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j))
        = (∑ j ∈ Finset.range (m + 1), if ⌈(m : ℝ) * τ⌉₊ ≤ j then
            (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) else 0)
          + (∑ j ∈ Finset.range (m + 1), if ¬(⌈(m : ℝ) * τ⌉₊ ≤ j) then
            (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : ⌈(m : ℝ) * τ⌉₊ ≤ j <;> simp [h]
    rw [htotal] at hsplit
    have htail_eq : binomialTail m ⌈(m : ℝ) * τ⌉₊ p
        = (∑ j ∈ Finset.range (m + 1), if ⌈(m : ℝ) * τ⌉₊ ≤ j then
          (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) else 0) := rfl
    have hcomp_sum : (∑ j ∈ Finset.range (m + 1), if ¬(⌈(m : ℝ) * τ⌉₊ ≤ j) then
        (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) else 0)
        = 1 - binomialTail m ⌈(m : ℝ) * τ⌉₊ p := by
      rw [htail_eq]
      linarith
    have hsum_le : (∑ j ∈ Finset.range (m + 1), if ¬(⌈(m : ℝ) * τ⌉₊ ≤ j) then
        (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) else 0)
        ≤ (∑ j ∈ Finset.range (m + 1), if j ≤ ⌊(m : ℝ) * τ⌋₊ then
          (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) else 0) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h1 : ¬(⌈(m : ℝ) * τ⌉₊ ≤ j)
      · have h2 : j ≤ ⌊(m : ℝ) * τ⌋₊ := by
          have h3 : j + 1 ≤ ⌈(m : ℝ) * τ⌉₊ := by omega
          have h4 : (⌈(m : ℝ) * τ⌉₊ : ℕ) - 1 ≤ ⌊(m : ℝ) * τ⌋₊ :=
            ceil_sub_one_le_floor ((m : ℝ) * τ)
          omega
        simp [h1, h2]
      · by_cases h2 : j ≤ ⌊(m : ℝ) * τ⌋₊
        · simp only [h1, h2, ite_true, ite_false]
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _))
            (pow_nonneg (sub_nonneg.mpr hp1) _)
        · have : ⌈(m : ℝ) * τ⌉₊ ≤ j := not_not.mp h1
          simp only [this, h2, ite_false]
          exact le_refl _
    linarith [hcomp_sum, hsum_le]
  have : 1 - binomialTail m ⌈(m : ℝ) * τ⌉₊ p
      ≤ Real.exp ((m : ℝ) * (- (p - τ) ^ 2 / 2)) :=
    le_trans hcomp (le_trans hmarkov hmul_le)
  rw [hfinal] at this
  linarith

/-- For a threshold strictly above the success parameter, the binomial upper tail is at most the
exponential of minus twice the trial count times the squared gap. -/
private theorem binomialTail_le_exp_of_lt (m : ℕ) {p τ : ℝ}
    (hm : 0 < m) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hpt : p < τ) :
    binomialTail m ⌈m * τ⌉₊ p ≤ Real.exp (-2 * m * (τ - p) ^ 2) := by
  have hpos : 0 < τ - p := by linarith
  set t : ℝ := 4 * (τ - p) with htdef
  have ht : 0 < t := by rw [htdef]; positivity
  have hmarkov : binomialTail m ⌈(m : ℝ) * τ⌉₊ p
      ≤ Real.exp (-t * ((m : ℝ) * τ)) *
        (∑ j ∈ Finset.range (m + 1),
          (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) * Real.exp (t * j)) :=
    markov_exp_ge m p t ((m : ℝ) * τ) ht hp hp1 (mul_nonneg (Nat.cast_nonneg m) (le_of_lt hτ))
  have hmgf : (∑ j ∈ Finset.range (m + 1),
      (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) * Real.exp (t * j))
      = (1 - p + p * Real.exp t) ^ m := binomial_mgf_eq m p t
  have hh : 1 - p + p * Real.exp t ≤ Real.exp (p * t + t ^ 2 / 8) :=
    bernoulli_mgf_le_sharp p t hp hp1
  have hbase : 0 ≤ 1 - p + p * Real.exp t := by
    have h1 : 0 < Real.exp t := Real.exp_pos t
    nlinarith [mul_nonneg hp (le_of_lt h1), sub_nonneg.mpr hp1]
  have hpow : (1 - p + p * Real.exp t) ^ m ≤ Real.exp ((m : ℝ) * (p * t + t ^ 2 / 8)) := by
    have h : (1 - p + p * Real.exp t) ^ m
        ≤ (Real.exp (p * t + t ^ 2 / 8)) ^ m :=
      pow_le_pow_left₀ hbase hh m
    have hexp : (Real.exp (p * t + t ^ 2 / 8)) ^ m
        = Real.exp ((m : ℝ) * (p * t + t ^ 2 / 8)) := by
      rw [← Real.exp_nat_mul]
    rw [hexp] at h
    exact h
  rw [hmgf] at hmarkov
  have hmul_le : Real.exp (-t * ((m : ℝ) * τ)) * (1 - p + p * Real.exp t) ^ m
      ≤ Real.exp (-t * ((m : ℝ) * τ)) * Real.exp ((m : ℝ) * (p * t + t ^ 2 / 8)) :=
    mul_le_mul_of_nonneg_left hpow (le_of_lt (Real.exp_pos _))
  have hsum : Real.exp (-t * ((m : ℝ) * τ)) * Real.exp ((m : ℝ) * (p * t + t ^ 2 / 8))
      = Real.exp ((m : ℝ) * (t * (p - τ) + t ^ 2 / 8)) := by
    rw [← Real.exp_add]
    congr 1
    nlinarith
  have htval : t * (p - τ) + t ^ 2 / 8 = -2 * (τ - p) ^ 2 := by
    rw [htdef]
    ring
  rw [hsum, htval] at hmul_le
  have hfinal : Real.exp ((m : ℝ) * (-2 * (τ - p) ^ 2))
      = Real.exp (-2 * (m : ℝ) * (τ - p) ^ 2) := by
    congr 1
    ring
  calc binomialTail m ⌈(m : ℝ) * τ⌉₊ p
      ≤ Real.exp (-t * ((m : ℝ) * τ)) * (1 - p + p * Real.exp t) ^ m := hmarkov
    _ ≤ Real.exp ((m : ℝ) * (-2 * (τ - p) ^ 2)) := hmul_le
    _ = Real.exp (-2 * (m : ℝ) * (τ - p) ^ 2) := hfinal

/-- For a threshold strictly below the success parameter, the binomial tail is at least one
minus the exponential of minus twice the trial count times the squared gap. -/
private theorem binomialTail_ge_one_sub_exp_of_gt (m : ℕ) {p τ : ℝ}
    (hm : 0 < m) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hpt : τ < p) :
    1 - Real.exp (-2 * m * (p - τ) ^ 2) ≤ binomialTail m ⌈m * τ⌉₊ p := by
  have hpos : 0 < p - τ := by linarith
  set t : ℝ := 4 * (p - τ) with htdef
  have ht : 0 < t := by rw [htdef]; positivity
  have hmpos : 0 < m := hm

  have hmarkov : (∑ j ∈ Finset.range (m + 1), if j ≤ ⌊(m : ℝ) * τ⌋₊ then
      (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) else 0)
      ≤ Real.exp (t * ((m : ℝ) * τ)) *
        (∑ j ∈ Finset.range (m + 1),
          (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) * Real.exp (-t * j)) :=
    markov_exp_le m p t ((m : ℝ) * τ) ht hp hp1 (mul_nonneg (Nat.cast_nonneg m) (le_of_lt hτ))
  have hmgf : (∑ j ∈ Finset.range (m + 1),
      (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) * Real.exp (-t * j))
      = (1 - p + p * Real.exp (-t)) ^ m := binomial_mgf_eq m p (-t)
  have hh : 1 - p + p * Real.exp (-t) ≤ Real.exp (p * (-t) + (-t) ^ 2 / 8) :=
    bernoulli_mgf_le_sharp p (-t) hp hp1
  have hbase : 0 ≤ 1 - p + p * Real.exp (-t) := by
    have h1 : 0 < Real.exp (-t) := Real.exp_pos _
    nlinarith [mul_nonneg hp (le_of_lt h1), sub_nonneg.mpr hp1]
  have hpow : (1 - p + p * Real.exp (-t)) ^ m
      ≤ Real.exp ((m : ℝ) * (p * (-t) + (-t) ^ 2 / 8)) := by
    have h : (1 - p + p * Real.exp (-t)) ^ m
        ≤ (Real.exp (p * (-t) + (-t) ^ 2 / 8)) ^ m :=
      pow_le_pow_left₀ hbase hh m
    have hexp : (Real.exp (p * (-t) + (-t) ^ 2 / 8)) ^ m
        = Real.exp ((m : ℝ) * (p * (-t) + (-t) ^ 2 / 8)) := by
      rw [← Real.exp_nat_mul]
    rw [hexp] at h
    exact h
  rw [hmgf] at hmarkov
  have hmul_le : Real.exp (t * ((m : ℝ) * τ)) * (1 - p + p * Real.exp (-t)) ^ m
      ≤ Real.exp (t * ((m : ℝ) * τ)) * Real.exp ((m : ℝ) * (p * (-t) + (-t) ^ 2 / 8)) :=
    mul_le_mul_of_nonneg_left hpow (le_of_lt (Real.exp_pos _))
  have hsum : Real.exp (t * ((m : ℝ) * τ)) * Real.exp ((m : ℝ) * (p * (-t) + (-t) ^ 2 / 8))
      = Real.exp ((m : ℝ) * (t * (τ - p) + t ^ 2 / 8)) := by
    rw [← Real.exp_add]
    congr 1
    nlinarith
  have htval : t * (τ - p) + t ^ 2 / 8 = -2 * (p - τ) ^ 2 := by
    rw [htdef]
    ring
  rw [hsum, htval] at hmul_le
  have hfinal : Real.exp ((m : ℝ) * (-2 * (p - τ) ^ 2))
      = Real.exp (-2 * (m : ℝ) * (p - τ) ^ 2) := by
    congr 1
    ring

  have hcomp : 1 - binomialTail m ⌈(m : ℝ) * τ⌉₊ p
      ≤ (∑ j ∈ Finset.range (m + 1), if j ≤ ⌊(m : ℝ) * τ⌋₊ then
        (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) else 0) := by
    have htotal := binomial_total m p
    have hsplit : (∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j))
        = (∑ j ∈ Finset.range (m + 1), if ⌈(m : ℝ) * τ⌉₊ ≤ j then
            (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) else 0)
          + (∑ j ∈ Finset.range (m + 1), if ¬(⌈(m : ℝ) * τ⌉₊ ≤ j) then
            (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : ⌈(m : ℝ) * τ⌉₊ ≤ j <;> simp [h]
    rw [htotal] at hsplit
    have htail_eq : binomialTail m ⌈(m : ℝ) * τ⌉₊ p
        = (∑ j ∈ Finset.range (m + 1), if ⌈(m : ℝ) * τ⌉₊ ≤ j then
          (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) else 0) := rfl
    have hcomp_sum : (∑ j ∈ Finset.range (m + 1), if ¬(⌈(m : ℝ) * τ⌉₊ ≤ j) then
        (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) else 0)
        = 1 - binomialTail m ⌈(m : ℝ) * τ⌉₊ p := by
      rw [htail_eq]
      linarith
    have hsum_le : (∑ j ∈ Finset.range (m + 1), if ¬(⌈(m : ℝ) * τ⌉₊ ≤ j) then
        (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) else 0)
        ≤ (∑ j ∈ Finset.range (m + 1), if j ≤ ⌊(m : ℝ) * τ⌋₊ then
          (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) else 0) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h1 : ¬(⌈(m : ℝ) * τ⌉₊ ≤ j)
      · have h2 : j ≤ ⌊(m : ℝ) * τ⌋₊ := by
          have h3 : j + 1 ≤ ⌈(m : ℝ) * τ⌉₊ := by omega
          have h4 : (⌈(m : ℝ) * τ⌉₊ : ℕ) - 1 ≤ ⌊(m : ℝ) * τ⌋₊ :=
            ceil_sub_one_le_floor ((m : ℝ) * τ)
          omega
        simp [h1, h2]
      · have h2 : ⌈(m : ℝ) * τ⌉₊ ≤ j := not_not.mp h1
        by_cases h3 : j ≤ ⌊(m : ℝ) * τ⌋₊
        · simp only [h2, h3, ite_true]
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _))
            (pow_nonneg (sub_nonneg.mpr hp1) _)
        · simp only [h2, h3, ite_false]
          exact le_refl _
    linarith [hcomp_sum, hsum_le]
  have : 1 - binomialTail m ⌈(m : ℝ) * τ⌉₊ p
      ≤ Real.exp ((m : ℝ) * (-2 * (p - τ) ^ 2)) :=
    le_trans hcomp (le_trans hmarkov hmul_le)
  rw [hfinal] at this
  linarith

private noncomputable def gapStepCount (α β : ℝ) : ℕ :=
  if 0 < α - β then
    max 1 (Nat.floor (32 / (α - β) ^ 2))
  else 1

/-- The two specified parameter pairs with equal gaps give strictly different midpoint-threshold
binomial tails at success parameter one half. -/
private theorem gap_equal_binomial_tail_regression :
    binomialTail (gapStepCount (99 / 100) 0)
        (Nat.floor ((gapStepCount (99 / 100) 0 : ℝ) * ((99 / 100 + 0) / 2))) (1 / 2) >
      binomialTail (gapStepCount 1 (1 / 100))
        (Nat.floor ((gapStepCount 1 (1 / 100) : ℝ) * ((1 + 1 / 100) / 2))) (1 / 2) := by
  have hm₁ : gapStepCount (99 / 100) 0 = 32 := by
    norm_num [gapStepCount, Nat.floor_eq_iff]
  have hm₂ : gapStepCount 1 (1 / 100) = 32 := by
    norm_num [gapStepCount, Nat.floor_eq_iff]
  have hj₁ : Nat.floor ((↑(32 : ℕ) : ℝ) * ((99 / 100 + 0) / 2)) = 15 := by
    norm_num [Nat.floor_eq_iff]
  have hj₂ : Nat.floor ((↑(32 : ℕ) : ℝ) * ((1 + 1 / 100) / 2)) = 16 := by
    norm_num [Nat.floor_eq_iff]
  rw [hm₁, hm₂]
  rw [hj₁, hj₂]
  have hchoose : 0 < Nat.choose 32 15 := Nat.choose_pos (by omega)
  norm_num [binomialTail, Finset.sum_range_succ, hchoose]

/-- No response depending only on `gapStepCount` can match both of the specified
midpoint-threshold binomial tails at success parameter one half. -/
private theorem gap_only_response_cannot_match_binomial_tail
    (response : ℕ → ℝ) :
    ¬ (response (gapStepCount (99 / 100) 0) =
          binomialTail (gapStepCount (99 / 100) 0)
            (Nat.floor ((gapStepCount (99 / 100) 0 : ℝ) * ((99 / 100 + 0) / 2))) (1 / 2) ∧
        response (gapStepCount 1 (1 / 100)) =
          binomialTail (gapStepCount 1 (1 / 100))
            (Nat.floor ((gapStepCount 1 (1 / 100) : ℝ) * ((1 + 1 / 100) / 2))) (1 / 2)) := by
  intro h
  have hsame : gapStepCount (99 / 100) 0 = gapStepCount 1 (1 / 100) := by
    norm_num [gapStepCount]
  have hm₁ : gapStepCount (99 / 100) 0 = 32 := by
    norm_num [gapStepCount, Nat.floor_eq_iff]
  have hm₂ : gapStepCount 1 (1 / 100) = 32 := by
    norm_num [gapStepCount, Nat.floor_eq_iff]
  have hj₁ : Nat.floor ((↑(32 : ℕ) : ℝ) * ((99 / 100 + 0) / 2)) = 15 := by
    norm_num [Nat.floor_eq_iff]
  have hj₂ : Nat.floor ((↑(32 : ℕ) : ℝ) * ((1 + 1 / 100) / 2)) = 16 := by
    norm_num [Nat.floor_eq_iff]
  rcases h with ⟨h₁, h₂⟩
  rw [← hsame] at h₂
  rw [hm₁, hj₁] at h₁
  rw [hm₁, hj₂] at h₂
  have hreg := gap_equal_binomial_tail_regression
  rw [hm₁, hm₂, hj₁, hj₂] at hreg
  linarith [hreg]

/-- Twice the gap step count plus one is at most 256 divided by the squared
completeness-soundness gap under the stated parameter bounds. -/
private theorem gapStepCount_two_mul_add_one_le (α β : ℝ)
    (hβ : 0 ≤ β) (hlt : β < α) (hα : α ≤ 1) :
    (2 * (gapStepCount α β : ℝ) + 1) ≤ 256 / (α - β) ^ 2 := by
  have hpos : 0 < α - β := by linarith
  have hgap_le : α - β ≤ 1 := by linarith
  have hpow : 0 < (α - β) ^ 2 := by positivity
  have hsq_le : (α - β) ^ 2 ≤ 1 := by nlinarith [hgap_le, sq_nonneg (α - β)]
  have hfloor : (Nat.floor (32 / (α - β) ^ 2 : ℝ) : ℝ) ≤ 32 / (α - β) ^ 2 :=
    Nat.floor_le (by positivity : 0 ≤ 32 / (α - β) ^ 2)
  have hone : (1:ℝ) ≤ 32 / (α - β) ^ 2 := by
    rw [le_div_iff₀ hpow]
    nlinarith [sq_nonneg (α - β)]
  have hmax : (max 1 (Nat.floor (32 / (α - β) ^ 2)) : ℝ)
      ≤ 32 / (α - β) ^ 2 := by
    apply max_le hone hfloor
  have h2m : (2 * (max 1 (Nat.floor (32 / (α - β) ^ 2)) : ℝ) + 1)
      ≤ 2 * (32 / (α - β) ^ 2) + 1 := by
    nlinarith [hmax]
  have h264 : (2 * (32 / (α - β) ^ 2) + 1 : ℝ) ≤ 256 / (α - β) ^ 2 := by
    have h3 : (2 * (32 / (α - β) ^ 2) + 1 : ℝ)
        = 64 / (α - β) ^ 2 + 1 := by ring
    rw [h3, le_div_iff₀ hpow]
    have h4 : (64 / (α - β) ^ 2 + 1) * (α - β) ^ 2
        = 64 + (α - β) ^ 2 := by
      field_simp
    rw [h4]
    nlinarith [hsq_le]
  have hrew : gapStepCount α β = max 1 (Nat.floor (32 / (α - β) ^ 2)) := by
    unfold gapStepCount
    rw [ite_eq_left hpos]
  rw [hrew, Nat.cast_max, Nat.cast_one]
  linarith [h2m, h264]

/-- The gap step count is at most 256 divided by the squared completeness-soundness gap under
the stated parameter bounds. -/
private theorem gapStepCount_le (α β : ℝ)
    (hβ : 0 ≤ β) (hlt : β < α) (hα : α ≤ 1) :
    (gapStepCount α β : ℝ) ≤ 256 / (α - β) ^ 2 := by
  have h := gapStepCount_two_mul_add_one_le α β hβ hlt hα
  have h2 : (gapStepCount α β : ℝ) ≤ 2 * (gapStepCount α β : ℝ) + 1 := by
    have : (0:ℝ) ≤ gapStepCount α β := Nat.cast_nonneg _
    linarith
  linarith

/-- The Forrelation mass of every normalized witness is at most spectral Forrelation. -/
private theorem forrWitnessMass_le_spectral (S U : Reg n → Bool) (ψ : QState (Reg n))
    (hψ : Normalized ψ) :
    forrWitnessMass n S U ψ ≤ spectralForrelation n S U :=
  (spectralForrelationBasics (n := n) (S := S) (U := U)).2.2.1 ψ hψ

/-- Every lower bound on spectral Forrelation is achieved or exceeded by the mass of some
normalized witness. -/
private theorem spectral_attained (S U : Reg n → Bool) (α : ℝ)
    (h : α ≤ spectralForrelation n S U) :
    ∃ ψ : QState (Reg n), Normalized ψ ∧ α ≤ forrWitnessMass n S U ψ :=
  (spectralForrelationBasics (n := n) (S := S) (U := U)).2.2.2.1 α h

private noncomputable def toStepMatrix {I : Type} [Fintype I] [DecidableEq I]
    (oS oU : Matrix I I ℂ) : TOStep I → Matrix I I ℂ
  | TOStep.gate U => U
  | TOStep.queryS => oS
  | TOStep.queryU => oU

private noncomputable def toCircuitMatrix {I : Type} [Fintype I] [DecidableEq I]
    (oS oU : Matrix I I ℂ) : TOCircuit I → Matrix I I ℂ
  | [] => 1
  | s :: C => toCircuitMatrix oS oU C * toStepMatrix oS oU s

/-- Prepending a circuit step multiplies its matrix on the right of the remaining circuit
matrix. -/
private theorem toCircuitMatrix_cons {I : Type} [Fintype I] [DecidableEq I]
    (oS oU : Matrix I I ℂ) (s : TOStep I) (C : TOCircuit I) :
    toCircuitMatrix oS oU (s :: C) = toCircuitMatrix oS oU C * toStepMatrix oS oU s :=
  rfl

/-- The matrix of concatenated circuits is the matrix of the second circuit times that of the
first. -/
private theorem toCircuitMatrix_append {I : Type} [Fintype I] [DecidableEq I]
    (oS oU : Matrix I I ℂ) (C D : TOCircuit I) :
    toCircuitMatrix oS oU (C ++ D)
      = toCircuitMatrix oS oU D * toCircuitMatrix oS oU C := by
  induction C with
  | nil => simp [toCircuitMatrix]
  | cons s C ih =>
    rw [List.cons_append, toCircuitMatrix_cons, toCircuitMatrix_cons, ih,
      Matrix.mul_assoc]

/-- Running a two-oracle circuit is multiplication of the input state by its circuit matrix. -/
private theorem toRun_eq_mulVec {I : Type} [Fintype I] [DecidableEq I]
    (oS oU : Matrix I I ℂ) (C : TOCircuit I) (ψ : QState I) :
    TORun oS oU C ψ = toCircuitMatrix oS oU C *ᵥ ψ := by
  induction C generalizing ψ with
  | nil => simp [TORun, toCircuitMatrix]
  | cons s C ih =>
    cases s with
    | gate U =>
      rw [TORun, toCircuitMatrix_cons, toStepMatrix]
      have h : TORun oS oU C (ApplyGate U ψ) = toCircuitMatrix oS oU C *ᵥ ApplyGate U ψ := ih _
      rw [h, ApplyGate, Matrix.mulVec_mulVec]
    | queryS =>
      rw [TORun, toCircuitMatrix_cons, toStepMatrix]
      have h : TORun oS oU C (ApplyGate oS ψ) = toCircuitMatrix oS oU C *ᵥ ApplyGate oS ψ := ih _
      rw [h, ApplyGate, Matrix.mulVec_mulVec]
    | queryU =>
      rw [TORun, toCircuitMatrix_cons, toStepMatrix]
      have h : TORun oS oU C (ApplyGate oU ψ) = toCircuitMatrix oS oU C *ᵥ ApplyGate oU ψ := ih _
      rw [h, ApplyGate, Matrix.mulVec_mulVec]

/-- Running concatenated circuits equals running the first and then the second. -/
private theorem toRun_append {I : Type} [Fintype I] [DecidableEq I]
    (oS oU : Matrix I I ℂ) (C D : TOCircuit I) (ψ : QState I) :
    TORun oS oU (C ++ D) ψ = TORun oS oU D (TORun oS oU C ψ) := by
  rw [toRun_eq_mulVec, toRun_eq_mulVec, toRun_eq_mulVec, toCircuitMatrix_append,
    Matrix.mulVec_mulVec]

/-- A unitary two-oracle circuit evaluated with unitary oracle matrices has a unitary circuit
matrix. -/
private theorem toCircuitMatrix_unitary {I : Type} [Fintype I] [DecidableEq I]
    (oS oU : Matrix I I ℂ) (C : TOCircuit I) (hC : IsUnitaryTOCircuit C)
    (hS : oS ∈ Matrix.unitaryGroup I ℂ) (hU : oU ∈ Matrix.unitaryGroup I ℂ) :
    toCircuitMatrix oS oU C ∈ Matrix.unitaryGroup I ℂ := by
  induction C with
  | nil => simp [toCircuitMatrix]
  | cons s C ih =>
    have htail : IsUnitaryTOCircuit C := by
      intro G hG
      exact hC G (by simp [hG])
    have htailU := ih htail
    cases s with
    | gate G =>
      exact (Matrix.unitaryGroup I ℂ).mul_mem htailU (hC G (by simp))
    | queryS =>
      exact (Matrix.unitaryGroup I ℂ).mul_mem htailU hS
    | queryU =>
      exact (Matrix.unitaryGroup I ℂ).mul_mem htailU hU

/-- Summing a function against the one-hot indicator at `a` returns its value at `a`. -/
private theorem sum_oneHot_left {H : Type} [Fintype H] [DecidableEq H]
    (a : H) (F : H → ℂ) :
    ∑ x, (if x = a then (1 : ℂ) else 0) * F x = F a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hxa
    simp [hxa]
  · simp

/-- Summing a function multiplied on the right by the one-hot indicator at `a` returns its value
at `a`. -/
private theorem sum_oneHot_right {H : Type} [Fintype H] [DecidableEq H]
    (a : H) (F : H → ℂ) :
    ∑ x, F x * (if x = a then (1 : ℂ) else 0) = F a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hxa
    simp [hxa]
  · simp

/-- Compression between one-hot frames selects the matrix entry at the corresponding output and
input configurations. -/
private theorem oneHotFrame_compress {H I O : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (f : I → H) (g : O → H) (M : Matrix H H ℂ) (i : I) (o : O) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress
      (Matrix.of fun h j => if h = g j then (1 : ℂ) else 0) M
      (Matrix.of fun h j => if h = f j then (1 : ℂ) else 0) o i = M (g o) (f i) := by
  classical
  unfold Qatlib.Concepts.Execution.WorkspaceCP.compress
  have hL : ∀ p, ((Matrix.of fun h j => if h = g j then (1 : ℂ) else 0)ᴴ) o p =
      if p = g o then (1 : ℂ) else 0 := by
    intro p
    simp [Matrix.conjTranspose_apply, Matrix.of_apply]
  have hR : ∀ q, (Matrix.of fun h j => if h = f j then (1 : ℂ) else 0) q i =
      if q = f i then (1 : ℂ) else 0 := by
    intro q
    rfl
  calc
    ((Matrix.of fun h j => if h = g j then (1 : ℂ) else 0)ᴴ * M *
        Matrix.of fun h j => if h = f j then (1 : ℂ) else 0) o i
        = ∑ q, (∑ p, (if p = g o then (1 : ℂ) else 0) * M p q) *
            (if q = f i then (1 : ℂ) else 0) := by
          simp only [Matrix.mul_apply, hL, hR]
    _ = ∑ q, M (g o) q * (if q = f i then (1 : ℂ) else 0) := by
          apply Finset.sum_congr rfl
          intro q _
          rw [sum_oneHot_left (g o) (fun p => M p q)]
    _ = M (g o) (f i) := sum_oneHot_right (f i) _

private noncomputable def baseVerifierMatrix (S U : Reg n → Bool) :
    Matrix (ForrSpace n (Reg n × Bool)) (ForrSpace n (Reg n × Bool)) ℂ :=
  toCircuitMatrix (forrBitOracleS n S (Reg n × Bool)) (forrBitOracleU n U (Reg n × Bool))
    (baseVerifier n)

private abbrev MWCoreSpace (n : ℕ) := ForrSpace n (Reg n)

private def mwInputConfig (n : ℕ) (x : Reg n) : MWCoreSpace n :=
  ((ZeroStr n, false), ((ZeroStr n, false), x))

private def mwOutputConfig (n : ℕ) (y : Reg n) : MWCoreSpace n :=
  ((ZeroStr n, true), ((y, true), ZeroStr n))

private noncomputable def mwInputFrame (n : ℕ) :
    Matrix (MWCoreSpace n) (Reg n) ℂ :=
  Matrix.of fun p x => if p = mwInputConfig n x then (1 : ℂ) else 0

private noncomputable def mwOutputFrame (n : ℕ) :
    Matrix (MWCoreSpace n) (Reg n) ℂ :=
  Matrix.of fun p y => if p = mwOutputConfig n y then (1 : ℂ) else 0

/-- The one-hot frame associated with an injective configuration map is an isometry. -/
private theorem oneHotFrame_isometry {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (f : I → H) (hf : Function.Injective f) :
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry
      (Matrix.of fun h i => if h = f i then (1 : ℂ) else 0) := by
  classical
  unfold Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry
  ext i j
  rw [Matrix.mul_apply]
  by_cases hij : i = j
  · subst j
    have hsum : (∑ h, (if h = f i then (1 : ℂ) else 0) *
        (if h = f i then (1 : ℂ) else 0)) = 1 := by
      rw [Finset.sum_eq_single (f i)]
      · simp
      · intro h _ hne
        simp [hne]
      · simp
    simp [Matrix.conjTranspose_apply, Matrix.of_apply]
  · have hsum : (∑ h, (if h = f i then (1 : ℂ) else 0) *
        (if h = f j then (1 : ℂ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro h _
      by_cases hhi : h = f i
      · subst h
        have hne : f i ≠ f j := fun he => hij (hf he)
        simp [hne]
      · simp [hhi]
    simpa [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply, hij] using! hsum

/-- The Marriott-Watrous input configuration map is injective. -/
private theorem mwInputConfig_injective (n : ℕ) :
    Function.Injective (mwInputConfig n) := by
  intro x y h
  exact congrArg (fun p : MWCoreSpace n => p.2.2) h

/-- The Marriott-Watrous output configuration map is injective. -/
private theorem mwOutputConfig_injective (n : ℕ) :
    Function.Injective (mwOutputConfig n) := by
  intro x y h
  exact congrArg (fun p : MWCoreSpace n => p.2.1.1) h

/-- The Marriott-Watrous input frame is an isometry. -/
private theorem mwInputFrame_isometry (n : ℕ) :
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (mwInputFrame n) :=
  oneHotFrame_isometry (mwInputConfig n) (mwInputConfig_injective n)

/-- The Marriott-Watrous output frame is an isometry. -/
private theorem mwOutputFrame_isometry (n : ℕ) :
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (mwOutputFrame n) :=
  oneHotFrame_isometry (mwOutputConfig n) (mwOutputConfig_injective n)

private noncomputable def mwSwapXW (n : ℕ) : MWCoreSpace n ≃ MWCoreSpace n where
  toFun p := ((p.2.2, p.1.2), (p.2.1.1, p.2.1.2), p.1.1)
  invFun p := ((p.2.2, p.1.2), (p.2.1.1, p.2.1.2), p.1.1)
  left_inv p := rfl
  right_inv p := rfl

private noncomputable def mwSwapXY (n : ℕ) : MWCoreSpace n ≃ MWCoreSpace n where
  toFun p := ((p.2.1.1, p.1.2), (p.1.1, p.2.1.2), p.2.2)
  invFun p := ((p.2.1.1, p.1.2), (p.1.1, p.2.1.2), p.2.2)
  left_inv p := rfl
  right_inv p := rfl

private noncomputable def mwDataH (n : ℕ) : Matrix (MWCoreSpace n) (MWCoreSpace n) ℂ :=
  TensorGate (TensorGate (HadamardN n) (1 : Matrix Bool Bool ℂ))
    (1 : Matrix ((Reg n × Bool) × Reg n) ((Reg n × Bool) × Reg n) ℂ)

/-- The Marriott-Watrous core data Hadamard gate is unitary. -/
private theorem mwDataH_unitary (n : ℕ) :
    mwDataH n ∈ Matrix.unitaryGroup (MWCoreSpace n) ℂ :=
  tensorGate_unitary (tensorGate_unitary (hadamardN_unitary n) (Submonoid.one_mem _))
    (Submonoid.one_mem _)

private noncomputable def mwCoreVerifier (n : ℕ) : TOCircuit (MWCoreSpace n) :=
  [.gate (permGate (mwSwapXW n)), .queryS, .gate (mwDataH n),
    .gate (permGate (mwSwapXY n)), .queryU]

/-- The Marriott-Watrous core verifier is a unitary two-oracle circuit. -/
private theorem mwCoreVerifier_unitary (n : ℕ) :
    IsUnitaryTOCircuit (mwCoreVerifier n) := by
  intro G hG
  have h : G = permGate (mwSwapXW n) ∨ G = mwDataH n ∨ G = permGate (mwSwapXY n) := by
    simpa [mwCoreVerifier] using! hG
  rcases h with rfl | rfl | rfl
  · exact permGate_unitary _
  · exact mwDataH_unitary n
  · exact permGate_unitary _

/-- The Marriott-Watrous core verifier makes exactly one query to each oracle. -/
private theorem mwCoreVerifier_queries (n : ℕ) :
    TOQueryCountS (mwCoreVerifier n) = 1 ∧ TOQueryCountU (mwCoreVerifier n) = 1 :=
  ⟨rfl, rfl⟩

private noncomputable def mwCoreVerifierInv (n : ℕ) : TOCircuit (MWCoreSpace n) :=
  (mwCoreVerifier n).reverse

/-- Swapping the `X` and `W` core registers twice is the identity. -/
private theorem mwSwapXW_involutive (n : ℕ) : Function.Involutive (mwSwapXW n) := by
  intro p
  rfl

/-- Swapping the `X` and `Y` core registers twice is the identity. -/
private theorem mwSwapXY_involutive (n : ℕ) : Function.Involutive (mwSwapXY n) := by
  intro p
  rfl

/-- A permutation gate induced by an involution is self-adjoint. -/
private theorem permGate_involutive_selfadjoint {I : Type} [Fintype I] [DecidableEq I]
    (e : I ≃ I) (he : Function.Involutive e) : (permGate e)ᴴ = permGate e := by
  ext p q
  have hiff : e q = p ↔ e p = q := by
    constructor
    · intro h
      have h' : q = e p := by
        calc q = e (e q) := (he q).symm
          _ = e p := congrArg e h
      exact h'.symm
    · intro h
      have h' : p = e q := by
        calc p = e (e p) := (he p).symm
          _ = e q := congrArg e h
      exact h'.symm
  simp only [Matrix.conjTranspose_apply, permGate, Matrix.of_apply]
  simp [hiff]

/-- The Marriott-Watrous core data Hadamard gate is self-adjoint. -/
private theorem mwDataH_selfadjoint (n : ℕ) : (mwDataH n)ᴴ = mwDataH n := by
  have hH : (HadamardN n)ᴴ = HadamardN n := by
    have hsymm (i j : Reg n) : HadamardN n i j = HadamardN n j i := by
      simp [HadamardN, Hadamard, and_comm]
    ext i j
    simp only [Matrix.conjTranspose_apply, RCLike.star_def, hadamardN_conj]
    exact hsymm j i
  unfold mwDataH
  rw [tensorGate_conjTranspose, tensorGate_conjTranspose, hH]
  simp

/-- Every Boolean bit oracle is self-adjoint. -/
private theorem bitOracleOn_selfadjoint_local {I : Type} [Fintype I] [DecidableEq I]
    (f : I → Bool) : (BitOracleOn f)ᴴ = BitOracleOn f := by
  rw [BitOracleOn, permMatrix_conjTranspose (bitFlip_involutive f)]

/-- The Forrelation bit oracle for `S` on the core workspace is self-adjoint. -/
private theorem forrBitOracleS_core_selfadjoint (n : ℕ) (S : Reg n → Bool) :
    (forrBitOracleS n S (Reg n))ᴴ = forrBitOracleS n S (Reg n) := by
  simp only [forrBitOracleS, tensorGate_conjTranspose, Matrix.conjTranspose_one,
    bitOracleOn_selfadjoint_local]

/-- The Forrelation bit oracle for `U` on the core workspace is self-adjoint. -/
private theorem forrBitOracleU_core_selfadjoint (n : ℕ) (U : Reg n → Bool) :
    (forrBitOracleU n U (Reg n))ᴴ = forrBitOracleU n U (Reg n) := by
  simp only [forrBitOracleU, tensorGate_conjTranspose, Matrix.conjTranspose_one,
    bitOracleOn_selfadjoint_local]

/-- If every circuit step is self-adjoint, reversing the circuit gives the adjoint of its
matrix. -/
private theorem toCircuitMatrix_reverse_adjoint {I : Type} [Fintype I] [DecidableEq I]
    (oS oU : Matrix I I ℂ) (C : TOCircuit I)
    (hstep : ∀ s ∈ C, (toStepMatrix oS oU s)ᴴ = toStepMatrix oS oU s) :
    toCircuitMatrix oS oU C.reverse = (toCircuitMatrix oS oU C)ᴴ := by
  induction C with
  | nil => simp [toCircuitMatrix]
  | cons s C ih =>
    have htail : ∀ t ∈ C, (toStepMatrix oS oU t)ᴴ = toStepMatrix oS oU t := by
      intro t ht
      exact hstep t (by simp [ht])
    rw [List.reverse_cons]
    calc
      toCircuitMatrix oS oU (C.reverse ++ [s])
          = toCircuitMatrix oS oU [s] * toCircuitMatrix oS oU C.reverse :=
              toCircuitMatrix_append oS oU C.reverse [s]
      _ = toStepMatrix oS oU s * toCircuitMatrix oS oU C.reverse := by
        simp [toCircuitMatrix]
      _ = toStepMatrix oS oU s * (toCircuitMatrix oS oU C)ᴴ := by rw [ih htail]
      _ = (toCircuitMatrix oS oU C * toStepMatrix oS oU s)ᴴ := by
        rw [Matrix.conjTranspose_mul, hstep s (by simp)]
      _ = (toCircuitMatrix oS oU (s :: C))ᴴ := rfl

private noncomputable def mwCoreVerifierMatrix (S U : Reg n → Bool) :
    Matrix (MWCoreSpace n) (MWCoreSpace n) ℂ :=
  toCircuitMatrix (forrBitOracleS n S (Reg n)) (forrBitOracleU n U (Reg n))
    (mwCoreVerifier n)

/-- The inverse Marriott-Watrous core verifier has matrix equal to the adjoint of the core
verifier matrix. -/
private theorem mwCoreVerifier_matrix_adjoint (n : ℕ) (S U : Reg n → Bool) :
    toCircuitMatrix (forrBitOracleS n S (Reg n)) (forrBitOracleU n U (Reg n))
      (mwCoreVerifierInv n) = (mwCoreVerifierMatrix S U)ᴴ := by
  unfold mwCoreVerifierInv mwCoreVerifierMatrix
  apply toCircuitMatrix_reverse_adjoint
  intro s hs
  cases s with
  | gate G =>
    have hG : G = permGate (mwSwapXW n) ∨ G = mwDataH n ∨
        G = permGate (mwSwapXY n) := by
      simpa [mwCoreVerifier] using! hs
    rcases hG with h | h | h
    · subst G
      exact permGate_involutive_selfadjoint _ (mwSwapXW_involutive n)
    · subst G
      exact mwDataH_selfadjoint n
    · subst G
      exact permGate_involutive_selfadjoint _ (mwSwapXY_involutive n)
  | queryS => exact forrBitOracleS_core_selfadjoint n S
  | queryU => exact forrBitOracleU_core_selfadjoint n U

/-- The inverse Marriott-Watrous core verifier is a unitary two-oracle circuit. -/
private theorem mwCoreVerifierInv_unitary (n : ℕ) :
    IsUnitaryTOCircuit (mwCoreVerifierInv n) := by
  intro G hG
  have hmem : TOStep.gate G ∈ (mwCoreVerifier n).reverse := by
    simpa [mwCoreVerifierInv] using! hG
  have hunit : IsUnitaryTOCircuit (mwCoreVerifier n) := mwCoreVerifier_unitary n
  have horig : TOStep.gate G ∈ mwCoreVerifier n := by
    simpa using! hmem
  exact hunit G horig

private def mwWorkspaceEquiv (n : ℕ) :
    Bool × MWCoreSpace n ≃ ForrSpace n (Reg n × Bool) where
  toFun p := (p.2.1, (p.2.2.1, (p.2.2.2, p.1)))
  invFun p := (p.2.2.2, (p.1, (p.2.1, p.2.2.1)))
  left_inv p := rfl
  right_inv p := rfl

private noncomputable def mwLiftCoreGate (n : ℕ) (G : Matrix (MWCoreSpace n) (MWCoreSpace n) ℂ) :
    Matrix (ForrSpace n (Reg n × Bool)) (ForrSpace n (Reg n × Bool)) ℂ :=
  relabelGate (mwWorkspaceEquiv n)
    (TensorGate (1 : Matrix Bool Bool ℂ) G)

/-- The full-workspace bit oracle for `S` is the relabeled parallel lift of its core-workspace
oracle. -/
private theorem mwOracleS_lift (n : ℕ) (S : Reg n → Bool) :
    forrBitOracleS n S (Reg n × Bool) =
      relabelGate (mwWorkspaceEquiv n)
        (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle
          (forrBitOracleS n S (Reg n))) := by
  classical
  rw [Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle_eq_kronecker]
  ext p q
  cases p with
  | mk ps prest => cases prest with
    | mk pu pwork => cases pwork with
      | mk pw pb =>
        cases q with
        | mk qs qrest => cases qrest with
          | mk qu qwork => cases qwork with
            | mk qw qb =>
              by_cases hpb : pb = qb
              · simp [forrBitOracleS, mwWorkspaceEquiv, relabelGate, Matrix.reindex_apply,
                  Matrix.submatrix_apply, TensorGate, Matrix.kroneckerMap_apply,
                  Matrix.one_apply, BitOracleOn, permMatrix, BitFlip, hpb]
              · simp [forrBitOracleS, mwWorkspaceEquiv, relabelGate, Matrix.reindex_apply,
                  Matrix.submatrix_apply, TensorGate, Matrix.kroneckerMap_apply,
                  Matrix.one_apply, BitOracleOn, permMatrix, BitFlip, hpb]

/-- The full-workspace bit oracle for `U` is the relabeled parallel lift of its core-workspace
oracle. -/
private theorem mwOracleU_lift (n : ℕ) (U : Reg n → Bool) :
    forrBitOracleU n U (Reg n × Bool) =
      relabelGate (mwWorkspaceEquiv n)
        (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle
          (forrBitOracleU n U (Reg n))) := by
  classical
  rw [Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle_eq_kronecker]
  ext p q
  cases p with
  | mk ps prest => cases prest with
    | mk pu pwork => cases pwork with
      | mk pw pb =>
        cases q with
        | mk qs qrest => cases qrest with
          | mk qu qwork => cases qwork with
            | mk qw qb =>
              by_cases hpb : pb = qb
              · simp [forrBitOracleU, mwWorkspaceEquiv, relabelGate, Matrix.reindex_apply,
                  Matrix.submatrix_apply, TensorGate, Matrix.kroneckerMap_apply,
                  Matrix.one_apply, BitOracleOn, permMatrix, BitFlip, hpb]
              · simp [forrBitOracleU, mwWorkspaceEquiv, relabelGate, Matrix.reindex_apply,
                  Matrix.submatrix_apply, TensorGate, Matrix.kroneckerMap_apply,
                  Matrix.one_apply, BitOracleOn, permMatrix, BitFlip, hpb]

private noncomputable def mwLiftCoreStep (n : ℕ) : TOStep (MWCoreSpace n) →
    TOStep (ForrSpace n (Reg n × Bool))
  | .gate G => .gate (mwLiftCoreGate n G)
  | .queryS => .queryS
  | .queryU => .queryU

private noncomputable def mwLiftCoreCircuit (n : ℕ) (C : TOCircuit (MWCoreSpace n)) :
    TOCircuit (ForrSpace n (Reg n × Bool)) := C.map (mwLiftCoreStep n)

/-- Relabeling along an equivalence preserves matrix multiplication. -/
private theorem mwRelabelGate_mul {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (A B : Matrix I I ℂ) :
    relabelGate e (A * B) = relabelGate e A * relabelGate e B := by
  simpa only [relabelGate] using! map_mul (Matrix.reindexAlgEquiv ℂ ℂ e) A B

/-- Relabeling along an equivalence preserves the identity matrix. -/
private theorem mwRelabelGate_one {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) :
    relabelGate e (1 : Matrix I I ℂ) = 1 := by
  ext i j
  simp [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]

/-- Parallel lifting with a Boolean auxiliary register preserves matrix multiplication. -/
private theorem parallelOracle_mul_local {H : Type} [Fintype H] [DecidableEq H]
    (A B : Matrix H H ℂ) :
    Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) (A * B) =
      Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) A *
        Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) B := by
  rw [Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle,
    Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle,
    Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle,
    Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_mul]

/-- Lifting a core circuit to the full workspace gives the relabeled parallel lift of its
circuit matrix. -/
private theorem mwLiftCoreCircuit_matrix (n : ℕ) (S U : Reg n → Bool)
    (C : TOCircuit (MWCoreSpace n)) :
    toCircuitMatrix (forrBitOracleS n S (Reg n × Bool))
      (forrBitOracleU n U (Reg n × Bool)) (mwLiftCoreCircuit n C) =
    relabelGate (mwWorkspaceEquiv n)
      (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle
        (toCircuitMatrix (forrBitOracleS n S (Reg n)) (forrBitOracleU n U (Reg n)) C)) := by
  induction C with
  | nil =>
    simp [mwLiftCoreCircuit, toCircuitMatrix,
      Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle,
      Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_one]
    exact (mwRelabelGate_one (mwWorkspaceEquiv n)).symm
  | cons s C ih =>
    change toCircuitMatrix (forrBitOracleS n S (Reg n × Bool))
        (forrBitOracleU n U (Reg n × Bool))
        (mwLiftCoreStep n s :: mwLiftCoreCircuit n C) =
      relabelGate (mwWorkspaceEquiv n)
        (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle
          (toCircuitMatrix (forrBitOracleS n S (Reg n)) (forrBitOracleU n U (Reg n))
            (s :: C)))
    rw [toCircuitMatrix_cons, toCircuitMatrix_cons]
    have hstep : toStepMatrix (forrBitOracleS n S (Reg n × Bool))
        (forrBitOracleU n U (Reg n × Bool)) (mwLiftCoreStep n s) =
      relabelGate (mwWorkspaceEquiv n)
        (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle
          (toStepMatrix (forrBitOracleS n S (Reg n)) (forrBitOracleU n U (Reg n)) s)) := by
      cases s with
      | gate G =>
        change mwLiftCoreGate n G = relabelGate (mwWorkspaceEquiv n)
          (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle G)
        rw [mwLiftCoreGate,
          Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle_eq_kronecker (J := Bool)]
        simp [TensorGate]
      | queryS => exact mwOracleS_lift n S
      | queryU => exact mwOracleU_lift n U
    rw [ih, hstep, ← mwRelabelGate_mul,
      parallelOracle_mul_local]

private noncomputable def mwAdjointStepCircuit (n : ℕ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Bool × MWCoreSpace n) →
      TOCircuit (ForrSpace n (Reg n × Bool))
  | .gate G => [.gate (relabelGate (mwWorkspaceEquiv n) G)]
  | .forward => mwLiftCoreCircuit n (mwCoreVerifierInv n)
  | .backward => mwLiftCoreCircuit n (mwCoreVerifier n)

private noncomputable def mwInlineWord (n m j0 : ℕ) :
    TOCircuit (ForrSpace n (Reg n × Bool)) :=
  (binomialTailWord (mwOutputFrame n) (mwInputFrame n) m j0).reverse.flatMap
    (mwAdjointStepCircuit n)

/-- Compiling a reversed instruction word gives its relabeled evaluation matrix when every
compiled instruction has the required matrix. -/
private theorem toCircuitMatrix_reverse_flatMap {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (oS oU : Matrix I I ℂ) (e : J ≃ I) (O : Matrix J J ℂ)
    (word : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep J))
    (compile : Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep J → TOCircuit I)
    (hstep : ∀ s, toCircuitMatrix oS oU (compile s) =
      relabelGate e (Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix O s)) :
    toCircuitMatrix oS oU (word.reverse.flatMap compile) =
      relabelGate e (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O word) := by
  induction word with
  | nil =>
    simp [toCircuitMatrix, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate,
      mwRelabelGate_one]
  | cons s word ih =>
    rw [List.reverse_cons, List.flatMap_append, toCircuitMatrix_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [hstep s, ih, ← mwRelabelGate_mul]
    rfl

/-- The inlined Marriott-Watrous word has matrix equal to the relabeled evaluation of the
binomial tail word with the lifted adjoint core verifier oracle. -/
private theorem mwInlineWord_matrix (n : ℕ) (S U : Reg n → Bool) (m j0 : ℕ) :
    toCircuitMatrix (forrBitOracleS n S (Reg n × Bool))
      (forrBitOracleU n U (Reg n × Bool)) (mwInlineWord n m j0) =
    relabelGate (mwWorkspaceEquiv n)
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate
        (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (mwCoreVerifierMatrix S U)ᴴ)
        (binomialTailWord (mwOutputFrame n) (mwInputFrame n) m j0)) := by
  apply toCircuitMatrix_reverse_flatMap
  intro s
  cases s with
  | gate G => simp [mwAdjointStepCircuit, toCircuitMatrix, toStepMatrix,
      Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix]
  | forward =>
      change toCircuitMatrix (forrBitOracleS n S (Reg n × Bool))
        (forrBitOracleU n U (Reg n × Bool)) (mwLiftCoreCircuit n (mwCoreVerifierInv n)) = _
      rw [mwLiftCoreCircuit_matrix n S U (mwCoreVerifierInv n),
        mwCoreVerifier_matrix_adjoint,
        ← Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle_adjoint]
      rfl
  | backward =>
      change toCircuitMatrix (forrBitOracleS n S (Reg n × Bool))
        (forrBitOracleU n U (Reg n × Bool)) (mwLiftCoreCircuit n (mwCoreVerifier n)) = _
      simpa [mwAdjointStepCircuit, mwCoreVerifierMatrix,
        Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix,
        Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle_adjoint] using!
        mwLiftCoreCircuit_matrix n S U (mwCoreVerifier n)

private noncomputable def mwWitnessEmbed (n : ℕ) (ψ : QState (Reg n)) :
    QState (MWCoreSpace n) := fun p =>
  if p.1 = (ZeroStr n, false) ∧ p.2.1 = (ZeroStr n, false) then ψ p.2.2 else 0

/-- Applying the Marriott-Watrous input frame to a witness gives `mwWitnessEmbed`. -/
private theorem mwInputFrame_mulVec (n : ℕ) (ψ : QState (Reg n)) :
    mwInputFrame n *ᵥ ψ = mwWitnessEmbed n ψ := by
  classical
  ext p
  change (∑ x, (if p = mwInputConfig n x then (1 : ℂ) else 0) * ψ x) = _
  rw [Finset.sum_eq_single p.2.2]
  · have hcfg_iff : p = mwInputConfig n p.2.2 ↔
        p.1 = (ZeroStr n, false) ∧ p.2.1 = (ZeroStr n, false) := by
      cases p with
      | mk s rest => cases s with
        | mk sx sb => cases rest with
          | mk u w => cases u with
            | mk ux ub => simp [mwInputConfig]
    simp [mwWitnessEmbed, hcfg_iff]
  · intro x _ hx
    have hne : p ≠ mwInputConfig n x := by
      intro he
      exact hx (congrArg (fun q : MWCoreSpace n => q.2.2) he).symm
    simp [hne]
  · simp

/-- A gate tensored with the identity acts on each slice with the second coordinate fixed. -/
private theorem tensorGate_right_one_mulVec {X Y : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (G : Matrix X X ℂ) (φ : QState (X × Y)) (x : X) (y : Y) :
    (TensorGate G (1 : Matrix Y Y ℂ) *ᵥ φ) (x, y) =
      (G *ᵥ (fun x' => φ (x', y))) x := by
  classical
  have key : ∀ x' : X,
      ∑ y', (G x x' * (1 : Matrix Y Y ℂ) y y') * φ (x', y') =
        G x x' * φ (x', y) := by
    intro x'
    simp only [Matrix.one_apply]
    rw [Finset.sum_eq_single y]
    · simp
    · intro y' _ hy'
      simp [Ne.symm hy']
    · simp
  simp only [TensorGate, Matrix.mulVec, dotProduct, Matrix.kronecker_apply,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x' _
  exact key x'

/-- Applying the Marriott-Watrous core data Hadamard transforms the first data register and
leaves the remaining coordinates fixed. -/
private theorem applyGate_mwDataH (n : ℕ) (φ : QState (MWCoreSpace n))
    (p : MWCoreSpace n) :
    ApplyGate (mwDataH n) φ p =
      ∑ z, HadamardN n p.1.1 z * φ ((z, p.1.2), p.2) := by
  unfold ApplyGate mwDataH
  rw [tensorGate_right_one_mulVec, advTensor_mulVec]

/-- The Forrelation bit oracle for `S` on the core workspace is unitary. -/
private theorem forrBitOracleS_core_unitary (n : ℕ) (S : Reg n → Bool) :
    forrBitOracleS n S (Reg n) ∈ Matrix.unitaryGroup (MWCoreSpace n) ℂ :=
  tensorGate_unitary (bitOracleOn_unitary S) (Submonoid.one_mem _)

/-- The Forrelation bit oracle for `U` on the core workspace is unitary. -/
private theorem forrBitOracleU_core_unitary (n : ℕ) (U : Reg n → Bool) :
    forrBitOracleU n U (Reg n) ∈ Matrix.unitaryGroup (MWCoreSpace n) ℂ :=
  tensorGate_unitary (Submonoid.one_mem _)
    (tensorGate_unitary (bitOracleOn_unitary U) (Submonoid.one_mem _))

private noncomputable def verifierSpectralMatrix (S U : Reg n → Bool) :
    Matrix (Reg n) (Reg n) ℂ :=
  charProjector n U * HadamardN n * charProjector n S

private noncomputable def thresholdFunctionalOperator (S U : Reg n → Bool)
    (τ : ℝ) (k : ℕ) : Matrix (Reg n) (Reg n) ℂ :=
  aeval ((verifierSpectralMatrix S U)ᴴ * verifierSpectralMatrix S U)
    ((Qatlib.Concepts.WalshMoment.Forrelation.thresholdFactor τ k).map Complex.ofRealHom)

private noncomputable def thresholdFunctionalResponse (S U : Reg n → Bool)
    (ψ : QState (Reg n)) (τ : ℝ) (k : ℕ) : ℝ :=
  ‖toEuclidean_fromVec (thresholdFunctionalOperator S U τ k *ᵥ ψ)‖ ^ 2

/-- Every Forrelation witness mass is nonnegative. -/
private theorem forrWitnessMass_nonneg (S U : Reg n → Bool) (ψ : QState (Reg n)) :
    0 ≤ forrWitnessMass n S U ψ := by
  unfold forrWitnessMass
  positivity

/-- For a success parameter between zero and one, the binomial tail is antitone in its integer
threshold. -/
private theorem binomialTail_anti (m j0 j0' : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (h : j0 ≤ j0') :
    binomialTail m j0' p ≤ binomialTail m j0 p := by
  unfold binomialTail
  apply Finset.sum_le_sum
  intro j _
  by_cases h1 : j0' ≤ j
  · have h2 : j0 ≤ j := le_trans h h1
    simp [h1, h2]
  · by_cases h2 : j0 ≤ j
    · simp only [ite_eq_right h1, ite_eq_left h2]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _))
        (pow_nonneg (by linarith) _)
    · simp [h1, h2]

/-- The exponential of minus 31 eighths is at most one sixth. -/
private theorem exp_neg_31_8 : Real.exp (-(31 / 8 : ℝ)) ≤ 1 / 6 := by
  have h1 : Real.exp 1 > 2.71 := by
    have := Real.exp_one_gt_d9
    norm_num at this
    linarith
  have h2 : Real.exp 2 > 7.3 := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; ring
    rw [h]; nlinarith [h1, Real.exp_pos 1]
  have h3 : Real.exp (31/8 - 2) > 2.8 := by
    have h : (31/8 - 2 : ℝ) > 1.8 := by norm_num
    have := Real.add_one_le_exp (31/8 - 2)
    linarith
  have h4 : Real.exp (31/8 : ℝ) = Real.exp 2 * Real.exp (31/8 - 2) := by
    conv_lhs => rw [show (31/8 : ℝ) = 2 + (31/8 - 2) from by norm_num]
    rw [Real.exp_add]
  have h5 : Real.exp (31/8 : ℝ) > 7.3 * 2.8 := by
    rw [h4]; nlinarith [h2, h3, Real.exp_pos 2, Real.exp_pos (31/8 - 2)]
  have h6 : (7.3 * 2.8 : ℝ) > 20 := by norm_num
  have h7 : Real.exp (31/8 : ℝ) > 20 := by linarith
  have h8 : Real.exp (-(31 / 8 : ℝ)) = (Real.exp (31/8))⁻¹ := Real.exp_neg _
  rw [h8]
  have h9 : 0 < Real.exp (31/8) := Real.exp_pos _
  have h10 : (6:ℝ) ≤ Real.exp (31/8) := by linarith
  have h11 : (Real.exp (31/8))⁻¹ ≤ (6:ℝ)⁻¹ := inv_anti₀ (by norm_num) h10
  have h12 : (6:ℝ)⁻¹ = 1/6 := by norm_num
  rw [h12] at h11
  exact h11

/-- The stated step-count and gap-distance bounds force half the step count times the squared
distance to be at least 31 eighths. -/
private theorem exp_ge_31_8 (α β p m τ : ℝ)
    (hm : m ≥ 32 / (α - β) ^ 2 - 1)
    (hp : p - τ ≥ (α - β) / 2)
    (hgap : 0 < α - β) (hgap_le : α - β ≤ 1) :
    m * (p - τ) ^ 2 / 2 ≥ 31 / 8 := by
  have h1 : (p - τ) ^ 2 ≥ ((α - β) / 2) ^ 2 := by nlinarith [sq_nonneg (p - τ)]
  have h2 : (α - β) ^ 2 ≤ 1 := by nlinarith [hgap_le, sq_nonneg (α - β)]
  have h6 : 0 ≤ (32 / (α - β) ^ 2 - 1 : ℝ) := by
    have : (1:ℝ) ≤ 32 / (α - β) ^ 2 := by
      rw [le_div_iff₀ (by positivity : 0 < (α - β) ^ 2)]
      nlinarith [sq_nonneg (α - β)]
    linarith
  have h4 : m * (p - τ) ^ 2 ≥ (32 / (α - β) ^ 2 - 1) * ((α - β) / 2) ^ 2 := by
    nlinarith [hm, h1, h6, sq_nonneg (p - τ), sq_nonneg ((α-β)/2)]
  have h5 : (32 / (α - β) ^ 2 - 1) * ((α - β) / 2) ^ 2
      = (32 - (α - β) ^ 2) / 4 := by
    have hpow : 0 < (α - β) ^ 2 := by positivity
    field_simp
    ring
  rw [h5] at h4
  have h7 : m * (p - τ) ^ 2 / 2 ≥ (32 - (α - β) ^ 2) / 8 := by
    linarith
  have h8 : (32 - (α - β) ^ 2) / 8 ≥ 31 / 8 := by
    nlinarith [h2]
  linarith

/-- A success parameter at least the completeness threshold gives midpoint-threshold binomial
tail at least five sixths at the chosen gap step count. -/
private theorem binomial_gap_completeness (α β p : ℝ)
    (hβ : 0 ≤ β) (hlt : β < α) (hα : α ≤ 1)
    (hp : α ≤ p) (hp1 : p ≤ 1) :
    (5 / 6 : ℝ) ≤
      binomialTail (gapStepCount α β)
        (Nat.floor ((gapStepCount α β : ℝ) * ((α + β) / 2))) p := by
  have hpos : 0 < α - β := by linarith
  have hgap_le : α - β ≤ 1 := by linarith
  set m : ℕ := gapStepCount α β with hmdef
  set τ : ℝ := (α + β) / 2 with hτdef
  have hτle : τ ≤ 1 := by nlinarith [hα, hβ]
  have hτge : 0 ≤ τ := by nlinarith [hβ, hα]
  have hpt : τ < p := by nlinarith
  have hmpos : 0 < m := by
    rw [hmdef]
    unfold gapStepCount
    rw [ite_eq_left hpos]
    exact lt_of_lt_of_le (by norm_num : 0 < 1) (le_max_left _ _)
  have hchernoff : 1 - Real.exp (- (m : ℝ) * (p - τ) ^ 2 / 2)
      ≤ binomialTail m ⌈(m : ℝ) * τ⌉₊ p :=
    binomialTail_ge_one_sub_exp_half m hmpos (by nlinarith [hβ, hp]) hp1 hτge hτle (by linarith)
  have hfloor_le : (Nat.floor ((m : ℝ) * τ) : ℕ) ≤ ⌈(m : ℝ) * τ⌉₊ := by
    have h1 : (Nat.floor ((m : ℝ) * τ) : ℝ) ≤ (m : ℝ) * τ :=
      Nat.floor_le (mul_nonneg (Nat.cast_nonneg m) hτge)
    have h2 : ((m : ℝ) * τ) ≤ (⌈(m : ℝ) * τ⌉₊ : ℝ) := Nat.le_ceil _
    exact_mod_cast le_trans h1 h2
  have htail : binomialTail m ⌈(m : ℝ) * τ⌉₊ p
      ≤ binomialTail m (Nat.floor ((m : ℝ) * τ)) p :=
    binomialTail_anti m _ _ (by nlinarith [hβ, hp]) hp1 hfloor_le
  have hm_ge : (m : ℝ) ≥ 32 / (α - β) ^ 2 - 1 := by
    rw [hmdef]
    unfold gapStepCount
    rw [ite_eq_left hpos]
    have hfloor : (Nat.floor (32 / (α - β) ^ 2) : ℝ) ≥ 32 / (α - β) ^ 2 - 1 := by
      have h := Nat.lt_floor_add_one (32 / (α - β) ^ 2)
      linarith
    have hle : (Nat.floor (32 / (α - β) ^ 2) : ℝ) ≤ (max 1 (Nat.floor (32 / (α - β) ^ 2)) : ℝ) := by
      exact_mod_cast le_max_right _ _
    have hfinal : (max 1 (Nat.floor (32 / (α - β) ^ 2)) : ℝ) ≥ 32 / (α - β) ^ 2 - 1 :=
      le_trans hfloor hle
    exact_mod_cast hfinal
  have hexp_ge : (m : ℝ) * (p - τ) ^ 2 / 2 ≥ 31 / 8 :=
    exp_ge_31_8 α β p m τ hm_ge (by nlinarith) hpos hgap_le
  have hexp_le : Real.exp (- (m : ℝ) * (p - τ) ^ 2 / 2) ≤ Real.exp (-31 / 8) := by
    apply Real.exp_le_exp.mpr
    linarith
  have htail2 : (5 / 6 : ℝ) ≤ binomialTail m ⌈(m : ℝ) * τ⌉₊ p := by
    have := hchernoff
    nlinarith [hexp_le, exp_neg_31_8]
  linarith [htail2, htail]

/-- A binomial tail at a floored threshold above its mean satisfies the displayed exponential
bound including the floor correction. -/
private theorem binomialTail_floor_le_exp_half (m : ℕ) {p τ : ℝ}
    (hm : 0 < m) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hpt : p < τ) :
    binomialTail m (Nat.floor ((m : ℝ) * τ)) p
      ≤ Real.exp ((τ - p) - (m : ℝ) * (τ - p) ^ 2 / 2) := by
  have hpos : 0 < τ - p := by linarith
  set t : ℝ := τ - p with htdef
  have ht : 0 < t := by rw [htdef]; linarith
  have ha : 0 ≤ (Nat.floor ((m : ℝ) * τ) : ℝ) := Nat.cast_nonneg _
  have hfloor_nat : ⌈((Nat.floor ((m : ℝ) * τ) : ℝ))⌉₊ = Nat.floor ((m : ℝ) * τ) :=
    Nat.ceil_natCast _
  have hmarkov : binomialTail m (Nat.floor ((m : ℝ) * τ)) p
      ≤ Real.exp (-t * ((Nat.floor ((m : ℝ) * τ) : ℝ))) *
        (∑ j ∈ Finset.range (m + 1),
          (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) * Real.exp (t * j)) := by
    have h := markov_exp_ge m p t ((Nat.floor ((m : ℝ) * τ) : ℝ)) ht hp hp1 ha
    rwa [hfloor_nat] at h
  have hmgf : (∑ j ∈ Finset.range (m + 1),
      (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) * Real.exp (t * j))
      = (1 - p + p * Real.exp t) ^ m := binomial_mgf_eq m p t
  have hh : 1 - p + p * Real.exp t ≤ Real.exp (p * t + t ^ 2 / 2) :=
    bernoulli_mgf_le p t hp hp1
  have hbase : 0 ≤ 1 - p + p * Real.exp t := by
    have h1 : 0 < Real.exp t := Real.exp_pos t
    nlinarith [mul_nonneg hp (le_of_lt h1), sub_nonneg.mpr hp1]
  have hpow : (1 - p + p * Real.exp t) ^ m ≤ Real.exp ((m : ℝ) * (p * t + t ^ 2 / 2)) := by
    have h : (1 - p + p * Real.exp t) ^ m
        ≤ (Real.exp (p * t + t ^ 2 / 2)) ^ m :=
      pow_le_pow_left₀ hbase hh m
    have hexp : (Real.exp (p * t + t ^ 2 / 2)) ^ m
        = Real.exp ((m : ℝ) * (p * t + t ^ 2 / 2)) := by
      rw [← Real.exp_nat_mul]
    rw [hexp] at h
    exact h
  rw [hmgf] at hmarkov
  have hfloor_ge : ((m : ℝ) * τ) - 1 ≤ (Nat.floor ((m : ℝ) * τ) : ℝ) := by
    have h := Nat.lt_floor_add_one ((m : ℝ) * τ)
    linarith
  have hexp_mono : Real.exp (-t * ((Nat.floor ((m : ℝ) * τ) : ℝ)))
      ≤ Real.exp (-t * (((m : ℝ) * τ) - 1)) := by
    apply Real.exp_le_exp.mpr
    have : -t * ((Nat.floor ((m : ℝ) * τ) : ℝ)) ≤ -t * (((m : ℝ) * τ) - 1) := by
      nlinarith [ht, hfloor_ge]
    exact this
  have hmul_le : Real.exp (-t * ((Nat.floor ((m : ℝ) * τ) : ℝ))) * (1 - p + p * Real.exp t) ^ m
      ≤ Real.exp (-t * (((m : ℝ) * τ) - 1)) * Real.exp ((m : ℝ) * (p * t + t ^ 2 / 2)) := by
    have h1 : Real.exp (-t * ((Nat.floor ((m : ℝ) * τ) : ℝ))) * (1 - p + p * Real.exp t) ^ m
        ≤ Real.exp (-t * (((m : ℝ) * τ) - 1)) * (1 - p + p * Real.exp t) ^ m :=
      mul_le_mul_of_nonneg_right hexp_mono (pow_nonneg hbase _)
    have h2 : Real.exp (-t * (((m : ℝ) * τ) - 1)) * (1 - p + p * Real.exp t) ^ m
        ≤ Real.exp (-t * (((m : ℝ) * τ) - 1)) * Real.exp ((m : ℝ) * (p * t + t ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left hpow (le_of_lt (Real.exp_pos _))
    exact le_trans h1 h2
  have hsum : Real.exp (-t * (((m : ℝ) * τ) - 1)) * Real.exp ((m : ℝ) * (p * t + t ^ 2 / 2))
      = Real.exp (t + (m : ℝ) * (t * (p - τ) + t ^ 2 / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have htval : t + (m : ℝ) * (t * (p - τ) + t ^ 2 / 2)
      = (τ - p) - (m : ℝ) * (τ - p) ^ 2 / 2 := by
    rw [htdef]
    ring
  have hfinal : Real.exp (t + (m : ℝ) * (t * (p - τ) + t ^ 2 / 2))
      = Real.exp ((τ - p) - (m : ℝ) * (τ - p) ^ 2 / 2) := by
    rw [htval]
  calc binomialTail m (Nat.floor ((m : ℝ) * τ)) p
      ≤ Real.exp (-t * ((Nat.floor ((m : ℝ) * τ) : ℝ))) * (1 - p + p * Real.exp t) ^ m :=
        hmarkov
    _ ≤ Real.exp (-t * (((m : ℝ) * τ) - 1)) * Real.exp ((m : ℝ) * (p * t + t ^ 2 / 2)) :=
        hmul_le
    _ = Real.exp (t + (m : ℝ) * (t * (p - τ) + t ^ 2 / 2)) := hsum
    _ = Real.exp ((τ - p) - (m : ℝ) * (τ - p) ^ 2 / 2) := hfinal

/-- Under the stated gap and step-count bounds, the floor-corrected exponential exponent is at
most minus 23 eighths. -/
private theorem floor_exp_le_neg_23_8 (α β p m τ : ℝ)
    (hm : m ≥ 32 / (α - β) ^ 2 - 1)
    (hgapdist : τ - p ≥ (α - β) / 2)
    (hgap : 0 < α - β) (hgap_le : α - β ≤ 1)
    (hτp : τ - p ≤ 1) :
    (τ - p) - m * (τ - p) ^ 2 / 2 ≤ -23 / 8 := by
  have h1 : (τ - p) ^ 2 ≥ ((α - β) / 2) ^ 2 := by nlinarith [sq_nonneg (τ - p)]
  have h2 : (α - β) ^ 2 ≤ 1 := by nlinarith [hgap_le, sq_nonneg (α - β)]
  have h6 : 0 ≤ (32 / (α - β) ^ 2 - 1 : ℝ) := by
    have : (1:ℝ) ≤ 32 / (α - β) ^ 2 := by
      rw [le_div_iff₀ (by positivity : 0 < (α - β) ^ 2)]
      nlinarith [sq_nonneg (α - β)]
    linarith
  have h4 : m * (τ - p) ^ 2 ≥ (32 / (α - β) ^ 2 - 1) * ((α - β) / 2) ^ 2 := by
    nlinarith [hm, h1, h6, sq_nonneg (τ - p), sq_nonneg ((α-β)/2)]
  have h5 : (32 / (α - β) ^ 2 - 1) * ((α - β) / 2) ^ 2
      = (32 - (α - β) ^ 2) / 4 := by
    have hpow : 0 < (α - β) ^ 2 := by positivity
    field_simp
    ring
  rw [h5] at h4
  have h7 : m * (τ - p) ^ 2 / 2 ≥ (32 - (α - β) ^ 2) / 8 := by
    linarith
  have h8 : (32 - (α - β) ^ 2) / 8 ≥ 31 / 8 := by
    nlinarith [h2]
  have h9 : (τ - p) - m * (τ - p) ^ 2 / 2 ≤ (τ - p) - 31 / 8 := by
    linarith
  have h10 : (τ - p) - 31 / 8 ≤ 1 - 31 / 8 := by
    linarith [hτp]
  have h11 : (1 - 31 / 8 : ℝ) ≤ -23 / 8 := by norm_num
  linarith

/-- The exponential of minus 23 eighths is at most one third. -/
private theorem exp_neg_23_8 : Real.exp (-23 / 8 : ℝ) ≤ 1 / 3 := by
  have h1 : Real.exp 2 > 7.3 := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; ring
    have h2 := Real.exp_one_gt_d9
    norm_num at h2
    rw [h]; nlinarith [h2, Real.exp_pos 1]
  have h2 : (0:ℝ) < 23 / 8 - 2 := by norm_num
  have h3 : Real.exp (23/8 - 2) > 1 := by
    have := Real.add_one_le_exp (23/8 - 2)
    have hz : (0:ℝ) < 23/8 - 2 := by norm_num
    linarith
  have h4 : Real.exp (23/8 : ℝ) = Real.exp 2 * Real.exp (23/8 - 2) := by
    conv_lhs => rw [show (23/8 : ℝ) = 2 + (23/8 - 2) from by norm_num]
    rw [Real.exp_add]
  have h5 : Real.exp (23/8 : ℝ) > 7.3 * 1 := by
    rw [h4]; nlinarith [h1, h3, Real.exp_pos 2, Real.exp_pos (23/8 - 2)]
  have h6 : Real.exp (23/8 : ℝ) > 3 := by linarith
  have h7 : Real.exp (-23 / 8 : ℝ) = (Real.exp (23/8))⁻¹ := by
    have h : (-23 / 8 : ℝ) = -(23 / 8) := by ring
    rw [h, Real.exp_neg]
  rw [h7]
  have h8 : 0 < Real.exp (23/8) := Real.exp_pos _
  have h9 : (Real.exp (23/8))⁻¹ ≤ (3:ℝ)⁻¹ := inv_anti₀ (by norm_num) (le_of_lt h6)
  have h10 : (3:ℝ)⁻¹ = 1/3 := by norm_num
  rw [h10] at h9
  exact h9

/-- A success parameter at most the soundness threshold gives midpoint-threshold binomial tail
at most one third at the chosen gap step count. -/
private theorem binomial_gap_soundness (α β p : ℝ)
    (hβ : 0 ≤ β) (hlt : β < α) (hα : α ≤ 1)
    (hp : 0 ≤ p) (hpβ : p ≤ β) :
    binomialTail (gapStepCount α β)
      (Nat.floor ((gapStepCount α β : ℝ) * ((α + β) / 2))) p
      ≤ 1 / 3 := by
  have hpos : 0 < α - β := by linarith
  have hgap_le : α - β ≤ 1 := by linarith
  set m : ℕ := gapStepCount α β with hmdef
  set τ : ℝ := (α + β) / 2 with hτdef
  have hτle : τ ≤ 1 := by nlinarith [hα, hβ]
  have hτge : 0 ≤ τ := by nlinarith [hβ, hα]
  have hpt : p < τ := by nlinarith
  have hτp : τ - p ≤ 1 := by nlinarith
  have hmpos : 0 < m := by
    rw [hmdef]
    unfold gapStepCount
    rw [ite_eq_left hpos]
    exact lt_of_lt_of_le (by norm_num : 0 < 1) (le_max_left _ _)
  have hp1 : p ≤ 1 := by
    have : β ≤ 1 := le_of_lt (lt_of_lt_of_le hlt hα)
    nlinarith
  have htail : binomialTail m (Nat.floor ((m : ℝ) * τ)) p
      ≤ Real.exp ((τ - p) - (m : ℝ) * (τ - p) ^ 2 / 2) :=
    binomialTail_floor_le_exp_half m hmpos hp hp1 hτge hτle hpt
  have hm_ge : (m : ℝ) ≥ 32 / (α - β) ^ 2 - 1 := by
    rw [hmdef]
    unfold gapStepCount
    rw [ite_eq_left hpos]
    have hfloor : (Nat.floor (32 / (α - β) ^ 2) : ℝ) ≥ 32 / (α - β) ^ 2 - 1 := by
      have h := Nat.lt_floor_add_one (32 / (α - β) ^ 2)
      linarith
    have hle : (Nat.floor (32 / (α - β) ^ 2) : ℝ) ≤ (max 1 (Nat.floor (32 / (α - β) ^ 2)) : ℝ) := by
      exact_mod_cast le_max_right _ _
    have hfinal : (max 1 (Nat.floor (32 / (α - β) ^ 2)) : ℝ) ≥ 32 / (α - β) ^ 2 - 1 :=
      le_trans hfloor hle
    exact_mod_cast hfinal
  have hgapdist : τ - p ≥ (α - β) / 2 := by nlinarith
  have hexp_le : (τ - p) - (m : ℝ) * (τ - p) ^ 2 / 2 ≤ -23 / 8 :=
    floor_exp_le_neg_23_8 α β p m τ hm_ge hgapdist hpos hgap_le hτp
  have hbound : Real.exp ((τ - p) - (m : ℝ) * (τ - p) ^ 2 / 2) ≤ Real.exp (-23 / 8) := by
    apply Real.exp_le_exp.mpr
    exact hexp_le
  have hfinal : Real.exp (-23 / 8) ≤ 1 / 3 := exp_neg_23_8
  linarith [htail, hbound, hfinal]

/-- Applying the displayed permutation matrix evaluates each output amplitude at the permuted
index. -/
private theorem applyGate_perm {I : Type} [Fintype I] [DecidableEq I]
    (e : I ≃ I) (φ : QState I) (p : I) :
    ApplyGate (Matrix.of fun p q => if e p = q then (1 : ℂ) else 0) φ p = φ (e p) := by
  classical
  unfold ApplyGate
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_eq_single (e p)]
  · simp
  · intro q _ hq
    have : e p ≠ q := fun hc => hq (hc ▸ rfl)
    rw [ite_eq_right this]
    ring
  · intro hc
    exact absurd (Finset.mem_univ (e p)) hc

/-- Applying a permutation gate evaluates the state at the permuted index. -/
private theorem applyGate_permGate {I : Type} [Fintype I] [DecidableEq I]
    (e : I ≃ I) (φ : QState I) (p : I) :
    ApplyGate (permGate e) φ p = φ (e p) := applyGate_perm e φ p

/-- The Forrelation bit oracle for `S` acts on amplitudes by XORing `S` into its answer bit. -/
private theorem applyGate_forrBitOracleS (n : ℕ) (S : Reg n → Bool) (W : Type)
    [Fintype W] [DecidableEq W] (φ : QState (ForrSpace n W)) (p : ForrSpace n W) :
    ApplyGate (forrBitOracleS n S W) φ p
      = φ ((p.1.1, p.1.2 ^^ S p.1.1), p.2) := by
  unfold ApplyGate forrBitOracleS
  rw [advTensor_mulVec,
    show (∑ y, BitOracleOn S p.1 y * φ (y, p.2))
      = ApplyGate (BitOracleOn S) (fun q => φ (q, p.2)) p.1 from rfl,
    applyGate_bitOracleOn]
  rfl

/-- The identity tensored with a gate acts on each slice with the first coordinate fixed. -/
private theorem tensorGate_left_one_mulVec {X Y : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    (G : Matrix Y Y ℂ) (φ : QState (X × Y)) (x : X) (y : Y) :
    (TensorGate (1 : Matrix X X ℂ) G *ᵥ φ) (x, y) = (G *ᵥ (fun y' => φ (x, y'))) y := by
  classical
  have key : ∀ y' : Y,
      (∑ x', ((1 : Matrix X X ℂ) x x' * G y y') * φ (x', y'))
        = G y y' * φ (x, y') := by
    intro y'
    have h1 : ∀ x', ((1 : Matrix X X ℂ) x x' * G y y') * φ (x', y')
        = (if x = x' then G y y' * φ (x', y') else 0) := by
      intro x'
      rw [Matrix.one_apply]
      by_cases h : x = x' <;> simp [h]
    rw [Finset.sum_congr rfl (fun x' _ => h1 x')]
    simp
  simp only [TensorGate, Matrix.mulVec, dotProduct, Matrix.kronecker_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun y' _ => key y')]

/-- The Forrelation bit oracle for `U` acts on amplitudes by XORing `U` into its answer bit. -/
private theorem applyGate_forrBitOracleU (n : ℕ) (U : Reg n → Bool) (W : Type)
    [Fintype W] [DecidableEq W] (φ : QState (ForrSpace n W)) (p : ForrSpace n W) :
    ApplyGate (forrBitOracleU n U W) φ p
      = φ (p.1, ((p.2.1.1, p.2.1.2 ^^ U p.2.1.1), p.2.2)) := by
  classical
  unfold ApplyGate forrBitOracleU
  rw [tensorGate_left_one_mulVec]
  have hinner : ∀ q : (Reg n × Bool) × W,
      (TensorGate (BitOracleOn U) (1 : Matrix W W ℂ) *ᵥ
        (fun r : (Reg n × Bool) × W => φ (p.1, r))) q
        = φ (p.1, ((q.1.1, q.1.2 ^^ U q.1.1), q.2)) := by
    intro q
    rw [advTensor_mulVec,
      show (∑ y, BitOracleOn U q.1 y * (fun r : (Reg n × Bool) × W => φ (p.1, r)) (y, q.2))
        = ApplyGate (BitOracleOn U)
            (fun z => (fun r : (Reg n × Bool) × W => φ (p.1, r)) (z, q.2)) q.1 from rfl,
      applyGate_bitOracleOn]
    rfl
  rw [hinner]

/-- The verifier data Hadamard acts by a Hadamard sum on the first data register with all other
coordinates fixed. -/
private theorem applyGate_verifierDataH (n : ℕ)
    (φ : QState (ForrSpace n (Reg n × Bool))) (p : ForrSpace n (Reg n × Bool)) :
    ApplyGate (verifierDataH n) φ p =
      ∑ z, HadamardN n p.1.1 z * φ ((z,p.1.2),p.2) := by
  classical
  unfold ApplyGate verifierDataH
  rw [advTensor_mulVec]
  simp only [TensorGate,Fintype.sum_prod_type]
  cases hb : p.1.2 <;> simp [hb,Matrix.one_apply]

/-- The core verifier's accepting amplitudes equal the spectral verifier matrix applied to the
witness when the auxiliary data registers are zero, and vanish otherwise. -/
private theorem mwCoreVerifier_accept_amplitude (S U : Reg n → Bool)
    (ψ : QState (Reg n)) (x y w : Reg n) :
    TORun (forrBitOracleS n S (Reg n)) (forrBitOracleU n U (Reg n))
      (mwCoreVerifier n) (mwWitnessEmbed n ψ) ((x, true), (y, true), w) =
    if x = ZeroStr n ∧ w = ZeroStr n then
      (verifierSpectralMatrix S U *ᵥ ψ) y else 0 := by
  classical
  simp only [mwCoreVerifier, TORun, applyGate_forrBitOracleU, applyGate_permGate,
    applyGate_mwDataH, applyGate_forrBitOracleS]
  simp only [mwSwapXY, mwSwapXW, mwWitnessEmbed]
  simp only [verifierSpectralMatrix]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hp (f : Reg n → Bool) (v : QState (Reg n)) :
      charProjector n f *ᵥ v = fun z => if f z then v z else 0 := by
    ext z
    simp [charProjector, Matrix.mulVec_diagonal]
  rw [hp, hp]
  simp only [Matrix.mulVec, dotProduct]
  by_cases hx : x = ZeroStr n <;> by_cases hw : w = ZeroStr n <;>
    cases hu : U y <;> simp_all

/-- Multiplying a matrix by a basis ket selects its corresponding column. -/
private theorem matrix_mulVec_ket {H I : Type} [Fintype I] [DecidableEq I]
    (M : Matrix H I ℂ) (i : H) (j : I) : (M *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i = M i j := by
  simp [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]

/-- The core verifier matrix entries between the designated input and output configurations
equal those of the spectral verifier matrix. -/
private theorem mwCoreVerifierMatrix_entry (S U : Reg n → Bool) (x y : Reg n) :
    mwCoreVerifierMatrix S U (mwOutputConfig n y) (mwInputConfig n x) =
      verifierSpectralMatrix S U y x := by
  have hket : mwWitnessEmbed n (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (mwInputConfig n x) := by
    calc
      mwWitnessEmbed n (Qatlib.Foundations.PureStateMath.Ket x) = mwInputFrame n *ᵥ Qatlib.Foundations.PureStateMath.Ket x :=
        (mwInputFrame_mulVec n (Qatlib.Foundations.PureStateMath.Ket x)).symm
      _ = Qatlib.Foundations.PureStateMath.Ket (mwInputConfig n x) := by
        ext p
        rw [matrix_mulVec_ket]
        simp [mwInputFrame, Qatlib.Foundations.PureStateMath.Ket]
  have hentry : mwCoreVerifierMatrix S U (mwOutputConfig n y) (mwInputConfig n x) =
      TORun (forrBitOracleS n S (Reg n)) (forrBitOracleU n U (Reg n))
        (mwCoreVerifier n) (Qatlib.Foundations.PureStateMath.Ket (mwInputConfig n x)) (mwOutputConfig n y) := by
    calc
      _ = (mwCoreVerifierMatrix S U *ᵥ Qatlib.Foundations.PureStateMath.Ket (mwInputConfig n x)) (mwOutputConfig n y) :=
        (matrix_mulVec_ket _ _ _).symm
      _ = TORun (forrBitOracleS n S (Reg n)) (forrBitOracleU n U (Reg n))
          (mwCoreVerifier n) (Qatlib.Foundations.PureStateMath.Ket (mwInputConfig n x)) (mwOutputConfig n y) := by
        exact congrArg (fun v : QState (MWCoreSpace n) => v (mwOutputConfig n y))
          (toRun_eq_mulVec _ _ _ _).symm
  rw [hentry, ← hket]
  have hacc :=
      mwCoreVerifier_accept_amplitude S U (Qatlib.Foundations.PureStateMath.Ket x)
      (ZeroStr n) y (ZeroStr n)
  simpa [mwOutputConfig, verifierSpectralMatrix, Matrix.mulVec, dotProduct,
      Qatlib.Foundations.PureStateMath.Ket] using! hacc

/-- The Marriott-Watrous core verifier gives a projected unitary encoding of the spectral
verifier matrix between its input and output frames. -/
private theorem mwCoreVerifier_encoding (S U : Reg n → Bool) :
    Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
      (verifierSpectralMatrix S U) (mwCoreVerifierMatrix S U)
      (mwOutputFrame n) (mwInputFrame n) := by
  refine ⟨?_, mwOutputFrame_isometry n, mwInputFrame_isometry n, ?_⟩
  · exact toCircuitMatrix_unitary _ _ _ (mwCoreVerifier_unitary n)
      (forrBitOracleS_core_unitary n S) (forrBitOracleU_core_unitary n U)
  · ext y x
    change Qatlib.Concepts.Execution.WorkspaceCP.compress
      (Matrix.of fun p j => if p = mwOutputConfig n j then (1 : ℂ) else 0)
      (mwCoreVerifierMatrix S U)
      (Matrix.of fun p j => if p = mwInputConfig n j then (1 : ℂ) else 0) y x = _
    rw [oneHotFrame_compress (mwInputConfig n) (mwOutputConfig n)
      (mwCoreVerifierMatrix S U) x y]
    exact mwCoreVerifierMatrix_entry S U x y

private def mwFullInputConfig (n : ℕ) (x : Reg n) : ForrSpace n (Reg n × Bool) :=
  mwWorkspaceEquiv n (false, mwInputConfig n x)

private noncomputable def mwFullInputFrame (n : ℕ) :
    Matrix (ForrSpace n (Reg n × Bool)) (Reg n) ℂ :=
  Matrix.of fun p x => if p = mwFullInputConfig n x then (1 : ℂ) else 0

/-- The full Marriott-Watrous input configuration map is injective. -/
private theorem mwFullInputConfig_injective (n : ℕ) :
    Function.Injective (mwFullInputConfig n) := by
  intro x y h
  have h' : (false, mwInputConfig n x) = (false, mwInputConfig n y) :=
    (mwWorkspaceEquiv n).injective h
  exact congrArg (fun p : Bool × MWCoreSpace n => p.2.2.2) h'

/-- The full Marriott-Watrous input frame is an isometry. -/
private theorem mwFullInputFrame_isometry (n : ℕ) :
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (mwFullInputFrame n) :=
  oneHotFrame_isometry (mwFullInputConfig n) (mwFullInputConfig_injective n)

/-- Applying the full Marriott-Watrous input frame to a witness gives `witnessEmbed`. -/
private theorem mwFullInputFrame_mulVec (n : ℕ) (ψ : QState (Reg n)) :
    mwFullInputFrame n *ᵥ ψ = witnessEmbed n ψ := by
  classical
  ext p
  change (∑ x, (if p = mwFullInputConfig n x then (1 : ℂ) else 0) * ψ x) = _
  rw [Finset.sum_eq_single p.2.2.1]
  · have hcfg : p = mwFullInputConfig n p.2.2.1 ↔
        p.1 = (ZeroStr n, false) ∧ p.2.1 = (ZeroStr n, false) ∧ p.2.2.2 = false := by
      cases p with
      | mk s rest => cases s with
        | mk sx sb => cases rest with
          | mk u w => cases u with
            | mk ux ub => cases w with
              | mk wx wb => simp [mwFullInputConfig, mwWorkspaceEquiv, mwInputConfig]
    simp [witnessEmbed, hcfg]
  · intro x _ hx
    have hne : p ≠ mwFullInputConfig n x := by
      intro he
      exact hx (congrArg (fun q : ForrSpace n (Reg n × Bool) => q.2.2.1) he).symm
    simp [hne]
  · simp

private noncomputable def mwFlagHadamard (n : ℕ) :
    Matrix (ForrSpace n (Reg n × Bool)) (ForrSpace n (Reg n × Bool)) ℂ :=
  relabelGate (mwWorkspaceEquiv n)
    (TensorGate Hadamard (1 : Matrix (MWCoreSpace n) (MWCoreSpace n) ℂ))

/-- The Marriott-Watrous flag Hadamard gate is self-adjoint. -/
private theorem mwFlagHadamard_selfadjoint (n : ℕ) :
    (mwFlagHadamard n)ᴴ = mwFlagHadamard n := by
  have hbase : (TensorGate Hadamard
      (1 : Matrix (MWCoreSpace n) (MWCoreSpace n) ℂ))ᴴ =
      TensorGate Hadamard (1 : Matrix (MWCoreSpace n) (MWCoreSpace n) ℂ) := by
    rw [tensorGate_conjTranspose, hadamard_conjTranspose, Matrix.conjTranspose_one]
  ext p q
  have hentry := congrFun (congrFun hbase ((mwWorkspaceEquiv n).symm p))
    ((mwWorkspaceEquiv n).symm q)
  simpa [mwFlagHadamard, relabelGate, Matrix.reindex_apply,
    Matrix.conjTranspose_apply] using! hentry

/-- The Marriott-Watrous flag Hadamard gate is unitary. -/
private theorem mwFlagHadamard_unitary (n : ℕ) :
    mwFlagHadamard n ∈ Matrix.unitaryGroup (ForrSpace n (Reg n × Bool)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    mwFlagHadamard_selfadjoint]
  have hsquare :
      TensorGate Hadamard (1 : Matrix (MWCoreSpace n) (MWCoreSpace n) ℂ) *
        TensorGate Hadamard (1 : Matrix (MWCoreSpace n) (MWCoreSpace n) ℂ) = 1 := by
    rw [tensorGate_mul, hadamard_mul_self]
    simp [TensorGate]
  rw [mwFlagHadamard, ← mwRelabelGate_mul, hsquare, mwRelabelGate_one]

private noncomputable def mwActualAmplificationCircuit (n m j0 : ℕ) :
    TOCircuit (ForrSpace n (Reg n × Bool)) :=
  [.gate (mwFlagHadamard n)] ++ mwInlineWord n m j0 ++ [.gate (mwFlagHadamard n)]

/-- The binomial tail word built from the Marriott-Watrous frames is a well-formed adjoint
circuit. -/
private theorem binomialTailWord_wellFormed (n m j0 : ℕ) :
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
      (binomialTailWord (mwOutputFrame n) (mwInputFrame n) m j0) := by
  obtain ⟨hb, hzs, _, _⟩ := binomialTail_phase_word_response m j0
  unfold binomialTailWord
  exact Qatlib.Concepts.QspSimulation.Achievability.compileRealPartQSVT_wellFormed
    (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector_isOrthogonalProjector
      (mwOutputFrame_isometry n))
    (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector_isOrthogonalProjector
      (mwInputFrame_isometry n)) hb _ hzs

/-- Lifting a unitary core circuit to the full Marriott-Watrous workspace preserves circuit
unitarity. -/
private theorem mwLiftCoreCircuit_unitary (n : ℕ) (C : TOCircuit (MWCoreSpace n))
    (hC : IsUnitaryTOCircuit C) :
    IsUnitaryTOCircuit (mwLiftCoreCircuit n C) := by
  intro G hG
  rcases List.mem_map.mp hG with ⟨s, hs, heq⟩
  cases s with
  | gate V =>
      have hV : V ∈ Matrix.unitaryGroup (MWCoreSpace n) ℂ := hC V hs
      simp only [mwLiftCoreStep] at heq
      injection heq with hG
      subst G
      exact (Qatlib.Concepts.GateVocabulary.GateVocab.relabelGate_mem_unitaryGroup (mwWorkspaceEquiv n)
        (TensorGate (1 : Matrix Bool Bool ℂ) V)).2
          (tensorGate_unitary (Submonoid.one_mem _) hV)
  | queryS => simp [mwLiftCoreStep] at heq
  | queryU => simp [mwLiftCoreStep] at heq

/-- Every gate compiled from an instruction in the reversed well-formed binomial tail word is
unitary. -/
private theorem mwAdjointStepCircuit_unitary (n m j0 : ℕ)
    (hwf : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
      (binomialTailWord (mwOutputFrame n) (mwInputFrame n) m j0))
    (s : Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Bool × MWCoreSpace n))
    (hs : s ∈ (binomialTailWord (mwOutputFrame n) (mwInputFrame n) m j0).reverse)
    (G : Matrix (ForrSpace n (Reg n × Bool)) (ForrSpace n (Reg n × Bool)) ℂ)
    (hG : TOStep.gate G ∈ mwAdjointStepCircuit n s) :
    G ∈ Matrix.unitaryGroup (ForrSpace n (Reg n × Bool)) ℂ := by
  cases s with
  | gate V =>
      have hV := hwf V (List.mem_reverse.mp hs)
      simp only [mwAdjointStepCircuit, List.mem_singleton] at hG
      injection hG with hG
      subst G
      exact (Qatlib.Concepts.GateVocabulary.GateVocab.relabelGate_mem_unitaryGroup
        (mwWorkspaceEquiv n) V).2 hV
  | forward =>
      exact (mwLiftCoreCircuit_unitary n (mwCoreVerifierInv n)
        (mwCoreVerifierInv_unitary n)) G hG
  | backward =>
      exact (mwLiftCoreCircuit_unitary n (mwCoreVerifier n)
        (mwCoreVerifier_unitary n)) G hG

/-- The inlined Marriott-Watrous word is a unitary two-oracle circuit. -/
private theorem mwInlineWord_unitary (n m j0 : ℕ) :
    IsUnitaryTOCircuit (mwInlineWord n m j0) := by
  intro G hG
  unfold mwInlineWord at hG
  rcases List.mem_flatMap.mp hG with ⟨s, hs, hstep⟩
  exact mwAdjointStepCircuit_unitary n m j0
    (binomialTailWord_wellFormed n m j0) s hs G hstep

/-- The actual Marriott-Watrous amplification circuit is unitary. -/
private theorem mwActualAmplificationCircuit_unitary (n m j0 : ℕ) :
    IsUnitaryTOCircuit (mwActualAmplificationCircuit n m j0) := by
  have hflag : IsUnitaryTOCircuit
      ([.gate (mwFlagHadamard n)] : TOCircuit (ForrSpace n (Reg n × Bool))) := by
    intro G hG
    have hEq := List.mem_singleton.mp hG
    injection hEq with hEq
    subst G
    exact mwFlagHadamard_unitary n
  intro G hG
  have hmem : TOStep.gate G ∈
      ([.gate (mwFlagHadamard n)] ++ mwInlineWord n m j0) ++
        [.gate (mwFlagHadamard n)] := by
    simpa [mwActualAmplificationCircuit] using! hG
  rcases List.mem_append.mp hmem with hprefix | hlast
  · rcases List.mem_append.mp hprefix with hfirst | hmiddle
    · exact hflag G hfirst
    · exact mwInlineWord_unitary n m j0 G hmiddle
  · exact hflag G hlast

/-- Lifting a core circuit to the full workspace preserves its `S`-query count. -/
private theorem mwLiftCoreCircuit_queryS (n : ℕ) (C : TOCircuit (MWCoreSpace n)) :
    TOQueryCountS (mwLiftCoreCircuit n C) = TOQueryCountS C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
      change TOQueryCountS (mwLiftCoreStep n s :: mwLiftCoreCircuit n C) = _
      cases s <;> simp [mwLiftCoreStep, TOQueryCountS, ih]

/-- Lifting a core circuit to the full workspace preserves its `U`-query count. -/
private theorem mwLiftCoreCircuit_queryU (n : ℕ) (C : TOCircuit (MWCoreSpace n)) :
    TOQueryCountU (mwLiftCoreCircuit n C) = TOQueryCountU C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
      change TOQueryCountU (mwLiftCoreStep n s :: mwLiftCoreCircuit n C) = _
      cases s <;> simp [mwLiftCoreStep, TOQueryCountU, ih]

/-- The inverse Marriott-Watrous core verifier makes exactly one query to each oracle. -/
private theorem mwCoreVerifierInv_queries (n : ℕ) :
    TOQueryCountS (mwCoreVerifierInv n) = 1 ∧ TOQueryCountU (mwCoreVerifierInv n) = 1 := by
  simp [mwCoreVerifierInv, mwCoreVerifier, TOQueryCountS, TOQueryCountU]

/-- The `S`-query count of a compiled adjoint step equals the abstract query count of that
instruction. -/
private theorem mwAdjointStepCircuit_queryS (n : ℕ)
    (s : Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Bool × MWCoreSpace n)) :
    TOQueryCountS (mwAdjointStepCircuit n s) =
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount [s] := by
  cases s with
  | gate G => simp [mwAdjointStepCircuit, TOQueryCountS,
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount]
  | forward => simp [mwAdjointStepCircuit, mwLiftCoreCircuit_queryS,
      mwCoreVerifierInv_queries,
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount]
  | backward => simp [mwAdjointStepCircuit, mwLiftCoreCircuit_queryS,
      mwCoreVerifier_queries,
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount]

/-- The `U`-query count of a compiled adjoint step equals the abstract query count of that
instruction. -/
private theorem mwAdjointStepCircuit_queryU (n : ℕ)
    (s : Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Bool × MWCoreSpace n)) :
    TOQueryCountU (mwAdjointStepCircuit n s) =
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount [s] := by
  cases s with
  | gate G => simp [mwAdjointStepCircuit, TOQueryCountU,
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount]
  | forward => simp [mwAdjointStepCircuit, mwLiftCoreCircuit_queryU,
      mwCoreVerifierInv_queries,
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount]
  | backward => simp [mwAdjointStepCircuit, mwLiftCoreCircuit_queryU,
      mwCoreVerifier_queries,
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount]

/-- The inlined Marriott-Watrous word makes twice the trial count many `S` queries. -/
private theorem mwInlineWord_queryS (n m j0 : ℕ) :
    TOQueryCountS (mwInlineWord n m j0) = 2 * m := by
  have hflat (word : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep
      (Bool × MWCoreSpace n))) :
      TOQueryCountS (word.reverse.flatMap (mwAdjointStepCircuit n)) =
        Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount word := by
    induction word with
    | nil => rfl
    | cons s word ih =>
        calc
          TOQueryCountS ((s :: word).reverse.flatMap (mwAdjointStepCircuit n))
              = TOQueryCountS (word.reverse.flatMap (mwAdjointStepCircuit n)) +
                  TOQueryCountS (mwAdjointStepCircuit n s) := by
                    rw [List.reverse_cons, List.flatMap_append, toQueryCountS_append]
                    simp [List.flatMap]
          _ = Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount word +
                Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount [s] := by
                  rw [ih, mwAdjointStepCircuit_queryS]
          _ = Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (s :: word) := by
                cases s <;> simp [Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount,
                  Nat.add_comm]
  rw [mwInlineWord, hflat]
  unfold binomialTailWord
  rw [(Qatlib.Concepts.CopyEvolution.Discriminate.counts_compileRealPartQSVT _ _ _ _).1]
  exact (binomialTail_phase_word_response m j0).2.2.1

/-- The inlined Marriott-Watrous word makes twice the trial count many `U` queries. -/
private theorem mwInlineWord_queryU (n m j0 : ℕ) :
    TOQueryCountU (mwInlineWord n m j0) = 2 * m := by
  have hflat (word : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep
      (Bool × MWCoreSpace n))) :
      TOQueryCountU (word.reverse.flatMap (mwAdjointStepCircuit n)) =
        Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount word := by
    induction word with
    | nil => rfl
    | cons s word ih =>
        calc
          TOQueryCountU ((s :: word).reverse.flatMap (mwAdjointStepCircuit n))
              = TOQueryCountU (word.reverse.flatMap (mwAdjointStepCircuit n)) +
                  TOQueryCountU (mwAdjointStepCircuit n s) := by
                    rw [List.reverse_cons, List.flatMap_append, toQueryCountU_append]
                    simp [List.flatMap]
          _ = Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount word +
                Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount [s] := by
                  rw [ih, mwAdjointStepCircuit_queryU]
          _ = Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (s :: word) := by
                cases s <;> simp [Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount,
                  Nat.add_comm]
  rw [mwInlineWord, hflat]
  unfold binomialTailWord
  rw [(Qatlib.Concepts.CopyEvolution.Discriminate.counts_compileRealPartQSVT _ _ _ _).1]
  exact (binomialTail_phase_word_response m j0).2.2.1

/-- The actual Marriott-Watrous amplification circuit makes twice the trial count many queries
to each oracle. -/
private theorem mwActualAmplificationCircuit_queries (n m j0 : ℕ) :
    TOQueryCountS (mwActualAmplificationCircuit n m j0) = 2 * m ∧
      TOQueryCountU (mwActualAmplificationCircuit n m j0) = 2 * m := by
  constructor
  · simp [mwActualAmplificationCircuit, toQueryCountS_append,
      mwInlineWord_queryS, TOQueryCountS]
  · simp [mwActualAmplificationCircuit, toQueryCountU_append,
      mwInlineWord_queryU, TOQueryCountU]

private noncomputable def mwActualSuccessEvent (n : ℕ) :
    Finset (ForrSpace n (Reg n × Bool)) :=
  Finset.univ.filter (fun p => ∃ x : Reg n, p = mwFullInputConfig n x)

private noncomputable def mwBinomialResponseOperator (S U : Reg n → Bool) (m j0 : ℕ) :
    Matrix (Reg n) (Reg n) ℂ :=
  Polynomial.aeval ((verifierSpectralMatrix S U)ᴴ * verifierSpectralMatrix S U)
    ((binomialTailPolynomial m j0).map Complex.ofRealHom)

private noncomputable def mwBinomialResponse (S U : Reg n → Bool)
    (ψ : QState (Reg n)) (m j0 : ℕ) : ℝ :=
  ‖toEuclidean_fromVec (mwBinomialResponseOperator S U m j0 *ᵥ ψ)‖ ^ 2

private noncomputable def mwRowsReindex {H K I : Type} (e : H ≃ K)
    (F : Matrix H I ℂ) : Matrix K I ℂ :=
  Matrix.of fun k i => F (e.symm k) i

/-- Multiplying a reindexed frame by a relabeled matrix equals reindexing their original
product. -/
private theorem mwRowsReindex_mul {H K I : Type} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    (e : H ≃ K) (M : Matrix H H ℂ) (F : Matrix H I ℂ) :
    relabelGate e M * mwRowsReindex e F = mwRowsReindex e (M * F) := by
  classical
  ext k i
  simp only [Matrix.mul_apply, relabelGate, Matrix.reindex_apply, mwRowsReindex,
    Matrix.of_apply]
  apply Fintype.sum_equiv e.symm
  intro h
  simp

private noncomputable def mwLabelInputFrame (n : ℕ) :
    Matrix (Bool × MWCoreSpace n) (Reg n) ℂ :=
  Matrix.of fun p x => if p = (false, mwInputConfig n x) then (1 : ℂ) else 0

private noncomputable def mwGlobalPhase : ℂ :=
  (1 + Complex.I) * (Real.sqrt 2 : ℂ)⁻¹

/-- The Marriott-Watrous global phase has squared modulus one. -/
private theorem mwGlobalPhase_norm_sq : star mwGlobalPhase * mwGlobalPhase = 1 := by
  apply Complex.ext
  · simp [mwGlobalPhase, Complex.mul_re, Complex.mul_im, ]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  · simp [mwGlobalPhase, Complex.mul_re, Complex.mul_im, ]

/-- Multiplying the first Hadamard column by the Marriott-Watrous global phase gives
`realPartAmplitude`. -/
private theorem mwGlobalPhase_hadamard_column (b : Bool) :
    mwGlobalPhase * Hadamard b false =
      Qatlib.Concepts.QspSimulation.Achievability.realPartAmplitude b := by
  have hsq : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) := by
    have hsqrt : (Real.sqrt 2 : ℝ) ^ 2 = 2 :=
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
    field_simp [hn]
    exact_mod_cast hsqrt.symm
  cases b <;> simp [Hadamard, Matrix.of_apply, mwGlobalPhase,
    Qatlib.Concepts.QspSimulation.Achievability.realPartAmplitude]
  all_goals
    calc
      _ = (1 + Complex.I) * ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 := by ring
      _ = (1 + Complex.I) * (1 / 2 : ℂ) := by rw [hsq]
      _ = _ := by ring

/-- Applying the label Hadamard to the label input frame gives the average input frame scaled by
the conjugate global phase. -/
private theorem mwLabelHadamard_frame (n : ℕ) :
    TensorGate Hadamard (1 : Matrix (MWCoreSpace n) (MWCoreSpace n) ℂ) *
      mwLabelInputFrame n =
    star mwGlobalPhase •
      Qatlib.Concepts.QspSimulation.Achievability.averageFrame (mwInputFrame n) := by
  classical
  ext p x
  cases p with
  | mk b h =>
    simp only [Matrix.mul_apply, TensorGate,
      mwLabelInputFrame, Matrix.of_apply]
    have hcol : Hadamard b false = star mwGlobalPhase *
        Qatlib.Concepts.QspSimulation.Achievability.realPartAmplitude b := by
      calc
        Hadamard b false = (star mwGlobalPhase * mwGlobalPhase) * Hadamard b false := by
          rw [mwGlobalPhase_norm_sq]
          simp
        _ = star mwGlobalPhase *
            (mwGlobalPhase * Hadamard b false) := by ring
        _ = _ := by rw [mwGlobalPhase_hadamard_column]
    by_cases hh : h = mwInputConfig n x
    · subst h
      simp [Qatlib.Concepts.QspSimulation.Achievability.averageFrame,
        Qatlib.Concepts.BlockEncoding.LCU.prepareLift, Matrix.mul_apply, Matrix.of_apply,
        Matrix.one_apply, mwInputFrame, mwInputConfig, hcol]
    · simp [Qatlib.Concepts.QspSimulation.Achievability.averageFrame,
        Qatlib.Concepts.BlockEncoding.LCU.prepareLift, Matrix.mul_apply, Matrix.of_apply,
        Matrix.one_apply, mwInputFrame, mwInputConfig, hcol]

/-- The full Marriott-Watrous input frame is the label input frame reindexed by the workspace
equivalence. -/
private theorem mwFullInputFrame_reindex (n : ℕ) :
    mwFullInputFrame n = mwRowsReindex (mwWorkspaceEquiv n) (mwLabelInputFrame n) := by
  ext p x
  have hiff : p = mwFullInputConfig n x ↔
      (mwWorkspaceEquiv n).symm p = (false, mwInputConfig n x) := by
    constructor
    · intro h
      rw [h, mwFullInputConfig]
      exact (mwWorkspaceEquiv n).symm_apply_apply _
    · intro h
      have h' := congrArg (mwWorkspaceEquiv n) h
      simpa [mwFullInputConfig] using! h'
  change (if p = mwFullInputConfig n x then (1 : ℂ) else 0) =
    if (mwWorkspaceEquiv n).symm p = (false, mwInputConfig n x) then 1 else 0
  exact if_congr hiff rfl rfl

/-- The flag Hadamard maps the full input frame to the reindexed average input frame scaled by
the conjugate global phase. -/
private theorem mwFlagHadamard_prepare (n : ℕ) :
    mwFlagHadamard n * mwFullInputFrame n =
      star mwGlobalPhase •
        mwRowsReindex (mwWorkspaceEquiv n)
          (Qatlib.Concepts.QspSimulation.Achievability.averageFrame (mwInputFrame n)) := by
  rw [mwFullInputFrame_reindex, mwFlagHadamard, mwRowsReindex_mul,
    mwLabelHadamard_frame]
  ext k i
  rfl

/-- Reindexing a frame and relabeling an operator along the same equivalence preserves
compression. -/
private theorem mwRowsReindex_compress {H K I : Type}
    [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] (e : H ≃ K) (F : Matrix H I ℂ)
    (M : Matrix H H ℂ) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress (mwRowsReindex e F) (relabelGate e M)
      (mwRowsReindex e F) = Qatlib.Concepts.Execution.WorkspaceCP.compress F M F := by
  classical
  unfold Qatlib.Concepts.Execution.WorkspaceCP.compress
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, mwRowsReindex,
    Matrix.of_apply, relabelGate, Matrix.reindex_apply]
  calc
    (∑ q : K, (∑ p : K,
        star (F (e.symm p) i) * M (e.symm p) (e.symm q)) * F (e.symm q) j)
        = ∑ q : H, (∑ p : H, star (F p i) * M p q) * F q j := by
          apply Fintype.sum_equiv e.symm
          intro q
          congr 1
          apply Fintype.sum_equiv e.symm
          intro p
          simp
    _ = (∑ q : H, (∑ p : H,
        star (F p i) * M p q) * F q j) := rfl

/-- The actual amplification circuit matrix is the relabeled binomial tail word evaluation
sandwiched between flag Hadamard gates. -/
private theorem mwActualAmplificationCircuit_matrix (n m j0 : ℕ)
    (S U : Reg n → Bool) :
    toCircuitMatrix (forrBitOracleS n S (Reg n × Bool))
      (forrBitOracleU n U (Reg n × Bool)) (mwActualAmplificationCircuit n m j0) =
    mwFlagHadamard n *
      relabelGate (mwWorkspaceEquiv n)
        (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate
          (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (mwCoreVerifierMatrix S U)ᴴ)
          (binomialTailWord (mwOutputFrame n) (mwInputFrame n) m j0)) *
      mwFlagHadamard n := by
  unfold mwActualAmplificationCircuit
  rw [toCircuitMatrix_append, toCircuitMatrix_append]
  simp only [toCircuitMatrix, toStepMatrix]
  rw [mwInlineWord_matrix]
  simp [Matrix.mul_assoc]

/-- Scaling both compression frames by the conjugate Marriott-Watrous global phase leaves the
compressed operator unchanged. -/
private theorem mwGlobalPhase_compress {I : Type} [Fintype I] [DecidableEq I]
    (F : Matrix I (Reg n) ℂ) (M : Matrix I I ℂ) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress (star mwGlobalPhase • F) M
      (star mwGlobalPhase • F) = Qatlib.Concepts.Execution.WorkspaceCP.compress F M F := by
  unfold Qatlib.Concepts.Execution.WorkspaceCP.compress
  rw [Matrix.conjTranspose_smul]
  simp only [star_star]
  rw [Matrix.smul_mul, Matrix.mul_smul]
  rw [Matrix.smul_mul, smul_smul, mwGlobalPhase_norm_sq, one_smul]

/-- Compressing the actual amplification circuit to the full input frame gives
`mwBinomialResponseOperator`. -/
private theorem mwActualAmplification_compress (n : ℕ) (S U : Reg n → Bool)
    (m j0 : ℕ) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress (mwFullInputFrame n)
      (toCircuitMatrix (forrBitOracleS n S (Reg n × Bool))
        (forrBitOracleU n U (Reg n × Bool)) (mwActualAmplificationCircuit n m j0))
      (mwFullInputFrame n) = mwBinomialResponseOperator S U m j0 := by
  let A := verifierSpectralMatrix S U
  let V := mwCoreVerifierMatrix S U
  let W := Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate
    (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle Vᴴ)
    (binomialTailWord (mwOutputFrame n) (mwInputFrame n) m j0)
  have henc := binomialTailWord_exact_gram_encoding A V (mwOutputFrame n)
    (mwInputFrame n) m j0 (mwCoreVerifier_encoding S U)
  calc
    Qatlib.Concepts.Execution.WorkspaceCP.compress (mwFullInputFrame n)
        (toCircuitMatrix (forrBitOracleS n S (Reg n × Bool))
          (forrBitOracleU n U (Reg n × Bool)) (mwActualAmplificationCircuit n m j0))
        (mwFullInputFrame n)
        = Qatlib.Concepts.Execution.WorkspaceCP.compress (mwFlagHadamard n * mwFullInputFrame n)
            (relabelGate (mwWorkspaceEquiv n) W)
            (mwFlagHadamard n * mwFullInputFrame n) := by
          rw [mwActualAmplificationCircuit_matrix]
          unfold Qatlib.Concepts.Execution.WorkspaceCP.compress
          rw [Matrix.conjTranspose_mul, mwFlagHadamard_selfadjoint]
          simp [Matrix.mul_assoc, W, V]
    _ = Qatlib.Concepts.Execution.WorkspaceCP.compress
          (mwRowsReindex (mwWorkspaceEquiv n)
            (Qatlib.Concepts.QspSimulation.Achievability.averageFrame (mwInputFrame n)))
          (relabelGate (mwWorkspaceEquiv n) W)
          (mwRowsReindex (mwWorkspaceEquiv n)
            (Qatlib.Concepts.QspSimulation.Achievability.averageFrame (mwInputFrame n))) := by
          rw [mwFlagHadamard_prepare, mwGlobalPhase_compress]
    _ = Qatlib.Concepts.Execution.WorkspaceCP.compress
          (Qatlib.Concepts.QspSimulation.Achievability.averageFrame (mwInputFrame n))
          (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate
            (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle Vᴴ)
            (binomialTailWord (mwOutputFrame n) (mwInputFrame n) m j0))
          (Qatlib.Concepts.QspSimulation.Achievability.averageFrame (mwInputFrame n)) :=
            mwRowsReindex_compress (mwWorkspaceEquiv n)
              (Qatlib.Concepts.QspSimulation.Achievability.averageFrame (mwInputFrame n)) W
    _ = mwBinomialResponseOperator S U m j0 := by
          simpa [mwBinomialResponseOperator, A, W] using! henc.encoded

/-- The actual amplification circuit's success probability on an embedded witness equals
`mwBinomialResponse`. -/
private theorem mwActualSuccess_probability (n : ℕ) (S U : Reg n → Bool)
    (ψ : QState (Reg n)) (m j0 : ℕ) :
    MeasureProb
      (TORun (forrBitOracleS n S (Reg n × Bool))
        (forrBitOracleU n U (Reg n × Bool))
        (mwActualAmplificationCircuit n m j0) (witnessEmbed n ψ))
      (mwActualSuccessEvent n) = mwBinomialResponse S U ψ m j0 := by
  classical
  let M := toCircuitMatrix (forrBitOracleS n S (Reg n × Bool))
    (forrBitOracleU n U (Reg n × Bool)) (mwActualAmplificationCircuit n m j0)
  let F := mwFullInputFrame n
  have hrun : TORun (forrBitOracleS n S (Reg n × Bool))
      (forrBitOracleU n U (Reg n × Bool)) (mwActualAmplificationCircuit n m j0)
      (witnessEmbed n ψ) = M *ᵥ (F *ᵥ ψ) := by
    rw [toRun_eq_mulVec, mwFullInputFrame_mulVec]
  have hset : mwActualSuccessEvent n =
      Finset.univ.image (mwFullInputConfig n) := by
    ext p
    simp [mwActualSuccessEvent, eq_comm]
  have hresponse_entry (x y : Reg n) :
      (Qatlib.Concepts.Execution.WorkspaceCP.compress F M F) x y =
        M (mwFullInputConfig n x) (mwFullInputConfig n y) := by
    simpa [F, mwFullInputFrame] using!
      (oneHotFrame_compress (mwFullInputConfig n) (mwFullInputConfig n) M y x)
  have hcoord (x : Reg n) :
      (TORun (forrBitOracleS n S (Reg n × Bool))
        (forrBitOracleU n U (Reg n × Bool))
        (mwActualAmplificationCircuit n m j0) (witnessEmbed n ψ))
          (mwFullInputConfig n x) =
        (mwBinomialResponseOperator S U m j0 *ᵥ ψ) x := by
    rw [hrun]
    have hMF (y : Reg n) :
        (M * F) (mwFullInputConfig n x) y =
          M (mwFullInputConfig n x) (mwFullInputConfig n y) := by
      rw [Matrix.mul_apply]
      simp [F, mwFullInputFrame]
    calc
      (M *ᵥ (F *ᵥ ψ)) (mwFullInputConfig n x)
          = ((M * F) *ᵥ ψ) (mwFullInputConfig n x) := by
              rw [Matrix.mulVec_mulVec]
      _ = ((Qatlib.Concepts.Execution.WorkspaceCP.compress F M F) *ᵥ ψ) x := by
            simp only [Matrix.mulVec, dotProduct]
            apply Finset.sum_congr rfl
            intro y _
            rw [hMF, hresponse_entry]
      _ = (mwBinomialResponseOperator S U m j0 *ᵥ ψ) x := by
            rw [mwActualAmplification_compress n S U m j0]
  unfold MeasureProb
  rw [hset, Finset.sum_image]
  · simp only [BornProb, hcoord]
    rw [← norm_toEuclidean_fromVec_sq]
    rfl
  · intro x _ y _ hxy
    exact mwFullInputConfig_injective n hxy

/-- The base verifier's accepting amplitude is the projected Hadamard action on the witness when
the auxiliary registers have their required zero values, and is zero otherwise. -/
private theorem baseVerifier_accept_amplitude (n : ℕ) (S U : Reg n → Bool)
    (ψ : QState (Reg n)) (x y w : Reg n) (o : Bool) :
    TORun (forrBitOracleS n S (Reg n × Bool)) (forrBitOracleU n U (Reg n × Bool))
      (baseVerifier n) (witnessEmbed n ψ) ((x,true),(y,true),(w,o)) =
    if x = ZeroStr n ∧ w = ZeroStr n ∧ o = false then
      ((charProjector n U * HadamardN n * charProjector n S) *ᵥ ψ) y else 0 := by
  classical
  simp only [baseVerifier,TORun,applyGate_forrBitOracleU,applyGate_permGate,
    applyGate_verifierDataH,applyGate_forrBitOracleS]
  simp only [swapXY,swapXW,witnessEmbed]
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
  have hp (f : Reg n → Bool) (v : QState (Reg n)) :
      charProjector n f *ᵥ v = fun z => if f z then v z else 0 := by
    ext z
    simp [charProjector,Matrix.mulVec_diagonal]
  rw [hp,hp]
  simp only [Matrix.mulVec,dotProduct]
  by_cases hx : x = ZeroStr n <;> by_cases hw : w = ZeroStr n <;>
    cases o <;> cases hu : U y <;> simp_all

/-- The base verifier's acceptance probability on an embedded witness equals its Forrelation
witness mass. -/
private theorem baseVerifier_accept_eq_mass (S U : Reg n → Bool) (ψ : QState (Reg n)) :
    MeasureProb
      (TORun (forrBitOracleS n S (Reg n × Bool)) (forrBitOracleU n U (Reg n × Bool))
        (baseVerifier n) (witnessEmbed n ψ)) (acceptEvent n)
      = forrWitnessMass n S U ψ := by
  classical
  rw [forrWitnessMass,norm_toEuclidean_fromVec_sq]
  simp only [acceptEvent,MeasureProb,Finset.sum_filter,BornProb,Fintype.sum_prod_type,
    Fintype.sum_bool]
  simp [baseVerifier_accept_amplitude,ite_and]
  simp_rw [apply_ite (fun z : ℂ => ‖z‖)]
  simp [ite_pow]

/-- A rectangular matrix acting in the first inner-product argument can be moved to the second
argument as its adjoint. -/
private theorem inner_mulVec_left_rect {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J ℂ)
    (ψ : QState J) (φ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (A *ᵥ ψ) φ = Qatlib.Foundations.PureStateMath.Inner ψ (Aᴴ *ᵥ φ) := by
  simp only [Qatlib.Foundations.PureStateMath.Inner]
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec]

/-- Forrelation witness mass is the real quadratic form of the spectral verifier's Gram matrix. -/
private theorem forrWitnessMass_eq_gramRayleigh (S U : Reg n → Bool)
    (ψ : QState (Reg n)) :
    forrWitnessMass n S U ψ =
      (Qatlib.Foundations.PureStateMath.Inner ψ ((verifierSpectralMatrix S U)ᴴ *ᵥ
        (verifierSpectralMatrix S U *ᵥ ψ))).re := by
  rw [forrWitnessMass, norm_toEuclidean_sq_eq_re_inner]
  exact congrArg Complex.re
    (inner_mulVec_left_rect (verifierSpectralMatrix S U) ψ
      (verifierSpectralMatrix S U *ᵥ ψ))

/-- Each Gram-matrix eigenbasis vector is normalized and has Forrelation witness mass equal to
its eigenvalue. -/
private theorem gram_eigenvalue_is_witnessMass (S U : Reg n → Bool)
    (hB : ((verifierSpectralMatrix S U)ᴴ * verifierSpectralMatrix S U).IsHermitian)
    (i : Reg n) :
    Normalized (⇑(hB.eigenvectorBasis i)) ∧
      forrWitnessMass n S U (⇑(hB.eigenvectorBasis i)) = hB.eigenvalues i := by
  let ψ : QState (Reg n) := ⇑(hB.eigenvectorBasis i)
  have hψ : Normalized ψ := (normalized_iff_norm_toEuclidean_fromVec _).mpr
    (hB.eigenvectorBasis.orthonormal.1 i)
  have he : ((verifierSpectralMatrix S U)ᴴ * verifierSpectralMatrix S U) *ᵥ ψ =
      (hB.eigenvalues i : ℂ) • ψ := by
    simpa only [ψ, RCLike.real_smul_eq_coe_smul] using! hB.mulVec_eigenvectorBasis i
  refine ⟨hψ, ?_⟩
  rw [forrWitnessMass_eq_gramRayleigh, Matrix.mulVec_mulVec, he,
      Qatlib.Foundations.PureStateMath.Inner, dotProduct_smul]
  change ((hB.eigenvalues i : ℂ) * Qatlib.Foundations.PureStateMath.Inner ψ ψ).re = hB.eigenvalues i
  rw [(normalized_iff_inner_self ψ).mp hψ, mul_one, Complex.ofReal_re]

/-- Polynomial evaluation at a Hermitian matrix is obtained by evaluating on its eigenvalues and
conjugating the resulting diagonal matrix by its eigenvector unitary. -/
private theorem aeval_hermitian_diagonalization {I : Type} [Fintype I] [DecidableEq I]
    (B : Matrix I I ℂ) (hB : B.IsHermitian) (p : Polynomial ℂ) :
    Polynomial.aeval B p =
      (hB.eigenvectorUnitary : Matrix I I ℂ) *
        Matrix.diagonal (fun i => p.eval (hB.eigenvalues i : ℂ)) *
        (hB.eigenvectorUnitary : Matrix I I ℂ)ᴴ := by
  let eigVals : I → ℂ := fun i => (hB.eigenvalues i : ℂ)
  let D := Matrix.diagonal eigVals
  let Φ := Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) hB.eigenvectorUnitary
  have heval : (aeval eigVals) p = fun i => p.eval (eigVals i) := by
    funext i
    rw [Polynomial.aeval_pi_apply₂]
    simp [Polynomial.aeval_def]
  have hpd : aeval D p = Matrix.diagonal (fun i => p.eval (eigVals i)) := by
    have h := Polynomial.aeval_algHom_apply (Matrix.diagonalAlgHom ℂ) eigVals p
    rw [heval] at h
    exact h
  have hpd' : aeval (Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues)) p =
      Matrix.diagonal (fun i => p.eval (eigVals i)) := by
    simpa [D, eigVals] using! hpd
  have hp : aeval B p = Φ (Matrix.diagonal (fun i => p.eval (eigVals i))) := by
    rw [hB.spectral_theorem, Polynomial.aeval_algHom_apply, hpd']
  simpa [Φ, eigVals] using! hp

/-- Every eigenvalue of the spectral verifier's Gram matrix is at most spectral Forrelation. -/
private theorem gram_eigenvalue_le_spectral (S U : Reg n → Bool)
    (hB : ((verifierSpectralMatrix S U)ᴴ * verifierSpectralMatrix S U).IsHermitian)
    (i : Reg n) : hB.eigenvalues i ≤ spectralForrelation n S U := by
  obtain ⟨hψ, hmass⟩ := gram_eigenvalue_is_witnessMass S U hB i
  rw [← hmass]
  exact forrWitnessMass_le_spectral S U _ hψ

/-- Every normalized witness mass is a weighted sum of Gram eigenvalues with weights given by
squared amplitudes of a normalized state. -/
private theorem gramRayleigh_eigenExpansion (S U : Reg n → Bool)
    (ψ : QState (Reg n)) (hψ : Normalized ψ) :
    ∃ z : QState (Reg n), Normalized z ∧
      forrWitnessMass n S U ψ = ∑ i : Reg n,
        (Matrix.isHermitian_conjTranspose_mul_self
          (verifierSpectralMatrix S U)).eigenvalues i * ‖z i‖ ^ 2 := by
  classical
  let A := verifierSpectralMatrix S U
  let B := Aᴴ * A
  let hB : B.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  let V : Matrix (Reg n) (Reg n) ℂ := hB.eigenvectorUnitary
  let D := Matrix.diagonal (fun i => (hB.eigenvalues i : ℂ))
  let z : QState (Reg n) := Vᴴ *ᵥ ψ
  have hV : V ∈ Matrix.unitaryGroup (Reg n) ℂ := hB.eigenvectorUnitary.2
  have hVadj : Vᴴ ∈ Matrix.unitaryGroup (Reg n) ℂ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem hV
  have hVright : V * Vᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hV
    rwa [Matrix.star_eq_conjTranspose] at h
  have hVleft : Vᴴ * V = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hV
    rwa [Matrix.star_eq_conjTranspose] at h
  have hz : Normalized z := by
    change Normalized (Vᴴ *ᵥ ψ)
    exact normalized_applyGate hVadj hψ
  have hψeq : V *ᵥ z = ψ := by
    calc
      V *ᵥ z = V *ᵥ (Vᴴ *ᵥ ψ) := rfl
      _ = (V * Vᴴ) *ᵥ ψ := Matrix.mulVec_mulVec ψ V Vᴴ
      _ = ψ := by rw [hVright]; simp
  have hdiag : Vᴴ * B * V = D := by
    have h := hB.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose] at h
    simpa [V, D] using! h
  have hBexp : B = V * D * Vᴴ := by
    calc
      B = (V * Vᴴ) * B * (V * Vᴴ) := by rw [hVright, Matrix.one_mul, Matrix.mul_one]
      _ = V * (Vᴴ * B * V) * Vᴴ := by noncomm_ring
      _ = V * D * Vᴴ := by rw [hdiag]
  have hBψ : B *ᵥ ψ = V *ᵥ (D *ᵥ z) := by
    calc
      B *ᵥ ψ = (V * D * Vᴴ) *ᵥ ψ := by rw [hBexp]
      _ = (V * D) *ᵥ (Vᴴ *ᵥ ψ) := (Matrix.mulVec_mulVec ψ (V * D) Vᴴ).symm
      _ = V *ᵥ (D *ᵥ (Vᴴ *ᵥ ψ)) := (Matrix.mulVec_mulVec (Vᴴ *ᵥ ψ) V D).symm
      _ = V *ᵥ (D *ᵥ z) := rfl
  have hinner : Qatlib.Foundations.PureStateMath.Inner ψ (B *ᵥ ψ) = Qatlib.Foundations.PureStateMath.Inner z (D *ᵥ z) := by
    calc
      Qatlib.Foundations.PureStateMath.Inner ψ (B *ᵥ ψ) = Qatlib.Foundations.PureStateMath.Inner (V *ᵥ z) (B *ᵥ ψ) := by rw [← hψeq]
      _ = Qatlib.Foundations.PureStateMath.Inner (V *ᵥ z) (V *ᵥ (D *ᵥ z)) := by rw [hBψ]
      _ = Qatlib.Foundations.PureStateMath.Inner z (D *ᵥ z) := inner_applyGate hV z (D *ᵥ z)
  have hDmul : D *ᵥ z = fun i => (hB.eigenvalues i : ℂ) * z i := by
    funext i
    simp [D, Matrix.mulVec_diagonal]
  have hterm (i : Reg n) :
      (star (z i) * ((hB.eigenvalues i : ℂ) * z i)).re =
        hB.eigenvalues i * ‖z i‖ ^ 2 := by
    have hzz : star (z i) * z i = ((‖z i‖ ^ 2 : ℝ) : ℂ) := by
      simpa only [Complex.star_def, Complex.ofReal_pow] using! (RCLike.conj_mul (z i))
    calc
      _ = ((hB.eigenvalues i : ℂ) * (star (z i) * z i)).re := by ring
      _ = hB.eigenvalues i * ‖z i‖ ^ 2 := by
            rw [hzz]
            rw [← Complex.ofReal_mul, Complex.ofReal_re]
  have hdiagInner : (Qatlib.Foundations.PureStateMath.Inner z (D *ᵥ z)).re =
      ∑ i : Reg n, hB.eigenvalues i * ‖z i‖ ^ 2 := by
    rw [inner_apply, hDmul, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => hterm i
  refine ⟨z, hz, ?_⟩
  calc
    forrWitnessMass n S U ψ =
        (Qatlib.Foundations.PureStateMath.Inner ψ (Aᴴ *ᵥ (A *ᵥ ψ))).re := by
          simpa [A] using! forrWitnessMass_eq_gramRayleigh S U ψ
    _ = (Qatlib.Foundations.PureStateMath.Inner ψ ((Aᴴ * A) *ᵥ ψ)).re := by
          rw [Matrix.mulVec_mulVec]
    _ = (Qatlib.Foundations.PureStateMath.Inner ψ (B *ᵥ ψ)).re := by rfl
    _ = ∑ i : Reg n, hB.eigenvalues i * ‖z i‖ ^ 2 := by
          rw [hinner, hdiagInner]

/-- Every lower bound on spectral Forrelation is met by some eigenvalue of the spectral
verifier's Gram matrix. -/
private theorem exists_gram_eigenvalue_ge (S U : Reg n → Bool) (α : ℝ)
    (hspec : α ≤ spectralForrelation n S U) :
    ∃ i : Reg n, α ≤
      (Matrix.isHermitian_conjTranspose_mul_self
        (verifierSpectralMatrix S U)).eigenvalues i := by
  classical
  let hB := Matrix.isHermitian_conjTranspose_mul_self (verifierSpectralMatrix S U)
  obtain ⟨ψ, hψ, hmass⟩ := spectral_attained S U α hspec
  obtain ⟨z, hz, hsum⟩ := gramRayleigh_eigenExpansion S U ψ hψ
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_max_image Finset.univ hB.eigenvalues
    Finset.univ_nonempty
  have hle : forrWitnessMass n S U ψ ≤ hB.eigenvalues i₀ := by
    rw [hsum]
    calc
      (∑ i : Reg n, hB.eigenvalues i * ‖z i‖ ^ 2)
          ≤ ∑ i : Reg n, hB.eigenvalues i₀ * ‖z i‖ ^ 2 := by
              apply Finset.sum_le_sum
              intro i _
              exact mul_le_mul_of_nonneg_right
                (hi₀ i (Finset.mem_univ i)) (sq_nonneg ‖z i‖)
      _ = hB.eigenvalues i₀ := by
            rw [← Finset.mul_sum]
            have hzsum := hz
            change ∑ i : Reg n, ‖z i‖ ^ 2 = 1 at hzsum
            rw [hzsum, mul_one]
  refine ⟨i₀, ?_⟩
  change α ≤ hB.eigenvalues i₀
  linarith

/-- Mapping the binomial tail polynomial to complex coefficients and evaluating at a real input
gives the corresponding real binomial tail embedded in the complex numbers. -/
private theorem binomialTailPolynomial_complex_eval (m j0 : ℕ) (p : ℝ) :
    ((binomialTailPolynomial m j0).map Complex.ofRealHom).eval (p : ℂ) =
      (binomialTail m j0 p : ℂ) := by
  calc
    Polynomial.eval (Complex.ofRealHom p)
        ((binomialTailPolynomial m j0).map Complex.ofRealHom) =
        Polynomial.eval₂ Complex.ofRealHom (Complex.ofRealHom p)
          (binomialTailPolynomial m j0) :=
            Polynomial.eval_map Complex.ofRealHom (Complex.ofRealHom p)
    _ = Complex.ofRealHom ((binomialTailPolynomial m j0).eval p) :=
          Polynomial.eval₂_at_apply Complex.ofRealHom p
    _ = (binomialTail m j0 p : ℂ) := by rw [binomialTailPolynomial_eval]; rfl

/-- Below the spectral soundness threshold, every normalized witness has Marriott-Watrous
binomial response at most one ninth with the chosen gap parameters. -/
private theorem mwBinomialResponse_soundness_bound (S U : Reg n → Bool)
    (ψ : QState (Reg n)) (α β : ℝ) (hβ : 0 ≤ β) (hlt : β < α)
    (hα : α ≤ 1) (hspec : spectralForrelation n S U ≤ β)
    (hψ : Normalized ψ) :
    mwBinomialResponse S U ψ (gapStepCount α β)
      (Nat.floor ((gapStepCount α β : ℝ) * ((α + β) / 2))) ≤ 1 / 9 := by
  classical
  let A := verifierSpectralMatrix S U
  let B := Aᴴ * A
  let hB : B.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  let p := (binomialTailPolynomial (gapStepCount α β)
    (Nat.floor ((gapStepCount α β : ℝ) * ((α + β) / 2)))).map Complex.ofRealHom
  have hscalar (i : Reg n) :
      0 ≤ binomialTail (gapStepCount α β)
          (Nat.floor ((gapStepCount α β : ℝ) * ((α + β) / 2))) (hB.eigenvalues i) ∧
      binomialTail (gapStepCount α β)
          (Nat.floor ((gapStepCount α β : ℝ) * ((α + β) / 2))) (hB.eigenvalues i) ≤ 1 / 3 := by
    have hmass := gram_eigenvalue_is_witnessMass S U hB i
    have hlam0 : 0 ≤ hB.eigenvalues i := by
      rw [← hmass.2]
      exact forrWitnessMass_nonneg S U _
    have hEigSpect : hB.eigenvalues i ≤ spectralForrelation n S U := by
      exact gram_eigenvalue_le_spectral S U hB i
    have hEigBeta : hB.eigenvalues i ≤ β := hEigSpect.trans hspec
    have hEigOne : hB.eigenvalues i ≤ 1 :=
      hEigSpect.trans (spectralForrelationBasics (n := n) (S := S) (U := U)).2.1
    refine ⟨binomialTail_nonneg _ _ hlam0 hEigOne, ?_⟩
    exact binomial_gap_soundness α β (hB.eigenvalues i) hβ hlt hα hlam0 hEigBeta
  have hPnorm : ‖Polynomial.aeval B p‖ ≤ 1 / 3 := by
    rw [aeval_hermitian_diagonalization B hB p]
    change ‖(hB.eigenvectorUnitary : Matrix (Reg n) (Reg n) ℂ) *
        Matrix.diagonal (fun i => p.eval (hB.eigenvalues i : ℂ)) *
        (star hB.eigenvectorUnitary : unitary (Matrix (Reg n) (Reg n) ℂ))‖ ≤ 1 / 3
    rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)).2
    intro i
    have hev := hscalar i
    rw [binomialTailPolynomial_complex_eval (gapStepCount α β)
      (Nat.floor ((gapStepCount α β : ℝ) * ((α + β) / 2))) (hB.eigenvalues i)]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hev.1]
    exact hev.2
  have hmul := l2_norm_mulVec_fromVec_le (Polynomial.aeval B p) ψ
  have hψnorm : ‖toEuclidean_fromVec ψ‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ
  rw [hψnorm, mul_one] at hmul
  have hstate : ‖toEuclidean_fromVec (Polynomial.aeval B p *ᵥ ψ)‖ ≤ 1 / 3 :=
    hmul.trans hPnorm
  have hnonneg : 0 ≤ ‖toEuclidean_fromVec (Polynomial.aeval B p *ᵥ ψ)‖ := norm_nonneg _
  change ‖toEuclidean_fromVec (Polynomial.aeval B p *ᵥ ψ)‖ ^ 2 ≤ 1 / 9
  nlinarith

/-- A polynomial in a Hermitian matrix acts on each eigenbasis vector by the polynomial
evaluated at its eigenvalue. -/
private theorem aeval_hermitian_eigenvector_action {I : Type} [Fintype I] [DecidableEq I]
    (B : Matrix I I ℂ) (hB : B.IsHermitian) (p : Polynomial ℂ) (i : I) :
    Polynomial.aeval B p *ᵥ ⇑(hB.eigenvectorBasis i) =
      p.eval (hB.eigenvalues i : ℂ) • ⇑(hB.eigenvectorBasis i) := by
  let V : Matrix I I ℂ := hB.eigenvectorUnitary
  let v : QState I := ⇑(hB.eigenvectorBasis i)
  let D := Matrix.diagonal (fun j => p.eval (hB.eigenvalues j : ℂ))
  have hket : Qatlib.Foundations.PureStateMath.Ket i = Pi.single i (1 : ℂ) := by
    funext j
    simp [Qatlib.Foundations.PureStateMath.Ket, Pi.single_apply, eq_comm]
  have hstar : Vᴴ *ᵥ v = Qatlib.Foundations.PureStateMath.Ket i := by
    have h := hB.star_eigenvectorUnitary_mulVec i
    change Vᴴ *ᵥ v = Pi.single i (1 : ℂ) at h
    exact h.trans hket.symm
  have hcol : V *ᵥ Qatlib.Foundations.PureStateMath.Ket i = v := by
    have h := hB.eigenvectorUnitary_mulVec i
    change V *ᵥ Pi.single i (1 : ℂ) = v at h
    simpa only [← hket] using! h
  have hDsingle : D *ᵥ Pi.single i (1 : ℂ) =
      p.eval (hB.eigenvalues i : ℂ) • Pi.single i (1 : ℂ) := by
    ext j
    by_cases h : i = j <;>
      simp [D, Matrix.mulVec_diagonal, eq_comm, h]
  calc
    Polynomial.aeval B p *ᵥ v = (V * D * Vᴴ) *ᵥ v := by
      rw [aeval_hermitian_diagonalization B hB p]
    _ = (V * D) *ᵥ (Vᴴ *ᵥ v) :=
      (Matrix.mulVec_mulVec v (V * D) Vᴴ).symm
    _ = V *ᵥ (D *ᵥ (Vᴴ *ᵥ v)) :=
      (Matrix.mulVec_mulVec (Vᴴ *ᵥ v) V D).symm
    _ = V *ᵥ (D *ᵥ Qatlib.Foundations.PureStateMath.Ket i) := by rw [hstar]
    _ = V *ᵥ (p.eval (hB.eigenvalues i : ℂ) • Qatlib.Foundations.PureStateMath.Ket i) := by
      rw [hket, hDsingle]
    _ = p.eval (hB.eigenvalues i : ℂ) • v := by rw [Matrix.mulVec_smul, hcol]

/-- On a Gram eigenvector with eigenvalue between zero and one, the Marriott-Watrous binomial
response is the square of the binomial tail at that eigenvalue. -/
private theorem mwBinomialResponse_eigenvalue (S U : Reg n → Bool)
    (m j0 : ℕ) (i : Reg n) (hEig0 : 0 ≤
      (Matrix.isHermitian_conjTranspose_mul_self (verifierSpectralMatrix S U)).eigenvalues i)
    (hEig1 : (Matrix.isHermitian_conjTranspose_mul_self
      (verifierSpectralMatrix S U)).eigenvalues i ≤ 1) :
    mwBinomialResponse S U (⇑((Matrix.isHermitian_conjTranspose_mul_self
      (verifierSpectralMatrix S U)).eigenvectorBasis i)) m j0 =
      (binomialTail m j0 ((Matrix.isHermitian_conjTranspose_mul_self
        (verifierSpectralMatrix S U)).eigenvalues i)) ^ 2 := by
  classical
  let A := verifierSpectralMatrix S U
  let B := Aᴴ * A
  let hB : B.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  let p := (binomialTailPolynomial m j0).map Complex.ofRealHom
  let ψ : QState (Reg n) := ⇑(hB.eigenvectorBasis i)
  have hact := aeval_hermitian_eigenvector_action B hB p i
  have heval : p.eval (hB.eigenvalues i : ℂ) =
      (binomialTail m j0 (hB.eigenvalues i) : ℂ) := by
    exact binomialTailPolynomial_complex_eval m j0 (hB.eigenvalues i)
  have hψnorm : ‖toEuclidean_fromVec ψ‖ = 1 := by
    exact (normalized_iff_norm_toEuclidean_fromVec _).mp
      ((normalized_iff_norm_toEuclidean_fromVec _).mpr
        (hB.eigenvectorBasis.orthonormal.1 i))
  unfold mwBinomialResponse
  change ‖toEuclidean_fromVec (mwBinomialResponseOperator S U m j0 *ᵥ ψ)‖ ^ 2 = _
  change ‖toEuclidean_fromVec (Polynomial.aeval B p *ᵥ ψ)‖ ^ 2 = _
  have hsmul : ∀ c : ℂ, toEuclidean_fromVec (c • ψ) = c • toEuclidean_fromVec ψ := by
    intro c
    ext x
    rfl
  rw [hact, heval, hsmul, norm_smul, hψnorm]
  have htail0 := binomialTail_nonneg m j0 hEig0 hEig1
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htail0]

/-- Above the spectral completeness threshold, some normalized witness has Marriott-Watrous
binomial response at least two thirds with the chosen gap parameters. -/
private theorem mwBinomialResponse_completeness_bound (S U : Reg n → Bool)
    (α β : ℝ) (hβ : 0 ≤ β) (hlt : β < α) (hα : α ≤ 1)
    (hspec : α ≤ spectralForrelation n S U) :
    ∃ ψ : QState (Reg n), Normalized ψ ∧
      2 / 3 ≤ mwBinomialResponse S U ψ (gapStepCount α β)
        (Nat.floor ((gapStepCount α β : ℝ) * ((α + β) / 2))) := by
  classical
  obtain ⟨i, hEig⟩ := exists_gram_eigenvalue_ge S U α hspec
  let hB := Matrix.isHermitian_conjTranspose_mul_self (verifierSpectralMatrix S U)
  let ψ : QState (Reg n) := ⇑(hB.eigenvectorBasis i)
  have hψ : Normalized ψ := (normalized_iff_norm_toEuclidean_fromVec _).mpr
    (hB.eigenvectorBasis.orthonormal.1 i)
  have hEig0 : 0 ≤ hB.eigenvalues i := by
    obtain ⟨_, hmass⟩ := gram_eigenvalue_is_witnessMass S U hB i
    rw [← hmass]
    exact forrWitnessMass_nonneg S U ψ
  have hEig1 : hB.eigenvalues i ≤ 1 :=
    (gram_eigenvalue_le_spectral S U hB i).trans
      (spectralForrelationBasics (n := n) (S := S) (U := U)).2.1
  have htail := binomial_gap_completeness α β (hB.eigenvalues i)
    hβ hlt hα hEig hEig1
  have hresponse := mwBinomialResponse_eigenvalue S U
    (gapStepCount α β)
    (Nat.floor ((gapStepCount α β : ℝ) * ((α + β) / 2))) i hEig0 hEig1
  refine ⟨ψ, hψ, ?_⟩
  rw [hresponse]
  have htail0 := binomialTail_nonneg (gapStepCount α β)
    (Nat.floor ((gapStepCount α β : ℝ) * ((α + β) / 2))) hEig0 hEig1
  nlinarith

/-- Constructs a unitary bit-oracle verifier with completeness two thirds, soundness one third,
and at most 256 divided by the squared spectral gap queries to each oracle. -/
theorem marriottWatrousAmplification : MarriottWatrousAmplification := by
  intro n α β hβ hlt hα
  classical
  let m := gapStepCount α β
  let j0 := Nat.floor ((m : ℝ) * ((α + β) / 2))
  refine ⟨2 * m + 1, mwActualAmplificationCircuit n m j0,
    mwActualSuccessEvent n, ?_, ?_, ?_, ?_, ?_⟩
  · have hb := gapStepCount_two_mul_add_one_le α β hβ hlt hα
    exact_mod_cast hb
  · exact mwActualAmplificationCircuit_unitary n m j0
  · rw [(mwActualAmplificationCircuit_queries n m j0).1]
    omega
  · rw [(mwActualAmplificationCircuit_queries n m j0).2]
    omega
  · intro S U
    constructor
    · intro hspec
      obtain ⟨ψ, hψ, hp⟩ :=
        mwBinomialResponse_completeness_bound S U α β hβ hlt hα hspec
      refine ⟨ψ, hψ, ?_⟩
      rw [mwActualSuccess_probability]
      exact hp
    · intro hspec ψ hψ
      rw [mwActualSuccess_probability]
      exact (mwBinomialResponse_soundness_bound S U ψ α β hβ hlt hα hspec hψ).trans
        (by norm_num : (1 / 9 : ℝ) ≤ 1 / 3)

end G1

end Qatlib.Papers.QMAvsQCMA25.Forrelation.MarriottWatrousAmplificationSepa
