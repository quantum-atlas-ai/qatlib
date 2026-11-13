/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.QlsHhlDefs
import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteGatePhaseBoundary

/-!
# Signed diagonal instances for HHL lower-bound arguments

`q86Data` and `q86Req` define one-sparse sign-diagonal linear systems with Hadamard-prepared
uniform inputs. Their matrices are unitary and self-inverse, so their least-squares solutions
are the signed uniform states `q86Target`, providing explicit instances in the linear-systems
setting of [HarrowHassidimLloyd2009].

The module verifies preparation legality, register embeddings, and zero-extension identities,
then expresses target-state separation in terms of the Hamming distance `q86Ham`.

## Main statements

* `q86_leastSquaresDirection`: the least-squares direction is the signed uniform target.
* `q86_zeroExtend_sub_sq`: zero extension preserves squared target distances.
* `q86_target_sub_sq`: squared distance is four times normalized Hamming distance.

## References

* [Harrow et al., 2009][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL
open Qatlib.Concepts.HhlAlgorithms.Postselection
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

open Matrix Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The finite-gate word applying a Hadamard gate to each of the first `m` wires. -/
def q86HWord (m : ℕ) : List FiniteGateCode := (List.range m).map FiniteGateCode.h

/-- The diagonal sparse-oracle data with entry `1` when `σ` is true and `-1` otherwise, and zero
recorded access and arithmetic costs. -/
def q86Data {N : ℕ} (σ : Fin N → Bool) : SparseOracleData (Fin N) (Fin N) where
  rowPos := fun o => [o]
  colPos := fun i => [i]
  value := fun o i => if o = i then (if σ o then (1, 0) else (-1, 0)) else (0, 0)
  rowCallGates := 0
  colCallGates := 0
  valueCallGates := 0
  arithBits := 0

/-- The complex sign vector taking value `1` on true bits and `-1` on false bits. -/
def q86Sign {N : ℕ} (σ : Fin N → Bool) : Fin N → ℂ := fun j => if σ j then 1 else -1

/-- The matrix represented by `q86Data σ` is diagonal with diagonal entries `q86Sign σ`. -/
theorem q86Data_matrix {N : ℕ} (σ : Fin N → Bool) :
    (q86Data σ).matrix = diagonal (q86Sign σ) := by
  ext o i
  simp only [SparseOracleData.matrix, q86Data, gaussianRatComplex]
  by_cases h : o = i
  · subst h
    by_cases hs : σ o = true <;> simp [q86Sign, hs]
  · simp [h]

/-- The sign-diagonal oracle data is one-sparse with entry bound one. -/
theorem q86_sparseBounded {N : ℕ} (σ : Fin N → Bool) :
    (q86Data σ).IsSparseBounded 1 1 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · intro o
    constructor
    · simp [q86Data]
    · simp [q86Data]
  · intro i
    constructor
    · simp [q86Data]
    · simp [q86Data]
  · intro o i hi
    have hoi : o ≠ i := by
      intro h
      apply hi
      subst h
      simp [q86Data]
    show (if o = i then _ else (0, 0)) = gzero
    simp [hoi, gzero]
  · intro o i hi
    have hio : o ≠ i := by
      intro h
      apply hi
      subst h
      simp [q86Data]
    show (if o = i then _ else (0, 0)) = gzero
    simp [hio, gzero]
  · intro o i
    show ‖gaussianRatComplex (if o = i then (if σ o then (1, 0) else (-1, 0)) else (0, 0))‖ ≤ 1
    by_cases h : o = i
    · subst h
      by_cases hs : σ o = true <;> simp [gaussianRatComplex, hs]
    · simp [gaussianRatComplex, h]

/-- The complex sign vector is self-adjoint under pointwise conjugation. -/
theorem q86_sign_selfAdjoint {N : ℕ} (σ : Fin N → Bool) :
    IsSelfAdjoint (q86Sign σ) := by
  show star (q86Sign σ) = q86Sign σ
  funext j
  by_cases hs : σ j = true <;> simp [q86Sign, hs]

/-- The sign-diagonal data satisfies `qlsSparseHermitianBounded`. -/
theorem q86_hermitianBounded {N : ℕ} (σ : Fin N → Bool) :
    qlsSparseHermitianBounded (q86Data σ) := by
  refine ⟨?_, ?_⟩
  · rw [q86Data_matrix]
    exact Matrix.isHermitian_diagonal_of_self_adjoint _ (q86_sign_selfAdjoint σ)
  · rw [q86Data_matrix, Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr ?_
    intro i
    by_cases hs : σ i = true <;> simp [q86Sign, hs]

/-- The sign-diagonal oracle matrix is unitary. -/
theorem q86_matrix_unitary {N : ℕ} (σ : Fin N → Bool) :
    (q86Data σ).matrix ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [q86Data_matrix, Matrix.mem_unitaryGroup_iff']
  have hsq : diagonal (q86Sign σ) * diagonal (q86Sign σ) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    by_cases hs : σ j = true <;> simp [q86Sign, hs]
  have hstar : star (diagonal (q86Sign σ)) = diagonal (q86Sign σ) := by
    rw [Matrix.star_eq_conjTranspose]
    exact Matrix.isHermitian_diagonal_of_self_adjoint _ (q86_sign_selfAdjoint σ)
  rw [hstar, hsq]

/-- The sign-diagonal oracle matrix satisfies the condition window with parameter one. -/
theorem q86_condWindow {N : ℕ} (σ : Fin N → Bool) :
    HasConditionWindow ((q86Data σ).matrix : Operator N) 1 := by
  refine ⟨by norm_num, ?_⟩
  intro v
  rw [one_mul]
  have hunit := q86_matrix_unitary σ
  have hsq := sum_normSq_mulVec_of_mem_unitaryGroup hunit v
  have hsq' : (∑ p, ‖v p‖ ^ 2) = ∑ p, ‖((q86Data σ).matrix *ᵥ v) p‖ ^ 2 := by
    simp_rw [← Complex.normSq_eq_norm_sq]
    exact hsq.symm
  have h1 : ‖toEuclidean_fromVec v‖ = (∑ p, ‖v p‖ ^ 2).sqrt := by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_toEuclidean_fromVec_sq]
  have h2 : ‖toEuclidean_fromVec ((q86Data σ).matrix *ᵥ v)‖
      = (∑ p, ‖((q86Data σ).matrix *ᵥ v) p‖ ^ 2).sqrt := by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_toEuclidean_fromVec_sq]
  rw [h1, h2, hsq']

/-- Running a concatenated circuit equals running its first part and then its second part. -/
theorem run_append {I : Type} [Fintype I] [DecidableEq I] (o : Matrix I I ℂ)
    (C1 C2 : List (Step I)) (ψ : QState I) :
    Run o (C1 ++ C2) ψ = Run o C2 (Run o C1 ψ) := by
  induction C1 generalizing ψ with
  | nil => simp
  | cons s C1 ih =>
    cases s with
    | gate U => simpa using! ih (ApplyGate U ψ)
    | query => simpa using! ih (ApplyGate o ψ)

/-- A gate on wire `w` acts at each register value by summing over the two possible replacements
of that wire. -/
theorem wireGate_mulVec_update {n : ℕ} (w : Fin n) (U : Matrix Bool Bool ℂ)
    (ψ : QState (Reg n)) (z : Reg n) :
    (wireGate n w U *ᵥ ψ) z = ∑ b : Bool, U (z w) b * ψ (Function.update z w b) := by
  have hexp : (wireGate n w U *ᵥ ψ) z = ∑ y : Reg n, wireGate n w U z y * ψ y := by
    simp [Matrix.mulVec, dotProduct]
  rw [hexp]
  have hcond : ∀ y : Reg n, (∀ k : Fin n, k ≠ w → z k = y k) →
      y = Function.update z w (y w) := by
    intro y hy
    funext i
    by_cases hi : i = w
    · subst hi
      simp
    · have h1 : Function.update z w (y w) i = z i := by
        simp [Function.update_of_ne hi]
      rw [h1, hy i hi]
  have hinj : Set.InjOn (fun b : Bool => Function.update z w b)
      (Finset.univ : Finset Bool) := by
    intro b₁ _ b₂ _ h
    have := congrFun h w
    simp at this
    exact this
  have hfilter : (Finset.univ : Finset (Reg n)).filter (fun y => ∀ k : Fin n, k ≠ w → z k = y k)
      = (Finset.univ : Finset Bool).image (fun b => Function.update z w b) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hy
      exact Exists.intro (y w) ((hcond y hy).symm)
    · intro hy
      obtain ⟨b, hb⟩ := hy
      have hyz : y = Function.update z w b := hb.symm
      subst hyz
      intro k hk
      simp [Function.update_of_ne hk]
  have houtside : ∀ y : Reg n, ¬(∀ k : Fin n, k ≠ w → z k = y k) →
      wireGate n w U z y * ψ y = 0 := by
    intro y hy
    rw [wireGate_apply, if_neg hy, zero_mul]
  have hpart : (∑ y : Reg n, wireGate n w U z y * ψ y)
      = ∑ y ∈ (Finset.univ : Finset (Reg n)).filter (fun y => ∀ k : Fin n, k ≠ w → z k = y k),
        wireGate n w U z y * ψ y := by
    have hz : (∑ y ∈ (Finset.univ : Finset (Reg n)).filter
        (fun y => ¬(∀ k : Fin n, k ≠ w → z k = y k)), wireGate n w U z y * ψ y) = 0 :=
      Finset.sum_eq_zero (fun y hy => houtside y (by simpa using! hy))
    conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Reg n)))
      (p := fun y : Reg n => ∀ k : Fin n, k ≠ w → z k = y k)]
    rw [hz, add_zero]
  rw [hpart]
  have hstep : (∑ y ∈ (Finset.univ : Finset (Reg n)).filter
        (fun y => ∀ k : Fin n, k ≠ w → z k = y k), wireGate n w U z y * ψ y)
      = ∑ y ∈ (Finset.univ : Finset Bool).image (fun b => Function.update z w b),
        U (z w) (y w) * ψ y := by
    rw [hfilter]
    refine Finset.sum_congr rfl ?_
    intro y hy
    have hy' : ∀ k : Fin n, k ≠ w → z k = y k := by
      obtain ⟨b, _, hb⟩ := by simpa only [Finset.mem_image] using! hy
      intro k hk
      rw [← hb]
      simp [Function.update_of_ne hk]
    rw [wireGate_apply, if_pos hy']
  rw [hstep, Finset.sum_image hinj]
  simp only [Function.update_self]

/-- Applying Hadamards to the first `k` wires of the zero register gives amplitude `((sqrt
2)⁻¹)^k` on registers whose remaining wires are false, and zero elsewhere. -/
theorem q86HWord_run (n m : ℕ) (hmn : m ≤ n) : ∀ k, k ≤ m → ∀ z : Reg n,
    Run (1 : Matrix (Reg n) (Reg n) ℂ)
      (finiteCodeCircuit n ((List.range k).map FiniteGateCode.h))
      (Qatlib.Foundations.PureStateMath.Ket (qlsZeroReg n)) z =
    (if ∀ i : Fin n, k ≤ i.val → z i = false then ((Real.sqrt 2 : ℂ)⁻¹) ^ k else 0) := by
  intro k
  induction k with
  | zero =>
    intro hk z
    have hrun : Run (1 : Matrix (Reg n) (Reg n) ℂ)
        (finiteCodeCircuit n ((List.range 0).map FiniteGateCode.h))
        (Qatlib.Foundations.PureStateMath.Ket (qlsZeroReg n)) z = (Qatlib.Foundations.PureStateMath.Ket (qlsZeroReg n) : QState (Reg n)) z := by
      rfl
    have hket : (Qatlib.Foundations.PureStateMath.Ket (qlsZeroReg n) : QState (Reg n)) z
        = if z = qlsZeroReg n then (1 : ℂ) else 0 := by
      simp [Qatlib.Foundations.PureStateMath.Ket]
    rw [hrun, hket]
    have hcond : (∀ i : Fin n, (0:ℕ) ≤ i.val → z i = false) ↔
        z = qlsZeroReg n := by
      constructor
      · intro h
        funext i
        exact h i (Nat.zero_le _)
      · intro h i _
        rw [h]
        rfl
    simp only [hcond]
    by_cases hz : z = qlsZeroReg n <;> simp [hz]
  | succ k ih =>
    intro hk z
    have hklt : k < n := by omega
    have hword : (List.range (k + 1)).map FiniteGateCode.h
        = ((List.range k).map FiniteGateCode.h) ++ [FiniteGateCode.h k] := by
      rw [List.range_succ, List.map_append]
      rfl
    have hcat : finiteCodeCircuit n ((List.range (k + 1)).map FiniteGateCode.h)
        = finiteCodeCircuit n ((List.range k).map FiniteGateCode.h) ++
          [Step.gate (finiteCodeMatrix n (FiniteGateCode.h k))] := by
      simp only [finiteCodeCircuit, hword, List.map_append, List.map_cons, List.map_nil]
    have hgate : finiteCodeMatrix n (FiniteGateCode.h k)
        = wireGate n ⟨k, hklt⟩ Hadamard := by
      simp [finiteCodeMatrix, hklt]
    have hrun : Run (1 : Matrix (Reg n) (Reg n) ℂ)
        (finiteCodeCircuit n ((List.range (k + 1)).map FiniteGateCode.h))
        (Qatlib.Foundations.PureStateMath.Ket (qlsZeroReg n)) z
        = (wireGate n ⟨k, hklt⟩ Hadamard *ᵥ
            Run (1 : Matrix (Reg n) (Reg n) ℂ)
              (finiteCodeCircuit n ((List.range k).map FiniteGateCode.h))
              (Qatlib.Foundations.PureStateMath.Ket (qlsZeroReg n))) z := by
      rw [hcat, run_append, hgate]
      rfl
    have ihz : ∀ y : Reg n,
        Run (1 : Matrix (Reg n) (Reg n) ℂ)
          (finiteCodeCircuit n ((List.range k).map FiniteGateCode.h))
          (Qatlib.Foundations.PureStateMath.Ket (qlsZeroReg n)) y =
        (if ∀ i : Fin n, k ≤ i.val → y i = false then ((Real.sqrt 2 : ℂ)⁻¹) ^ k else 0) :=
      ih (by omega)
    rw [hrun, wireGate_mulVec_update, Fintype.sum_bool,
      ihz (Function.update z ⟨k, hklt⟩ false), ihz (Function.update z ⟨k, hklt⟩ true)]
    by_cases hz : ∀ i : Fin n, k + 1 ≤ i.val → z i = false
    · rw [if_pos hz]
      have hz1 : ∀ i : Fin n, k ≤ i.val → Function.update z ⟨k, hklt⟩ false i = false := by
        intro i hi
        by_cases hi' : i.val = k
        · subst hi'
          simp
        · rw [Function.update_of_ne (by intro h; exact hi' (congrArg Fin.val h))]
          exact hz i (by omega)
      have hz2 : ¬ ∀ i : Fin n, k ≤ i.val → Function.update z ⟨k, hklt⟩ true i = false := by
        intro h
        have := h ⟨k, hklt⟩ (Nat.le_refl k)
        simp at this
      rw [if_pos hz1, if_neg hz2, mul_zero]
      simp only [zero_add, hadamard_apply_false]
      ring
    · have hzn : ¬ ∀ i : Fin n, k + 1 ≤ i.val → z i = false := hz
      push Not at hz
      obtain ⟨i, hi, hzi⟩ := hz
      have hi1 : k < i.val := by omega
      have hne : (i : Fin n) ≠ ⟨k, hklt⟩ := by
        intro he
        exact hi1.ne (congrArg Fin.val he).symm
      rw [if_neg hzn]
      have hz1 : ¬ ∀ j : Fin n, k ≤ j.val → Function.update z ⟨k, hklt⟩ false j = false := by
        intro h
        have := h i (by omega)
        rw [Function.update_of_ne hne] at this
        exact hzi this
      have hz2 : ¬ ∀ j : Fin n, k ≤ j.val → Function.update z ⟨k, hklt⟩ true j = false := by
        intro h
        have := h i (by omega)
        rw [Function.update_of_ne hne] at this
        exact hzi this
      rw [if_neg hz1, if_neg hz2]
      simp only [mul_zero, add_zero]

/-- The Hadamard preparation has amplitude `((sqrt 2)⁻¹)^m` at every embedded label of `Fin
(2^m)`. -/
theorem q86_run_at_label (m : ℕ) (i : Fin (2 ^ m)) :
    Run (1 : Matrix (Reg (qlsBitWidth (2 ^ m))) (Reg (qlsBitWidth (2 ^ m))) ℂ)
      (finiteCodeCircuit (qlsBitWidth (2 ^ m)) ((List.range m).map FiniteGateCode.h))
      (Qatlib.Foundations.PureStateMath.Ket (qlsZeroReg (qlsBitWidth (2 ^ m)))) (qlsRegEmbed (2 ^ m) i)
      = ((Real.sqrt 2 : ℂ)⁻¹) ^ m := by
  have hlog : Nat.log2 (2 ^ m) = m := by
    rw [Nat.log2_eq_log_two, Nat.log_pow (by norm_num)]
  have hle : m ≤ qlsBitWidth (2 ^ m) := by
    simp only [qlsBitWidth, hlog]
    omega
  rw [q86HWord_run _ m hle m (le_refl m)]
  have hcond : ∀ j : Fin (qlsBitWidth (2 ^ m)), m ≤ j.val →
      qlsRegEmbed (2 ^ m) i j = false := by
    intro j hj
    have hi : i.val < 2 ^ m := i.isLt
    have h2 : (2 : ℕ) ^ m ≤ 2 ^ j.val := pow_le_pow_right' (by norm_num) hj
    have hi2 : i.val < 2 ^ j.val := lt_of_lt_of_le hi h2
    simp only [qlsRegEmbed]
    rw [Nat.testBit_lt_two_pow hi2]
  simp only [if_pos hcond]

/-- The dimension-`2^m` sparse HHL request with sign-diagonal data, sparsity and condition
parameter one, error `1 / 4`, and Hadamard input preparation. -/
noncomputable def q86Req (m : ℕ) (σ : Fin (2 ^ m) → Bool) : SparseHHLRequest where
  dim := 2 ^ m
  sparsity := 1
  kappa := 1
  eps := 1 / 4
  data := q86Data σ
  inputPrep := q86HWord m

/-- The Hadamard input-preparation word of `q86Req` is legal on its allocated register. -/
theorem q86_inputPrep_legal (m : ℕ) (σ : Fin (2 ^ m) → Bool) :
    finiteWordLegal (qlsBitWidth (q86Req m σ).dim) (q86Req m σ).inputPrep = true := by
  have hbw : qlsBitWidth (q86Req m σ).dim = m + 1 := by
    have hlog : Nat.log2 (2 ^ m) = m := by
      rw [Nat.log2_eq_log_two, Nat.log_pow (by norm_num)]
    simp only [q86Req, qlsBitWidth, hlog]
  rw [hbw]
  have h : ∀ g ∈ q86HWord m, finiteCodeLegal (m + 1) g = true := by
    intro g hg
    simp only [q86HWord, List.mem_map, List.mem_range] at hg
    obtain ⟨i, hi, hg⟩ := hg
    subst hg
    simp only [finiteCodeLegal]
    show decide (i < m + 1) = true
    simp only [decide_eq_true_eq]
    omega
  have hall : (q86HWord m).all (finiteCodeLegal (m + 1)) = true := by
    rw [List.all_eq_true]
    exact h
  simpa [finiteWordLegal, q86Req, q86HWord] using! hall

/-- The prepared input of `q86Req` is the constant vector with amplitude `((sqrt 2)⁻¹)^m`. -/
theorem q86_preparedInput (m : ℕ) (σ : Fin (2 ^ m) → Bool) :
    qlsPreparedInput (q86Req m σ) = fun _ : Fin (2 ^ m) => ((Real.sqrt 2 : ℂ)⁻¹) ^ m := by
  funext i
  show qlsWordRunState (q86Req m σ).inputPrep
      (Qatlib.Foundations.PureStateMath.Ket (qlsZeroReg (qlsBitWidth (q86Req m σ).dim))) (qlsRegEmbed (q86Req m σ).dim i)
      = ((Real.sqrt 2 : ℂ)⁻¹) ^ m
  exact q86_run_at_label m i

/-- The uniform-amplitude target vector with signs prescribed by `σ`. -/
noncomputable def q86Target (m : ℕ) (σ : Fin (2 ^ m) → Bool) : QState (Fin (2 ^ m)) :=
  fun j => q86Sign σ j * ((Real.sqrt 2 : ℂ)⁻¹) ^ m

/-- The signed uniform target vector `q86Target m σ` is normalized. -/
theorem q86_target_normalized (m : ℕ) (σ : Fin (2 ^ m) → Bool) :
    Normalized (q86Target m σ) := by
  have hterm : ∀ j : Fin (2 ^ m),
      ‖q86Sign σ j * ((Real.sqrt 2 : ℂ)⁻¹) ^ m‖ ^ 2 = ((2 : ℝ) ^ m)⁻¹ := by
    intro j
    have hs1 : ‖(q86Sign σ j : ℂ)‖ = 1 := by
      by_cases hs : σ j = true <;> simp [q86Sign, hs]
    have h2 : ‖((Real.sqrt 2 : ℂ)⁻¹) ^ m‖ = ((Real.sqrt 2 : ℝ)⁻¹) ^ m := by
      rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [norm_mul, hs1, h2, one_mul]
    calc (((Real.sqrt 2 : ℝ)⁻¹) ^ m) ^ 2 = ((Real.sqrt 2 : ℝ)⁻¹) ^ (m * 2) := by rw [← pow_mul]
      _ = ((Real.sqrt 2 : ℝ)⁻¹) ^ (2 * m) := by rw [mul_comm]
      _ = (((Real.sqrt 2 : ℝ)⁻¹) ^ 2) ^ m := by rw [pow_mul]
      _ = ((2 : ℝ)⁻¹) ^ m := by rw [pow_two, ← mul_inv, ← pow_two, hsq]
      _ = ((2 : ℝ) ^ m)⁻¹ := by rw [inv_pow]
  have hsum : ∑ j : Fin (2 ^ m), ‖q86Sign σ j * ((Real.sqrt 2 : ℂ)⁻¹) ^ m‖ ^ 2
      = ∑ j : Fin (2 ^ m), ((2 : ℝ) ^ m)⁻¹ := by
    apply Finset.sum_congr rfl
    intro j _
    exact hterm j
  unfold Normalized q86Target
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcast : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m := by norm_cast
  rw [hcast, mul_inv_cancel₀ (by positivity)]

/-- The sign-diagonal oracle matrix is its own inverse. -/
theorem q86_matrix_selfInv (m : ℕ) (σ : Fin (2 ^ m) → Bool) :
    (q86Data σ).matrix * (q86Data σ).matrix = 1 := by
  rw [q86Data_matrix, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  by_cases hs : σ j = true <;> simp [q86Sign, hs]

/-- The least-squares vector of the sign-diagonal request is exactly `q86Target m σ`. -/
theorem q86_leastSquaresVector (m : ℕ) (σ : Fin (2 ^ m) → Bool) :
    leastSquaresVector ((q86Req m σ).data.matrix) (qlsPreparedInput (q86Req m σ))
      = q86Target m σ := by
  have hpseudo : matrixPseudoinverse ((q86Data σ).matrix : Matrix (Fin (2 ^ m)) _ ℂ)
      = (q86Data σ).matrix := by
    have hAA := q86_matrix_selfInv m σ
    have hsym : (((q86Data σ).matrix * (q86Data σ).matrix) : Matrix (Fin (2 ^ m)) _ ℂ)ᴴ
        = (q86Data σ).matrix * (q86Data σ).matrix := by
      rw [hAA]
      simp
    have h := matrixPseudoinverse_unique ((q86Data σ).matrix : Matrix (Fin (2 ^ m)) _ ℂ)
      ((q86Data σ).matrix)
      (by rw [Matrix.mul_assoc, hAA, Matrix.mul_one])
      (by rw [Matrix.mul_assoc, hAA, Matrix.mul_one])
      hsym hsym
    exact h.symm
  have hmul : (((q86Data σ).matrix : Matrix (Fin (2 ^ m)) _ ℂ) *ᵥ
      qlsPreparedInput (q86Req m σ)) = q86Target m σ := by
    rw [q86Data_matrix, q86_preparedInput]
    funext j
    rw [Matrix.mulVec_diagonal]
    rfl
  show leastSquaresVector ((q86Data σ).matrix : Matrix (Fin (2 ^ m)) _ ℂ)
      (qlsPreparedInput (q86Req m σ)) = q86Target m σ
  unfold leastSquaresVector
  rw [hpseudo, hmul]

/-- The least-squares direction of the sign-diagonal request is `some (q86Target m σ)`. -/
theorem q86_leastSquaresDirection (m : ℕ) (σ : Fin (2 ^ m) → Bool) :
    leastSquaresDirection ((q86Req m σ).data.matrix) (qlsPreparedInput (q86Req m σ))
      = some (q86Target m σ) := by
  have hne : q86Target m σ ≠ 0 := by
    intro h
    have := congrFun h 0
    simp only [q86Target, Pi.zero_apply] at this
    have hne0 : q86Sign σ 0 * ((Real.sqrt 2 : ℂ)⁻¹) ^ m ≠ 0 := by
      apply mul_ne_zero
      · by_cases hs : σ 0 = true <;> simp [q86Sign, hs]
      · exact pow_ne_zero _ (inv_ne_zero (by
          exact_mod_cast (Real.sqrt_ne_zero (by norm_num) |>.mpr (by norm_num))))
    exact hne0 this
  show leastSquaresDirection ((q86Data σ).matrix : Matrix (Fin (2 ^ m)) _ ℂ)
      (qlsPreparedInput (q86Req m σ)) = some (q86Target m σ)
  have hvec : leastSquaresVector ((q86Data σ).matrix : Matrix (Fin (2 ^ m)) _ ℂ)
      (qlsPreparedInput (q86Req m σ)) = q86Target m σ :=
    q86_leastSquaresVector m σ
  show (if leastSquaresVector ((q86Data σ).matrix : Matrix (Fin (2 ^ m)) _ ℂ)
        (qlsPreparedInput (q86Req m σ)) = 0 then none
      else some (PostMeasure (leastSquaresVector ((q86Data σ).matrix : Matrix (Fin (2 ^ m)) _ ℂ)
        (qlsPreparedInput (q86Req m σ))) Finset.univ))
    = some (q86Target m σ)
  rw [hvec, if_neg hne]
  congr 1
  have hn : Normalized (q86Target m σ) := q86_target_normalized m σ
  have hcollapse : Collapse (q86Target m σ) Finset.univ = q86Target m σ := by
    funext i
    rw [collapse_apply, if_pos (Finset.mem_univ i)]
  have hprob : MeasureProb (q86Target m σ) Finset.univ = 1 := hn
  funext i
  simp [PostMeasure, hcollapse, hprob]

/-- The register width allocated to dimension `2^m` is `m + 1`. -/
theorem q86_bitWidth (m : ℕ) : qlsBitWidth (2 ^ m) = m + 1 := by
  have hlog : Nat.log2 (2 ^ m) = m := by
    rw [Nat.log2_eq_log_two, Nat.log_pow (by norm_num)]
  simp only [qlsBitWidth, hlog]

/-- The register embedding for `Fin (2^m)` is injective. -/
theorem q86_regEmbed_inj (m : ℕ) : Function.Injective (qlsRegEmbed (2 ^ m)) := by
  intro i j hij
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < m + 1
  · have hbound : t < qlsBitWidth (2 ^ m) := by rw [q86_bitWidth]; exact ht
    have := congrFun hij ⟨t, hbound⟩
    simpa [qlsRegEmbed] using! this
  · have hi : i.val < 2 ^ t := lt_of_lt_of_le i.isLt (pow_le_pow_right' (by norm_num) (by omega))
    have hj : j.val < 2 ^ t := lt_of_lt_of_le j.isLt (pow_le_pow_right' (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow hi, Nat.testBit_lt_two_pow hj]

/-- Zero extension evaluated at an embedded label returns the original vector entry. -/
theorem q86_zeroExtend_apply (m : ℕ) (ψ : QState (Fin (2 ^ m))) (j : Fin (2 ^ m)) :
    qlsZeroExtend ψ (qlsRegEmbed (2 ^ m) j) = ψ j := by
  simp only [qlsZeroExtend]
  have hex : ∃ i, qlsRegEmbed (2 ^ m) i = qlsRegEmbed (2 ^ m) j := ⟨j, rfl⟩
  rw [dif_pos hex]
  exact congrArg ψ (q86_regEmbed_inj m (Classical.choose_spec hex))

/-- Zero extension preserves the sum of squared entrywise distances between two signed target
vectors. -/
theorem q86_zeroExtend_sub_sq (m : ℕ) (σ τ : Fin (2 ^ m) → Bool) :
    ∑ x : Reg (qlsBitWidth (2 ^ m)),
        ‖qlsZeroExtend (q86Target m σ) x - qlsZeroExtend (q86Target m τ) x‖ ^ 2
      = ∑ j : Fin (2 ^ m), ‖q86Target m σ j - q86Target m τ j‖ ^ 2 := by
  have hinj : Set.InjOn (qlsRegEmbed (2 ^ m)) (Finset.univ : Finset (Fin (2 ^ m))) := by
    intro a _ b _ h
    exact q86_regEmbed_inj m h
  have hzero : ∀ x : Reg (qlsBitWidth (2 ^ m)),
      (¬∃ i : Fin (2 ^ m), qlsRegEmbed (2 ^ m) i = x) →
        ‖qlsZeroExtend (q86Target m σ) x - qlsZeroExtend (q86Target m τ) x‖ ^ 2 = 0 := by
    intro x hx
    show ‖(if h : ∃ i, qlsRegEmbed (2 ^ m) i = x then q86Target m σ h.choose else 0)
        - (if h : ∃ i, qlsRegEmbed (2 ^ m) i = x then q86Target m τ h.choose else 0)‖ ^ 2 = 0
    rw [dif_neg hx, dif_neg hx, sub_self, norm_zero]
    norm_num
  calc (∑ x : Reg (qlsBitWidth (2 ^ m)),
        ‖qlsZeroExtend (q86Target m σ) x - qlsZeroExtend (q86Target m τ) x‖ ^ 2)
      = (∑ x ∈ (Finset.univ : Finset (Reg (qlsBitWidth (2 ^ m))))
            \ (Finset.univ.image (qlsRegEmbed (2 ^ m))),
          ‖qlsZeroExtend (q86Target m σ) x - qlsZeroExtend (q86Target m τ) x‖ ^ 2)
        + ∑ x ∈ Finset.univ.image (qlsRegEmbed (2 ^ m)),
          ‖qlsZeroExtend (q86Target m σ) x - qlsZeroExtend (q86Target m τ) x‖ ^ 2 :=
      (Finset.sum_sdiff (Finset.subset_univ _)).symm
    _ = ∑ x ∈ Finset.univ.image (qlsRegEmbed (2 ^ m)),
          ‖qlsZeroExtend (q86Target m σ) x - qlsZeroExtend (q86Target m τ) x‖ ^ 2 := by
        rw [Finset.sum_eq_zero, zero_add]
        intro x hx
        apply hzero
        have hx2 : x ∉ Finset.univ.image (qlsRegEmbed (2 ^ m)) := (Finset.mem_sdiff.1 hx).2
        simpa [Finset.mem_image, Finset.mem_univ] using! hx2
    _ = ∑ j : Fin (2 ^ m), ‖qlsZeroExtend (q86Target m σ) (qlsRegEmbed (2 ^ m) j)
          - qlsZeroExtend (q86Target m τ) (qlsRegEmbed (2 ^ m) j)‖ ^ 2 := by
        rw [Finset.sum_image hinj]
    _ = ∑ j : Fin (2 ^ m), ‖q86Target m σ j - q86Target m τ j‖ ^ 2 :=
      Finset.sum_congr rfl (fun j _ => by
        rw [q86_zeroExtend_apply, q86_zeroExtend_apply])

/-- The Hamming distance between the Boolean sign assignments `σ` and `τ`. -/
def q86Ham (m : ℕ) (σ τ : Fin (2 ^ m) → Bool) : ℕ :=
  (Finset.univ.filter fun j : Fin (2 ^ m) => σ j ≠ τ j).card

/-- The complex number `2` has norm two. -/
theorem q86_norm_two : ‖(2 : ℂ)‖ = 2 := by
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from rfl, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num)]

/-- Different Boolean labels give signs whose complex distance is two. -/
theorem q86_sign_sub_norm {N : ℕ} (σ τ : Fin N → Bool) (j : Fin N)
    (hne : σ j ≠ τ j) : ‖(q86Sign σ j - q86Sign τ j : ℂ)‖ = 2 := by
  by_cases hs : σ j = true <;> by_cases ht : τ j = true
  · simp [hs, ht] at hne
  · have h1 : (q86Sign σ j - q86Sign τ j : ℂ) = 2 := by
      simp only [q86Sign, hs, ht]
      norm_num
    rw [h1, q86_norm_two]
  · have h1 : (q86Sign σ j - q86Sign τ j : ℂ) = -2 := by
      simp only [q86Sign, hs, ht]
      norm_num
    rw [h1, norm_neg, q86_norm_two]
  · simp [hs, ht] at hne

/-- The squared distance between two signed uniform targets is `4 * q86Ham m σ τ / 2^m`. -/
theorem q86_target_sub_sq (m : ℕ) (σ τ : Fin (2 ^ m) → Bool) :
    ∑ j : Fin (2 ^ m), ‖q86Target m σ j - q86Target m τ j‖ ^ 2
      = (4 : ℝ) * q86Ham m σ τ * ((2 : ℝ) ^ m)⁻¹ := by
  have hscale : ∀ j : Fin (2 ^ m),
      q86Target m σ j - q86Target m τ j
        = (q86Sign σ j - q86Sign τ j) * ((Real.sqrt 2 : ℂ)⁻¹) ^ m := by
    intro j
    simp only [q86Target]
    ring
  have hnormsq : ‖((Real.sqrt 2 : ℂ)⁻¹) ^ m‖ ^ 2 = ((2 : ℝ) ^ m)⁻¹ := by
    have h1 : ‖((Real.sqrt 2 : ℂ)⁻¹) ^ m‖ = ((Real.sqrt 2 : ℝ)⁻¹) ^ m := by
      rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [h1]
    calc (((Real.sqrt 2 : ℝ)⁻¹) ^ m) ^ 2 = (((Real.sqrt 2 : ℝ)⁻¹) ^ 2) ^ m := by
          rw [← pow_mul, mul_comm, pow_mul]
        _ = ((2 : ℝ)⁻¹) ^ m := by
          rw [pow_two, ← mul_inv, ← pow_two, Real.sq_sqrt (by norm_num)]
        _ = ((2 : ℝ) ^ m)⁻¹ := by rw [inv_pow]
  have hterm : ∀ j : Fin (2 ^ m),
      ‖q86Target m σ j - q86Target m τ j‖ ^ 2
        = if σ j = τ j then (0 : ℝ) else (4 : ℝ) * ((2 : ℝ) ^ m)⁻¹ := by
    intro j
    rw [hscale j]
    by_cases h : σ j = τ j
    · rw [if_pos h]
      have hz : (q86Sign σ j - q86Sign τ j : ℂ) = 0 := by
        have heq : q86Sign σ j = q86Sign τ j := by simp [q86Sign, h]
        rw [heq, sub_self]
      rw [hz, zero_mul, norm_zero, zero_pow (by norm_num)]
    · rw [if_neg h]
      have hsn : ‖(q86Sign σ j - q86Sign τ j : ℂ)‖ = 2 := q86_sign_sub_norm σ τ j h
      rw [norm_mul, hsn, mul_pow, hnormsq]
      ring
  have hsum : (∑ j : Fin (2 ^ m), ‖q86Target m σ j - q86Target m τ j‖ ^ 2)
      = ∑ j : Fin (2 ^ m), if σ j = τ j then (0 : ℝ) else (4 : ℝ) * ((2 : ℝ) ^ m)⁻¹ :=
    Finset.sum_congr rfl (fun j _ => hterm j)
  rw [hsum]
  have hsplit : (∑ j : Fin (2 ^ m), if σ j = τ j then (0 : ℝ) else (4 : ℝ) * ((2 : ℝ) ^ m)⁻¹)
      = ∑ j ∈ Finset.univ.filter fun j : Fin (2 ^ m) => σ j ≠ τ j,
        ((4 : ℝ) * ((2 : ℝ) ^ m)⁻¹) := by
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, zero_add]
  rw [hsplit, Finset.sum_const, nsmul_eq_mul, q86Ham]
  ring

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
