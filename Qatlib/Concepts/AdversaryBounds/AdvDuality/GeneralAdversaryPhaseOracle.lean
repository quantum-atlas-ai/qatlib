/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryDefs
import Mathlib.Algebra.Order.Floor.Semiring
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitCompile
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedRelabel
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedPairedExecution
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.DensityPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitMixed
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Concepts.Execution.CircuitCompile.InstrumentCircuitTransport
import Qatlib.Concepts.AdversaryBounds.AdvDuality.VariableKrausStatistics
import Qatlib.Concepts.AdversaryBounds.AdvDuality.InstrumentMachinePrefix

/-!
# Adversary progress for phase-oracle queries

Analyzes how a finite-alphabet phase oracle changes the adversary progress functional. The
coordinate slices `phaseSlice` have total squared norm one for normalized input families, and
each query changes progress by at most twice `maxFilterNorm input Gamma`.

The resulting bounds accumulate over unitary query circuits and combine with successful POVM
readout to yield general and binary-output adversary lower bounds. These use the negative-weight
adversary method of [HoyerLeeSpalek2007].

## Main statements

* `phase_progress_step`: progress change for one phase query.
* `phase_progress_run`: progress change bounded by query count times the one-query bound.
* `phase_povm_query_lower_bound`: error-dependent lower bound for general output types.
* `phase_povm_binary_query_lower_bound`: sharper error factor for two outputs.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal ComplexConjugate
open Qatlib
open Qatlib

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
set_option linter.unusedVariables false in
noncomputable section

/-- The magnitude of `Inner u (A *ᵥ v)` is at most the operator norm of `A` times the Euclidean
norms of `u` and `v`. -/
theorem inner_mulVec_bound {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℂ) (u : QState I) (v : QState J) :
    ‖Inner u (A *ᵥ v)‖ ≤ ‖A‖ * ‖toEuclidean_fromVec u‖ * ‖toEuclidean_fromVec v‖ := by
  rw [← inner_euclidean_fromVec]
  calc _ ≤ ‖toEuclidean_fromVec u‖ * ‖toEuclidean_fromVec (A *ᵥ v)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖toEuclidean_fromVec u‖ * (‖A‖ * ‖toEuclidean_fromVec v‖) :=
      mul_le_mul_of_nonneg_left (l2_norm_mulVec_fromVec_le A v) (norm_nonneg _)
    _ = _ := by ring
end
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false
variable {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
variable {n q : ℕ} [NeZero q]
noncomputable section

/-- The complex phase `exp (2πi x p / q)` associated with an alphabet symbol and a
phase-register index. -/
noncomputable def phaseFactor (x p : Fin q) : ℂ :=
  Complex.exp ((2 * Real.pi * Complex.I) * (((x.val : ℝ) * ((p.val : ℝ) / (q : ℝ)))))
end
noncomputable section

/-- Multiplies each joint input-register amplitude by the phase determined by its input symbol
at coordinate `i`. -/
noncomputable def phaseAction (input : X → Fin n → Fin q) (i : Fin n)
    (v : QState (X × (Fin q × W))) : QState (X × (Fin q × W)) :=
  fun p => phaseFactor (input p.1 i) p.2.1 * v p
end
noncomputable section

/-- The weighted joint state obtained by fixing the query-coordinate register to `i`. -/
noncomputable def phaseSlice (weight : QState X) (states : X → QState ((Fin n × Fin q) × W))
    (i : Fin n) : QState (X × (Fin q × W)) :=
  fun p => weight p.1 * states p.1 ((i, p.2.1), p.2.2)
end
noncomputable section

/-- Every alphabet phase factor has complex norm one. -/
theorem phaseFactor_norm (x p : Fin q) : ‖phaseFactor x p‖ = 1 := by
  unfold phaseFactor
  rw [Complex.norm_exp]
  have hre : ((2 * Real.pi * Complex.I) * (((x.val : ℝ) * ((p.val : ℝ) / (q : ℝ))))).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [hre]
  simp
end
noncomputable section

/-- Equal alphabet symbols give equal phase factors at every phase-register index. -/
theorem phaseFactor_eq (x y p : Fin q) (h : x = y) : phaseFactor x p = phaseFactor y p := by
  subst h
  rfl
end
noncomputable section

/-- For two inputs agreeing at coordinate `i`, applying the coordinate phase action preserves
the inner product of their state slices. -/
theorem phaseAction_inner (input : X → Fin n → Fin q) (i : Fin n)
    (v : QState (X × (Fin q × W))) (x y : X) (hxy : input x i = input y i) :
    Inner (fun h => phaseAction input i v (x, h)) (fun h => phaseAction input i v (y, h)) =
      Inner (fun h => v (x, h)) (fun h => v (y, h)) := by
  simp only [inner_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro w _
  simp only [phaseAction]
  have hphase : phaseFactor (input x i) p = phaseFactor (input y i) p :=
    phaseFactor_eq _ _ _ hxy
  rw [hphase]
  simp only [map_mul]
  have hmod : (starRingEnd ℂ) (phaseFactor (input y i) p) * phaseFactor (input y i) p = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, phaseFactor_norm]
    simp
  calc ((starRingEnd ℂ) (phaseFactor (input y i) p) * (starRingEnd ℂ) (v (x, p, w))) *
        (phaseFactor (input y i) p * v (y, p, w)) =
      (starRingEnd ℂ) (v (x, p, w)) *
        ((starRingEnd ℂ) (phaseFactor (input y i) p) * phaseFactor (input y i) p) *
        v (y, p, w) := by ring
    _ = (starRingEnd ℂ) (v (x, p, w)) * v (y, p, w) := by rw [hmod]; ring
end
noncomputable section

/-- The coordinate phase action preserves the squared Euclidean norm. -/
theorem phaseAction_norm (input : X → Fin n → Fin q) (i : Fin n)
    (v : QState (X × (Fin q × W))) :
    ‖toEuclidean_fromVec (phaseAction input i v)‖ ^ 2 = ‖toEuclidean_fromVec v‖ ^ 2 := by
  simp only [norm_toEuclidean_fromVec_sq, Fintype.sum_prod_type, phaseAction]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro w _
  rw [norm_mul, mul_pow, phaseFactor_norm, one_pow, one_mul]
end

/-- Expands the quadratic form of `Gamma` tensored with the identity as a sum of matrix entries
times inner products of state fibers. -/
private theorem phaseFormExpand {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] (Gamma : Matrix X X ℂ) (v : QState (X × H)) :
    Inner v (TensorGate Gamma (1 : Matrix H H ℂ) *ᵥ v) =
      ∑ x, ∑ y, Gamma x y * Inner (fun h => v (x, h)) (fun h => v (y, h)) := by
  simp only [inner_apply, Fintype.sum_prod_type, advTensor_mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  exact Finset.sum_congr rfl fun h _ => by ring

/-- The phase-induced change in the quadratic form of `Gamma` equals the change for its
coordinate-filtered matrix. -/
private theorem phase_filter_difference (input : X → Fin n → Fin q) (i : Fin n)
    (Gamma : Matrix X X ℂ) (v : QState (X × (Fin q × W))) :
    Inner (phaseAction input i v) (TensorGate Gamma 1 *ᵥ phaseAction input i v) -
      Inner v (TensorGate Gamma 1 *ᵥ v) =
      Inner (phaseAction input i v) (TensorGate (genAdvFilter input Gamma i) 1 *ᵥ phaseAction input i v) -
        Inner v (TensorGate (genAdvFilter input Gamma i) 1 *ᵥ v) := by
  simp only [phaseFormExpand, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : input x i = input y i
  · have hinner := phaseAction_inner input i v x y hxy
    rw [hinner]
    simp [genAdvFilter, hxy]
  · simp [genAdvFilter, Matrix.hadamard_apply, hxy]

/-- The absolute real change in a coordinate phase quadratic form is at most twice the
coordinate filter norm times the state's squared Euclidean norm. -/
private theorem phase_progress_bound (input : X → Fin n → Fin q) (i : Fin n)
    (Gamma : Matrix X X ℂ) (v : QState (X × (Fin q × W))) :
    |(Inner (phaseAction input i v) (TensorGate Gamma 1 *ᵥ phaseAction input i v) -
      Inner v (TensorGate Gamma 1 *ᵥ v)).re| ≤
      2 * ‖genAdvFilter input Gamma i‖ * ‖toEuclidean_fromVec v‖ ^ 2 := by
  let G : Matrix X X ℂ := genAdvFilter input Gamma i
  let A : Matrix (X × (Fin q × W)) (X × (Fin q × W)) ℂ := TensorGate G 1
  have hA : ‖A‖ ≤ ‖G‖ := by
    dsimp [A]
    rw [l2_norm_tensorGate]
    exact (mul_le_mul_of_nonneg_left l2_norm_one_le (norm_nonneg _)).trans_eq (mul_one _)
  rw [phase_filter_difference input i Gamma v]
  calc |(Inner (phaseAction input i v) (A *ᵥ phaseAction input i v) -
      Inner v (A *ᵥ v)).re| ≤
      ‖Inner (phaseAction input i v) (A *ᵥ phaseAction input i v) - Inner v (A *ᵥ v)‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ‖Inner (phaseAction input i v) (A *ᵥ phaseAction input i v)‖ +
        ‖Inner v (A *ᵥ v)‖ := norm_sub_le _ _
    _ ≤ ‖A‖ * ‖toEuclidean_fromVec (phaseAction input i v)‖ *
          ‖toEuclidean_fromVec (phaseAction input i v)‖ +
        ‖A‖ * ‖toEuclidean_fromVec v‖ * ‖toEuclidean_fromVec v‖ := by
          gcongr
          exact inner_mulVec_bound _ _ _
          exact inner_mulVec_bound _ _ _
    _ = 2 * ‖A‖ * ‖toEuclidean_fromVec v‖ ^ 2 := by
          have hnorm : ‖toEuclidean_fromVec (phaseAction input i v)‖ =
              ‖toEuclidean_fromVec v‖ :=
            (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (phaseAction_norm input i v)
          rw [hnorm]
          ring
    _ ≤ 2 * ‖G‖ * ‖toEuclidean_fromVec v‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hA (by norm_num)) (sq_nonneg _)
noncomputable section

/-- Applying the phase oracle multiplies each amplitude by the exponential phase determined by
its query coordinate and phase-register value. -/
theorem phaseOracle_mulVec {W : Type} [Fintype W] [DecidableEq W] {n q : ℕ} [NeZero q]
    (input : Fin n → Fin q) (v : QState ((Fin n × Fin q) × W))
    (k : (Fin n × Fin q) × W) :
    (phaseOracle (W := W) input *ᵥ v) k =
      Complex.exp ((2 * Real.pi * Complex.I) *
        (((input k.1.1).val : ℝ) * ((k.1.2.val : ℝ) / (q : ℝ)))) * v k := by
  simp only [Matrix.mulVec, dotProduct, phaseOracle]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    by_cases hkb : k = b
    · rw [hkb] at hb
      exact (hb rfl).elim
    · simp [hkb]
  · simp
end
noncomputable section

/-- Taking a coordinate slice after a phase query equals applying the coordinate phase action to
the original slice. -/
theorem phaseSlice_query {W : Type} [Fintype W] [DecidableEq W] {n q : ℕ} [NeZero q]
    (input : X → Fin n → Fin q) (weight : QState X)
    (states : X → QState ((Fin n × Fin q) × W)) (i : Fin n) :
    phaseSlice weight (fun x => phaseOracle (W := W) (input x) *ᵥ states x) i =
      phaseAction input i (phaseSlice weight states i) := by
  ext p
  simp only [phaseSlice, phaseAction]
  rw [phaseOracle_mulVec (input p.1) (states p.1) ((i, p.2.1), p.2.2)]
  simp [phaseFactor]
  ring
end
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false
variable {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
variable {n q : ℕ} [NeZero q]
set_option maxHeartbeats 0 in

/-- Adversary progress is the real part of the sum of the coordinate-slice quadratic forms. -/
private theorem phase_progress_slices {W : Type} [Fintype X] [DecidableEq X]
    [Fintype W] [DecidableEq W] {n q : ℕ} (Gamma : Matrix X X ℂ) (weight : QState X)
    (states : X → QState ((Fin n × Fin q) × W)) :
    advProgress Gamma weight states =
      (∑ i, Inner (phaseSlice weight states i)
        (TensorGate Gamma (1 : Matrix (Fin q × W) (Fin q × W) ℂ) *ᵥ phaseSlice weight states i)).re := by
  unfold advProgress
  congr 1
  simp_rw [phaseFormExpand]
  simp only [inner_apply, Fintype.sum_prod_type, phaseSlice, map_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro p _
  exact Finset.sum_congr rfl fun w _ => by simp only [RCLike.star_def]; ring

/-- For normalized weight and state families, the squared Euclidean norms of all coordinate
slices sum to one. -/
private theorem phaseSlice_energy {W : Type} [Fintype X] [DecidableEq X] [Fintype W]
    [DecidableEq W] {n q : ℕ} (weight : QState X) (states : X → QState ((Fin n × Fin q) × W))
    (hw : Normalized weight) (hs : ∀ x, Normalized (states x)) :
    ∑ i, ‖toEuclidean_fromVec (phaseSlice weight states i)‖ ^ 2 = 1 := by
  simp only [norm_toEuclidean_fromVec_sq, Fintype.sum_prod_type, phaseSlice, norm_mul,
    mul_pow, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have hsn : ∀ x, (∑ i, ∑ p, ∑ w, ‖states x ((i, p), w)‖ ^ 2) = 1 := by
    intro x
    simpa only [Normalized, Fintype.sum_prod_type] using! hs x
  simp only [hsn, mul_one]
  exact hw
noncomputable section

/-- For normalized weight and state families, one phase query changes adversary progress by at
most twice the maximum coordinate filter norm. -/
theorem phase_progress_step {W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
    {n q : ℕ} [NeZero q] (input : X → Fin n → Fin q) (Gamma : Matrix X X ℂ) (weight : QState X)
    (states : X → QState ((Fin n × Fin q) × W)) (hw : Normalized weight)
    (hs : ∀ x, Normalized (states x)) :
    |advProgress Gamma weight (fun x => phaseOracle (W := W) (input x) *ᵥ states x) -
      advProgress Gamma weight states| ≤ 2 * maxFilterNorm input Gamma := by
  rw [phase_progress_slices, phase_progress_slices, ← Complex.sub_re, ← Finset.sum_sub_distrib]
  simp only [phaseSlice_query, Complex.re_sum]
  calc _ ≤ ∑ i, |(Inner (phaseAction input i (phaseSlice weight states i))
        (TensorGate Gamma 1 *ᵥ phaseAction input i (phaseSlice weight states i)) -
          Inner (phaseSlice weight states i) (TensorGate Gamma 1 *ᵥ phaseSlice weight states i)).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 2 * ‖genAdvFilter input Gamma i‖ *
          ‖toEuclidean_fromVec (phaseSlice weight states i)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => phase_progress_bound input i Gamma (phaseSlice weight states i)
    _ ≤ ∑ i, 2 * maxFilterNorm input Gamma *
          ‖toEuclidean_fromVec (phaseSlice weight states i)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (genAdvFilter_le_maxFilterNorm input Gamma i) (by norm_num)) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, phaseSlice_energy weight states hw hs, mul_one]
end

/-- The product of a complex number's conjugate with itself is its squared norm, viewed as a
complex number. -/
private theorem star_mul_self_sq (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  have h3 : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have h4 : star z = conj z := rfl
  rw [h4]
  exact h3

/-- A complex number of norm one has conjugate product equal to one. -/
private theorem star_mul_one (z : ℂ) (hz : ‖z‖ = 1) : star z * z = 1 := by
  rw [star_mul_self_sq, hz]
  norm_num
noncomputable section

/-- The finite-alphabet phase oracle is unitary. -/
theorem phaseOracle_unitary {n q : ℕ} [NeZero q] {W : Type} [Fintype W] [DecidableEq W]
    (input : Fin n → Fin q) :
    phaseOracle (W := W) input ∈ Matrix.unitaryGroup ((Fin n × Fin q) × W) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext k k'
  by_cases hkk : k = k'
  · subst hkk
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, phaseOracle, Matrix.of_apply]
    rw [Finset.sum_eq_single k]
    · have hz : ‖phaseFactor (input k.1.1) k.1.2‖ = 1 := phaseFactor_norm _ _
      simp only [Matrix.one_apply]
      exact star_mul_one _ hz
    · intro b _ hb
      simp [hb]
    · simp
  · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, phaseOracle, Matrix.of_apply, hkk,
      Ne.symm hkk]
end
noncomputable section

/-- Establishes that one phase query changes adversary progress by at most twice the maximum
filter norm for normalized weight and state families. -/
theorem stageA_general_adversary_clause16_phase_step
    {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
    {n q : ℕ} [NeZero q] (input : X → Fin n → Fin q) (Gamma : Matrix X X ℂ) (weight : QState X)
    (states : X → QState ((Fin n × Fin q) × W)) (hw : Normalized weight)
    (hs : ∀ x, Normalized (states x)) :
    |advProgress Gamma weight (fun x => phaseOracle (W := W) (input x) *ᵥ states x) -
      advProgress Gamma weight states| ≤ 2 * maxFilterNorm input Gamma :=
  phase_progress_step input Gamma weight states hw hs
end
noncomputable section

/-- If every oracle call changes progress by at most `B` on normalized state families, a unitary
circuit changes progress by at most `QueryCount C * B`. -/
theorem progress_run_of_step {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] (oracle : X → Matrix H H ℂ)
    (hO : ∀ x, oracle x ∈ Matrix.unitaryGroup H ℂ)
    (G : Matrix X X ℂ) (weight : QState X) (B : ℝ)
    (step : ∀ s : X → QState H, (∀ x, Normalized (s x)) →
      |advProgress G weight (fun x => oracle x *ᵥ s x) - advProgress G weight s| ≤ B)
    (C : Circuit H) (hC : IsUnitaryCircuit C) (s : X → QState H)
    (hs : ∀ x, Normalized (s x)) :
    |advProgress G weight (fun x => Run (oracle x) C (s x)) - advProgress G weight s| ≤
      (QueryCount C : ℝ) * B := by
  induction C generalizing s with
  | nil => simp only [Run, QueryCount, sub_self, abs_zero, Nat.cast_zero, zero_mul, le_refl]
  | cons a C ih =>
    cases a with
    | gate U =>
      obtain ⟨hU, ht⟩ := (isUnitaryCircuit_gate U C).mp hC
      have hh := ih ht (fun x => U *ᵥ s x) (fun x => normalized_applyGate hU (hs x))
      simpa only [Run, QueryCount,
        negative_adversary_same_gate_progress_invariant X H G weight s U hU] using! hh
    | query =>
      have ht := (isUnitaryCircuit_query C).mp hC
      let next := fun x => oracle x *ᵥ s x
      have hh := ih ht next (fun x => normalized_applyGate (hO x) (hs x))
      have hstep := step s hs
      calc
        _ ≤ |advProgress G weight (fun x => Run (oracle x) C (next x)) - advProgress G weight next| +
            |advProgress G weight next - advProgress G weight s| := abs_sub_le _ _ _
        _ ≤ (QueryCount C : ℝ) * B + B := add_le_add hh hstep
        _ = _ := by simp only [QueryCount, Nat.cast_add, Nat.cast_one]; ring
end
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false
variable {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
variable {n q : ℕ} [NeZero q]
set_option maxHeartbeats 0 in
noncomputable section

/-- For normalized weights and initial states, a unitary phase-query circuit changes adversary
progress by at most twice its query count times the maximum filter norm. -/
theorem phase_progress_run {X W : Type} [Fintype X] [DecidableEq X]
    [Fintype W] [DecidableEq W] {n q : ℕ} [NeZero q]
    (input : X → Fin n → Fin q) (G : Matrix X X ℂ)
    (weight : QState X) (C : Circuit ((Fin n × Fin q) × W))
    (s : X → QState ((Fin n × Fin q) × W)) (hw : Normalized weight)
    (hC : IsUnitaryCircuit C) (hs : ∀ x, Normalized (s x)) :
    |advProgress G weight (fun x => Run (phaseOracle (W := W) (input x)) C (s x)) -
      advProgress G weight s| ≤ 2 * (QueryCount C) * maxFilterNorm input G := by
  have h := progress_run_of_step (fun x => phaseOracle (W := W) (input x))
    (fun x => phaseOracle_unitary _) G weight (2 * maxFilterNorm input G)
    (fun s hs => phase_progress_step input G weight s hw hs) C hC s hs
  calc
    _ ≤ (QueryCount C : ℝ) * (2 * maxFilterNorm input G) := h
    _ = _ := by ring
end
noncomputable section

/-- Establishes the circuit progress bound for finite-alphabet phase oracles. -/
theorem phaseOracle_run_progress {X W : Type} [Fintype X] [DecidableEq X]
    [Fintype W] {n q : ℕ} [NeZero q]
    (input : X → Fin n → Fin q) (G : Matrix X X ℂ) :
    PhaseOracleProgressRunBound (W := W) input G := by
  intro weight C s hw hC hs
  exact phase_progress_run input G weight C s hw hC hs
end
noncomputable section

/-- Establishes the final adversary progress estimate for successful POVM readout encoded by
`PovmFinalProgressBound`. -/
theorem povm_final_progress {X H Y : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Fintype Y] [DecidableEq Y]
    (G : Matrix X X ℂ) (f : X → Y) (out : Y → Matrix H H ℂ) (eps : ℝ) :
    Qatlib.Concepts.AdversaryBounds.AdvDuality.PovmFinalProgressBound G f out eps := by
  intro weight states hG hw hs hz he0 he1 hout hsuccess
  have hinner (x y : X) :
      Inner (povmLiftMatrix out *ᵥ states x) (povmLiftMatrix out *ᵥ states y) =
        Inner (states x) (states y) := povmLift_inner out hout _ _
  have hprog : advProgress G weight (fun x => povmLiftMatrix out *ᵥ states x) =
      advProgress G weight states := by
    unfold advProgress
    simp_rw [hinner]
  rw [← hprog]
  apply multioutput_adversary_actual_final_progress X (Y × H) Y G weight
    (fun x => povmLiftMatrix out *ᵥ states x) f Prod.fst eps hG hw
    (fun x => povmLift_normalized out hout _ (hs x)) hz he0 he1
  intro x
  have hb := povmLift_born out hout (states x) (f x)
  exact hb.symm ▸ hsuccess x
end
noncomputable section

/-- A bounded-error phase-query circuit with POVM readout bounds `(1 - 2 * Real.sqrt (eps * (1 -
eps)) - 2 * eps) * ‖G‖` by twice its query count times the maximum filter norm for a
Hermitian witness supported on different outputs. -/
theorem phase_povm_query_lower_bound
    (q n : ℕ) [NeZero q] (X W Y : Type) [Fintype X] [DecidableEq X] [Fintype W] [Fintype Y]
    (input : X → Fin n → Fin q) (f : X → Y)
    (G : Matrix X X ℂ) (C : Circuit ((Fin n × Fin q) × W))
    (psi : QState ((Fin n × Fin q) × W))
    (out : Y → Matrix ((Fin n × Fin q) × W) ((Fin n × Fin q) × W) ℂ) (eps : ℝ)
    (hG : G.IsHermitian) (hz : ∀ x y, f x = f y → G x y = 0)
    (hrun : IsBoundedErrorRun input f C psi out eps) :
    (1 - 2 * Real.sqrt (eps * (1 - eps)) - 2 * eps) * ‖G‖ ≤
      2 * (QueryCount C) * maxFilterNorm input G := by
  classical
  exact clause16_engine_of_obligations q n X W Y input f G C psi out eps hG hz hrun
    (phaseOracle_run_progress input G) (povm_final_progress G f out eps)
    (fun x => hrun.1.normalized_run (phaseOracle_unitary (input x)) hrun.2.1)
end
noncomputable section

/-- A uniform inequality `a * ‖G‖ ≤ 2 * T * maxFilterNorm input G` for all supported Hermitian
witnesses implies `ENNReal.ofReal (a / 2) * advPmValue input f ≤ T`. -/
theorem adversary_value_of_multiplicative_bound
    {X Y : Type} [Fintype X] [DecidableEq X] {n q : ℕ} [NeZero q]
    (input : X → Fin n → Fin q) (f : X → Y) (a : ℝ) (T : ℕ)
    (hall : ∀ G : Matrix X X ℂ, G.IsHermitian → (∀ x y, f x = f y → G x y = 0) →
      a * ‖G‖ ≤ 2 * T * maxFilterNorm input G) :
    ENNReal.ofReal (a / 2) * advPmValue input f ≤ (T : ℝ≥0∞) := by
  by_cases ha : 0 < a
  · unfold advPmValue
    rw [ENNReal.mul_iSup]
    apply iSup_le
    intro G
    have hnorm : 0 < ‖G.val‖ := norm_pos_iff.mpr G.property.2.2
    have h := hall G.val G.property.1 G.property.2.1
    have hm : 0 < maxFilterNorm input G.val := by
      by_contra hh
      have hz := le_antisymm (not_lt.mp hh) (maxFilterNorm_nonneg input G.val)
      rw [hz, mul_zero] at h
      exact (not_le_of_gt (mul_pos ha hnorm)) h
    have hr : (a / 2) * (‖G.val‖ / maxFilterNorm input G.val) ≤ T := by
      apply (mul_le_mul_iff_right₀ (show 0 < 2 * maxFilterNorm input G.val by positivity)).mp
      calc
        _ = a * ‖G.val‖ := by field_simp
        _ ≤ 2 * (T : ℝ) * maxFilterNorm input G.val := h
        _ = _ := by ring
    rw [advPmWitnessValue, ← ENNReal.ofReal_div_of_pos hm,
        ← ENNReal.ofReal_mul (le_of_lt (div_pos ha (by norm_num)))]
    exact (ENNReal.ofReal_le_ofReal hr).trans_eq (by simp)
  · rw [ENNReal.ofReal_eq_zero.mpr (div_nonpos_of_nonpos_of_nonneg (not_lt.mp ha) (by norm_num)), zero_mul]
    exact bot_le
end
noncomputable section

/-- For a two-output POVM with error at most `eps ∈ [0, 1/2]`, normalized weights and states,
and a supported Hermitian witness, final absolute progress is at most `2 * Real.sqrt (eps *
(1 - eps)) * ‖G‖`. -/
theorem povm_final_progress_binary {X H Y : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Fintype Y] [DecidableEq Y]
    (G : Matrix X X ℂ) (f : X → Y) (out : Y → Matrix H H ℂ) (eps : ℝ)
    (e : Y ≃ Bool) (weight : QState X) (states : X → QState H)
    (hG : G.IsHermitian) (hw : Normalized weight) (hs : ∀ x, Normalized (states x))
    (hz : ∀ x y, f x = f y → G x y = 0) (he0 : 0 ≤ eps) (he1 : eps ≤ 1 / 2)
    (hout : IsPovm out) (hsuccess : ∀ x, 1 - eps ≤ povmProb out (f x) (states x)) :
    |advProgress G weight states| ≤ (2 * Real.sqrt (eps * (1 - eps))) * ‖G‖ := by
  let st := fun x => povmLiftMatrix out *ᵥ states x
  let E : Finset (Y × H) := Finset.univ.filter (fun p => e p.1 = true)
  have hevent (x : X) : (if e (f x) then E else Eᶜ) = outcomeEvent Prod.fst (f x) := by
    ext p
    have heq : p.1 = f x ↔ e p.1 = e (f x) := e.injective.eq_iff.symm
    cases h : e (f x) <;> cases hp : e p.1 <;>
      simp [E, h, outcomeEvent, heq, hp]
  have hprog : advProgress G weight st = advProgress G weight states := by
    unfold advProgress
    simp only [st, povmLift_inner out hout]
  rw [← hprog]
  apply negative_adversary_boolean_actual_output_progress X (Y × H) G weight st
    (fun x => e (f x)) E eps hG hw (fun x y h => hz x y (e.injective h)) he0 he1
    (fun x => povmLift_normalized out hout _ (hs x))
  intro x
  rw [hevent]
  exact (povmLift_born out hout (states x) (f x)).symm ▸ hsuccess x
end
noncomputable section

/-- For a bounded-error phase-query circuit with two outputs, `(1 - 2 * Real.sqrt (eps * (1 -
eps))) * ‖G‖` is bounded by twice its query count times the maximum filter norm, giving the
binary adversary bound of [HoyerLeeSpalek2007]. -/
theorem phase_povm_binary_query_lower_bound
    (q n : ℕ) [NeZero q] (X W Y : Type) [Fintype X] [DecidableEq X] [Fintype W] [Fintype Y]
    (input : X → Fin n → Fin q) (f : X → Y)
    (G : Matrix X X ℂ) (C : Circuit ((Fin n × Fin q) × W))
    (psi : QState ((Fin n × Fin q) × W))
    (out : Y → Matrix ((Fin n × Fin q) × W) ((Fin n × Fin q) × W) ℂ) (eps : ℝ)
    (hG : G.IsHermitian) (hz : ∀ x y, f x = f y → G x y = 0)
    (hrun : IsBoundedErrorRun input f C psi out eps) (hc : Fintype.card Y = 2) :
    (1 - 2 * Real.sqrt (eps * (1 - eps))) * ‖G‖ ≤
      2 * (QueryCount C) * maxFilterNorm input G := by
  classical
  by_cases hem : IsEmpty X
  · have hg0 : ‖G‖ = 0 := norm_eq_zero_of_isEmpty G
    rw [hg0, mul_zero]
    exact mul_nonneg (by positivity) (maxFilterNorm_nonneg input G)
  · haveI : Nonempty X := not_isEmpty_iff.mp hem
    let e : Y ≃ Bool := Fintype.equivOfCardEq (by simpa using! hc)
    obtain ⟨weight, lam, hw, hlam, _, hstart⟩ :=
      negative_adversary_extreme_eigenvector_and_start X _ G psi hG hrun.2.1
    have hrunProg := phaseOracle_run_progress input G weight C (fun _ => psi) hw hrun.1
      (fun _ => hrun.2.1)
    rw [hstart] at hrunProg
    have hfin := povm_final_progress_binary G f out eps e weight
      (fun x => Run (phaseOracle (W := W) (input x)) C psi) hG hw
      (fun x => hrun.1.normalized_run (phaseOracle_unitary (input x)) hrun.2.1)
      hz hrun.2.2.2.1 hrun.2.2.2.2.1 hrun.2.2.1 hrun.2.2.2.2.2
    have htri := abs_sub_le lam
      (advProgress G weight (fun x => Run (phaseOracle (W := W) (input x)) C psi)) 0
    rw [sub_zero, sub_zero, abs_sub_comm lam, hlam] at htri
    nlinarith
end
noncomputable section

/-- Establishes the general phase-oracle adversary proposition `clause16Prop`. -/
theorem stageA_general_adversary_clause16_full_endpoint_v2 : clause16Prop := by
  intro q n _ X W Y _ _ _ _ input f G C psi out eps hG hz hrun
  refine ⟨phase_povm_query_lower_bound q n X W Y input f G C psi out eps hG hz hrun, ?_, ?_⟩
  · exact adversary_value_of_multiplicative_bound input f
      (1 - 2 * Real.sqrt (eps * (1 - eps)) - 2 * eps) (QueryCount C)
      (fun G hG hz => phase_povm_query_lower_bound q n X W Y input f G C psi out eps hG hz hrun)
  · intro hc
    constructor
    · exact phase_povm_binary_query_lower_bound q n X W Y input f G C psi out eps hG hz hrun hc
    · exact adversary_value_of_multiplicative_bound input f
        (1 - 2 * Real.sqrt (eps * (1 - eps))) (QueryCount C)
        (fun G hG hz => phase_povm_binary_query_lower_bound q n X W Y input f G C psi out eps hG hz hrun hc)
end
end Qatlib.Concepts.AdversaryBounds.AdvDuality
