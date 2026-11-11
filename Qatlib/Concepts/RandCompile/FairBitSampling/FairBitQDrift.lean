/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.FairBitSampling.CappedWeightedCoinPath
import Qatlib.Concepts.RandCompile.ReferenceModel.QDriftReferenceSimulation

/-!
# Fair-bit qDRIFT circuits and reference errors

This module constructs qDRIFT circuits from capped fair-bit weighted samples and defines their
averaged output with an arbitrary ancilla. It connects that average to a power of the sampled
mixture channel and compares the capped sampler with the ideal importance law, in the randomized
compilation framework of [Campbell2019].

The final error bound adds a quadratic-in-time analytic term to the accumulated capped-sampling
error. Separate path ledgers record unitarity, gates, oracle queries, fair bits, and
comparisons.

## Main statements

* `fair_bit_qdrift_actual_fresh_channel_bridge`: identifies the averaged circuit output with the
  iterated mixture.
* `fair_bit_qdrift_actual_quantum_and_classical_path_counts`: bounds each sampled circuit and
  its classical sampling costs.
* `fair_bit_qdrift_derived_sampling_and_analytic_error`: combines analytic and sampling
  trace-norm errors.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.RandCompile.ReferenceModel

open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.RandCompile.FairBitSampling
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The circuit of `n` Hamiltonian evolution gates selected by capped fair-bit weighted samples,
with an empty circuit when the total weight is zero. -/
noncomputable def fairQdriftCircuit {L D : ℕ} (w : Fin L → ℕ) (j0 : Fin L)
    (n R : ℕ) (K : Fin L → Operator D) (t : ℝ)
    (ω : Fin n → Fin R → Reg (Nat.clog 2 (weightTotal w))) : Circuit (Fin D) :=
  if weightTotal w = 0 then [] else
    mixturePathCircuit (fun j => HamiltonianEvolution (K j) (t*(weightTotal w : ℝ)/(n : ℝ)))
      (fun k => (fairQdriftPick w j0 R (ω k)).1)

/-- The average ancillary output of independently sampled fair-bit qDRIFT paths, returning the
input unchanged at zero total weight. -/
noncomputable def fairQdriftReferenceOutput {L D : ℕ} (w : Fin L → ℕ) (j0 : Fin L)
    (n R : ℕ) (K : Fin L → Operator D) (t : ℝ) (r : ℕ)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ :=
  if weightTotal w = 0 then X else
    ∑ ω : Fin n → Fin R → Reg (Nat.clog 2 (weightTotal w)),
      ((independentSampleLaw (fun _ : Fin n =>
        fairQdriftUniform (Fin R → Reg (Nat.clog 2 (weightTotal w))))).prob ω : ℂ) •
      (TensorGate (mixturePathOperator
        (fun bits => HamiltonianEvolution (K (fairQdriftPick w j0 R bits).1)
          (t*(weightTotal w : ℝ)/(n : ℝ))) ω) (1 : Operator r) * X *
        (TensorGate (mixturePathOperator
          (fun bits => HamiltonianEvolution (K (fairQdriftPick w j0 R bits).1)
            (t*(weightTotal w : ℝ)/(n : ℝ))) ω) (1 : Operator r))ᴴ)

/-- Zero total weight gives an empty circuit, zero total sampled bit and comparison costs, and
reference output equal to the input. -/
theorem fairQdrift_zero_protocol {L D : ℕ} (w : Fin L → ℕ) (j0 : Fin L)
    (n R : ℕ) (K : Fin L → Operator D) (t : ℝ)
    (ω : Fin n → Fin R → Reg (Nat.clog 2 (weightTotal w))) (r : ℕ)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) (hW : weightTotal w = 0) :
    fairQdriftCircuit w j0 n R K t ω = [] ∧
      (∑ k, (fairQdriftPick w j0 R (ω k)).2.1) = 0 ∧
      (∑ k, (fairQdriftPick w j0 R (ω k)).2.2) = 0 ∧
      fairQdriftReferenceOutput w j0 n R K t r X = X := by
  simp [fairQdriftCircuit, fairQdriftPick, fairQdriftReferenceOutput, hW]

/-- Relabeling a finite mixture through a function equals using the pushforward distribution on
the target labels. -/
private theorem referenceMixture_pushforward {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] {D : ℕ} (d : FinDist A) (f : A → B)
    (U : B → Operator D) (r : ℕ) (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    referenceMixture d (fun a => U (f a)) r X =
      referenceMixture (fairQdriftPushforward d f) U r X := by
  rw [referenceMixture_apply, referenceMixture_apply]
  simp only [fairQdriftPushforward, Complex.ofReal_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [eq_comm]

/-- Every power of a relabeled reference mixture equals the corresponding power formed from the
pushforward distribution. -/
private theorem referenceMixturePower_pushforward {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] {D : ℕ} (d : FinDist A) (f : A → B)
    (U : B → Operator D) (r n : ℕ) (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    referenceMixturePower d (fun a => U (f a)) r n X =
      referenceMixturePower (fairQdriftPushforward d f) U r n X := by
  have he : referenceMixture d (fun a => U (f a)) r =
      referenceMixture (fairQdriftPushforward d f) U r := by
    funext Y
    exact referenceMixture_pushforward d f U r Y
  simp only [referenceMixturePower, he]

/-- For positive total weight, the averaged fair-bit circuit output equals the `n`th power of
the mixture with law `fairQdriftLaw` and evolution time `t * weightTotal w / n` per gate.
See [Campbell2019]. -/
theorem fair_bit_qdrift_actual_fresh_channel_bridge (L D n R r : ℕ)
    (w : Fin L → ℕ) (j0 : Fin L) (K : Fin L → Operator D) (t : ℝ)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) (hW : 0 < weightTotal w) :
    fairQdriftReferenceOutput w j0 n R K t r X =
      referenceMixturePower (fairQdriftLaw w j0 R)
        (fun j => HamiltonianEvolution (K j) (t*(weightTotal w : ℝ)/(n : ℝ))) r n X := by
  let d := fairQdriftUniform (Fin R → Reg (Nat.clog 2 (weightTotal w)))
  let f := fun bits => (fairQdriftPick w j0 R bits).1
  let U := fun j => HamiltonianEvolution (K j) (t*(weightTotal w : ℝ)/(n : ℝ))
  rw [fairQdriftReferenceOutput, if_neg (ne_of_gt hW)]
  exact (mixture_fresh_paths_reference_output d (fun bits => U (f bits)) n r X).symm.trans
    (referenceMixturePower_pushforward d f U r n X)

/-- With positive total weight and Hermitian terms, every fair-bit qDRIFT path is unitary, uses
zero oracle queries and `n` gates, and has bit and comparison counts bounded by `n *
Nat.clog 2 (weightTotal w) * R` and `n * L * R`. See [Campbell2019]. -/
theorem fair_bit_qdrift_actual_quantum_and_classical_path_counts (L D n R : ℕ)
    (w : Fin L → ℕ) (j0 : Fin L) (K : Fin L → Operator D) (t : ℝ)
    (ω : Fin n → Fin R → Reg (Nat.clog 2 (weightTotal w)))
    (hW : 0 < weightTotal w) (hK : ∀ j, (K j).IsHermitian) :
    IsUnitaryCircuit (fairQdriftCircuit w j0 n R K t ω) ∧
    QueryCount (fairQdriftCircuit w j0 n R K t ω) = 0 ∧
    GateCount (fairQdriftCircuit w j0 n R K t ω) = n ∧
    (∑ k, (fairQdriftPick w j0 R (ω k)).2.1) ≤ n*Nat.clog 2 (weightTotal w)*R ∧
    (∑ k, (fairQdriftPick w j0 R (ω k)).2.2) ≤ n*L*R := by
  have hc := mixture_path_circuit_semantics_cost
    (fun j => HamiltonianEvolution (K j) (t*(weightTotal w : ℝ)/(n : ℝ))) n
    (fun k => (fairQdriftPick w j0 R (ω k)).1) (0 : QState (Fin D))
  simp only [fairQdriftCircuit, if_neg (ne_of_gt hW)]
  refine ⟨hc.2.2.2 (fun j => hamiltonianEvolution_unitary (hK j) _), hc.2.1, hc.2.2.1, ?_, ?_⟩
  · calc _ ≤ ∑ _ : Fin n, Nat.clog 2 (weightTotal w)*R :=
        Finset.sum_le_sum (fun k _ => (fair_bit_qdrift_actual_coin_path_cost L R w j0 hW).1 (ω k) |>.1)
      _ = _ := by simp [Nat.mul_assoc]
  · calc _ ≤ ∑ _ : Fin n, L*R :=
        Finset.sum_le_sum (fun k _ => (fair_bit_qdrift_actual_coin_path_cost L R w j0 hW).1 (ω k) |>.2)
      _ = _ := by simp [Nat.mul_assoc]

/-- The ideal importance distribution assigning each label its weight divided by the positive
total weight. -/
noncomputable def fairQdriftImportanceLaw {L : ℕ} (w : Fin L → ℕ)
    (hW : 0 < weightTotal w) : FinDist (Fin L) where
  prob j := (w j : ℝ)/(weightTotal w : ℝ)
  nonneg _ := by positivity
  sum_one := by
    rw [← Finset.sum_div]
    have hs : (∑ j, (w j : ℝ)) = (weightTotal w : ℝ) := by simp [weightTotal]
    rw [hs, div_self (by positivity)]

/-- The importance-law qDRIFT Hamiltonian scaled by the total weight equals the weighted sum of
the Hamiltonian terms. -/
private theorem importance_hamiltonian {L D : ℕ} (w : Fin L → ℕ)
    (hW : 0 < weightTotal w) (K : Fin L → Operator D) :
    qdriftHamiltonian (fairQdriftImportanceLaw w hW) K (weightTotal w : ℝ) =
      ∑ j, (w j : ℂ) • K j := by
  unfold qdriftHamiltonian
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_smul, fairQdriftImportanceLaw, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [mul_div_cancel₀ _ (by exact_mod_cast (ne_of_gt hW))]

/-- For unitary branches and positive weight mass, replacing the ideal importance law by the
capped sampler changes one ancillary mixture output by at most `2 * (1/2)^R` times the input
trace norm. -/
private theorem fairQdrift_one_step_sampling_error {L D : ℕ} (w : Fin L → ℕ)
    (j0 : Fin L) (R : ℕ) (hW : 0 < weightTotal w) (U : Fin L → Operator D)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ) (r : ℕ)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Matrix.traceNorm (referenceMixture (fairQdriftLaw w j0 R) U r X -
      referenceMixture (fairQdriftImportanceLaw w hW) U r X) ≤
      2 * ((2 : ℝ)⁻¹)^R * Matrix.traceNorm X := by
  let q := 1 - (weightTotal w : ℝ)/(2^Nat.clog 2 (weightTotal w) : ℝ)
  let a := q^R
  let d := fairQdriftImportanceLaw w hW
  let A := TensorGate (U j0) (1 : Operator r) * X * (TensorGate (U j0) (1 : Operator r))ᴴ
  let B := referenceMixture d U r X
  have hq := fairQdriftReject_real w hW
  have ha : 0 ≤ a := pow_nonneg hq.2.1 R
  have hab : a ≤ ((2 : ℝ)⁻¹)^R := by
    exact pow_le_pow_left₀ hq.2.1 (by simpa using hq.2.2) R
  have hl (j : Fin L) : (fairQdriftLaw w j0 R).prob j =
      (1-a)*d.prob j + (if j=j0 then a else 0) := by
    rw [fair_bit_qdrift_actual_sampler_law L R w j0 hW j]
    dsimp [d, fairQdriftImportanceLaw, a, q]
    split_ifs <;> ring
  have hm : referenceMixture (fairQdriftLaw w j0 R) U r X =
      ((1-a : ℝ) : ℂ) • B + (a : ℂ) • A := by
    rw [referenceMixture_apply]
    simp_rw [hl, Complex.ofReal_add, Complex.ofReal_mul, add_smul, mul_smul]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum]
    congr 1
    simp [A]
  have hs : referenceMixture (fairQdriftLaw w j0 R) U r X - B = (a : ℂ) • (A-B) := by
    rw [hm, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul, smul_sub]
    abel
  rw [hs, Matrix.traceNorm_smul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
  have hA : Matrix.traceNorm A = Matrix.traceNorm X :=
      finite_reference_unitary_traceNorm _ r X (hU j0)
  have hB : Matrix.traceNorm B ≤ Matrix.traceNorm X :=
      finite_reference_mixture_contraction d U r X hU
  have ht : Matrix.traceNorm (A-B) ≤ 2*Matrix.traceNorm X := by
    calc
      Matrix.traceNorm (A-B) ≤ Matrix.traceNorm A + Matrix.traceNorm B := by
        simpa only [sub_eq_add_neg, Matrix.traceNorm_neg] using Matrix.traceNorm_add_le A (-B)
      _ ≤ _ := by rw [hA]; linarith
  calc a * Matrix.traceNorm (A-B) ≤ a*(2*Matrix.traceNorm X) := mul_le_mul_of_nonneg_left ht ha
    _ ≤ ((2 : ℝ)⁻¹)^R*(2*Matrix.traceNorm X) :=
      mul_le_mul_of_nonneg_right hab (mul_nonneg (by norm_num) (Matrix.traceNorm_nonneg X))
    _ = _ := by ring

/-- For unitary branches and positive weight mass, the trace-norm error between the capped and
ideal mixture powers is at most `2 * n * (1/2)^R` times the input trace norm. -/
private theorem fairQdrift_iterated_sampling_error {L D : ℕ} (w : Fin L → ℕ)
    (j0 : Fin L) (R : ℕ) (hW : 0 < weightTotal w) (U : Fin L → Operator D)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ) (r n : ℕ)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Matrix.traceNorm (referenceMixturePower (fairQdriftLaw w j0 R) U r n X -
      referenceMixturePower (fairQdriftImportanceLaw w hW) U r n X) ≤
      2*n*((2 : ℝ)⁻¹)^R*Matrix.traceNorm X := by
  let e := fairQdriftLaw w j0 R
  let d := fairQdriftImportanceLaw w hW
  induction n with
  | zero => simp [referenceMixturePower]
  | succ n ih =>
    let A := referenceMixturePower e U r n X
    let B := referenceMixturePower d U r n X
    have he : referenceMixturePower e U r (n+1) X = referenceMixture e U r A :=
      Function.iterate_succ_apply' _ n X
    have hd : referenceMixturePower d U r (n+1) X = referenceMixture d U r B :=
      Function.iterate_succ_apply' _ n X
    have hs : referenceMixture e U r A - referenceMixture d U r B =
        referenceMixture e U r (A-B) + (referenceMixture e U r B - referenceMixture d U r B) := by
      rw [referenceMixture_sub]
      abel
    change Matrix.traceNorm
        (referenceMixturePower e U r (n+1) X - referenceMixturePower d U r (n+1) X) ≤ _
    rw [he, hd, hs]
    have h1 := (finite_reference_mixture_contraction e U r (A-B) hU).trans ih
    have h2 := fairQdrift_one_step_sampling_error w j0 R hW U hU r B
    have hB := referenceMixturePower_contraction d U r n X hU
    have h2' := h2.trans (mul_le_mul_of_nonneg_left hB (by positivity))
    exact ((Matrix.traceNorm_add_le _ _).trans (add_le_add h1 h2')).trans_eq (by push_cast; ring)

/-- For positive total weight and step count and Hermitian contraction terms, the ancillary
output error relative to the weighted Hamiltonian evolution is at most `(4 * (weightTotal
w)^2 * t^2 / n + 2 * n * (1/2)^R)` times the input trace norm. See [Campbell2019]. -/
theorem fair_bit_qdrift_derived_sampling_and_analytic_error (L D n R r : ℕ)
    (w : Fin L → ℕ) (j0 : Fin L) (K : Fin L → Operator D) (t : ℝ)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (hW : 0 < weightTotal w) (hn : 0 < n)
    (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) :
    Matrix.traceNorm (fairQdriftReferenceOutput w j0 n R K t r X -
      TensorGate (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t) (1 : Operator r) * X *
        (TensorGate (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t) (1 : Operator r))ᴴ) ≤
      (4*(weightTotal w : ℝ)^2*t^2/(n : ℝ) + 2*n*((2 : ℝ)⁻¹)^R)*Matrix.traceNorm X := by
  let d := fairQdriftImportanceLaw w hW
  let U := fun j => HamiltonianEvolution (K j) (t*(weightTotal w : ℝ)/(n : ℝ))
  let B := referenceMixturePower d U r n X
  let C := TensorGate (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t) (1 : Operator r) * X *
    (TensorGate (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t) (1 : Operator r))ᴴ
  rw [fair_bit_qdrift_actual_fresh_channel_bridge L D n R r w j0 K t X hW]
  have hs : referenceMixturePower (fairQdriftLaw w j0 R) U r n X - C =
      (referenceMixturePower (fairQdriftLaw w j0 R) U r n X - B) + (B-C) := by abel
  change Matrix.traceNorm (referenceMixturePower (fairQdriftLaw w j0 R) U r n X - C) ≤ _
  rw [hs]
  have h1 := fairQdrift_iterated_sampling_error w j0 R hW U
    (fun j => hamiltonianEvolution_unitary (hK j).1 _) r n X
  have h2 := qdrift_fresh_reference_global_error L D r d K (weightTotal w : ℝ) t n
    (by positivity) hn hK X
  rw [importance_hamiltonian] at h2
  exact ((Matrix.traceNorm_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by ring)

end Qatlib.Concepts.RandCompile.FairBitSampling
