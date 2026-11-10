/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.LieStrang.HermitianEvolutionStability
import Qatlib.Concepts.RandCompile.ChannelBudget.FairBitQDriftConsumers
import Mathlib.Algebra.Order.Floor.Ring
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.RandCompile.FairBitSampling

open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.RandCompile.EffectiveInput
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

def dyadicCoefficient (b : ℕ) (a : ℚ) : ℤ := ⌊(2 : ℚ)^b*a+1/2⌋

def dyadicWeights {L : ℕ} (b : ℕ) (a : Fin L → ℚ) (j : Fin L) : ℕ :=
  (dyadicCoefficient b (a j)).natAbs

def dyadicSignedTerms {L D : ℕ} (b : ℕ) (a : Fin L → ℚ)
    (K : Fin L → Operator D) (j : Fin L) : Operator D :=
  if dyadicCoefficient b (a j) < 0 then -K j else K j

noncomputable def quantizedQdriftOutput {L D : ℕ} (b : ℕ) (a : Fin L → ℚ)
    (j0 : Fin L) (n R : ℕ) (K : Fin L → Operator D) (t : ℝ) (r : ℕ)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :=
  fairQdriftReferenceOutput (dyadicWeights b a) j0 n R
    (dyadicSignedTerms b a K) (t/(2 : ℝ)^b) r X

theorem dyadicCoefficient_error (b : ℕ) (a : ℚ) :
    |(dyadicCoefficient b a : ℝ)/(2 : ℝ)^b-(a : ℝ)| ≤ 1/(2 : ℝ)^(b+1) := by
  have hlo := Int.floor_le ((2 : ℚ)^b*a+1/2)
  have hhi := Int.lt_floor_add_one ((2 : ℚ)^b*a+1/2)
  have hlo' : (dyadicCoefficient b a : ℝ) ≤ (2 : ℝ)^b*(a : ℝ)+1/2 := by
    have hf : ((⌊(2 : ℚ)^b*a+1/2⌋ : ℤ) : ℝ) ≤ (((2 : ℚ)^b*a+1/2 : ℚ) : ℝ) := by
      exact_mod_cast hlo
    simpa only [dyadicCoefficient, Rat.cast_add, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using hf
  have hhi' : (2 : ℝ)^b*(a : ℝ)+1/2 < (dyadicCoefficient b a : ℝ)+1 := by
    have hf : (((2 : ℚ)^b*a+1/2 : ℚ) : ℝ) < ((⌊(2 : ℚ)^b*a+1/2⌋ : ℤ) : ℝ)+1 := by
      exact_mod_cast hhi
    simpa only [dyadicCoefficient, Rat.cast_add, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using hf
  have hp : (0 : ℝ) < 2^b := by positivity
  have hb : |(dyadicCoefficient b a : ℝ)-(2 : ℝ)^b*(a : ℝ)| ≤ 1/2 := by
    rw [abs_le]
    constructor <;> linarith
  have he : (dyadicCoefficient b a : ℝ)/(2 : ℝ)^b-(a : ℝ) =
      ((dyadicCoefficient b a : ℝ)-(2 : ℝ)^b*(a : ℝ))/(2 : ℝ)^b := by
    field_simp
  rw [he, abs_div, abs_of_pos hp, pow_succ]
  exact (div_le_div_of_nonneg_right hb hp.le).trans_eq (by ring)

theorem dyadic_signed_generator {L D : ℕ} (b : ℕ) (a : Fin L → ℚ)
    (K : Fin L → Operator D) :
    (((2 : ℂ)^b)⁻¹) • (∑ j, (dyadicWeights b a j : ℂ) • dyadicSignedTerms b a K j) =
      ∑ j, ((dyadicCoefficient b (a j) : ℂ)/(2 : ℂ)^b) • K j := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he : (dyadicWeights b a j : ℂ) • dyadicSignedTerms b a K j =
      (dyadicCoefficient b (a j) : ℂ) • K j := by
    unfold dyadicWeights dyadicSignedTerms
    split_ifs with hz
    · have hh : ((dyadicCoefficient b (a j)).natAbs : ℤ) = -dyadicCoefficient b (a j) :=
        by rw [Int.natCast_natAbs, abs_of_nonpos hz.le]
      have hc : ((dyadicCoefficient b (a j)).natAbs : ℂ) = -(dyadicCoefficient b (a j) : ℂ) := by
        simpa only [Int.cast_natCast, Int.cast_neg] using congrArg (fun z : ℤ => (z : ℂ)) hh
      rw [hc, neg_smul, smul_neg, neg_neg]
    · have hh : ((dyadicCoefficient b (a j)).natAbs : ℤ) = dyadicCoefficient b (a j) :=
        by rw [Int.natCast_natAbs, abs_of_nonneg (le_of_not_gt hz)]
      have hc : ((dyadicCoefficient b (a j)).natAbs : ℂ) = (dyadicCoefficient b (a j) : ℂ) := by
        simpa only [Int.cast_natCast, Int.cast_neg] using congrArg (fun z : ℤ => (z : ℂ)) hh
      rw [hc]
  rw [he, smul_smul]
  congr 1
  ring

theorem dyadic_actual_signed_rounding_and_generator (L D b : ℕ) (a : Fin L → ℚ)
    (K : Fin L → Operator D) (_hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) :
    (∀ j, |(dyadicCoefficient b (a j) : ℝ)/(2 : ℝ)^b-(a j : ℝ)| ≤ 1/(2 : ℝ)^(b+1)) ∧
      (((2 : ℂ)^b)⁻¹) • (∑ j, (dyadicWeights b a j : ℂ) • dyadicSignedTerms b a K j) =
        ∑ j, ((dyadicCoefficient b (a j) : ℂ)/(2 : ℂ)^b) • K j :=
  ⟨fun j => dyadicCoefficient_error b (a j), dyadic_signed_generator b a K⟩

theorem dyadicSignedTerms_contract {L D : ℕ} (b : ℕ) (a : Fin L → ℚ)
    (K : Fin L → Operator D) (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) :
    ∀ j, (dyadicSignedTerms b a K j).IsHermitian ∧ ‖dyadicSignedTerms b a K j‖ ≤ 1 := by
  intro j
  unfold dyadicSignedTerms
  split_ifs
  · exact ⟨(hK j).1.neg, by simpa using (hK j).2⟩
  · exact hK j

theorem dyadic_target_generator_error (L D b : ℕ) (a : Fin L → ℚ)
    (h : Fin L → ℝ) (K : Fin L → Operator D) (δ : ℝ)
    (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1)
    (ha : (∑ j, |h j-(a j : ℝ)|) ≤ δ) :
    ‖(∑ j, (h j : ℂ) • K j)-
      (∑ j, ((dyadicCoefficient b (a j) : ℂ)/(2 : ℂ)^b) • K j)‖ ≤
        δ+(L : ℝ)/(2 : ℝ)^(b+1) := by
  have hc (j : Fin L) : ‖((h j : ℂ)-(dyadicCoefficient b (a j) : ℂ)/(2 : ℂ)^b) • K j‖ ≤
      |h j-(a j : ℝ)| + 1/(2 : ℝ)^(b+1) := by
    have he : (h j : ℂ)-(dyadicCoefficient b (a j) : ℂ)/(2 : ℂ)^b =
        ((h j-(dyadicCoefficient b (a j) : ℝ)/(2 : ℝ)^b : ℝ) : ℂ) := by push_cast; rfl
    rw [norm_smul, he, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |h j-(dyadicCoefficient b (a j) : ℝ)/(2 : ℝ)^b| * 1 := by gcongr; exact (hK j).2
      _ = |h j-(dyadicCoefficient b (a j) : ℝ)/(2 : ℝ)^b| := mul_one _
      _ ≤ |h j-(a j : ℝ)| + |(dyadicCoefficient b (a j) : ℝ)/(2 : ℝ)^b-(a j : ℝ)| := by
        simpa [abs_sub_comm] using abs_sub_le (h j) (a j : ℝ)
          ((dyadicCoefficient b (a j) : ℝ)/(2 : ℝ)^b)
      _ ≤ _ := add_le_add_right (dyadicCoefficient_error b (a j)) _
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_smul]
  calc
    _ ≤ ∑ j, ‖((h j : ℂ)-(dyadicCoefficient b (a j) : ℂ)/(2 : ℂ)^b) • K j‖ := norm_sum_le _ _
    _ ≤ ∑ j, (|h j-(a j : ℝ)| + 1/(2 : ℝ)^(b+1)) := Finset.sum_le_sum (fun j _ => hc j)
    _ = (∑ j, |h j-(a j : ℝ)|) + (L : ℝ)/(2 : ℝ)^(b+1) := by
      simp [Finset.sum_add_distrib, div_eq_mul_inv]
    _ ≤ _ := add_le_add_left ha _

theorem quantized_real_generator_hermitian {L D : ℕ} (c : Fin L → ℝ)
    (K : Fin L → Operator D) (hK : ∀ j, (K j).IsHermitian) :
    (∑ j, (c j : ℂ) • K j).IsHermitian := by
  change (∑ j, (c j : ℂ) • K j)ᴴ = _
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact ((hK j).smul (by simp [IsSelfAdjoint])).eq

theorem quantized_evolution_scale {D : ℕ} (H : Operator D) (t c : ℝ) :
    HamiltonianEvolution ((c : ℂ) • H) t = HamiltonianEvolution H (t*c) := by
  unfold HamiltonianEvolution
  rw [smul_smul]
  congr 2
  push_cast
  ring

theorem dyadic_generator_evolution {L D : ℕ} (b : ℕ) (a : Fin L → ℚ)
    (K : Fin L → Operator D) (t : ℝ) :
    HamiltonianEvolution (∑ j, (dyadicWeights b a j : ℂ) • dyadicSignedTerms b a K j)
      (t/(2 : ℝ)^b) =
    HamiltonianEvolution (∑ j, ((dyadicCoefficient b (a j) : ℂ)/(2 : ℂ)^b) • K j) t := by
  rw [← dyadic_signed_generator]
  have hc : (((2 : ℂ)^b)⁻¹) = (((2 : ℝ)^b)⁻¹ : ℝ) := by push_cast; rfl
  rw [hc, quantized_evolution_scale, div_eq_mul_inv]

theorem quantized_qdrift_actual_reference_error (L D b n R r : ℕ)
    (a : Fin L → ℚ) (h : Fin L → ℝ) (j0 : Fin L) (K : Fin L → Operator D)
    (t δ : ℝ) (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (hn : 0 < n) (hW : 0 < weightTotal (dyadicWeights b a))
    (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1)
    (ha : (∑ j, |h j-(a j : ℝ)|) ≤ δ) :
    Matrix.traceNorm (quantizedQdriftOutput b a j0 n R K t r X-
      TensorGate (HamiltonianEvolution (∑ j, (h j : ℂ) • K j) t) (1 : Operator r)*X*
      (TensorGate (HamiltonianEvolution (∑ j, (h j : ℂ) • K j) t) (1 : Operator r))ᴴ) ≤
      (4*((weightTotal (dyadicWeights b a) : ℝ)/(2 : ℝ)^b)^2*t^2/(n : ℝ)+
        2*n*(1/2 : ℝ)^R+2 * |t| * (δ+(L : ℝ)/(2 : ℝ)^(b+1)))*Matrix.traceNorm X := by
  let Q := ∑ j, ((dyadicCoefficient b (a j) : ℂ)/(2 : ℂ)^b) • K j
  let H := ∑ j, (h j : ℂ) • K j
  let Y := TensorGate (HamiltonianEvolution Q t) (1 : Operator r)*X*
    (TensorGate (HamiltonianEvolution Q t) (1 : Operator r))ᴴ
  let Z := TensorGate (HamiltonianEvolution H t) (1 : Operator r)*X*
    (TensorGate (HamiltonianEvolution H t) (1 : Operator r))ᴴ
  have hQ : Q.IsHermitian := by
    change Qᴴ = Q
    dsimp [Q]
    rw [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.conjTranspose_smul, (hK j).1.eq]
    congr 1
    simp [RCLike.star_def]
  have hH : H.IsHermitian := quantized_real_generator_hermitian h K (fun j => (hK j).1)
  have h1 := fair_bit_qdrift_derived_sampling_and_analytic_error L D n R r
    (dyadicWeights b a) j0 (dyadicSignedTerms b a K) (t/(2 : ℝ)^b) X hW hn
    (dyadicSignedTerms_contract b a K hK)
  rw [dyadic_generator_evolution] at h1
  have h2 := hermitian_evolution_reference_stability D r Q H t X hQ hH
  have hg : ‖Q-H‖ ≤ δ+(L : ℝ)/(2 : ℝ)^(b+1) := by
    rw [norm_sub_rev]
    exact dyadic_target_generator_error L D b a h K δ hK ha
  have h2' : Matrix.traceNorm (Y-Z) ≤
      (2 * |t| * (δ+(L : ℝ)/(2 : ℝ)^(b+1)))*Matrix.traceNorm X :=
    h2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hg (by positivity)) (Matrix.traceNorm_nonneg X))
  have he : quantizedQdriftOutput b a j0 n R K t r X-Z =
      (quantizedQdriftOutput b a j0 n R K t r X-Y)+(Y-Z) := by abel
  change Matrix.traceNorm (quantizedQdriftOutput b a j0 n R K t r X-Z) ≤ _
  rw [he]
  exact ((Matrix.traceNorm_add_le _ _).trans (add_le_add h1 h2')).trans_eq (by
    dsimp [quantizedQdriftOutput] at *
    ring)

theorem quantized_qdrift_zero_and_path_ledger (L D b n R : ℕ) (a : Fin L → ℚ)
    (j0 : Fin L) (K : Fin L → Operator D) (t : ℝ)
    (ω : Fin n → Fin R → Reg (Nat.clog 2 (weightTotal (dyadicWeights b a)))) :
    let w := dyadicWeights b a
    let terms := dyadicSignedTerms b a K
    (weightTotal w = 0 → fairQdriftCircuit w j0 n R terms (t/(2 : ℝ)^b) ω = []) ∧
      (0 < weightTotal w →
        (∑ k, (fairQdriftPick w j0 R (ω k)).2.1) ≤ n*Nat.clog 2 (weightTotal w)*R ∧
        (∑ k, (fairQdriftPick w j0 R (ω k)).2.2) ≤ n*L*R ∧
        GateCount (fairQdriftCircuit w j0 n R terms (t/(2 : ℝ)^b) ω) = n) := by
  dsimp
  constructor
  · intro hw
    simp [fairQdriftCircuit, hw]
  · intro hw
    refine ⟨?_, ?_, ?_⟩
    · calc
        _ ≤ ∑ _ : Fin n, Nat.clog 2 (weightTotal (dyadicWeights b a))*R :=
          Finset.sum_le_sum (fun k _ =>
            ((fair_bit_qdrift_actual_coin_path_cost L R (dyadicWeights b a) j0 hw).1 (ω k)).1)
        _ = _ := by simp [Nat.mul_assoc]
    · calc
        _ ≤ ∑ _ : Fin n, L*R := Finset.sum_le_sum (fun k _ =>
          ((fair_bit_qdrift_actual_coin_path_cost L R (dyadicWeights b a) j0 hw).1 (ω k)).2)
        _ = _ := by simp [Nat.mul_assoc]
    · simp only [fairQdriftCircuit, if_neg (ne_of_gt hw)]
      exact (mixture_path_circuit_semantics_cost _ n _ (0 : QState (Fin D))).2.2.1

theorem quantized_qdrift_actual_path_counts (L D b n R : ℕ) (a : Fin L → ℚ)
    (j0 : Fin L) (K : Fin L → Operator D) (t : ℝ)
    (ω : Fin n → Fin R → Reg (Nat.clog 2 (weightTotal (dyadicWeights b a))))
    (hW : 0 < weightTotal (dyadicWeights b a))
    (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) :
    let w := dyadicWeights b a
    let terms := dyadicSignedTerms b a K
    IsUnitaryCircuit (fairQdriftCircuit w j0 n R terms (t/(2 : ℝ)^b) ω) ∧
      QueryCount (fairQdriftCircuit w j0 n R terms (t/(2 : ℝ)^b) ω)=0 ∧
      GateCount (fairQdriftCircuit w j0 n R terms (t/(2 : ℝ)^b) ω)=n ∧
      (∑ k, (fairQdriftPick w j0 R (ω k)).2.1) ≤ n*Nat.clog 2 (weightTotal w)*R ∧
      (∑ k, (fairQdriftPick w j0 R (ω k)).2.2) ≤ n*L*R :=
  fair_bit_qdrift_actual_quantum_and_classical_path_counts L D n R
    (dyadicWeights b a) j0 (dyadicSignedTerms b a K) (t/(2 : ℝ)^b) ω hW
    (fun j => (dyadicSignedTerms_contract b a K hK j).1)

theorem quantized_qdrift_computed_budget (L D b T s r : ℕ)
    (a : Fin L → ℚ) (h : Fin L → ℝ) (j0 : Fin L) (K : Fin L → Operator D)
    (t δ : ℝ) (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (hW : 0 < weightTotal (dyadicWeights b a)) (ht : |t| ≤ T)
    (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1)
    (ha : (∑ j, |h j-(a j : ℝ)|) ≤ δ) :
    let n := fairQdriftSteps (weightTotal (dyadicWeights b a)) T s
    let R := fairQdriftFuel n s
    0 < n ∧
    Matrix.traceNorm (quantizedQdriftOutput b a j0 n R K t r X-
      TensorGate (HamiltonianEvolution (∑ j, (h j : ℂ) • K j) t) (1 : Operator r)*X*
      (TensorGate (HamiltonianEvolution (∑ j, (h j : ℂ) • K j) t) (1 : Operator r))ᴴ) ≤
      ((1/2 : ℝ)^s+2 * |t| * (δ+(L : ℝ)/(2 : ℝ)^(b+1)))*Matrix.traceNorm X := by
  let n := fairQdriftSteps (weightTotal (dyadicWeights b a)) T s
  let R := fairQdriftFuel n s
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)
  refine ⟨hn, ?_⟩
  have ht' : |t/(2 : ℝ)^b| ≤ T := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2^b)]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^b)).mpr
    exact ht.trans (by
      have hp : (1 : ℝ) ≤ 2^b := one_le_pow₀ (by norm_num)
      simpa using mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg T))
  let Q := ∑ j, ((dyadicCoefficient b (a j) : ℂ)/(2 : ℂ)^b) • K j
  let H := ∑ j, (h j : ℂ) • K j
  let Y := TensorGate (HamiltonianEvolution Q t) (1 : Operator r)*X*
    (TensorGate (HamiltonianEvolution Q t) (1 : Operator r))ᴴ
  let Z := TensorGate (HamiltonianEvolution H t) (1 : Operator r)*X*
    (TensorGate (HamiltonianEvolution H t) (1 : Operator r))ᴴ
  have hQ : Q.IsHermitian := by
    change Qᴴ = Q
    dsimp [Q]
    rw [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.conjTranspose_smul, (hK j).1.eq]
    congr 1
    simp [RCLike.star_def]
  have hH : H.IsHermitian := quantized_real_generator_hermitian h K (fun j => (hK j).1)
  have h1 := fairQdrift_computed_budget_trace L D T s r (dyadicWeights b a) j0
    (dyadicSignedTerms b a K) (t/(2 : ℝ)^b) X hW ht'
    (dyadicSignedTerms_contract b a K hK)
  rw [dyadic_generator_evolution] at h1
  have h2 := hermitian_evolution_reference_stability D r Q H t X hQ hH
  have hg : ‖Q-H‖ ≤ δ+(L : ℝ)/(2 : ℝ)^(b+1) := by
    rw [norm_sub_rev]
    exact dyadic_target_generator_error L D b a h K δ hK ha
  have h2' : Matrix.traceNorm (Y-Z) ≤
      (2 * |t| * (δ+(L : ℝ)/(2 : ℝ)^(b+1)))*Matrix.traceNorm X :=
    h2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hg (by positivity)) (Matrix.traceNorm_nonneg X))
  have he : quantizedQdriftOutput b a j0 n R K t r X-Z =
      (quantizedQdriftOutput b a j0 n R K t r X-Y)+(Y-Z) := by abel
  change Matrix.traceNorm (quantizedQdriftOutput b a j0 n R K t r X-Z) ≤ _
  rw [he]
  exact ((Matrix.traceNorm_add_le _ _).trans (add_le_add h1 h2')).trans_eq (by norm_num; ring)
end Qatlib.Concepts.RandCompile.EffectiveInput
