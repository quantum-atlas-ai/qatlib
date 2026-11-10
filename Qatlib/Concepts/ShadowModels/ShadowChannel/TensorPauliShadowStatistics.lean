/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliRecords
import Qatlib.Concepts.GateVocabulary.GateVocab.GateVocabulary
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.ShadowModels.ShadowChannel

open Matrix
open scoped ComplexOrder Kronecker

set_option maxHeartbeats 4000000

noncomputable def tensorPauliWordFactor : Option (Fin 3) → Operator 2
  | none => 1
  | some a => pauliMatrix a

noncomputable def tensorPauliWord (n : ℕ) (w : Fin n → Option (Fin 3)) :
    Operator (2 ^ n) := tensorPauliProduct n (fun i => tensorPauliWordFactor (w i))

def tensorPauliWeight {n : ℕ} (w : Fin n → Option (Fin 3)) : ℕ :=
  ∑ i, if (w i).isSome then 1 else 0

noncomputable def tensorPauliSnapshot (n : ℕ) (o : Fin n → Fin 3 × Bool) :
    Operator (2 ^ n) := tensorPauliProduct n (fun i => PauliShadow (o i).2 (o i).1)

def tensorPauliLocalValue : Option (Fin 3) → (Fin 3 × Bool) → ℝ
  | none, _ => 1
  | some a, o => if o.1 = a then 3 * (if o.2 then 1 else -1) else 0

def tensorPauliValue {n : ℕ} (w : Fin n → Option (Fin 3))
    (o : Fin n → Fin 3 × Bool) : ℝ := ∏ i, tensorPauliLocalValue (w i) (o i)

theorem tensorPauliLocalValue_trace (w : Option (Fin 3)) (o : Fin 3 × Bool) :
    Matrix.trace (tensorPauliWordFactor w * PauliShadow o.2 o.1) =
      (tensorPauliLocalValue w o : ℂ) := by
  rcases w with _ | a
  · simp only [tensorPauliWordFactor, Matrix.one_mul, tensorPauliLocalValue]
    rw [PauliShadow, Matrix.trace_sub, Matrix.trace_smul]
    have hp : Matrix.trace (PauliProjector o.1 o.2) = 1 := by
      rw [PauliProjector, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_smul,
        trace_pauliMatrix]
      norm_num [Matrix.trace_one]
    rw [hp]
    norm_num [Matrix.trace_one]
  · rw [tensorPauliWordFactor, PauliShadow, Matrix.mul_sub, Matrix.mul_smul,
      Matrix.trace_sub, Matrix.trace_smul, Matrix.mul_one, trace_pauliMatrix]
    rw [PauliProjector, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one,
      Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_smul,
      trace_pauliMatrix, trace_pauliMatrix_mul]
    by_cases h : o.1 = a
    · subst a
      rcases o with ⟨a, b⟩
      cases b <;> norm_num [tensorPauliLocalValue]
    · have h' : a ≠ o.1 := Ne.symm h
      simp [h', tensorPauliLocalValue, h]

theorem tensorPauliValue_trace (n : ℕ) (w : Fin n → Option (Fin 3))
    (o : Fin n → Fin 3 × Bool) :
    Matrix.trace (tensorPauliWord n w * tensorPauliSnapshot n o) =
      (tensorPauliValue w o : ℂ) := by
  rw [tensorPauliWord, tensorPauliSnapshot, tensorPauliProduct_mul,
    tensorPauliProduct_trace]
  simp only [tensorPauliLocalValue_trace, tensorPauliValue, Complex.ofReal_prod]

theorem tensorPauliLocalValue_sq (w : Option (Fin 3)) (o : Fin 3 × Bool) :
    (tensorPauliLocalValue w o) ^ 2 =
      match w with
      | none => 1
      | some a => if o.1 = a then 9 else 0 := by
  rcases w with _ | a
  · norm_num [tensorPauliLocalValue]
  · rcases o with ⟨b, s⟩
    by_cases h : b = a <;> cases s <;> norm_num [tensorPauliLocalValue, h]

theorem tensorPauliLocalSecondMomentEffect (w : Option (Fin 3)) :
    (∑ o : Fin 3 × Bool,
      (((tensorPauliLocalValue w o) ^ 2 : ℝ) : ℂ) •
        ((1 / 3 : ℂ) • PauliProjector o.1 o.2)) =
      ((3 : ℂ) ^ (if w.isSome then 1 else 0)) • (1 : Operator 2) := by
  simp_rw [tensorPauliLocalValue_sq]
  rcases w with _ | a
  · simp only [Option.isSome_none, Bool.false_eq_true, if_false, pow_zero, one_smul]
    rw [← pauliRecordKraus_complete]
    exact Finset.sum_congr rfl fun o _ => by
      simpa using (pauliRecordKraus_conj_mul o).symm
  · rw [Fintype.sum_prod_type]
    simp only [Option.isSome_some, if_true, pow_one]
    have hh : ∀ b : Fin 3,
        (∑ s : Bool, Complex.ofReal (if b = a then (9 : ℝ) else 0) •
          ((1 / 3 : ℂ) • PauliProjector b s)) =
        if b = a then (3 : ℂ) • (1 : Operator 2) else 0 := by
      intro b
      by_cases h : b = a
      · rw [if_pos h]
        simp_rw [if_pos h]
        rw [← Finset.smul_sum, ← Finset.smul_sum, pauliProjector_sum]
        ext i j
        norm_num [Matrix.smul_apply]
        ring
      · simp [h]
    change (∑ b : Fin 3, ∑ s : Bool, Complex.ofReal (if b = a then (9 : ℝ) else 0) •
      ((1 / 3 : ℂ) • PauliProjector b s)) = (3 : ℂ) • (1 : Operator 2)
    rw [Finset.sum_congr rfl (fun b _ => hh b)]
    simp

theorem tensorPauliLocalReconstructionKernel (x y u v : Fin 2) :
    (∑ o : Fin 3 × Bool,
      ((1 / 3 : ℂ) * PauliProjector o.1 o.2 y x) * PauliShadow o.2 o.1 u v) =
      (if u = x then 1 else 0) * (if v = y then 1 else 0) := by
  exact Qatlib.Concepts.GateVocabulary.GateVocab.pauli_shadow_reconstruction_kernel x y u v

theorem tensorPauliDeltaProduct {n : ℕ} {α : Type*} [DecidableEq α]
    (x y : Fin n → α) :
    (∏ i, (if x i = y i then (1 : ℂ) else 0)) = if x = y then 1 else 0 := by
  by_cases h : x = y
  · subst y
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem tensorPauliReconstruction_algebraic {n : ℕ} (σ : Matrix (Reg n) (Reg n) ℂ) :
    (∑ o : Fin n → Fin 3 × Bool,
      Matrix.trace (pauliProductDensity
        (fun i => (1 / 3 : ℂ) • PauliProjector (o i).1 (o i).2) * σ) •
        pauliProductDensity (fun i => PauliShadow (o i).2 (o i).1)) = σ := by
  ext u v
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.trace,
    pauliProductDensity, Matrix.of_apply]
  change (∑ o : Fin n → Fin 3 × Bool,
    (∑ x : Reg n, ∑ y : Reg n,
      (∏ i, (1 / 3 : ℂ) * PauliProjector (o i).1 (o i).2
        (boolEquivFin2 (x i)) (boolEquivFin2 (y i))) * σ y x) *
      (∏ i, PauliShadow (o i).2 (o i).1
        (boolEquivFin2 (u i)) (boolEquivFin2 (v i)))) = σ u v
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Eq.trans (Finset.sum_congr rfl fun x _ => Finset.sum_comm)
  have hk : ∀ x y : Reg n,
      (∑ o : Fin n → Fin 3 × Bool,
        ((∏ i, (1 / 3 : ℂ) * PauliProjector (o i).1 (o i).2
          (boolEquivFin2 (x i)) (boolEquivFin2 (y i))) * σ y x) *
        (∏ i, PauliShadow (o i).2 (o i).1
          (boolEquivFin2 (u i)) (boolEquivFin2 (v i)))) =
      σ y x * (if u = y then 1 else 0) * (if v = x then 1 else 0) := by
    intro x y
    have hterm : ∀ o : Fin n → Fin 3 × Bool,
        ((∏ i, (1 / 3 : ℂ) * PauliProjector (o i).1 (o i).2
          (boolEquivFin2 (x i)) (boolEquivFin2 (y i))) * σ y x) *
          (∏ i, PauliShadow (o i).2 (o i).1
            (boolEquivFin2 (u i)) (boolEquivFin2 (v i))) =
        σ y x * ∏ i, (((1 / 3 : ℂ) * PauliProjector (o i).1 (o i).2
          (boolEquivFin2 (x i)) (boolEquivFin2 (y i))) *
          PauliShadow (o i).2 (o i).1
            (boolEquivFin2 (u i)) (boolEquivFin2 (v i))) := by
      intro o
      rw [Finset.prod_mul_distrib (f := fun i : Fin n =>
        (1 / 3 : ℂ) * PauliProjector (o i).1 (o i).2
          (boolEquivFin2 (x i)) (boolEquivFin2 (y i)))
        (g := fun i : Fin n => PauliShadow (o i).2 (o i).1
          (boolEquivFin2 (u i)) (boolEquivFin2 (v i)))]
      ring
    rw [Finset.sum_congr rfl (fun o _ => hterm o), ← Finset.mul_sum,
      ← Fintype.prod_sum (fun (i : Fin n) (o : Fin 3 × Bool) =>
        ((1 / 3 : ℂ) * PauliProjector o.1 o.2
          (boolEquivFin2 (x i)) (boolEquivFin2 (y i))) *
          PauliShadow o.2 o.1 (boolEquivFin2 (u i)) (boolEquivFin2 (v i)))]
    simp_rw [tensorPauliLocalReconstructionKernel, Equiv.apply_eq_iff_eq]
    rw [Finset.prod_mul_distrib, tensorPauliDeltaProduct, tensorPauliDeltaProduct]
    ring
  simp_rw [hk]
  simp

theorem tensor_pauli_snapshot_reconstructs_entangled_input (n : ℕ)
    (ρ : Operator (2 ^ n)) (hρ : IsDensityOperator ρ) :
    (∑ o : Fin n → Fin 3 × Bool,
      ((tensorPauliLaw n ρ hρ).prob o : ℂ) • tensorPauliSnapshot n o) = ρ := by
  simp_rw [tensorPauliLaw_complex_mass, tensorPauliKraus_effect,
    tensorPauliProduct, tensorPauliTrace_relabel_mul]
  have h := tensorPauliReconstruction_algebraic
    (ρ.submatrix (bitVecEquiv n) (bitVecEquiv n))
  ext u v
  have he := congrFun (congrFun h ((bitVecEquiv n).symm u)) ((bitVecEquiv n).symm v)
  simpa only [Matrix.sum_apply, Matrix.smul_apply, tensorPauliSnapshot,
    tensorPauliProduct, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.apply_symm_apply] using he

theorem tensorPauliValue_mean (n : ℕ) (ρ : Operator (2 ^ n))
    (hρ : IsDensityOperator ρ) (w : Fin n → Option (Fin 3)) :
    (tensorPauliLaw n ρ hρ).expect (tensorPauliValue w) =
      (Matrix.trace (tensorPauliWord n w * ρ)).re := by
  have h := congrArg (fun σ => (Matrix.trace (tensorPauliWord n w * σ)).re)
    (tensor_pauli_snapshot_reconstructs_entangled_input n ρ hρ)
  simp only [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum] at h
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    tensorPauliValue_trace, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] at h
  exact h

theorem tensorPauliValue_second_effect (n : ℕ) (w : Fin n → Option (Fin 3)) :
    (∑ o : Fin n → Fin 3 × Bool,
      (((tensorPauliValue w o) ^ 2 : ℝ) : ℂ) •
        ((tensorPauliKraus n o)ᴴ * tensorPauliKraus n o)) =
      (3 : ℂ) ^ tensorPauliWeight w • (1 : Operator (2 ^ n)) := by
  simp_rw [tensorPauliKraus_effect]
  have ht : ∀ o : Fin n → Fin 3 × Bool,
      (((tensorPauliValue w o) ^ 2 : ℝ) : ℂ) •
        tensorPauliProduct n (fun i => (1 / 3 : ℂ) • PauliProjector (o i).1 (o i).2) =
      tensorPauliProduct n (fun i =>
        (((tensorPauliLocalValue (w i) (o i)) ^ 2 : ℝ) : ℂ) •
          ((1 / 3 : ℂ) • PauliProjector (o i).1 (o i).2)) := by
    intro o
    rw [tensorPauliProduct_smul n
      (fun i => (((tensorPauliLocalValue (w i) (o i)) ^ 2 : ℝ) : ℂ))
      (fun i => (1 / 3 : ℂ) • PauliProjector (o i).1 (o i).2)]
    congr 1
    simp only [tensorPauliValue, ← Finset.prod_pow, Complex.ofReal_prod]
  rw [Finset.sum_congr rfl (fun o _ => ht o)]
  rw [tensorPauliProduct_sum (n := n) (fun i o =>
    (((tensorPauliLocalValue (w i) o) ^ 2 : ℝ) : ℂ) •
      ((1 / 3 : ℂ) • PauliProjector o.1 o.2))]
  simp_rw [tensorPauliLocalSecondMomentEffect]
  rw [tensorPauliProduct_smul, tensorPauliProduct_one,
    Finset.prod_pow_eq_pow_sum]
  rfl

theorem tensorPauliValue_second_moment (n : ℕ) (ρ : Operator (2 ^ n))
    (hρ : IsDensityOperator ρ) (w : Fin n → Option (Fin 3)) :
    (tensorPauliLaw n ρ hρ).expect (fun o => (tensorPauliValue w o) ^ 2) =
      (3 : ℝ) ^ tensorPauliWeight w := by
  have ht : (Matrix.trace ((∑ o : Fin n → Fin 3 × Bool,
      (((tensorPauliValue w o) ^ 2 : ℝ) : ℂ) •
        ((tensorPauliKraus n o)ᴴ * tensorPauliKraus n o)) * ρ)).re =
      (tensorPauliLaw n ρ hρ).expect (fun o => (tensorPauliValue w o) ^ 2) := by
    rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro o _
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      ← tensorPauliLaw_complex_mass n ρ hρ o]
    norm_cast
    ring
  rw [← ht, tensorPauliValue_second_effect, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, hρ.2, smul_eq_mul, mul_one]
  norm_cast

theorem tensor_pauli_word_exact_moments (n : ℕ) (ρ : Operator (2 ^ n))
    (hρ : IsDensityOperator ρ) (w : Fin n → Option (Fin 3)) :
    (∀ o, tensorPauliValue w o =
      (Matrix.trace (tensorPauliWord n w * tensorPauliSnapshot n o)).re) ∧
    (tensorPauliLaw n ρ hρ).expect (tensorPauliValue w) =
      (Matrix.trace (tensorPauliWord n w * ρ)).re ∧
    (tensorPauliLaw n ρ hρ).expect (fun o => (tensorPauliValue w o) ^ 2) =
      (3 : ℝ) ^ tensorPauliWeight w ∧
    (tensorPauliLaw n ρ hρ).variance (tensorPauliValue w) =
      (3 : ℝ) ^ tensorPauliWeight w - (Matrix.trace (tensorPauliWord n w * ρ)).re ^ 2 := by
  refine ⟨fun o => ?_, tensorPauliValue_mean n ρ hρ w,
    tensorPauliValue_second_moment n ρ hρ w, ?_⟩
  · rw [tensorPauliValue_trace, Complex.ofReal_re]
  · rw [FinDist.variance_eq_expect_sq_sub, tensorPauliValue_second_moment,
      tensorPauliValue_mean]

theorem tensor_pauli_many_words_same_record_concentration
    (n L K M : ℕ) (ρ : Operator (2 ^ n)) (hρ : IsDensityOperator ρ)
    (w : Fin M → Fin n → Option (Fin 3)) (ε : ℝ)
    (hL : 0 < L) (hK : 0 < K) (hε : 0 < ε)
    (hbud : ∀ j, 4 * (3 : ℝ) ^ tensorPauliWeight (w j) ≤ (L : ℝ) * ε ^ 2) :
    let p := tensorPauliLaw n ρ hρ
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin K → Fin L → (Fin n → Fin 3 × Bool) =>
      ∃ j : Fin M, ε < |p.medianOfMeans (tensorPauliValue (w j)) ω -
        (Matrix.trace (tensorPauliWord n (w j) * ρ)).re|),
      ∏ k, p.probOf (ω k)) ≤ (M : ℝ) * 3 ^ (K / 2) / 2 ^ K := by
  let p := tensorPauliLaw n ρ hρ
  let q : FinDist (Fin L → (Fin n → Fin 3 × Bool)) :=
    ⟨p.probOf, fun ω => Finset.prod_nonneg fun _ _ => p.nonneg _, p.sum_probOf L⟩
  have hper : ∀ j : Fin M,
      q.probEvent (fun ω : Fin K → Fin L → (Fin n → Fin 3 × Bool) =>
        ε < |p.medianOfMeans (tensorPauliValue (w j)) ω -
          (Matrix.trace (tensorPauliWord n (w j) * ρ)).re|) ≤ 3 ^ (K / 2) / 2 ^ K := by
    intro j
    have hv := (tensor_pauli_word_exact_moments n ρ hρ (w j)).2.2.2
    have hvb : 4 * p.variance (tensorPauliValue (w j)) ≤ (L : ℝ) * ε ^ 2 := by
      change 4 * (tensorPauliLaw n ρ hρ).variance _ ≤ _
      rw [hv]
      nlinarith [sq_nonneg (Matrix.trace (tensorPauliWord n (w j) * ρ)).re, hbud j]
    have hh := p.median_of_means_concentration (tensorPauliValue (w j)) hL hK ε hε hvb
    rw [tensorPauliValue_mean] at hh
    exact hh
  have hu := FinDist.union_bound q (fun j (ω : Fin K → Fin L → (Fin n → Fin 3 × Bool)) =>
    ε < |p.medianOfMeans (tensorPauliValue (w j)) ω -
      (Matrix.trace (tensorPauliWord n (w j) * ρ)).re|)
  change q.probEvent (fun ω => ∃ j : Fin M,
    ε < |p.medianOfMeans (tensorPauliValue (w j)) ω -
      (Matrix.trace (tensorPauliWord n (w j) * ρ)).re|) ≤ _
  calc _ ≤ ∑ j : Fin M, q.probEvent (fun ω =>
        ε < |p.medianOfMeans (tensorPauliValue (w j)) ω -
          (Matrix.trace (tensorPauliWord n (w j) * ρ)).re|) := hu
    _ ≤ ∑ _j : Fin M, 3 ^ (K / 2) / 2 ^ K := Finset.sum_le_sum fun j _ => hper j
    _ = (M : ℝ) * 3 ^ (K / 2) / 2 ^ K := by simp [mul_div_assoc]

theorem tensor_pauli_linear_observable_variance (n M : ℕ)
    (ρ : Operator (2 ^ n)) (hρ : IsDensityOperator ρ)
    (w : Fin M → Fin n → Option (Fin 3)) (c : Fin M → ℝ) :
    let f := fun o => ∑ j, c j * tensorPauliValue (w j) o
    (tensorPauliLaw n ρ hρ).expect f =
      (Matrix.trace ((∑ j, (c j : ℂ) • tensorPauliWord n (w j)) * ρ)).re ∧
    (tensorPauliLaw n ρ hρ).variance f ≤
      (M : ℝ) * ∑ j, (c j) ^ 2 * (3 : ℝ) ^ tensorPauliWeight (w j) := by
  let p := tensorPauliLaw n ρ hρ
  let f := fun o => ∑ j, c j * tensorPauliValue (w j) o
  have hlin : p.expect f = ∑ j, c j * p.expect (tensorPauliValue (w j)) := by
    change (∑ o, p.prob o * ∑ j, c j * tensorPauliValue (w j) o) = _
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [FinDist.expect, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro o _
    ring
  refine ⟨?_, ?_⟩
  · rw [hlin, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [tensorPauliValue_mean]
  · have hf : ∀ o, (f o) ^ 2 ≤ (M : ℝ) * ∑ j, (c j) ^ 2 * (tensorPauliValue (w j) o) ^ 2 := by
      intro o
      have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : Fin M => (1 : ℝ)) (fun j => c j * tensorPauliValue (w j) o)
      simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, mul_pow] using hh
    have hm : p.expect (fun o => (f o) ^ 2) ≤
        (M : ℝ) * ∑ j, (c j) ^ 2 * (3 : ℝ) ^ tensorPauliWeight (w j) := by
      calc p.expect (fun o => (f o) ^ 2)
          ≤ ∑ o, p.prob o * ((M : ℝ) * ∑ j, (c j) ^ 2 * (tensorPauliValue (w j) o) ^ 2) :=
            Finset.sum_le_sum fun o _ => mul_le_mul_of_nonneg_left (hf o) (p.nonneg o)
        _ = (M : ℝ) * ∑ j, (c j) ^ 2 * p.expect (fun o => (tensorPauliValue (w j) o) ^ 2) := by
            simp only [FinDist.expect, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro o _
            ring
        _ = _ := by
          change (M : ℝ) * ∑ j, (c j) ^ 2 *
            (tensorPauliLaw n ρ hρ).expect (fun o => (tensorPauliValue (w j) o) ^ 2) = _
          simp only [tensorPauliValue_second_moment]
    rw [FinDist.variance_eq_expect_sq_sub]
    exact (sub_le_self _ (sq_nonneg _)).trans hm

noncomputable def tensorPauliFreshProduct {t n : ℕ} (A : Fin t → Operator (2 ^ n)) :
    Matrix (Fin t → Fin (2 ^ n)) (Fin t → Fin (2 ^ n)) ℂ :=
  Matrix.of (fun x y => ∏ i, A i (x i) (y i))

theorem tensorPauliFreshProduct_mul {t n : ℕ} (A B : Fin t → Operator (2 ^ n)) :
    tensorPauliFreshProduct A * tensorPauliFreshProduct B =
      tensorPauliFreshProduct (fun i => A i * B i) := by
  ext x y
  simp only [Matrix.mul_apply, tensorPauliFreshProduct, Matrix.of_apply]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i z => A i (x i) z * B i z (y i))]

theorem tensorPauliFreshProduct_conjTranspose {t n : ℕ} (A : Fin t → Operator (2 ^ n)) :
    (tensorPauliFreshProduct A)ᴴ = tensorPauliFreshProduct (fun i => (A i)ᴴ) := by
  ext x y
  simp [tensorPauliFreshProduct, Matrix.conjTranspose_apply]

theorem tensorPauliFreshProduct_trace {t n : ℕ} (A : Fin t → Operator (2 ^ n)) :
    Matrix.trace (tensorPauliFreshProduct A) = ∏ i, Matrix.trace (A i) := by
  change (∑ x : Fin t → Fin (2 ^ n), ∏ i, A i (x i) (x i)) = _
  exact (Fintype.prod_sum (fun i z => A i z z)).symm

theorem tensorPauliFreshProduct_succ {t n : ℕ} (A : Fin (t + 1) → Operator (2 ^ n)) :
    tensorPauliFreshProduct A =
      ((tensorPauliFreshProduct (fun i => A (Fin.castAdd 1 i))) ⊗ₖ
        A (Fin.natAdd t 0)).submatrix (Fin.succFunEquiv (Fin (2 ^ n)) t)
          (Fin.succFunEquiv (Fin (2 ^ n)) t) := by
  ext x y
  simp only [tensorPauliFreshProduct, Matrix.of_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply]
  rw [Fin.prod_univ_add, Fin.prod_univ_one]
  rfl

theorem tensorPauliFreshProduct_density {t n : ℕ} (ρ : Operator (2 ^ n))
    (hρ : IsDensityOperator ρ) :
    (tensorPauliFreshProduct (fun _ : Fin t => ρ)).PosSemidef ∧
      Matrix.trace (tensorPauliFreshProduct (fun _ : Fin t => ρ)) = 1 := by
  refine ⟨?_, ?_⟩
  · induction t with
    | zero =>
      have he : tensorPauliFreshProduct (fun _ : Fin 0 => ρ) = 1 := by
        ext x y
        rw [Subsingleton.elim x y]
        simp [tensorPauliFreshProduct]
      rw [he]
      exact Matrix.PosSemidef.one
    | succ t ih =>
      rw [tensorPauliFreshProduct_succ]
      exact (Matrix.posSemidef_submatrix_equiv _).mpr (ih.kronecker hρ.1)
  · rw [tensorPauliFreshProduct_trace]
    simp [hρ.2]

theorem tensorPauliFreshProduct_born {t n : ℕ} (ρ : Operator (2 ^ n))
    (hρ : IsDensityOperator ρ) (o : Fin t → Fin n → Fin 3 × Bool) :
    (Matrix.trace (tensorPauliFreshProduct (fun i => tensorPauliKraus n (o i)) *
      tensorPauliFreshProduct (fun _ : Fin t => ρ) *
        (tensorPauliFreshProduct (fun i => tensorPauliKraus n (o i)))ᴴ)).re =
      ∏ i, (tensorPauliLaw n ρ hρ).prob (o i) := by
  rw [tensorPauliFreshProduct_conjTranspose, tensorPauliFreshProduct_mul,
    tensorPauliFreshProduct_mul, tensorPauliFreshProduct_trace]
  have ht : ∀ i, Matrix.trace (tensorPauliKraus n (o i) * ρ * (tensorPauliKraus n (o i))ᴴ) =
      ((tensorPauliLaw n ρ hρ).prob (o i) : ℂ) := by
    intro i
    rw [tensorPauliLaw_complex_mass]
    exact Matrix.trace_mul_cycle _ _ _
  simp_rw [ht]
  rw [← Complex.ofReal_prod, Complex.ofReal_re]

theorem tensor_pauli_fresh_born_and_cost (n L K : ℕ) (ρ : Operator (2 ^ n))
    (hρ : IsDensityOperator ρ) (ω : Fin K → Fin L → (Fin n → Fin 3 × Bool)) :
    (∏ k : Fin K, ∏ l : Fin L,
      (Matrix.trace (tensorPauliKraus n (ω k l) * ρ * (tensorPauliKraus n (ω k l))ᴴ)).re) =
      ∏ k : Fin K, (tensorPauliLaw n ρ hρ).probOf (ω k) ∧
    (∑ k : Fin K, ∑ l : Fin L,
      (observedLeaf 1 (tensorPauliProgram n (fun i => (ω k l i).1))
        (tensorPauliLeaf n (fun i => (ω k l i).1) (fun i => (ω k l i).2))).gates) =
        2 * n * (K * L) ∧
    (∑ k : Fin K, ∑ l : Fin L,
      (observedLeaf 1 (tensorPauliProgram n (fun i => (ω k l i).1))
        (tensorPauliLeaf n (fun i => (ω k l i).1) (fun i => (ω k l i).2))).measurements) =
        n * (K * L) := by
  refine ⟨rfl, ?_, ?_⟩
  · simp_rw [(tensor_pauli_actual_local_program n _).2.2.2 _ |>.2.2.1]
    simp
    ring
  · simp_rw [(tensor_pauli_actual_local_program n _).2.2.2 _ |>.2.2.2.1]
    simp
    ring

noncomputable def tensorPauliFreshResourceCounts (n L K : ℕ)
    (ω : Fin K → Fin L → (Fin n → Fin 3 × Bool)) : ℕ × ℕ × ℕ × ℕ :=
  let leaves := List.ofFn (fun t : Fin (K * L) =>
    let o := ω (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2
    observedLeaf 1 (tensorPauliProgram n (fun i => (o i).1))
      (tensorPauliLeaf n (fun i => (o i).1) (fun i => (o i).2)))
  (leaves.length, (leaves.map ObservedKrausLeaf.gates).sum,
    (leaves.map ObservedKrausLeaf.measurements).sum,
    (leaves.map ObservedKrausLeaf.queries).sum)

theorem tensorPauliFreshResourceCounts_spec (n L K : ℕ)
    (ω : Fin K → Fin L → (Fin n → Fin 3 × Bool)) :
    tensorPauliFreshResourceCounts n L K ω = (K * L, 2 * n * (K * L), n * (K * L), 0) := by
  simp only [tensorPauliFreshResourceCounts, List.length_ofFn, List.map_ofFn,
    List.sum_ofFn, Function.comp_def]
  simp_rw [(tensor_pauli_actual_local_program n _).2.2.2 _ |>.2.2.1,
    (tensor_pauli_actual_local_program n _).2.2.2 _ |>.2.2.2.1,
    (tensor_pauli_actual_local_program n _).2.2.2 _ |>.2.1]
  simp [mul_comm]

end Qatlib.Concepts.ShadowModels.ShadowChannel
