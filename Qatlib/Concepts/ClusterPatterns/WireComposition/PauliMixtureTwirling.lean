/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ReferenceError.RefTraceError.ChannelMixtureComposition
import Qatlib.Foundations.QueryWordCore.Circuit
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.ClusterPatterns.WireComposition

open Matrix
open scoped ComplexOrder

set_option autoImplicit false

private lemma smul_smul' {α : Type*} [Fintype α] (c d : ℂ) (M : Matrix α α ℂ) :
    c • (d • M) = (c * d) • M := by
  ext i j
  show c * (d * M i j) = c * d * M i j
  ring

private lemma smul_conj' {α : Type*} [Fintype α] (c : ℂ) (V Y : Matrix α α ℂ) :
    V * (c • Y) * Vᴴ = c • (V * Y * Vᴴ) := by
  simp only [Matrix.mul_smul, Matrix.smul_mul]

private lemma smul_conj {α : Type*} [Fintype α] (c : ℂ) (V Y : Matrix α α ℂ) :
    c • (V * Y * Vᴴ) = V * (c • Y) * Vᴴ :=
  (smul_conj' c V Y).symm

private lemma fintype_smul_sum {J : Type*} [Fintype J] {α : Type*} [Fintype α] (c : ℂ)
    (f : J → Matrix α α ℂ) : (∑ j, c • f j) = c • (∑ j, f j) :=
  (Finset.smul_sum (s := Finset.univ)).symm

private lemma fintype_mul_sum {J : Type*} [Fintype J] {α : Type*} [Fintype α]
    (Z : Matrix α α ℂ) (f : J → Matrix α α ℂ) : (∑ j, Z * f j) = Z * (∑ j, f j) := by
  show Finset.univ.sum (fun j => Z * f j) = Z * Finset.univ.sum f
  exact (Finset.mul_sum (Finset.univ : Finset J) f Z).symm

private lemma fintype_mul_sum' {J : Type*} [Fintype J] {α : Type*} [Fintype α]
    (f : J → Matrix α α ℂ) (Z : Matrix α α ℂ) : (∑ j, f j) * Z = ∑ j, f j * Z := by
  show Finset.univ.sum f * Z = Finset.univ.sum (fun j => f j * Z)
  exact Finset.sum_mul (Finset.univ : Finset J) f Z

private lemma fintype_sum_swap {J K : Type*} [Fintype J] [Fintype K]
    {M : Type*} [AddCommMonoid M] (f : J → K → M) :
    (∑ j, ∑ k, f j k) = ∑ k, ∑ j, f j k := by
  calc (∑ j, ∑ k, f j k) = ∑ x : J × K, f x.1 x.2 := (Fintype.sum_prod_type' f).symm
    _ = ∑ y : K × J, f y.2 y.1 :=
        Fintype.sum_equiv (Equiv.prodComm J K) (fun x : J × K => f x.1 x.2)
          (fun y : K × J => f y.2 y.1) (fun _ => rfl)
    _ = ∑ k, ∑ j, f j k := Fintype.sum_prod_type' (fun k j => f j k)

private lemma rebracket2 {α : Type*} [Fintype α] (V U M : Matrix α α ℂ) :
    V * ((U * M) * Uᴴ) * Vᴴ = (V * U) * M * (V * U)ᴴ := by
  simp only [Matrix.mul_assoc, Matrix.conjTranspose_mul]

private lemma rebracket1 {α : Type*} [Fintype α] (V U M : Matrix α α ℂ) :
    (V * U) * M * (V * U)ᴴ = V * ((U * M) * Uᴴ) * Vᴴ := by
  simp only [Matrix.mul_assoc, Matrix.conjTranspose_mul]

private lemma conj_outerProduct {D : ℕ} (V : Operator D) (x : QState (Fin D)) :
    V * (outerProduct x) * Vᴴ = outerProduct (V *ᵥ x) := by
  show conjBranch V (outerProduct x) = _
  rw [conjBranch_outerProduct]

private lemma relabel_mul {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (U V : Matrix I I ℂ) :
    relabelGate e U * relabelGate e V = relabelGate e (U * V) := by
  ext i j
  simp only [relabelGate, Matrix.reindex_apply, Matrix.mul_apply, Matrix.submatrix_apply]
  rw [Equiv.sum_comp e.symm (fun y => U (e.symm i) y * V y (e.symm j))]

private lemma relabel_star {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (U : Matrix I I ℂ) : (relabelGate e U)ᴴ = relabelGate e Uᴴ := by
  ext i j
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]

private lemma relabel_one {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) : relabelGate e (1 : Matrix I I ℂ) = 1 := by
  ext i j
  simp [relabelGate, Matrix.reindex_apply, Matrix.one_apply]

private lemma relabel_unitary {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (e : I ≃ J) {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    relabelGate e U ∈ Matrix.unitaryGroup J ℂ := by
  have h : Uᴴ * U = 1 := by
    have h' := (Matrix.mem_unitaryGroup_iff').mp hU
    rwa [Matrix.star_eq_conjTranspose] at h'
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, relabel_star, relabel_mul, h,
    relabel_one]

theorem one_unitary {D : ℕ} : (1 : Operator D) ∈ Matrix.unitaryGroup (Fin D) ℂ :=
  Matrix.mem_unitaryGroup_iff'.mpr (by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_one, Matrix.one_mul])

noncomputable def pauliFairBit : FinDist Bool where
  prob _ := 1 / 2
  nonneg _ := by norm_num
  sum_one := by rw [Fintype.sum_bool]; norm_num

theorem pauliFairBit_prob (b : Bool) : pauliFairBit.prob b = 1 / 2 := rfl

theorem pauliFairBit_weight (j k : Bool) :
    ((pauliFairBit.prob j * pauliFairBit.prob k : ℝ) : ℂ) = (1 / 4 : ℂ) := by
  rw [pauliFairBit_prob, pauliFairBit_prob, Complex.ofReal_mul]
  norm_num

noncomputable def pauliXChoice (b : Bool) : Operator 2 :=
  if b then relabelGate boolEquivFin2 PauliX else 1

noncomputable def pauliZChoice (b : Bool) : Operator 2 :=
  if b then relabelGate boolEquivFin2 PauliZ else 1

theorem pauliXChoice_unitary (b : Bool) : pauliXChoice b ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  cases b with
  | true => exact relabel_unitary boolEquivFin2 pauliX_unitary
  | false => exact one_unitary

theorem pauliZChoice_unitary (b : Bool) : pauliZChoice b ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  cases b with
  | true => exact relabel_unitary boolEquivFin2 pauliZ_unitary
  | false => exact one_unitary

theorem pauliXChoice_true : pauliXChoice true = relabelGate boolEquivFin2 PauliX := by
  simp [pauliXChoice]

theorem pauliXChoice_false : pauliXChoice false = 1 := by
  simp [pauliXChoice]

theorem pauliZChoice_true : pauliZChoice true = relabelGate boolEquivFin2 PauliZ := by
  simp [pauliZChoice]

theorem pauliZChoice_false : pauliZChoice false = 1 := by
  simp [pauliZChoice]

theorem relabel_pauliX_entry (i j : Fin 2) :
    relabelGate boolEquivFin2 PauliX i j = if i = j then 0 else 1 := by
  fin_cases i <;> fin_cases j <;>
    simp [relabelGate, Matrix.reindex_apply, boolEquivFin2, PauliX, permMatrix]

theorem relabel_pauliZ_entry (i j : Fin 2) :
    relabelGate boolEquivFin2 PauliZ i j = if i = j then (if j = 1 then -1 else 1) else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [relabelGate, Matrix.reindex_apply, boolEquivFin2, PauliZ]

theorem conj_pauliX_true (ρ : Operator 2) :
    relabelGate boolEquivFin2 PauliX * ρ * (relabelGate boolEquivFin2 PauliX)ᴴ
      = fun i j => ρ (1 - i) (1 - j) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, relabel_pauliX_entry, Matrix.conjTranspose_apply]

theorem conj_pauliZ_true (ρ : Operator 2) :
    relabelGate boolEquivFin2 PauliZ * ρ * (relabelGate boolEquivFin2 PauliZ)ᴴ
      = fun i j => (if i = j then 1 else -1) * ρ i j := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, relabel_pauliZ_entry, Matrix.conjTranspose_apply]

theorem twirl_path_XZ (ρ : Operator 2) :
    (pauliZChoice true * pauliXChoice true) * ρ * (pauliZChoice true * pauliXChoice true)ᴴ
      = fun i j => (if i = j then 1 else -1) * ρ (1 - i) (1 - j) := by
  rw [pauliZChoice_true, pauliXChoice_true, rebracket1, conj_pauliZ_true]
  funext i j
  rw [conj_pauliX_true]

theorem twirl_path_IZ (ρ : Operator 2) :
    (pauliZChoice true * pauliXChoice false) * ρ * (pauliZChoice true * pauliXChoice false)ᴴ
      = fun i j => (if i = j then 1 else -1) * ρ i j := by
  simp only [pauliZChoice_true, pauliXChoice_false, Matrix.mul_one]
  exact conj_pauliZ_true ρ

theorem twirl_path_XI (ρ : Operator 2) :
    (pauliZChoice false * pauliXChoice true) * ρ * (pauliZChoice false * pauliXChoice true)ᴴ
      = fun i j => ρ (1 - i) (1 - j) := by
  simp only [pauliZChoice_false, pauliXChoice_true, Matrix.one_mul]
  exact conj_pauliX_true ρ

theorem twirl_path_II (ρ : Operator 2) :
    (pauliZChoice false * pauliXChoice false) * ρ * (pauliZChoice false * pauliXChoice false)ᴴ
      = ρ := by
  simp only [pauliZChoice_false, pauliXChoice_false, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_one, Matrix.conjTranspose_one]

theorem pauliTwirl_dephasing (ρ : Operator 2) :
    ChannelMixture (FinDist.independentPair pauliFairBit pauliFairBit)
      (fun jk => pauliZChoice jk.2 * pauliXChoice jk.1) ρ
      = (Matrix.trace ρ / (2 : ℂ)) • (1 : Operator 2) := by
  simp only [ChannelMixture, FinDist.independentPair]
  have hstep : (∑ jk : Bool × Bool, ((pauliFairBit.prob jk.1 * pauliFairBit.prob jk.2 : ℝ) : ℂ) •
        ((pauliZChoice jk.2 * pauliXChoice jk.1) * ρ * (pauliZChoice jk.2 * pauliXChoice jk.1)ᴴ))
      = ∑ jk : Bool × Bool, ((1 / 4 : ℂ)) •
        ((pauliZChoice jk.2 * pauliXChoice jk.1) * ρ * (pauliZChoice jk.2 * pauliXChoice jk.1)ᴴ) := by
    refine Finset.sum_congr rfl fun jk _ => ?_
    rw [pauliFairBit_weight]
  rw [hstep, Fintype.sum_prod_type' (fun j k => (1 / 4 : ℂ) •
    ((pauliZChoice k * pauliXChoice j) * ρ * (pauliZChoice k * pauliXChoice j)ᴴ))]
  simp only [Fintype.sum_bool]
  rw [twirl_path_XZ ρ, twirl_path_IZ ρ, twirl_path_XI ρ, twirl_path_II ρ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, smul_eq_mul, Matrix.trace, Fin.sum_univ_two] <;> ring

noncomputable def pauliTwirlCircuit (j k : Bool) : Circuit (Fin 2) :=
  [Step.gate (pauliXChoice j), Step.gate (pauliZChoice k)]

theorem pauliTwirlCircuit_counts (j k : Bool) :
    QueryCount (pauliTwirlCircuit j k) = 0 ∧ GateCount (pauliTwirlCircuit j k) = 2 ∧
      IsUnitaryCircuit (pauliTwirlCircuit j k) := by
  refine ⟨rfl, rfl, ?_⟩
  intro U hU
  rcases List.mem_cons.mp hU with hU | hU
  · cases hU
    exact pauliXChoice_unitary j
  · rcases List.mem_cons.mp hU with hU | hU
    · cases hU
      exact pauliZChoice_unitary k
    · simp at hU

theorem run_pauliTwirlCircuit (ψ : QState (Fin 2)) (j k : Bool) :
    Run (1 : Operator 2) (pauliTwirlCircuit j k) ψ
      = (pauliZChoice k * pauliXChoice j) *ᵥ ψ := by
  show Run 1 [Step.gate (pauliXChoice j), Step.gate (pauliZChoice k)] ψ = _
  simp only [Run, ApplyGate, Matrix.mulVec_mulVec]

theorem pauliTwirl_run_outerProduct (ψ : QState (Fin 2)) :
    ChannelMixture (FinDist.independentPair pauliFairBit pauliFairBit)
      (fun jk => pauliZChoice jk.2 * pauliXChoice jk.1) (outerProduct ψ)
      = ∑ jk : Bool × Bool, (1 / 4 : ℂ) •
        outerProduct (Run (1 : Operator 2) (pauliTwirlCircuit jk.1 jk.2) ψ) := by
  rw [(unitaryMixture_composition pauliFairBit pauliFairBit pauliXChoice pauliZChoice
    pauliXChoice_unitary pauliZChoice_unitary (outerProduct ψ)).1]
  simp only [ChannelMixture, pauliFairBit_prob]
  have hmix : ∀ k : Bool,
      ((1 / 2 : ℝ) : ℂ) • (pauliZChoice k *
          (∑ j, ((1 / 2 : ℝ) : ℂ) • ((pauliXChoice j) * (outerProduct ψ) * (pauliXChoice j)ᴴ)) *
            (pauliZChoice k)ᴴ)
        = ∑ j, (1 / 4 : ℂ) • outerProduct ((pauliZChoice k * pauliXChoice j) *ᵥ ψ) := by
    intro k
    have hone : pauliZChoice k *
          (∑ j, ((1 / 2 : ℝ) : ℂ) • ((pauliXChoice j) * (outerProduct ψ) * (pauliXChoice j)ᴴ)) *
            (pauliZChoice k)ᴴ
        = ∑ j, pauliZChoice k *
            (((1 / 2 : ℝ) : ℂ) • ((pauliXChoice j) * (outerProduct ψ) * (pauliXChoice j)ᴴ)) *
              (pauliZChoice k)ᴴ := by
      rw [Matrix.mul_sum, fintype_mul_sum']
    have hpush : ((1 / 2 : ℝ) : ℂ) • (pauliZChoice k *
          (∑ j, ((1 / 2 : ℝ) : ℂ) • ((pauliXChoice j) * (outerProduct ψ) * (pauliXChoice j)ᴴ)) *
            (pauliZChoice k)ᴴ)
        = ∑ j, ((1 / 2 : ℝ) : ℂ) • (((1 / 2 : ℝ) : ℂ) • (pauliZChoice k *
            ((pauliXChoice j) * (outerProduct ψ) * (pauliXChoice j)ᴴ) * (pauliZChoice k)ᴴ)) := by
      calc ((1 / 2 : ℝ) : ℂ) • (pauliZChoice k *
              (∑ j, ((1 / 2 : ℝ) : ℂ) • ((pauliXChoice j) * (outerProduct ψ) *
                (pauliXChoice j)ᴴ)) * (pauliZChoice k)ᴴ)
          = ((1 / 2 : ℝ) : ℂ) • (∑ j, pauliZChoice k *
              (((1 / 2 : ℝ) : ℂ) • ((pauliXChoice j) * (outerProduct ψ) * (pauliXChoice j)ᴴ)) *
                (pauliZChoice k)ᴴ) := by rw [hone]
        _ = ∑ j, ((1 / 2 : ℝ) : ℂ) • (pauliZChoice k *
              (((1 / 2 : ℝ) : ℂ) • ((pauliXChoice j) * (outerProduct ψ) * (pauliXChoice j)ᴴ)) *
                (pauliZChoice k)ᴴ) := (fintype_smul_sum _ _).symm
        _ = ∑ j, ((1 / 2 : ℝ) : ℂ) • (((1 / 2 : ℝ) : ℂ) • (pauliZChoice k *
              ((pauliXChoice j) * (outerProduct ψ) * (pauliXChoice j)ᴴ) * (pauliZChoice k)ᴴ)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← smul_conj]
    refine (hpush.trans (Finset.sum_congr rfl fun j _ => ?_))
    show ((1 / 2 : ℝ) : ℂ) • (((1 / 2 : ℝ) : ℂ) • (pauliZChoice k *
        ((pauliXChoice j) * (outerProduct ψ) * (pauliXChoice j)ᴴ) * (pauliZChoice k)ᴴ)) = _
    rw [smul_smul', conj_outerProduct, conj_outerProduct, Matrix.mulVec_mulVec,
      show ((1 / 2 : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ) = (1 / 4 : ℂ) by norm_num]
  have hswap := fintype_sum_swap (M := Operator 2)
    (fun k j => (1 / 4 : ℂ) • outerProduct ((pauliZChoice k * pauliXChoice j) *ᵥ ψ))
  calc (∑ k, ((1 / 2 : ℝ) : ℂ) • (pauliZChoice k *
        (∑ j, ((1 / 2 : ℝ) : ℂ) • ((pauliXChoice j) * (outerProduct ψ) * (pauliXChoice j)ᴴ)) *
          (pauliZChoice k)ᴴ))
      = ∑ k, ∑ j, (1 / 4 : ℂ) • outerProduct ((pauliZChoice k * pauliXChoice j) *ᵥ ψ) :=
        Finset.sum_congr rfl fun k _ => hmix k
    _ = ∑ j, ∑ k, (1 / 4 : ℂ) • outerProduct ((pauliZChoice k * pauliXChoice j) *ᵥ ψ) := hswap
    _ = ∑ j, ∑ k, (1 / 4 : ℂ) • outerProduct (Run (1 : Operator 2) (pauliTwirlCircuit j k) ψ) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        show (1 / 4 : ℂ) • outerProduct ((pauliZChoice k * pauliXChoice j) *ᵥ ψ) = _
        simp only [run_pauliTwirlCircuit]
    _ = ∑ jk : Bool × Bool, (1 / 4 : ℂ) •
        outerProduct (Run (1 : Operator 2) (pauliTwirlCircuit jk.1 jk.2) ψ) :=
        (Fintype.sum_prod_type' (fun j k => (1 / 4 : ℂ) •
          outerProduct (Run (1 : Operator 2) (pauliTwirlCircuit j k) ψ))).symm

theorem pauliTwirl_branch_run
    (hX : ∀ b, pauliXChoice b ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hZ : ∀ b, pauliZChoice b ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (ψ : QState (Fin 2)) (j k : Bool) :
    ((unitaryMixtureInstrument pauliFairBit pauliXChoice hX).seq
      (unitaryMixtureInstrument pauliFairBit pauliZChoice hZ)).branch (j, k) (outerProduct ψ)
      = (1 / 4 : ℂ) • outerProduct (Run (1 : Operator 2) (pauliTwirlCircuit j k) ψ) := by
  refine (unitaryMixtureInstrument_seq_outerProduct pauliFairBit pauliFairBit
    pauliXChoice pauliZChoice hX hZ ψ j k).trans ?_
  show ((pauliFairBit.prob j * pauliFairBit.prob k : ℝ) : ℂ) •
      outerProduct ((pauliZChoice k * pauliXChoice j) *ᵥ ψ) = _
  rw [pauliFairBit_weight, run_pauliTwirlCircuit]

set_option linter.unusedVariables false in

theorem pauliTwirl_correct :
    (∀ b, pauliFairBit.prob b = 1 / 2) ∧
      (∀ b, pauliXChoice b ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        pauliZChoice b ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
      (∀ ρ : Operator 2,
        ChannelMixture (FinDist.independentPair pauliFairBit pauliFairBit)
          (fun jk => pauliZChoice jk.2 * pauliXChoice jk.1) ρ
          = (Matrix.trace ρ / (2 : ℂ)) • (1 : Operator 2)) ∧
      (∀ (ψ : QState (Fin 2)) (j k : Bool),
        ChannelMixture (FinDist.independentPair pauliFairBit pauliFairBit)
          (fun jk => pauliZChoice jk.2 * pauliXChoice jk.1) (outerProduct ψ)
          = ∑ jk : Bool × Bool, (1 / 4 : ℂ) •
            outerProduct (Run (1 : Operator 2) (pauliTwirlCircuit jk.1 jk.2) ψ)) ∧
      (∀ j k, QueryCount (pauliTwirlCircuit j k) = 0 ∧
        GateCount (pauliTwirlCircuit j k) = 2 ∧ IsUnitaryCircuit (pauliTwirlCircuit j k)) :=
  ⟨pauliFairBit_prob, fun b => ⟨pauliXChoice_unitary b, pauliZChoice_unitary b⟩,
    pauliTwirl_dephasing, fun ψ _ _ => pauliTwirl_run_outerProduct ψ,
    pauliTwirlCircuit_counts⟩

end Qatlib.Concepts.ClusterPatterns.WireComposition
