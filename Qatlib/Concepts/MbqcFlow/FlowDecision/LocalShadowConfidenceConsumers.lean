/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.FairBitRecords.SharpLocalPauliShadows
open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.FairBitRecords
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.ShadowVariance

namespace Qatlib.Concepts.MbqcFlow.FlowDecision
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

def localShadowBlockBudget (k : ℕ) (B ε : ℚ) : ℕ := max 1 (Nat.ceil (16*4^k*B^2/ε^2))

def localShadowRepetitions (D : ℕ) (δ : ℚ) : ℕ :=
  Nat.clog 2 (max 1 D) + Nat.clog 2 (max 1 (Nat.ceil (1/δ))) + 2

theorem localShadowBlockBudget_spec (k : ℕ) (B ε : ℚ) (hε : 0 < ε) :
    0 < localShadowBlockBudget k B ε ∧
    (4:ℝ)^k*(B:ℝ)^2 / (localShadowBlockBudget k B ε : ℝ) ≤ (ε:ℝ)^2/16 := by
  let m := localShadowBlockBudget k B ε
  have hm : 1 ≤ m := le_max_left _ _
  have hmright : Nat.ceil (16*4^k*B^(2:ℕ)/ε^(2:ℕ)) ≤ m := le_max_right _ _
  have hceil : (16*4^k*B^2/ε^2 : ℚ) ≤ (m:ℚ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hmright)
  have hr : (16*(4:ℝ)^k*(B:ℝ)^2/(ε:ℝ)^2) ≤ (m:ℝ) := by exact_mod_cast hceil
  have he : (0:ℝ)<(ε:ℝ) := by exact_mod_cast hε
  have hmp : (0:ℝ)<(m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  refine ⟨by change 0 < m; omega,?_⟩
  change (4:ℝ)^k*(B:ℝ)^2 / (m:ℝ) ≤ (ε:ℝ)^2/16
  apply (div_le_iff₀ hmp).mpr
  have hraw := (div_le_iff₀ (pow_pos he 2)).mp hr
  nlinarith

private theorem localShadow_tail (r : ℕ) :
    (2:ℝ)^(2*r+1)*(1/16:ℝ)^(r+1) ≤ (1/2:ℝ)^r := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    have he : 2*(r+1)+1 = (2*r+1)+2 := by omega
    rw [he,pow_add]
    rw [pow_succ (1/16:ℝ) (r+1),pow_succ (1/2:ℝ) r]
    norm_num only [pow_two]
    norm_num at ih ⊢
    nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) r]

theorem localShadowRepetitions_spec (D : ℕ) (δ : ℚ) (hδ : 0<δ) :
    (D:ℝ)*((2:ℝ)^(2*localShadowRepetitions D δ+1)*
      (1/16:ℝ)^(localShadowRepetitions D δ+1)) ≤ (δ:ℝ) := by
  let A := Nat.clog 2 (max 1 D)
  let B := Nat.clog 2 (max 1 (Nat.ceil (1/δ)))
  let r := localShadowRepetitions D δ
  have hD : D ≤ 2^A := (le_max_right 1 D).trans (Nat.le_pow_clog (by decide) _)
  have hd : (1/δ:ℚ) ≤ (2^B:ℕ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right 1 (Nat.ceil (1/δ))).trans (Nat.le_pow_clog (by decide) _))
  have hDr : (D:ℝ) ≤ (2:ℝ)^A := by exact_mod_cast hD
  have hdr : (1:ℝ)/(δ:ℝ) ≤ (2:ℝ)^B := by exact_mod_cast hd
  have hdp : (0:ℝ)<(δ:ℝ) := by exact_mod_cast hδ
  have hprod : 1 ≤ (δ:ℝ)*(2:ℝ)^B := by
    have ht := (div_le_iff₀ hdp).mp hdr
    nlinarith
  have hr : (D:ℝ) ≤ (δ:ℝ)*(2:ℝ)^r := by
    have he : (2:ℝ)^r = (2:ℝ)^A*(2:ℝ)^B*4 := by
      dsimp [r,localShadowRepetitions,A,B]
      rw [pow_add,pow_add]
      norm_num
    rw [he]
    have hp : (0:ℝ)≤2^A := by positivity
    nlinarith
  calc
    _ ≤ (D:ℝ)*(1/2:ℝ)^r :=
      mul_le_mul_of_nonneg_left (localShadow_tail r) (by positivity)
    _ = (D:ℝ)/(2:ℝ)^r := by simp only [div_eq_mul_inv,one_mul,inv_pow]
    _ ≤ (δ:ℝ) := (div_le_iff₀ (by positivity)).mpr (by simpa [mul_comm] using hr)

theorem local_pauli_same_records_computed_joint_confidence
    (n q D k : ℕ) (S : Fin D → Finset (Fin n))
    (w : Fin D → Fin q → Fin n → Option (Fin 3)) (c : Fin D → Fin q → ℚ)
    (B ε δ : ℚ) (ρ : Operator (2^n)) (hρ : IsDensityOperator ρ)
    (hB : 0 ≤ B) (hε : 0 < ε) (hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    (hs : ∀ j, (S j).card ≤ k ∧ localShadowSupported (S j) (w j) (c j) ∧
      ‖sparsePauliObservable (w j) (c j)‖ ≤ (B:ℝ)) :
    let m := localShadowBlockBudget k B ε
    let r := localShadowRepetitions D δ
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin (2*r+1) → Fin m → Fin n → Fin 3 × Bool =>
      ∃ j : Fin D, (ε:ℝ) < |((localSparseMedianCounted (w j) (c j) m r ω).1 : ℝ) -
        (Matrix.trace (sparsePauliObservable (w j) (c j)*ρ)).re|),
      (blockRecordLaw r m (fun _ _ => tensorPauliLaw n ρ hρ)).prob ω) ≤ (δ:ℝ) := by
  (try dsimp only)
  let m := localShadowBlockBudget k B ε
  let r := localShadowRepetitions D δ
  let p := tensorPauliLaw n ρ hρ
  let θ := fun j => (Matrix.trace (sparsePauliObservable (w j) (c j)*ρ)).re
  have hm := (localShadowBlockBudget_spec k B ε hε).1
  have hmp : (0:ℝ)<(m:ℝ) := by exact_mod_cast hm
  have hm0 : (m:ℝ)≠0 := ne_of_gt hmp
  have he : (0:ℝ)<(ε:ℝ) := by exact_mod_cast hε
  have hb : (0:ℝ)≤(B:ℝ) := by exact_mod_cast hB
  have hmean : ∀ j, p.expect (sparsePauliValue (w j) (c j)) = θ j := by
    intro j
    exact (local_pauli_shadow_sharp_support_moments n q (S j) (w j) (c j) ρ hρ (hs j).2.1).1
  have hvar : ∀ j, p.expect (fun o => (sparsePauliValue (w j) (c j) o-θ j)^2) ≤
      (4:ℝ)^k*(B:ℝ)^2 := by
    intro j
    have hv := (local_pauli_shadow_sharp_support_moments n q (S j) (w j) (c j) ρ hρ
      (hs j).2.1).2.2
    refine hv.trans ?_
    exact mul_le_mul (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤4) (hs j).1)
      (by nlinarith [(hs j).2.2,norm_nonneg (sparsePauliObservable (w j) (c j))])
      (sq_nonneg _) (by positivity)
  have hmmean : ∀ (j : Fin D) (_b : Fin (2*r+1)),
      (∑ _i : Fin m, (m:ℝ)⁻¹ * p.expect (sparsePauliValue (w j) (c j))) = θ j := by
    intro j b
    rw [hmean]
    simp [hm0]
  have hmvar : ∀ (j : Fin D) (_b : Fin (2*r+1)),
      (∑ _i : Fin m, ((m:ℝ)⁻¹)^2 * p.expect
        (fun o => (sparsePauliValue (w j) (c j) o-p.expect (sparsePauliValue (w j) (c j)))^2)) ≤
          (ε:ℝ)^2/16 := by
    intro j b
    simp_rw [hmean]
    calc
      _ ≤ ∑ _i : Fin m, ((m:ℝ)⁻¹)^2 * ((4:ℝ)^k*(B:ℝ)^2) :=
        Finset.sum_le_sum (fun _ _ => mul_le_mul_of_nonneg_left (hvar j) (sq_nonneg _))
      _ = (4:ℝ)^k*(B:ℝ)^2/(m:ℝ) := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; field_simp
      _ ≤ _ := (localShadowBlockBudget_spec k B ε hε).2
  have hprob := heterogeneous_same_records_many_observables r m (fun _ _ => p)
    (fun _ _ _ => (m:ℝ)⁻¹) (fun j _ _ => sparsePauliValue (w j) (c j)) θ (ε:ℝ) he
    hmmean hmvar
  have hout : ∀ (j : Fin D) ω,
      ((localSparseMedianCounted (w j) (c j) m r ω).1 : ℝ) =
      sortedBlockMedian r (weightedBlock r m (fun _ _ => (m:ℝ)⁻¹)
        (fun _ _ => sparsePauliValue (w j) (c j)) ω) := by
    intro j ω
    rw [(local_pauli_native_means_median_and_work n q m r (w j) (c j) ω).1]
    congr 1
    funext b
    simp [weightedBlock,Finset.mul_sum]
  dsimp [m,r] at hout
  simp_rw [hout]
  have ht : (Fintype.card (Fin D) : ℝ)*((2:ℝ)^(2*r+1)*(1/16:ℝ)^(r+1)) ≤ (δ:ℝ) := by
    simpa [r] using localShadowRepetitions_spec D δ hδ
  simpa [p,θ] using hprob.trans ht

theorem local_pauli_many_observables_shared_quantum_ledger
    (n q D k : ℕ) (w : Fin D → Fin q → Fin n → Option (Fin 3))
    (c : Fin D → Fin q → ℚ) (B ε δ : ℚ) :
    let m := localShadowBlockBudget k B ε
    let r := localShadowRepetitions D δ
    ∀ ω : Fin (2*r+1) → Fin m → Fin n → Fin 3 × Bool,
    (∑ j, (localSparseMedianCounted (w j) (c j) m r ω).2.1) =
      D*(2*r+1)*m*q*(n+1) ∧
    (∑ j, (localSparseMedianCounted (w j) (c j) m r ω).2.2) ≤ D*10000*(2*r+1) ∧
    tensorPauliFreshResourceCounts n m (2*r+1) ω =
      ((2*r+1)*m,2*n*((2*r+1)*m),n*((2*r+1)*m),0) := by
  (try dsimp only)
  intro ω
  let m := localShadowBlockBudget k B ε
  let r := localShadowRepetitions D δ
  have hm : ∀ j, (localSparseMedianCounted (w j) (c j) m r ω).2.1 = (2*r+1)*m*q*(n+1) :=
    fun j => (local_pauli_native_means_median_and_work n q m r (w j) (c j) ω).2.1
  have hc : ∀ j, (localSparseMedianCounted (w j) (c j) m r ω).2.2 ≤ 10000*(2*r+1) :=
    fun j => (local_pauli_native_means_median_and_work n q m r (w j) (c j) ω).2.2
  refine ⟨?_,?_,tensorPauliFreshResourceCounts_spec n m (2*r+1) ω⟩
  dsimp [m,r] at hm hc
  · simp_rw [hm]
    simp [mul_assoc]
  · calc
      _ ≤ ∑ _j : Fin D, 10000*(2*r+1) := Finset.sum_le_sum (fun j _ => hc j)
      _ = _ := by simp [r,mul_assoc]

end Qatlib.Concepts.MbqcFlow.FlowDecision
