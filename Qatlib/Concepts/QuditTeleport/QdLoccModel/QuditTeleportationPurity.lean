/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportationDefs
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationInstrument
import Qatlib.Concepts.QuditTeleport.TeleportCore.CountedQuditTeleportation
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditResourceMarginalConverse
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditMaxEntCharacterization
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditMaxEntResourceTeleportation
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditPureResourceMaxEntForm
import Qatlib.Concepts.QuditTeleport.QdLoccModel.RedundantCodingReliability
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceMarginalConverse
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditMaxEntCharacterization
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditMaxEntResourceTeleportation
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditPureResourceMaxEntForm
import Qatlib.Concepts.QuditTeleport.MessagingBounds.RedundantCodingReliability
import Qatlib.Concepts.QuditTeleport.CommLowerBound.CommBoundRestrictedTele
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportationBranchMarginal
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option warningAsError false
open Qatlib.Concepts.QuditTeleport.CommLowerBound
open Qatlib.Concepts.QuditTeleport.MessagingBounds
open Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Concepts.QuditTeleport.ResourceIff
open Matrix
open scoped ComplexOrder

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Concepts.BlockEncoding.LinearCombination

namespace Qatlib.Concepts.QuditTeleport.QdLoccModel
open Matrix
open scoped BigOperators ComplexOrder
open scoped BigOperators
set_option autoImplicit false
set_option warningAsError false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
open Matrix Qatlib.Concepts.QuditTeleport.CommLowerBound
open Qatlib.Concepts.QuditTeleport.MessagingBounds Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Concepts.QuditTeleport.ResourceIff
open scoped BigOperators ComplexOrder MatrixOrder

theorem g8p_psdSqrt {ι : Type} [Fintype ι] [DecidableEq ι] (ω : Matrix ι ι ℂ)
    (hω : ω.PosSemidef) :
    ∃ S : Matrix ι ι ℂ, S * S = ω ∧ S.conjTranspose = S ∧ S.PosSemidef :=
  ⟨CFC.sqrt ω, CFC.sqrt_mul_sqrt_self ω hω.nonneg,
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg ω) : IsSelfAdjoint (CFC.sqrt ω)).star_eq,
    (CFC.sqrt_nonneg ω).posSemidef⟩

theorem g8p_local_gate {n : ℕ} (A : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    relabelGate (qdBobFirstEquiv n) (TensorGate A (1 : Operator n)) =
      TensorGate (1 : Operator n) (relabelGate finProdFinEquiv A) :=
  quditBobFirst_local_gate A

theorem g8p_branch_bobFirst {n : ℕ}
    (K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (ρ : Operator n) :
    qdBranchMarginal K ω ρ =
      PartialTrace (TensorGate (1 : Operator n) (relabelGate finProdFinEquiv K) *
        relabelGate (qdBobFirstEquiv n)
          (relabelGate (Equiv.prodAssoc (Fin n) (Fin n) (Fin n)).symm (TensorGate ρ ω)) *
        (TensorGate (1 : Operator n) (relabelGate finProdFinEquiv K))ᴴ) := by
  unfold qdBranchMarginal
  rw [converse_relabel_mul, converse_relabel_mul, converse_relabel_adjoint, g8p_local_gate]

theorem g8p_noSignalling {n : ℕ} {κ : Type} [Fintype κ]
    (K : κ → Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hK : ∑ k, (K k).conjTranspose * K k = 1)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (ρ : Operator n) :
    ∑ k, qdBranchMarginal (K k) ω ρ =
      (Matrix.trace ρ) •
        PartialTrace (relabelGate (Equiv.prodComm (Fin n) (Fin n)) ω) := by
  let V : κ → Matrix (Fin n × Fin (n * n)) (Fin n × Fin (n * n)) ℂ :=
    fun k => TensorGate (1 : Operator n) (relabelGate finProdFinEquiv (K k))
  let X : Matrix (Fin n × Fin (n * n)) (Fin n × Fin (n * n)) ℂ :=
    relabelGate (qdBobFirstEquiv n)
      (relabelGate (Equiv.prodAssoc (Fin n) (Fin n) (Fin n)).symm (TensorGate ρ ω))
  have hVX : ∀ k, qdBranchMarginal (K k) ω ρ = PartialTrace (V k * X * (V k)ᴴ) := by
    intro k
    rw [g8p_branch_bobFirst]
  have hV1 : ∀ k, (V k)ᴴ * V k
      = TensorGate (1 : Operator n)
          (relabelGate finProdFinEquiv ((K k).conjTranspose * K k)) := by
    intro k
    simp only [V]
    rw [tensorGate_conjTranspose, Matrix.conjTranspose_one, tensorGate_mul, Matrix.one_mul]
    rw [← converse_relabel_adjoint, ← converse_relabel_mul]
  have hex : (∑ k : κ, TensorGate (1 : Operator n)
        (relabelGate finProdFinEquiv ((K k).conjTranspose * K k)))
      = TensorGate (1 : Operator n)
          (relabelGate finProdFinEquiv (∑ k : κ, (K k).conjTranspose * K k)) := by
    ext p q
    have hL : (∑ k : κ, TensorGate (1 : Operator n)
          (relabelGate finProdFinEquiv ((K k).conjTranspose * K k))) p q
        = ∑ k : κ, (1 : Operator n) p.1 q.1 *
            relabelGate finProdFinEquiv ((K k).conjTranspose * K k) p.2 q.2 := by
      rw [Matrix.sum_apply]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact tensorGate_apply (1 : Operator n)
        (relabelGate finProdFinEquiv ((K k).conjTranspose * K k)) p.1 q.1 p.2 q.2
    have hR : TensorGate (1 : Operator n)
          (relabelGate finProdFinEquiv (∑ k : κ, (K k).conjTranspose * K k)) p q
        = (1 : Operator n) p.1 q.1 *
            relabelGate finProdFinEquiv (∑ k : κ, (K k).conjTranspose * K k) p.2 q.2 :=
      tensorGate_apply (1 : Operator n)
        (relabelGate finProdFinEquiv (∑ k : κ, (K k).conjTranspose * K k)) p.1 q.1 p.2 q.2
    rw [hL, hR]
    simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [Matrix.sum_apply, Finset.mul_sum]
  have hone : relabelGate finProdFinEquiv
      (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) = 1 := by
    ext p q
    rw [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply,
      Matrix.one_apply]
    by_cases h : p = q
    · subst h; simp
    · have hne : ¬ ((finProdFinEquiv (m := n) (n := n)).symm p
          = (finProdFinEquiv (m := n) (n := n)).symm q) :=
        fun he => h ((finProdFinEquiv (m := n) (n := n)).symm.injective he)
      rw [if_neg hne, if_neg h]
  have hc : ∑ k, (V k)ᴴ * V k = 1 := by
    calc ∑ k, (V k)ᴴ * V k
        = ∑ k, TensorGate (1 : Operator n)
            (relabelGate finProdFinEquiv ((K k).conjTranspose * K k)) :=
          Finset.sum_congr rfl (fun k _ => hV1 k)
      _ = TensorGate (1 : Operator n)
            (relabelGate finProdFinEquiv (∑ k : κ, (K k).conjTranspose * K k)) := hex
      _ = TensorGate (1 : Operator n)
            (relabelGate finProdFinEquiv
              (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)) := by rw [hK]
      _ = TensorGate (1 : Operator n) (1 : Operator (n * n)) := by rw [hone]
      _ = (1 : Matrix (Fin n × Fin (n * n)) (Fin n × Fin (n * n)) ℂ) := tensorGate_one
  calc ∑ k, qdBranchMarginal (K k) ω ρ
      = ∑ k, PartialTrace (V k * X * (V k)ᴴ) :=
        Finset.sum_congr rfl (fun k _ => hVX k)
    _ = ∑ k, PartialTrace (X * ((V k)ᴴ * V k)) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [partialTrace_discard_sandwich]
      simp only [V, tensorGate_conjTranspose, Matrix.conjTranspose_one, tensorGate_mul,
        Matrix.one_mul]
    _ = PartialTrace (X * (∑ k, (V k)ᴴ * V k)) := by
      rw [Matrix.mul_sum, partialTrace_sum]
    _ = PartialTrace X := by rw [hc, Matrix.mul_one]
    _ = (Matrix.trace ρ) •
        PartialTrace (relabelGate (Equiv.prodComm (Fin n) (Fin n)) ω) := by
      ext i j
      change (∑ a : Fin (n * n),
          ρ ((finProdFinEquiv (m := n) (n := n)).symm a).1
              ((finProdFinEquiv (m := n) (n := n)).symm a).1 *
            ω (((finProdFinEquiv (m := n) (n := n)).symm a).2, i)
              (((finProdFinEquiv (m := n) (n := n)).symm a).2, j)) =
        (Matrix.trace ρ) * ∑ b : Fin n, ω (b, i) (b, j)
      rw [← (finProdFinEquiv (m := n) (n := n)).sum_comp]
      simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Matrix.trace,
        Matrix.diag_apply, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_comm

theorem g8p_corrBranch_one_scalar {n : ℕ} [NeZero n] {κ : Type} [Fintype κ]
    (P : QdLoccTeleport n κ) (U : κ → Operator n) (hU : QdLoccUnitaryCorr P U)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hω : ω.PosSemidef)
    (hperf : QdLoccPerfect P ω) :
    ∀ k : κ, ∃ a : ℂ,
      U k * qdBranchMarginal (P.kraus k) ω (1 : Operator n) * (U k).conjTranspose
        = a • (1 : Operator n) := by
  classical
  let F : κ → Operator n → Operator n :=
    fun k ρ => U k * qdBranchMarginal (P.kraus k) ω ρ * (U k).conjTranspose
  have hadd : ∀ k A B, F k (A + B) = F k A + F k B := by
    intro k A B
    simp only [F, qdBranchMarginal_add, Matrix.mul_add, Matrix.add_mul]
  have hsmul : ∀ k (c : ℂ) A, F k (c • A) = c • F k A := by
    intro k c A
    simp only [F, qdBranchMarginal_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hpos : ∀ k (A : Operator n), A.PosSemidef → (F k A).PosSemidef := by
    intro k A hA
    exact qdCorrectedBranch_positive (P.kraus k) ω hω (U k) A hA
  have hsum : ∀ A, ∑ k, F k A = A := by
    intro A
    have hkey : (∑ k : κ, F k A)
        = ∑ k : κ, P.corr k (qdBranchMarginal (P.kraus k) ω A) :=
      Finset.sum_congr rfl (fun k _ => (hU.2 k _).symm)
    exact hkey.trans (hperf A)
  set m := Fintype.card κ
  let e : κ ≃ Fin m := Fintype.equivFin κ
  have h := qudit_positive_family_scalar_one m n (fun t => F (e.symm t))
    (fun t => hadd (e.symm t)) (fun t => hsmul (e.symm t))
    (fun t => hpos (e.symm t)) (by
      intro A
      rw [← e.sum_comp]
      simpa only [Equiv.symm_apply_apply] using! hsum A)
  intro k
  simpa only [Equiv.symm_apply_apply] using! h (e k)

theorem g8p_branchOne_eq {n : ℕ} [NeZero n] {κ : Type} [Fintype κ]
    (P : QdLoccTeleport n κ) (U : κ → Operator n) (hU : QdLoccUnitaryCorr P U)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hω : ω.PosSemidef)
    (hperf : QdLoccPerfect P ω) :
    ∀ k : κ,
      qdBranchMarginal (P.kraus k) ω (1 : Operator n)
        = U k * qdBranchMarginal (P.kraus k) ω (1 : Operator n) * (U k).conjTranspose := by
  intro k
  obtain ⟨a, ha⟩ := g8p_corrBranch_one_scalar P U hU ω hω hperf k
  have hu : (U k)ᴴ * U k = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using!
      Matrix.mem_unitaryGroup_iff'.mp (hU.1 k)
  have hundo : (U k)ᴴ * (U k * qdBranchMarginal (P.kraus k) ω (1 : Operator n)
      * (U k).conjTranspose) * U k = qdBranchMarginal (P.kraus k) ω (1 : Operator n) := by
    have he : ((U k)ᴴ * U k) * qdBranchMarginal (P.kraus k) ω (1 : Operator n)
        * ((U k)ᴴ * U k) = qdBranchMarginal (P.kraus k) ω (1 : Operator n) := by
      rw [hu, Matrix.one_mul, Matrix.mul_one]
    simpa only [Matrix.mul_assoc] using! he
  rw [ha] at hundo
  have hc : (U k)ᴴ * (a • (1 : Operator n)) * U k = a • (1 : Operator n) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hu]
  rw [hc] at hundo
  exact hundo.symm.trans ha.symm

theorem g8p_bobMarginal {n : ℕ} [NeZero n] {κ : Type} [Fintype κ]
    (P : QdLoccTeleport n κ) (U : κ → Operator n) (hU : QdLoccUnitaryCorr P U)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hω : ω.PosSemidef)
    (hperf : QdLoccPerfect P ω) :
    PartialTrace (relabelGate (Equiv.prodComm (Fin n) (Fin n)) ω)
      = (1 / (n : ℂ)) • (1 : Operator n) := by
  classical
  have hsum1 : (∑ k : κ, qdBranchMarginal (P.kraus k) ω (1 : Operator n)) = 1 := by
    have h := hperf (1 : Operator n)
    have hkey : (∑ k : κ, qdBranchMarginal (P.kraus k) ω (1 : Operator n))
        = ∑ k : κ, U k * qdBranchMarginal (P.kraus k) ω (1 : Operator n) * (U k).conjTranspose :=
      Finset.sum_congr rfl (fun k _ => g8p_branchOne_eq P U hU ω hω hperf k)
    have hkey' : (∑ k : κ, U k * qdBranchMarginal (P.kraus k) ω (1 : Operator n) * (U k).conjTranspose)
        = ∑ k : κ, P.corr k (qdBranchMarginal (P.kraus k) ω (1 : Operator n)) :=
      Finset.sum_congr rfl (fun k _ => (hU.2 k _).symm)
    calc (∑ k : κ, qdBranchMarginal (P.kraus k) ω (1 : Operator n))
        = ∑ k : κ, U k * qdBranchMarginal (P.kraus k) ω (1 : Operator n) * (U k).conjTranspose := hkey
      _ = ∑ k : κ, P.corr k (qdBranchMarginal (P.kraus k) ω (1 : Operator n)) := hkey'
      _ = 1 := h
  have hns := g8p_noSignalling P.kraus P.krausComplete ω (1 : Operator n)
  rw [hsum1, show Matrix.trace (1 : Operator n) = (n : ℂ) by simp] at hns
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  ext i j
  have he := congrArg (fun A : Operator n => A i j) hns
  simp only [Matrix.smul_apply, smul_eq_mul] at he ⊢
  apply (mul_left_cancel₀ hn0)
  rw [← mul_assoc, mul_one_div_cancel hn0, one_mul]
  exact he.symm

theorem g8p_trace_relabelGate {I J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (A : Matrix I I ℂ) :
    Matrix.trace (relabelGate e A) = Matrix.trace A := by
  simp only [Matrix.trace, Matrix.diag_apply, relabelGate, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  rw [← e.sum_comp]
  simp only [Equiv.symm_apply_apply]

theorem g8p_trace_one {n : ℕ} [NeZero n] {κ : Type} [Fintype κ]
    (P : QdLoccTeleport n κ) (U : κ → Operator n) (hU : QdLoccUnitaryCorr P U)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hω : ω.PosSemidef)
    (hperf : QdLoccPerfect P ω) : Matrix.trace ω = 1 := by
  have hm := g8p_bobMarginal P U hU ω hω hperf
  have htr := congrArg Matrix.trace hm
  rw [trace_partialTrace, g8p_trace_relabelGate] at htr
  have h1 : Matrix.trace ((1 / (n : ℂ)) • (1 : Operator n)) = 1 := by
    have htrace : Matrix.trace (1 : Operator n) = (n : ℂ) := by simp
    rw [Matrix.trace_smul, htrace, smul_eq_mul]
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    field_simp
  exact h1 ▸ htr

noncomputable def g8pCol {n : ℕ} (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (s : Fin (n * n)) : QState (Fin n × Fin n) :=
  fun p => CFC.sqrt ω p ((finProdFinEquiv (m := n) (n := n)).symm s)

theorem g8p_sqrt_star {n : ℕ} (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    ∀ a b : Fin n × Fin n, star (CFC.sqrt ω a b) = CFC.sqrt ω b a := by
  intro a b
  have h := congrArg (fun M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ => M b a)
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg ω) : star (CFC.sqrt ω) = CFC.sqrt ω)
  exact h

theorem g8p_sqrt_starRing {n : ℕ} (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    ∀ a b : Fin n × Fin n, (starRingEnd ℂ) (CFC.sqrt ω a b) = CFC.sqrt ω b a :=
  fun a b => g8p_sqrt_star ω a b

theorem g8p_omega_sum_outerProduct {n : ℕ}
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hω : ω.PosSemidef) :
    (∑ s : Fin (n * n), outerProduct (g8pCol ω s)) = ω := by
  ext p q
  simp only [Matrix.sum_apply, outerProduct_apply, g8pCol]
  simp only [g8p_sqrt_starRing]
  rw [← (finProdFinEquiv (m := n) (n := n)).sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
  have h2 : (∑ x : Fin n, ∑ y : Fin n, CFC.sqrt ω p (x, y) * CFC.sqrt ω (x, y) q)
      = ∑ a : Fin n × Fin n, CFC.sqrt ω p a * CFC.sqrt ω a q :=
    (Fintype.sum_prod_type (fun a : Fin n × Fin n => CFC.sqrt ω p a * CFC.sqrt ω a q)).symm
  rw [h2]
  have hsq : (CFC.sqrt ω * CFC.sqrt ω) p q
      = ∑ a : Fin n × Fin n, CFC.sqrt ω p a * CFC.sqrt ω a q := rfl
  rw [← hsq, CFC.sqrt_mul_sqrt_self ω hω.nonneg]

theorem g8p_outerProduct_zero {I : Type} [Fintype I] [DecidableEq I] (φ : QState I)
    (h : outerProduct φ = 0) : φ = 0 := by
  ext p
  have hpp := congrArg (fun M : Matrix I I ℂ => M p p) h
  simp only [outerProduct_apply, Matrix.zero_apply] at hpp
  have hz : φ p * star (φ p) = 0 := hpp
  cases' mul_eq_zero.mp hz with h1 h2
  · exact h1
  · exact star_eq_zero.mp h2

theorem g8p_outerProduct_eq_smul {I : Type} [Fintype I] [DecidableEq I]
    (φ ψ : QState I) (d : ℂ) (h : outerProduct φ = d • outerProduct ψ) :
    ∃ z : ℂ, φ = z • ψ := by
  by_cases hd : d = 0
  · subst hd
    have h0 : outerProduct φ = 0 := by rw [h, zero_smul]
    exact ⟨0, (g8p_outerProduct_zero φ h0).trans (zero_smul ℂ ψ).symm⟩
  · by_cases hψ : ∀ p : I, ψ p = 0
    · have hψ0 : outerProduct ψ = 0 := by
        ext p q
        rw [outerProduct_apply, hψ p, zero_mul, Matrix.zero_apply]
      have hφ0 : outerProduct φ = 0 := by rw [h, hψ0, smul_zero]
      exact ⟨0, (g8p_outerProduct_zero φ hφ0).trans (zero_smul ℂ ψ).symm⟩
    · obtain ⟨p0, hp0⟩ := not_forall.mp hψ
      have hp0s : star (ψ p0) ≠ 0 := fun hs => hp0 (star_eq_zero.mp hs)
      have hφp0 : φ p0 ≠ 0 := by
        intro hh
        have hpp := congrArg (fun M : Matrix I I ℂ => M p0 p0) h
        simp only [outerProduct_apply, Matrix.smul_apply, smul_eq_mul] at hpp
        rw [hh, zero_mul] at hpp
        have hz : d * (ψ p0 * star (ψ p0)) = 0 := hpp.symm
        cases' mul_eq_zero.mp hz with h1 h2
        · exact hd h1
        · exact mul_ne_zero hp0 hp0s h2
      have hcross : ∀ q : I, φ q * ψ p0 = φ p0 * ψ q := by
        intro q
        have h2 := congrArg (fun M : Matrix I I ℂ => M q p0) h
        simp only [outerProduct_apply, Matrix.smul_apply, smul_eq_mul] at h2
        have h3 := congrArg (fun M : Matrix I I ℂ => M p0 p0) h
        simp only [outerProduct_apply, Matrix.smul_apply, smul_eq_mul] at h3
        have h2' : φ q * star (φ p0) = d * (ψ q * star (ψ p0)) := h2
        have h3' : φ p0 * star (φ p0) = d * (ψ p0 * star (ψ p0)) := h3
        have hL : φ q * star (φ p0) * ψ p0 = (φ q * ψ p0) * star (φ p0) := by ac_rfl
        have h4 : d * (ψ q * star (ψ p0)) * ψ p0 = ψ q * (d * (ψ p0 * star (ψ p0))) := by
          ac_rfl
        have hR : d * (ψ q * star (ψ p0)) * ψ p0 = (ψ q * φ p0) * star (φ p0) := by
          rw [h4, ← h3']
          ac_rfl
        have hkey : (φ q * ψ p0) * star (φ p0) = (ψ q * φ p0) * star (φ p0) := by
          rw [← hL, h2', hR]
        have hcancel := mul_right_cancel₀ (star_ne_zero.mpr hφp0) hkey
        exact hcancel.trans (mul_comm (ψ q) (φ p0))
      refine ⟨φ p0 / ψ p0, ?_⟩
      ext q
      have hq := hcross q
      have hgoal : φ q = (φ p0 / ψ p0) * ψ q := by
        have : φ q * ψ p0 = φ p0 * ψ q := hq
        field_simp [hp0] at this ⊢
        exact this
      exact hgoal

theorem g8p_outerProduct_sum_parallel {I : Type} [Fintype I] [DecidableEq I] {κ : Type} [Fintype κ]
    (φ : κ → QState I) (ψ : QState I) (c : ℝ) (hc : 0 ≤ c)
    (h : (∑ k : κ, outerProduct (φ k)) = (c : ℂ) • outerProduct ψ) :
    ∀ k : κ, ∃ w : ℂ, φ k = w • ψ := by
  classical
  set z : ℂ := (Real.sqrt c : ℂ) with hzdef
  have hz : z * (starRingEnd ℂ) z = (c : ℂ) := by
    rw [hzdef]
    simp only [Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  have hsz : outerProduct (z • ψ) = (c : ℂ) • outerProduct ψ := by
    ext i j
    simp only [outerProduct_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, map_mul]
    have hzz : z * ψ i * ((starRingEnd ℂ) z * (starRingEnd ℂ) (ψ j))
        = (z * (starRingEnd ℂ) z) * (ψ i * (starRingEnd ℂ) (ψ j)) := by
      ac_rfl
    rw [hzz, hz]
  have h' : (∑ k : κ, outerProduct (φ k)) = outerProduct (z • ψ) := by
    rw [h, hsz]
  intro k
  have hpos : (outerProduct (φ k)).PosSemidef := outerProduct_posSemidef (φ k)
  have hrest : (outerProduct (z • ψ) - outerProduct (φ k)).PosSemidef := by
    have he : (∑ j ∈ Finset.univ.erase k, outerProduct (φ j))
        = outerProduct (z • ψ) - outerProduct (φ k) := by
      have h1 : (∑ j ∈ Finset.univ.erase k, outerProduct (φ j)) + outerProduct (φ k)
          = outerProduct (z • ψ) := by
        rw [Finset.sum_erase_add (s := Finset.univ) (f := fun j => outerProduct (φ j))
          (a := k) (Finset.mem_univ k), h']
      calc (∑ j ∈ Finset.univ.erase k, outerProduct (φ j))
          = (∑ j ∈ Finset.univ.erase k, outerProduct (φ j)) + outerProduct (φ k)
            - outerProduct (φ k) := by abel
        _ = outerProduct (z • ψ) - outerProduct (φ k) := by rw [h1]
    rw [← he]
    exact Matrix.posSemidef_sum (Finset.univ.erase k) (fun j _ => outerProduct_posSemidef (φ j))
  obtain ⟨d, hd⟩ := psd_le_outerProduct (z • ψ) (outerProduct (φ k)) hpos hrest
  obtain ⟨w, hw⟩ := g8p_outerProduct_eq_smul (φ k) (z • ψ) d hd
  refine ⟨w * z, ?_⟩
  rw [hw, smul_smul]

theorem g8p_eq_smul_of_forall_smul {n : ℕ} [NeZero n] (A : Operator n)
    (h : ∀ v : Fin n → ℂ, ∃ c : ℂ, A *ᵥ v = c • v) : ∃ c : ℂ, A = c • 1 := by
  classical
  have i0 : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  have hoff : ∀ i j : Fin n, i ≠ j → A i j = 0 := by
    intro i j hij
    obtain ⟨c, hc⟩ := h (Qatlib.Foundations.PureStateMath.Ket j)
    have h1 := congrFun hc i
    simp only [mulVec_ket_apply, Pi.smul_apply, smul_eq_mul,
        Qatlib.Foundations.PureStateMath.Ket] at h1
    rw [if_neg hij, mul_zero] at h1
    exact h1
  have hdiag : ∀ i : Fin n, A i i = A i0 i0 := by
    intro i
    by_cases hi : i = i0
    · rw [hi]
    · have hne : i0 ≠ i := Ne.symm hi
      obtain ⟨c, hc⟩ :=
          h (Qatlib.Foundations.PureStateMath.Ket i0 + Qatlib.Foundations.PureStateMath.Ket i)
      have h0 := congrFun hc i0
      simp only [Matrix.mulVec_add, mulVec_ket_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Qatlib.Foundations.PureStateMath.Ket] at h0
      rw [if_neg hne, if_true, add_zero, hoff i0 i hne, add_zero, mul_one] at h0
      have h1 := congrFun hc i
      simp only [Matrix.mulVec_add, mulVec_ket_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Qatlib.Foundations.PureStateMath.Ket] at h1
      rw [if_neg hi, if_true, zero_add, hoff i i0 hi, zero_add, mul_one] at h1
      rw [h1, h0]
  refine ⟨A i0 i0, ?_⟩
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    rw [hdiag i, if_pos rfl, mul_one]
  · rw [if_neg hij, mul_zero, hoff i j hij]
end Qatlib.Concepts.QuditTeleport.QdLoccModel
