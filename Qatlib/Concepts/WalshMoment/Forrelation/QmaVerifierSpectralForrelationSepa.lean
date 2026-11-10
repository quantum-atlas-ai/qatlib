/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalshMoment.Forrelation.QmaVerifierSpectralForrelationStat
import Qatlib.Concepts.WalshMoment.Forrelation.SpectralForrelationBasicsSepa
import Qatlib.Concepts.QueryWordCore.QueryMachinery.NegativeAdversary
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.QmaCompleteness.WitnessSampler
open Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025

namespace Qatlib.Concepts.WalshMoment.Forrelation.QmaVerifierSpectralForrelationSepa

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Matrix

section G2

variable {n : ℕ}

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
    rw [if_neg this]
    ring
  · intro hc
    exact absurd (Finset.mem_univ (e p)) hc

private theorem perm_unitary {I : Type} [Fintype I] [DecidableEq I] (e : I ≃ I) :
    (Matrix.of fun p q => if e p = q then (1 : ℂ) else 0) ∈ Matrix.unitaryGroup I ℂ := by
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
      rw [if_neg h1]
      ring
    · intro hc
      exact absurd (Finset.mem_univ (e.symm p)) hc
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext p q
  have hconv : (∑ x, (starRingEnd ℂ) (if e x = p then (1 : ℂ) else 0) *
        (if e x = q then (1 : ℂ) else 0))
      = (∑ r, (if e r = p then (1 : ℂ) else 0) * (if e r = q then (1 : ℂ) else 0)) :=
    Finset.sum_congr rfl fun r _ => by
      by_cases hr : e r = p <;> simp [hr]
  exact hconv.trans (hsum p q)

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

private def toffoliE (n : ℕ) : ForrSpace n (Reg n × Bool) ≃ ForrSpace n (Reg n × Bool) where
  toFun p := (p.1, p.2.1, (p.2.2.1, p.2.2.2 ^^ (p.1.2 && p.2.1.2)))
  invFun p := (p.1, p.2.1, (p.2.2.1, p.2.2.2 ^^ (p.1.2 && p.2.1.2)))
  left_inv p := by
    ext <;> simp
  right_inv p := by
    ext <;> simp

private def permGate {I : Type} [DecidableEq I] (e : I ≃ I) : Matrix I I ℂ :=
  Matrix.of fun p q => if e p = q then (1 : ℂ) else 0

private theorem applyGate_permGate {I : Type} [Fintype I] [DecidableEq I]
    (e : I ≃ I) (φ : QState I) (p : I) :
    ApplyGate (permGate e) φ p = φ (e p) := applyGate_perm e φ p

private noncomputable def ctrlHGate (n : ℕ) : Matrix (Reg n × Bool) (Reg n × Bool) ℂ :=
  Matrix.of fun p q =>
    if p.2 = q.2 then
      (if p.2 then HadamardN n p.1 q.1 else if p.1 = q.1 then (1 : ℂ) else 0)
    else 0

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

private noncomputable def verifierDataH (n : ℕ) :
    Matrix (ForrSpace n (Reg n × Bool)) (ForrSpace n (Reg n × Bool)) ℂ :=
  TensorGate (TensorGate (HadamardN n) (1 : Matrix Bool Bool ℂ)) 1

private theorem verifierDataH_unitary (n : ℕ) :
    verifierDataH n ∈ Matrix.unitaryGroup (ForrSpace n (Reg n × Bool)) ℂ :=
  tensorGate_unitary (tensorGate_unitary (hadamardN_unitary n) (Submonoid.one_mem _))
    (Submonoid.one_mem _)

private theorem applyGate_verifierDataH (n : ℕ)
    (φ : QState (ForrSpace n (Reg n × Bool))) (p : ForrSpace n (Reg n × Bool)) :
    ApplyGate (verifierDataH n) φ p =
      ∑ z, HadamardN n p.1.1 z * φ ((z,p.1.2),p.2) := by
  classical
  unfold ApplyGate verifierDataH
  rw [advTensor_mulVec]
  simp only [TensorGate,Fintype.sum_prod_type]
  cases hb : p.1.2 <;> simp [hb,Matrix.one_apply]

private noncomputable def verifierCircuit (n : ℕ) : TOCircuit (ForrSpace n (Reg n × Bool)) :=
  [.gate (permGate (swapXW n)),.queryS,.gate (verifierDataH n),
    .gate (permGate (swapXY n)),.queryU]

private theorem verifierCircuit_unitary (n : ℕ) : IsUnitaryTOCircuit (verifierCircuit n) := by
  intro G hG
  have h : G = permGate (swapXW n) ∨ G = verifierDataH n ∨ G = permGate (swapXY n) := by
    simpa [verifierCircuit] using hG
  rcases h with rfl | rfl | rfl
  · exact perm_unitary _
  · exact verifierDataH_unitary n
  · exact perm_unitary _

private theorem verifier_accept_amplitude (n : ℕ) (S U : Reg n → Bool)
    (ψ : QState (Reg n)) (x y w : Reg n) (o : Bool) :
    TORun (forrBitOracleS n S (Reg n × Bool)) (forrBitOracleU n U (Reg n × Bool))
      (verifierCircuit n) (witnessEmbed n ψ) ((x,true),(y,true),(w,o)) =
    if x = ZeroStr n ∧ w = ZeroStr n ∧ o = false then
      ((charProjector n U * HadamardN n * charProjector n S) *ᵥ ψ) y else 0 := by
  classical
  simp only [verifierCircuit,TORun,applyGate_forrBitOracleU,applyGate_permGate,
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

theorem qmaVerifierSpectralForrelation : QmaVerifierSpectralForrelation := by
  classical
  intro n S U
  let E : Finset (ForrSpace n (Reg n × Bool)) :=
    Finset.univ.filter fun p => p.1.2 = true ∧ p.2.1.2 = true
  refine ⟨verifierCircuit n,E,verifierCircuit_unitary n,by rfl,by rfl,?_⟩
  intro ψ
  rw [forrWitnessMass,norm_toEuclidean_fromVec_sq]
  simp only [E,MeasureProb,Finset.sum_filter,BornProb,Fintype.sum_prod_type,
    Fintype.sum_bool]
  simp [verifier_accept_amplitude,ite_and]
  simp_rw [apply_ite (fun z : ℂ => ‖z‖)]
  simp [ite_pow]

end G2

end Qatlib.Concepts.WalshMoment.Forrelation.QmaVerifierSpectralForrelationSepa
