/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerRun
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

noncomputable section

namespace Qatlib.Concepts.PauliClifford.PauliAlgebra

open scoped BigOperators
open Qatlib
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Matrix

theorem relabel_star {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (A : Matrix I I ℂ) : (relabelGate e A)ᴴ = relabelGate e Aᴴ := by
  ext i j
  rfl

theorem relabel_add {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (A B : Matrix I I ℂ) : relabelGate e (A+B) = relabelGate e A+relabelGate e B := by
  ext i j
  rfl

theorem relabel_trace {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (A : Matrix I I ℂ) : Matrix.trace (relabelGate e A) = Matrix.trace A := by
  exact e.symm.sum_comp (fun i => A i i)

def branchK {n : ℕ} (p : PauliElem n) (b : Bool) : Operator (2^n) :=
  relabelGate (bitVecEquiv n) (pauliBranchProjector p b)

theorem branch_gram {n : ℕ} (p : PauliElem n) (hp : IsHermitianPauli p) (b : Bool) :
    (pauliBranchProjector p b)ᴴ * pauliBranchProjector p b = pauliBranchProjector p b := by
  have h := (isStarProjection_iff'.mp (pauliBranchProjector_isOrthogonalProjector hp b))
  have hs : (pauliBranchProjector p b)ᴴ = pauliBranchProjector p b := h.2
  rw [hs]
  exact h.1

theorem branchK_complete {n : ℕ} (p : PauliElem n) (hp : IsHermitianPauli p) :
    (∑ b : Bool, (branchK p b)ᴴ*branchK p b) = 1 := by
  have hK (b : Bool) : (branchK p b)ᴴ*branchK p b = branchK p b := by
    rw [branchK,relabel_star,← Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul,branch_gram p hp b]
  simp_rw [hK]
  rw [Fintype.sum_bool]
  rw [branchK,branchK,← relabel_add,pauliBranchProjector_add,Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_one]

def pauliInstrument {n : ℕ} (p : PauliElem n) (hp : IsHermitianPauli p) :
    Instrument Bool (2^n) (2^n) := Instrument.ofKraus (branchK p) (branchK_complete p hp)

theorem pauliInstrument_probability {n : ℕ} (p : PauliElem n) (hp : IsHermitianPauli p)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (b : Bool) :
    instrumentProb (pauliInstrument p hp) (relabelGate (bitVecEquiv n) ρ) b =
      (Matrix.trace (pauliBranchProjector p b * ρ * (pauliBranchProjector p b)ᴴ)).re := by
  unfold instrumentProb pauliInstrument
  rw [Instrument.ofKraus_branch]
  simp only [branchK,relabel_star,← Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul,relabel_trace]

theorem pauliInstrument_moment {n : ℕ} (p : PauliElem n) (hp : IsHermitianPauli p)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (b : Bool) :
    instrumentProb (pauliInstrument p hp) (relabelGate (bitVecEquiv n) ρ) b =
      if b then ((Matrix.trace ρ).re+(Matrix.trace (op p*ρ)).re)/2
      else ((Matrix.trace ρ).re-(Matrix.trace (op p*ρ)).re)/2 := by
  rw [pauliInstrument_probability]
  have htrace : Matrix.trace (pauliBranchProjector p b * ρ * (pauliBranchProjector p b)ᴴ) =
      Matrix.trace (pauliBranchProjector p b * ρ) := by
    rw [Matrix.trace_mul_cycle,branch_gram p hp b]
  rw [htrace]
  cases b <;> norm_num [pauliBranchProjector,Matrix.smul_mul,Matrix.add_mul,Matrix.sub_mul,
    Matrix.trace_smul,Matrix.trace_add,Matrix.trace_sub,smul_eq_mul,Complex.mul_re] <;> ring

theorem conjugate_star {n : ℕ} (U A : Matrix (Reg n) (Reg n) ℂ) :
    (conjugate U A)ᴴ = conjugate U Aᴴ := by
  simp only [conjugate,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]

theorem measurement_branch_covariance {n : ℕ} (gates : List (CliffordGate n))
    (hg : ∀ g ∈ gates, legalGate g) (p : PauliElem n) (b : Bool)
    (ρ : Matrix (Reg n) (Reg n) ℂ) :
    pauliBranchProjector (actionWord gates p) b * conjugate (Uword gates) ρ *
      (pauliBranchProjector (actionWord gates p) b)ᴴ =
    conjugate (Uword gates) (pauliBranchProjector p b * ρ * (pauliBranchProjector p b)ᴴ) := by
  rw [branch_projector_covariance gates hg,conjugate_star,
    ← conjugate_mul (Uword gates) (Uword_unitary gates hg),
    ← conjugate_mul (Uword gates) (Uword_unitary gates hg)]

theorem pauliInstrument_run_probability {n k : ℕ} (gates : List (CliffordGate n))
    (hg : ∀ g ∈ gates, legalGate g) (t : Tableau n k)
    (p : PauliElem n) (hp : IsHermitianPauli p) (b : Bool) :
    instrumentProb (pauliInstrument (actionWord gates p) ((actionWord_hermitian_iff gates p).mpr hp))
      (codeDensity (run gates t)) b = instrumentProb (pauliInstrument p hp) (codeDensity t) b := by
  unfold codeDensity
  rw [pauliInstrument_probability,pauliInstrument_probability,codeDensityMatrix_run_covariance gates hg,
    measurement_branch_covariance gates hg,conjugate_trace _ (Uword_unitary gates hg)]

end Qatlib.Concepts.PauliClifford.PauliAlgebra
