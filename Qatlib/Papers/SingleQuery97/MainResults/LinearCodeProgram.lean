/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.ActualQueryWord
import Qatlib.Papers.SingleQuery97.MainResults.FourierReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.SingleQuery97.MainResults.LinearCodeProgram

open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Foundations.PureStateMath.BornBridge
open FourierReadout ActualQuery
open scoped ComplexConjugate

variable {A m n : ℕ} [NeZero A]

def encode (g : Fin m → Fin n → ZMod A) (s : Fin m → ZMod A) : Fin n → ZMod A :=
  fun j => ∑ i, s i * g i j

def answer (y x : Fin n → ZMod A) : ZMod A := ∑ j, x j * y j

def response (g : Fin m → Fin n → ZMod A) (y : Fin n → ZMod A) : Fin m → ZMod A :=
  fun i => answer y (g i)

theorem answer_encode (g : Fin m → Fin n → ZMod A) (y : Fin n → ZMod A)
    (s : Fin m → ZMod A) : answer y (encode g s) = dotHom (response g y) s := by
  simp only [answer, encode, response, dotHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

noncomputable def positiveFourier (A m : ℕ) [NeZero A] :
    Matrix (Fin m → ZMod A) (Fin m → ZMod A) ℂ :=
  fourierGate (negativeDotCharacterEquiv A m)

theorem positiveFourier_unitary (A m : ℕ) [NeZero A] :
    positiveFourier A m ∈ Matrix.unitaryGroup (Fin m → ZMod A) ℂ :=
  fourierGate_unitary _

theorem positiveFourier_zero (A m : ℕ) [NeZero A] :
    ApplyGate (positiveFourier A m) (Ket 0) = Uniform (Fin m → ZMod A) := by
  funext s
  rw [positiveFourier, applyGate_fourierGate, fourier_ket]
  simp [Uniform, fourierScale]

theorem positiveFourier_response (z : Fin m → ZMod A) :
    ApplyGate (positiveFourier A m) (characterState (-dotCharacter z)) = Ket z := by
  exact actual_positive_fourier_readout A m z

theorem prepare_answer (A : ℕ) [NeZero A] :
    ApplyGate (zmodQFTGate (N:=A))ᴴ (Ket (-1 : ZMod A)) = charState (1:ZMod A) := by
  have h := zmodQFTGate_unitary (N:=A) (NeZero.pos A)
  have hinv := (Matrix.mem_unitaryGroup_iff').mp h
  rw [Matrix.star_eq_conjTranspose] at hinv
  calc
    _ = ApplyGate (zmodQFTGate (N:=A))ᴴ
        (ApplyGate (zmodQFTGate (N:=A)) (charState 1)) := by
      rw [applyGate_zmodQFTGate, zmodQFT_charState]
    _ = _ := by rw [← applyGate_mul, hinv, applyGate_one]

noncomputable def word (g : Fin m → Fin n → ZMod A) :
    Circuit (((Fin m → ZMod A) × (Fin n → ZMod A)) × ZMod A) :=
  [Step.gate (TensorGate 1 (zmodQFTGate (N:=A))ᴴ),
   Step.gate (TensorGate (TensorGate (positiveFourier A m) 1) 1)] ++
  encodedQueryWord (R:=ZMod A) (encode g) ++
  [Step.gate (TensorGate (TensorGate (positiveFourier A m) 1) 1)]

theorem word_unitary (g : Fin m → Fin n → ZMod A) : IsUnitaryCircuit (word g) := by
  have h1 (I : Type) [Fintype I] [DecidableEq I] :
      (1 : Matrix I I ℂ) ∈ Matrix.unitaryGroup I ℂ := (Matrix.unitaryGroup I ℂ).one_mem
  have hF := tensorGate_unitary
    (tensorGate_unitary (positiveFourier_unitary A m) (h1 (Fin n → ZMod A))) (h1 (ZMod A))
  simp only [word, isUnitaryCircuit_append, isUnitaryCircuit_gate,
    isUnitaryCircuit_nil, and_true]
  exact ⟨⟨⟨tensorGate_unitary (h1 _) (conjTranspose_mem_unitaryGroup
    (zmodQFTGate_unitary (N:=A) (NeZero.pos A))), hF⟩,
    encodedQueryWord_unitary _⟩, hF⟩

theorem word_resources (g : Fin m → Fin n → ZMod A) :
    QueryCount (word g) = 1 ∧ GateCount (word g) = 5 := by
  constructor <;> rfl

noncomputable def oracle (y : Fin n → ZMod A) :
    Matrix (((Fin m → ZMod A) × (Fin n → ZMod A)) × ZMod A)
      (((Fin m → ZMod A) × (Fin n → ZMod A)) × ZMod A) ℂ :=
  AddOracle (fun p => answer y p.2)

theorem oracle_unitary (y : Fin n → ZMod A) :
    oracle (m:=m) y ∈ Matrix.unitaryGroup _ ℂ := addOracle_unitary _

theorem run_word (g : Fin m → Fin n → ZMod A) (y : Fin n → ZMod A) :
    Run (oracle y) (word g)
      (TensorState (TensorState (Ket 0) (Ket 0)) (Ket (-1 : ZMod A))) =
    TensorState (TensorState (Ket (response g y)) (Ket 0)) (charState (1:ZMod A)) := by
  have hη : charState (1:ZMod A) = (fun b : ZMod A =>
      (Real.sqrt (A:ℝ):ℂ)⁻¹ * ZMod.stdAddChar b) := by
    funext b
    rw [charState_apply, one_mul]
  have hk := encodedQueryWord_clean (encode g) (answer y)
    (ZMod.stdAddChar (N:=A)) (Real.sqrt (A:ℝ):ℂ)⁻¹ (Uniform (Fin m → ZMod A))
  rw [← hη] at hk
  have hp : (fun s : Fin m → ZMod A =>
      ZMod.stdAddChar (-answer y (encode g s)) * Uniform (Fin m → ZMod A) s) =
      characterState (-dotCharacter (response g y)) := by
    funext s
    simp only [answer_encode, characterState, AddChar.neg_apply,
      dotCharacter, AddChar.compAddMonoidHom_apply, AddChar.map_neg_eq_conj]
    simp only [Uniform, fourierScale]
    ring
  rw [hp] at hk
  simp only [word, run_append, Run, applyGate_tensorGate, applyGate_one,
    prepare_answer, positiveFourier_zero]
  rw [show Run (oracle y) (encodedQueryWord (encode g))
      (TensorState (TensorState (Uniform (Fin m → ZMod A)) (Ket 0)) (charState 1)) = _ from hk]
  simp only [applyGate_tensorGate, applyGate_one, positiveFourier_response]

theorem normalized_output (g : Fin m → Fin n → ZMod A) (y : Fin n → ZMod A) :
    Normalized (Run (oracle y) (word g)
      (TensorState (TensorState (Ket 0) (Ket 0)) (Ket (-1 : ZMod A)))) := by
  rw [run_word]
  exact normalized_tensorState (normalized_tensorState (normalized_ket _) (normalized_ket _))
    (normalized_charState _)

theorem response_probability (g : Fin m → Fin n → ZMod A) (y : Fin n → ZMod A) :
    MeasureProb (Run (oracle y) (word g)
      (TensorState (TensorState (Ket 0) (Ket 0)) (Ket (-1 : ZMod A))))
      (({response g y} ×ˢ Finset.univ) ×ˢ Finset.univ) = 1 := by
  rw [run_word, measureProb_tensorState_left (normalized_charState _),
    measureProb_tensorState_left (normalized_ket _)]
  simp [MeasureProb, bornProb_ket]

theorem decoded_response (g : Fin m → Fin n → ZMod A)
    (Y : Set (Fin n → ZMod A)) (decode : (Fin m → ZMod A) → (Fin n → ZMod A))
    (hdecode : ∀ y ∈ Y, decode (response g y) = y) (y : Fin n → ZMod A) (hy : y ∈ Y) :
    decode (response g y) = y ∧ QueryCount (word g) = 1 ∧
    MeasureProb (Run (oracle y) (word g)
      (TensorState (TensorState (Ket 0) (Ket 0)) (Ket (-1 : ZMod A))))
      (({response g y} ×ˢ Finset.univ) ×ˢ Finset.univ) = 1 :=
  ⟨hdecode y hy, (word_resources g).1, response_probability g y⟩

theorem born_first_marginal {S X : Type} [Fintype S] [DecidableEq S]
    [Fintype X] [DecidableEq X] (z : S) (φ : QState X) (hφ : Normalized φ) :
    (bornDistribution (TensorState (Ket z) φ)
      (normalized_tensorState (normalized_ket z) hφ)).map Prod.fst = PMF.pure z := by
  classical
  have hs : (∑ x, ENNReal.ofReal (BornProb φ x)) = 1 := by
    simpa only [tsum_fintype, bornDistribution_apply] using (bornDistribution φ hφ).tsum_coe
  ext s
  by_cases hz : s = z
  · subst s
    simp [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, bornDistribution_apply,
      bornProb_tensorState, bornProb_ket, hs, PMF.pure_apply]
  · simp [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, bornDistribution_apply,
      bornProb_tensorState, bornProb_ket, hz, PMF.pure_apply]

noncomputable def outputLaw (g : Fin m → Fin n → ZMod A) (y : Fin n → ZMod A) :
    PMF (((Fin m → ZMod A) × (Fin n → ZMod A)) × ZMod A) :=
  bornDistribution (Run (oracle y) (word g)
    (TensorState (TensorState (Ket 0) (Ket 0)) (Ket (-1 : ZMod A)))) (normalized_output g y)

theorem outputLaw_response (g : Fin m → Fin n → ZMod A) (y : Fin n → ZMod A) :
    (outputLaw g y).map (fun p => p.1.1) = PMF.pure (response g y) := by
  have hstate : outputLaw g y = bornDistribution
      (TensorState (TensorState (Ket (response g y)) (Ket 0)) (charState (1:ZMod A)))
      (normalized_tensorState (normalized_tensorState (normalized_ket _) (normalized_ket _))
        (normalized_charState _)) := by
    ext p
    simp only [outputLaw, bornDistribution_apply, run_word]
  rw [hstate]
  simp only [tensorState_ket_ket]
  rw [show (fun p : (((Fin m → ZMod A) × (Fin n → ZMod A)) × ZMod A) => p.1.1) =
      Prod.fst ∘ Prod.fst from rfl, ← PMF.map_comp]
  rw [born_first_marginal _ _ (normalized_charState (1:ZMod A)), PMF.pure_map]

theorem outputLaw_decoded (g : Fin m → Fin n → ZMod A) (y : Fin n → ZMod A)
    {Y : Type} (decode : (Fin m → ZMod A) → Y) :
    (outputLaw g y).map (fun p => decode p.1.1) = PMF.pure (decode (response g y)) := by
  rw [show (fun p : (((Fin m → ZMod A) × (Fin n → ZMod A)) × ZMod A) => decode p.1.1) =
      decode ∘ (fun p => p.1.1) from rfl, ← PMF.map_comp, outputLaw_response, PMF.pure_map]

end Qatlib.Papers.SingleQuery97.MainResults.LinearCodeProgram
