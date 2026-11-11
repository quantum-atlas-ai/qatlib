/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.BellReferenceProtocol
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.QuditTeleport.TeleportCore.InstrumentConditioning

/-!
# Bell teleportation instruments and conditional recovery

This module packages the raw and Pauli corrected Bell branch operators as quantum instruments.
Kraus completeness gives valid instruments, and each corrected branch is exactly one quarter of
its input operator.

For density operators the four outcomes are uniform and every conditional corrected state is the
input. The same branch and channel identities hold with an arbitrary finite reference,
expressing the mixed and entangled extensions of teleportation in
[BennettEtAl1993Teleportation].

## Main statements

* `bell_raw_kraus_complete`: completeness of raw and corrected branch families.
* `bell_corrected_channel_and_mass`: branch formulas, probabilities, and the identity channel.
* `bell_conditional_recovery`: exact recovery conditioned on an outcome.
* `bell_reference_channel_identity`: recovery with a reference register.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AdaptiveCP.BranchTrace

namespace Qatlib.Concepts.QuditTeleport.TeleportCore

open Matrix
open scoped ComplexOrder

set_option linter.unusedSectionVars false

/-- Summing a fixed scalar multiple over the four Boolean outcome pairs multiplies its scalar by
four. -/
theorem sum_univ_boolPair_smul {M : Type*} [AddCommMonoid M] [Module ℂ M] (c : ℂ) (x : M) :
    (∑ _o : Bool × Bool, c • x) = ((4 : ℂ) * c) • x := by
  rw [← Finset.smul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_bool, show (2 * 2 : ℕ) = 4 from rfl, ← ofNat_smul_eq_nsmul ℂ 4 x, smul_smul]
  congr 1
  ring

/-- The Pauli X matrix equals its conjugate transpose. -/
theorem pauliX_conjTranspose : PauliXᴴ = PauliX := permMatrix_conjTranspose Bool.not_not

/-- The adjoint of the conditional Pauli product `X^b Z^a` multiplied by that product is the
identity. -/
theorem teleportPauliProd_conj_mul (a b : Bool) :
    (((if b then PauliX else 1) * (if a then PauliZ else 1))ᴴ *
      ((if b then PauliX else 1) * (if a then PauliZ else 1))) = 1 := by
  have hX : ∀ β : Bool, ((if β then PauliX else 1 : Matrix Bool Bool ℂ))ᴴ
      = if β then PauliX else 1 := by
    intro β; cases β <;> simp [pauliX_conjTranspose]
  have hZ : ∀ α : Bool, ((if α then PauliZ else 1 : Matrix Bool Bool ℂ))ᴴ
      = if α then PauliZ else 1 := by
    intro α; cases α <;> simp [pauliZ_conjTranspose]
  have hXX : (if b then PauliX else 1) * (if b then PauliX else 1) = 1 := by
    cases b
    · simp only [if_neg (by decide : ¬(false = true)), one_mul]
    · exact permMatrix_mul_self Bool.not_not
  have hZZ : (if a then PauliZ else 1) * (if a then PauliZ else 1) = 1 := by
    cases a
    · simp only [if_neg (by decide : ¬(false = true)), one_mul]
    · exact pauliZ_mul_self
  rw [Matrix.conjTranspose_mul, hX, hZ, Matrix.mul_assoc,
    ← Matrix.mul_assoc (if b then PauliX else 1) (if b then PauliX else 1)
      (if a then PauliZ else 1), hXX, Matrix.one_mul, hZZ]

/-- Each raw Bell branch Kraus operator has Gram matrix equal to one quarter of the identity. -/
theorem teleportBranchKraus_conj_mul (o : Bool × Bool) :
    (teleportBranchKraus o)ᴴ * teleportBranchKraus o = (1/4:ℂ) • (1:Operator 2) := by
  rw [bell_decoded_branch_operators.2 o, Matrix.conjTranspose_smul,
    teleportRelabelGate_conjTranspose, smul_mul_assoc, mul_smul_comm, smul_smul,
    ← teleportRelabelGate_mul, teleportPauliProd_conj_mul o.1 o.2, teleportRelabelGate_one]
  congr 1
  norm_num

/-- Each corrected Bell branch Kraus operator has Gram matrix equal to one quarter of the
identity. -/
theorem teleportCorrectedKraus_conj_mul (o : Bool × Bool) :
    (teleportCorrection o * teleportBranchKraus o)ᴴ
      * (teleportCorrection o * teleportBranchKraus o) = (1/4:ℂ) • (1:Operator 2) := by
  rw [(bell_pauli_corrections o).2, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.mul_one]
  congr 1
  norm_num

/-- Both the raw Bell branch operators and their corrected counterparts satisfy the Kraus
completeness relation. -/
theorem bell_raw_kraus_complete :
    (∑ o : Bool × Bool, (teleportBranchKraus o)ᴴ * teleportBranchKraus o) = 1 ∧
      (∑ o : Bool × Bool, (teleportCorrection o * teleportBranchKraus o)ᴴ *
        (teleportCorrection o * teleportBranchKraus o)) = 1 := by
  refine ⟨?_, ?_⟩
  ·     rw [Finset.sum_congr rfl (fun o _ => teleportBranchKraus_conj_mul o),
      sum_univ_boolPair_smul, show ((4 : ℂ) * (1 / 4 : ℂ)) = 1 from by norm_num, one_smul]
  · rw [Finset.sum_congr rfl (fun o _ => teleportCorrectedKraus_conj_mul o),
      sum_univ_boolPair_smul, show ((4 : ℂ) * (1 / 4 : ℂ)) = 1 from by norm_num, one_smul]

/-- The four outcome quantum instrument formed from the uncorrected Bell teleportation branch
operators. -/
noncomputable def teleportRawInstrument : Instrument (Bool × Bool) 2 2 :=
  Instrument.ofKraus teleportBranchKraus bell_raw_kraus_complete.1

/-- The four outcome quantum instrument formed by composing each Bell branch operator with Bob's
Pauli correction. -/
noncomputable def teleportCorrectedInstrument : Instrument (Bool × Bool) 2 2 :=
  Instrument.ofKraus (fun o => teleportCorrection o * teleportBranchKraus o)
    bell_raw_kraus_complete.2

/-- The raw instrument branch is conjugation by its decoded Kraus operator, and the corrected
branch is obtained by conjugating the raw branch with Bob's correction. -/
theorem bell_instrument_branches :
    ∀ (ρ : Operator 2) (o : Bool × Bool),
      teleportRawInstrument.branch o ρ = conjBranch (teleportBranchKraus o) ρ ∧
      teleportCorrectedInstrument.branch o ρ
        = conjBranch (teleportCorrection o) (teleportRawInstrument.branch o ρ) := by
  intro ρ o
  refine ⟨rfl, ?_⟩
  show (teleportCorrection o * teleportBranchKraus o) * ρ
      * (teleportCorrection o * teleportBranchKraus o)ᴴ
    = teleportCorrection o * (teleportBranchKraus o * ρ * (teleportBranchKraus o)ᴴ)
        * (teleportCorrection o)ᴴ
  rw [Matrix.conjTranspose_mul]
  simp [Matrix.mul_assoc]

/-- Every corrected Bell instrument branch sends an operator to one quarter of itself. -/
theorem teleportCorrectedInstrument_branch_apply (ρ : Operator 2) (o : Bool × Bool) :
    teleportCorrectedInstrument.branch o ρ = (1/4:ℂ) • ρ := by
  show (teleportCorrection o * teleportBranchKraus o) * ρ
      * (teleportCorrection o * teleportBranchKraus o)ᴴ = (1/4:ℂ) • ρ
  rw [(bell_pauli_corrections o).2, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.one_mul, Matrix.mul_one]
  congr 1
  norm_num

/-- Every corrected Bell branch is one quarter of the input, its probability is one quarter of
the real input trace, and forgetting the outcome gives the identity channel
[BennettEtAl1993Teleportation]. -/
theorem bell_corrected_channel_and_mass :
    ∀ (ρ : Operator 2),
      (∀ o, teleportCorrectedInstrument.branch o ρ = (1/4:ℂ) • ρ ∧
        instrumentProb teleportCorrectedInstrument ρ o = (Matrix.trace ρ).re/4) ∧
      teleportCorrectedInstrument.forget.map ρ = ρ := by
  intro ρ
  refine ⟨fun o => ⟨teleportCorrectedInstrument_branch_apply ρ o, ?_⟩, ?_⟩
  · rw [instrumentProb, teleportCorrectedInstrument_branch_apply ρ o, Matrix.trace_smul,
      smul_eq_mul, Complex.mul_re]
    norm_num
    field_simp
  · rw [Instrument.forget_apply,
      Finset.sum_congr rfl
        (fun o _ => teleportCorrectedInstrument_branch_apply ρ o),
      sum_univ_boolPair_smul, show ((4 : ℂ) * (1 / 4 : ℂ)) = 1 from by norm_num, one_smul]

set_option linter.unusedVariables false in

/-- For every density operator, each Bell outcome has probability one quarter and its
conditional corrected state equals the input [BennettEtAl1993Teleportation]. -/
theorem bell_conditional_recovery :
    ∀ (ρ : Operator 2) (hρ : IsDensityOperator ρ) (o : Bool × Bool),
      instrumentProb teleportCorrectedInstrument ρ o = 1/4 ∧
      (∀ h : 0 < instrumentProb teleportCorrectedInstrument ρ o,
        teleportCorrectedInstrument.conditionalState ρ o h = ρ) := by
  intro ρ hρ o
  have hprob : instrumentProb teleportCorrectedInstrument ρ o = 1/4 := by
    have h := (bell_corrected_channel_and_mass ρ).1 o
    rw [h.2, hρ.2]
    norm_num
  refine ⟨hprob, fun h => ?_⟩
  have hr := (Instrument.conditionalState_reconstruction
    teleportCorrectedInstrument ρ o h).1
  rw [hprob, teleportCorrectedInstrument_branch_apply ρ o] at hr
  have hc := congrArg (fun σ : Operator 2 => (4 : ℂ) • σ) hr
  norm_num [smul_smul] at hc
  exact hc

/-- With any finite reference register, each corrected Bell branch is one quarter of the joint
operator and their sum recovers that operator. -/
theorem bell_reference_channel_identity :
    ∀ (R : ℕ) (ρ : Matrix (Fin 2 × Fin R) (Fin 2 × Fin R) ℂ) (o : Bool × Bool),
      tensorLeft (teleportCorrectedInstrument.branch o) ρ = (1/4:ℂ) • ρ ∧
      (∑ o : Bool × Bool, tensorLeft (teleportCorrectedInstrument.branch o) ρ) = ρ := by
  intro R ρ o
  refine ⟨tensorLeft_eq_smul _
      (fun ρ' => teleportCorrectedInstrument_branch_apply ρ' o) ρ, ?_⟩
  rw [Finset.sum_congr rfl
      (fun o' _ => tensorLeft_eq_smul _
        (fun ρ' => teleportCorrectedInstrument_branch_apply ρ' o') ρ),
    sum_univ_boolPair_smul, show ((4 : ℂ) * (1 / 4 : ℂ)) = 1 from by norm_num, one_smul]

end Qatlib.Concepts.QuditTeleport.TeleportCore
