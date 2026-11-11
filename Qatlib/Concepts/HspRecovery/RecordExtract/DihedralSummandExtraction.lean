/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.RecordExtract.DihedralCosetRecord

/-!
# Extraction of sum and difference phase qubits

This module models extraction from a pair of phase qubits by applying `CNOT` and measuring its
second output. The extracted state is a sum-label or difference-label phase qubit up to a scalar
of norm one, as used by the dihedral sieve [Kuperberg2005].

`dihedralExtractionLaw` gives the complete probability mass function: the two tagged conditional
states each have mass one half. The module also defines Hadamard-basis parity readout and proves
the conditional-state identities needed for extraction.

## Main statements

* `dihedralExtraction`: extraction law on tagged normalized qubits.
* `parityReadout`: computational measurement after a Hadamard gate.
* `dihedralExtractionLaw`: the exact sum/difference extraction distribution.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option warningAsError false


open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Qatlib.Concepts.HspRecovery.RecordExtract
open Matrix
open scoped Classical BigOperators

/-- Apply `CNOT` to two normalized qubits and return the law of the measured second bit together
with the normalized conditional first qubit. -/
noncomputable def dihedralExtraction (ψ φ : QState Bool) (hψ : Normalized ψ)
    (hφ : Normalized φ) : PMF (Bool × NormQ) :=
  let χ : QState (Bool × Bool) := ApplyGate CNOT (TensorState ψ φ)
  (bornDistribution χ
    (normalized_applyGate cnot_unitary (normalized_tensorState hψ hφ))).map
    fun q =>
      let branch : QState Bool := fun a => χ (a, q.2)
      (q.2, actualRecordState branch)

/-- The Boolean Born distribution obtained by applying a Hadamard gate to a normalized qubit. -/
noncomputable def parityReadout (ψ : QState Bool) (hψ : Normalized ψ) : PMF Bool :=
  bornDistribution (ApplyGate Hadamard ψ) (normalized_applyGate hadamard_unitary hψ)

/-- Multiplying a normalized qubit by a complex scalar of norm one preserves normalization. -/
private theorem extraction_unit_scalar_normalized (u : ℂ) (hu : ‖u‖=1)
    (ξ : QState Bool) (hξ : Normalized ξ) : Normalized (u • ξ) := by
  unfold Normalized
  simp only [Pi.smul_apply,smul_eq_mul,norm_mul,hu,one_mul]
  exact hξ

/-- Applying a function after proof-dependent option elimination equals eliminating the option
with that function composed into each branch. -/
private theorem extraction_option_guard_map {α β γ : Type} (x : Option α) (P : Option α → Prop)
    (f : P none → β) (g : ∀ a, P (some a) → β) (hx : P x) (H : β → γ) :
    H (Option.rec (motive := fun o => P o → β) f g x hx) =
      Option.rec (motive := fun o => P o → γ) (fun h => H (f h)) (fun a h => H (g a h)) x hx := by
  cases x <;> rfl

/-- Transporting a proof-dependent subtype construction along equality preserves its underlying
value. -/
private theorem extraction_guarded_subtype_cast {α A : Type} (P : α → Prop) (R : A → Prop)
    {x y : α} (h : x=y) (a : A) (f : P x → R a) (hy : P y) :
    (Eq.ndrec (motive := fun z => P z → Subtype R) (fun hp => ⟨a,f hp⟩) h hy).val=a := by
  cases h
  rfl

/-- An option eliminator whose outputs do not depend on its guard proofs equals ordinary option
elimination. -/
private theorem extraction_option_guard_forget {α β : Type} (x : Option α) (P : Option α → Prop)
    (hx : P x) (b : β) (f : α → β) :
    Option.rec (motive := fun o => P o → β) (fun _ => b) (fun a _ => f a) x hx =
      x.elim b f := by cases x <;> rfl

/-- When `ConditionalState ψ` returns the normalized state `ξ`, `actualRecordState ψ` is the
subtype value represented by `ξ`. -/
theorem actualRecordState_eq_of_some (ψ ξ : QState Bool) (hξ : Normalized ξ) (hc : ConditionalState ψ=some ξ) :
    actualRecordState ψ=⟨ξ,hξ⟩ := by
  apply Subtype.ext
  unfold actualRecordState
  rw [extraction_option_guard_map (H := fun q : NormQ => q.val)]
  simp only [extraction_guarded_subtype_cast]
  rw [extraction_option_guard_forget,hc]
  rfl

/-- The conditional record state of a normalized qubit scaled by `1 / sqrt 2` is the original
normalized qubit. -/
private theorem extraction_half_conditional (ξ : QState Bool) (hξ : Normalized ξ) :
    actualRecordState (fun a => ((1 : ℂ)/Real.sqrt 2)*ξ a)=⟨ξ,hξ⟩ := by
  have hα : ‖(1 : ℂ)/Real.sqrt 2‖^2=1/2 := by
    rw [norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),div_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hmass : MeasureProb (fun a => ((1 : ℂ)/Real.sqrt 2)*ξ a) Finset.univ=1/2 := by
    simp only [MeasureProb,BornProb,norm_mul,mul_pow,hα,← Finset.mul_sum]
    change (1/2 : ℝ)*(∑ a, ‖ξ a‖^2)=1/2
    rw [hξ,mul_one]
  have hs : (Real.sqrt ((1 : ℝ)/2) : ℂ)⁻¹*((1 : ℂ)/Real.sqrt 2)=1 := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1),Real.sqrt_one]
    push_cast
    field_simp
  have hp : PostMeasure (fun a => ((1 : ℂ)/Real.sqrt 2)*ξ a) Finset.univ=ξ := by
    ext a
    simp only [PostMeasure,collapse_apply,Finset.mem_univ,if_true,hmass]
    rw [← mul_assoc,hs,one_mul]
  have hc : ConditionalState (fun a => ((1 : ℂ)/Real.sqrt 2)*ξ a)=some ξ := by
    unfold ConditionalState
    rw [hmass,if_pos (by norm_num : (0 : ℝ) < 1/2),hp]
  exact actualRecordState_eq_of_some _ ξ hξ hc

/-- Extracting phase qubits with labels `k` and `ℓ` produces the tagged sum and difference
states, up to scalars of norm one, each with mass one half and zero mass elsewhere
[Kuperberg2005]. -/
theorem dihedralExtractionLaw (N : ℕ) [NeZero N] (s k ℓ : ZMod N) :
    ∃ xiPlus xiMinus : QState Bool, ∃ _hPlus : Normalized xiPlus, ∃ _hMinus : Normalized xiMinus,
    ∃ uPlus uMinus : ℂ, ‖uPlus‖=1 ∧ ‖uMinus‖=1 ∧
      xiPlus=uPlus • dihedralQubitState N s (k+ℓ) ∧
      xiMinus=uMinus • dihedralQubitState N s (k-ℓ) ∧
      ∀ (b : Bool) (ξ : QState Bool) (hξ : Normalized ξ),
        dihedralExtraction (dihedralQubitState N s k) (dihedralQubitState N s ℓ)
          (normalized_dihedralQubitState N s k) (normalized_dihedralQubitState N s ℓ) (b,⟨ξ,hξ⟩) =
          if (b=false ∧ ξ=xiPlus) ∨ (b=true ∧ ξ=xiMinus) then 1/2 else 0 := by
  let xiPlus := dihedralQubitState N s (k+ℓ)
  let u := dihedralQubitPhase N s ℓ
  let xiMinus := u • dihedralQubitState N s (k-ℓ)
  have hu : ‖u‖=1 := norm_dihedralQubitPhase N s ℓ
  have hPlus : Normalized xiPlus := normalized_dihedralQubitState N s (k+ℓ)
  have hMinus : Normalized xiMinus :=
      extraction_unit_scalar_normalized u hu _ (normalized_dihedralQubitState N s (k-ℓ))
  let χ := ApplyGate CNOT (TensorState (dihedralQubitState N s k) (dihedralQubitState N s ℓ))
  have hplus : dihedralQubitPhase N s (k+ℓ)=dihedralQubitPhase N s k*dihedralQubitPhase N s ℓ := by
    simp only [dihedralQubitPhase_eq_stdAddChar,add_mul,ZMod.stdAddChar.map_add_eq_mul]
  have hminus : u*dihedralQubitPhase N s (k-ℓ)=dihedralQubitPhase N s k := by
    have h : dihedralQubitPhase N s ((k-ℓ)+ℓ)=dihedralQubitPhase N s (k-ℓ)*dihedralQubitPhase N s ℓ := by
      simp only [dihedralQubitPhase_eq_stdAddChar,add_mul,ZMod.stdAddChar.map_add_eq_mul]
    have he : dihedralQubitPhase N s k=dihedralQubitPhase N s (k-ℓ)*dihedralQubitPhase N s ℓ := by
      simpa only [sub_add_cancel] using h
    exact (mul_comm u _).trans he.symm
  have hbranch (a b : Bool) : χ (a,b)=((1 : ℂ)/Real.sqrt 2)*(if b then xiMinus else xiPlus) a := by
    dsimp [χ]
    rw [CNOT,applyGate_permMatrix cnotFlip_involutive]
    cases a <;> cases b <;>
      simp only [cnotFlip,TensorState,dihedralQubitState,xiPlus,xiMinus,u,Pi.smul_apply,smul_eq_mul,
        Bool.xor_false,Bool.xor_true,Bool.not_false,Bool.not_true,Bool.cond_false,Bool.cond_true,Bool.false_eq_true,if_false,if_true]
    · ring
    · ring
    · rw [hplus]; ring
    · rw [show dihedralQubitPhase N s k=u*dihedralQubitPhase N s (k-ℓ) from hminus.symm]; ring
  have hbMass (a b : Bool) : BornProb χ (a,b)=1/4 := by
    unfold BornProb
    rw [hbranch,norm_mul,mul_pow]
    have hα : ‖(1 : ℂ)/Real.sqrt 2‖^2=1/2 := by
      rw [norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _),div_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [hα]
    cases b
    · change (1/2 : ℝ)*BornProb (dihedralQubitState N s (k+ℓ)) a=1/4
      rw [dihedralQubitState_born]
      norm_num
    · change (1/2 : ℝ)*‖u*dihedralQubitState N s (k-ℓ) a‖^2=1/4
      rw [norm_mul,hu,one_mul,show ‖dihedralQubitState N s (k-ℓ) a‖^2=1/2 from dihedralQubitState_born _ _ _ _]
      norm_num
  have hcond (b : Bool) : actualRecordState (fun a => χ (a,b))=
      if b then ⟨xiMinus,hMinus⟩ else (⟨xiPlus,hPlus⟩ : NormQ) := by
    simp only [hbranch]
    cases b
    · exact extraction_half_conditional xiPlus hPlus
    · exact extraction_half_conditional xiMinus hMinus
  refine ⟨xiPlus,xiMinus,hPlus,hMinus,1,u,by norm_num,hu,by simp [xiPlus], rfl,?_⟩
  intro b ξ hξ
  dsimp only [χ] at hbMass hcond
  unfold dihedralExtraction
  rw [PMF.map_apply,tsum_fintype,Fintype.sum_prod_type]
  simp only [bornDistribution_apply]
  simp only [hbMass,hcond,Fintype.sum_bool]
  cases b <;> simp [Subtype.mk.injEq,eq_comm] <;> split_ifs <;> norm_num
  all_goals
    have hn : (2 : NNReal)⁻¹=(4 : NNReal)⁻¹+(4 : NNReal)⁻¹ := by norm_num
    have he := congrArg (fun x : NNReal => (x : ENNReal)) hn
    (try dsimp only at he)
    rw [ENNReal.coe_add,ENNReal.coe_inv (by norm_num : (2 : NNReal) ≠ 0),
      ENNReal.coe_inv (by norm_num : (4 : NNReal) ≠ 0)] at he
    norm_num at he
    exact he

end Qatlib.Concepts.HspRecovery.RecordExtract
