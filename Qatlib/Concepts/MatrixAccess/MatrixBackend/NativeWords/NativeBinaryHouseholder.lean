/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeBinaryPairUnitary
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.LchsSimulation.StaticLchs
/-! Source-compatible binary label model of the complete supplied PREP.
The valid-label frame transports V, its true adjoint and the origin
reflection to the existing logical table. Padding of the PREP is -I. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical

/-- Construction for source Binary Givens in the native binary householder model. -/
def sourceBinaryGivens (m n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m) :
    List (Fin n × Circle) → Matrix (Reg m) (Reg m) ℂ
  | [] => 1
  | r::rs => sourceBinaryPair m n h r.1 (pivots r.1) r.2 * sourceBinaryGivens m n h pivots rs

/-- The constructed finite matrix is unitary under the stated hypotheses. -/
theorem sourceBinaryGivens_unitary (m n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hp : ∀ r∈rs,(r.1.val+1).testBit (pivots r.1).val=true) :
    sourceBinaryGivens m n h pivots rs ∈ unitaryGroup (Reg m) ℂ := by
  induction rs with
  | nil => exact (unitaryGroup (Reg m) ℂ).one_mem
  | cons r rs ih =>
    exact (unitaryGroup (Reg m) ℂ).mul_mem
      (sourceBinaryPair_unitary m n h r.1 (pivots r.1) r.2 (hp r (by simp)))
      (ih (fun r hr => hp r (by simp [hr])))

/-- The actual native matrix satisfies the stated frame-transport identity. -/
theorem sourceBinaryGivens_frame (m n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hp : ∀ r∈rs,(r.1.val+1).testBit (pivots r.1).val=true) :
    sourceBinaryGivens m n h pivots rs * sourceLabelFrame m n h =
      sourceLabelFrame m n h * tableGivens rs := by
  induction rs with
  | nil => simp [sourceBinaryGivens, tableGivens, tableGivensWord, evaluate]
  | cons r rs ih =>
    have ht := ih (fun r hr => hp r (by simp [hr]))
    have hh := sourceBinaryPair_frame m n h r.1 (pivots r.1) r.2 (hp r (by simp))
    change (sourceBinaryPair m n h r.1 (pivots r.1) r.2 * sourceBinaryGivens m n h pivots rs) *
      sourceLabelFrame m n h = sourceLabelFrame m n h *
        (weightTwoLevel r.1 (r.2.c : ℂ) (r.2.s : ℂ) * tableGivens rs)
    rw [Matrix.mul_assoc, ht, ← Matrix.mul_assoc, hh, Matrix.mul_assoc]

/-- The actual native matrix satisfies the stated frame-transport identity. -/
theorem sourceBinaryGivens_adjoint_frame (m n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hp : ∀ r∈rs,(r.1.val+1).testBit (pivots r.1).val=true) :
    (sourceBinaryGivens m n h pivots rs)ᴴ * sourceLabelFrame m n h =
      sourceLabelFrame m n h * (tableGivens rs)ᴴ := by
  let B := sourceBinaryGivens m n h pivots rs
  let E := sourceLabelFrame m n h
  let T := tableGivens rs
  have hb : Bᴴ*B=1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using
      sourceBinaryGivens_unitary m n h pivots rs hp
  have ht : T*Tᴴ=1 := by
    simpa only [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] using tableGivens_unitary rs
  have hf : B*E=E*T := sourceBinaryGivens_frame m n h pivots rs hp
  change Bᴴ*E=E*Tᴴ
  calc
    Bᴴ*E = Bᴴ*(E*(T*Tᴴ)) := by rw [ht, Matrix.mul_one]
    _ = Bᴴ*((E*T)*Tᴴ) := by rw [Matrix.mul_assoc]
    _ = Bᴴ*((B*E)*Tᴴ) := by rw [hf]
    _ = E*Tᴴ := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hb, Matrix.one_mul]

/-- The emitted program has the displayed exact basis or coherent-fibre action. -/
private theorem origin_reflect_ket {I : Type*} [Fintype I] [DecidableEq I] (z a : I) :
    ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket z)) *ᵥ Qatlib.Foundations.PureStateMath.Ket a =
      (if a=z then (1 : ℂ) else -1) • Qatlib.Foundations.PureStateMath.Ket a := by
  rw [show (ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket z)) *ᵥ Qatlib.Foundations.PureStateMath.Ket a) =
    ApplyGate (ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket z))) (Qatlib.Foundations.PureStateMath.Ket a) from rfl, applyGate_reflectionAbout]
  change (2 : ℂ) • ((outerProduct (Qatlib.Foundations.PureStateMath.Ket z)) *ᵥ Qatlib.Foundations.PureStateMath.Ket a) - Qatlib.Foundations.PureStateMath.Ket a = _
  rw [outerProduct_mulVec, inner_ket_ket]
  by_cases ha : a=z
  · subst a
    simp
    module
  · rw [ite_eq_right (Ne.symm ha), zero_smul, smul_zero, zero_sub, ite_eq_right ha]
    simp

/-- The emitted program has the displayed exact basis or coherent-fibre action. -/
theorem sourceOrigin_reflect_ket {I : Type*} [Fintype I] [DecidableEq I] (z a : I) :
    ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket z)) *ᵥ Qatlib.Foundations.PureStateMath.Ket a =
      (if a=z then (1 : ℂ) else -1) • Qatlib.Foundations.PureStateMath.Ket a := origin_reflect_ket z a

/-- The actual native matrix satisfies the stated frame-transport identity. -/
theorem sourceBinaryOrigin_frame (m n : ℕ) (h : n+1≤2^m) :
    ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket (fun _ : Fin m => false))) * sourceLabelFrame m n h =
      sourceLabelFrame m n h * ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket (none : Option (Fin n)))) := by
  apply Qatlib.Concepts.GateVocabulary.GateVocab.matrix_ext_on_kets
  intro a
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, sourceLabelFrame_ket,
    origin_reflect_ket, origin_reflect_ket, Matrix.mulVec_smul, sourceLabelFrame_ket]
  have ha : sourceLabelBits m n h a=(fun _ => false) ↔ a=none := by
    constructor
    · intro he
      exact sourceLabelBits_injective m n h (he.trans (sourceLabelBits_none m n h).symm)
    · intro he
      subst a
      exact sourceLabelBits_none m n h
  simp only [ha]

/-- Construction for source Binary Householder in the native binary householder model. -/
def sourceBinaryHouseholder (m n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) : Matrix (Reg m) (Reg m) ℂ :=
  sourceBinaryGivens m n h pivots rs *
    ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket (fun _ : Fin m => false))) *
    (sourceBinaryGivens m n h pivots rs)ᴴ

/-- The actual native matrix satisfies the stated frame-transport identity. -/
theorem sourceBinaryHouseholder_frame (m n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hp : ∀ r∈rs,(r.1.val+1).testBit (pivots r.1).val=true) :
    sourceBinaryHouseholder m n h pivots rs * sourceLabelFrame m n h =
      sourceLabelFrame m n h * tableHouseholder rs := by
  let B := sourceBinaryGivens m n h pivots rs
  let E := sourceLabelFrame m n h
  let T := tableGivens rs
  let R := ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket (fun _ : Fin m => false)))
  let Q := ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket (none : Option (Fin n))))
  have hb : B*E=E*T := sourceBinaryGivens_frame m n h pivots rs hp
  have hba : Bᴴ*E=E*Tᴴ := sourceBinaryGivens_adjoint_frame m n h pivots rs hp
  have ho : R*E=E*Q := sourceBinaryOrigin_frame m n h
  change (B*R*Bᴴ)*E=E*tableHouseholder rs
  calc
    (B*R*Bᴴ)*E = B*(R*(Bᴴ*E)) := by simp only [Matrix.mul_assoc]
    _ = B*(R*(E*Tᴴ)) := by rw [hba]
    _ = (B*E)*(Q*Tᴴ) := by rw [← Matrix.mul_assoc R E, ho]; simp only [Matrix.mul_assoc]
    _ = E*(T*Q*Tᴴ) := by rw [hb]; simp only [Matrix.mul_assoc]
    _ = E*tableHouseholder rs := by rw [tableHouseholder_conjugation]

/-- The constructed finite matrix is unitary under the stated hypotheses. -/
theorem sourceBinaryHouseholder_unitary (m n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hp : ∀ r∈rs,(r.1.val+1).testBit (pivots r.1).val=true) :
    sourceBinaryHouseholder m n h pivots rs ∈ unitaryGroup (Reg m) ℂ := by
  have hb := sourceBinaryGivens_unitary m n h pivots rs hp
  have hba : (sourceBinaryGivens m n h pivots rs)ᴴ ∈ unitaryGroup (Reg m) ℂ := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.star_mem hb
  exact (unitaryGroup (Reg m) ℂ).mul_mem ((unitaryGroup (Reg m) ℂ).mul_mem hb
    (outerProduct_reflection_unitary (normalized_ket (fun _ : Fin m => false)))) hba

/-- The explicit unselected-address or padding condition gives the stated coordinate behaviour. -/
theorem sourceBinaryGivens_padding (m n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hp : ∀ r∈rs,(r.1.val+1).testBit (pivots r.1).val=true)
    (x : Reg m) (hx : n+1≤(sourceLEEquiv m x).val) :
    ApplyGate (sourceBinaryGivens m n h pivots rs) (Qatlib.Foundations.PureStateMath.Ket x)=Qatlib.Foundations.PureStateMath.Ket x := by
  induction rs with
  | nil => simp [sourceBinaryGivens, applyGate_one]
  | cons r rs ih =>
    rw [sourceBinaryGivens, applyGate_mul, ih (fun r hr => hp r (by simp [hr]))]
    exact sourceBinaryPair_padding m n h r.1 (pivots r.1) r.2 (hp r (by simp)) x hx

/-- The explicit unselected-address or padding condition gives the stated coordinate behaviour. -/
theorem sourceBinaryHouseholder_padding (m n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hp : ∀ r∈rs,(r.1.val+1).testBit (pivots r.1).val=true)
    (x : Reg m) (hx : n+1≤(sourceLEEquiv m x).val) :
    ApplyGate (sourceBinaryHouseholder m n h pivots rs) (Qatlib.Foundations.PureStateMath.Ket x)=(-1 : ℂ) • Qatlib.Foundations.PureStateMath.Ket x := by
  let B := sourceBinaryGivens m n h pivots rs
  have hfix : ApplyGate B (Qatlib.Foundations.PureStateMath.Ket x)=Qatlib.Foundations.PureStateMath.Ket x := sourceBinaryGivens_padding m n h pivots rs hp x hx
  have hBB : Bᴴ*B=1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using
      sourceBinaryGivens_unitary m n h pivots rs hp
  have hadj : ApplyGate Bᴴ (Qatlib.Foundations.PureStateMath.Ket x)=Qatlib.Foundations.PureStateMath.Ket x := by
    calc
      ApplyGate Bᴴ (Qatlib.Foundations.PureStateMath.Ket x) = ApplyGate Bᴴ (ApplyGate B (Qatlib.Foundations.PureStateMath.Ket x)) := congrArg (ApplyGate Bᴴ) hfix.symm
      _ = Qatlib.Foundations.PureStateMath.Ket x := by rw [ApplyGate, ApplyGate, Matrix.mulVec_mulVec, hBB, Matrix.one_mulVec]
  have hx0 : x≠(fun _ => false) := by
    intro he
    have hv : (sourceLEEquiv m x).val=0 := by rw [he, sourceLEEquiv_zero]; rfl
    omega
  change ApplyGate (B * ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket (fun _ : Fin m => false))) * Bᴴ) (Qatlib.Foundations.PureStateMath.Ket x) = _
  rw [applyGate_mul, applyGate_mul, hadj]
  change ApplyGate B (ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket (fun _ : Fin m => false))) *ᵥ Qatlib.Foundations.PureStateMath.Ket x) = _
  rw [origin_reflect_ket, ite_eq_right hx0, Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionApplyGate_smul, hfix]

/-- The actual matrix or program has the displayed value on its origin column. -/
theorem sourceBinaryHouseholder_origin_column (m n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hp : ∀ r∈rs,(r.1.val+1).testBit (pivots r.1).val=true)
    (x : Reg m) :
    sourceBinaryHouseholder m n h pivots rs x (fun _ => false) =
      ∑ a,sourceLabelFrame m n h x a * (tablePreparedColumn rs a : ℂ) := by
  have ht : tableHouseholder rs *ᵥ Qatlib.Foundations.PureStateMath.Ket none = fun a => (tablePreparedColumn rs a : ℂ) := by
    funext a
    rw [Qatlib.Concepts.BlockEncoding.LinearCombination.mulVec_ket_apply, tableHouseholder_origin_column]
  have hh := congrArg (fun M => M *ᵥ Qatlib.Foundations.PureStateMath.Ket none) (sourceBinaryHouseholder_frame m n h pivots rs hp)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, sourceLabelFrame_ket,
    sourceLabelBits_none, ht] at hh
  have hr := congrFun hh x
  rw [Qatlib.Concepts.BlockEncoding.LinearCombination.mulVec_ket_apply] at hr
  exact hr

/-- The actual matrix or program has the displayed value on its origin column. -/
theorem sourceBinaryHouseholder_origin_valid (m n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hp : ∀ r∈rs,(r.1.val+1).testBit (pivots r.1).val=true)
    (a : Option (Fin n)) :
    sourceBinaryHouseholder m n h pivots rs (sourceLabelBits m n h a) (fun _ => false) =
      (tablePreparedColumn rs a : ℂ) := by
  rw [sourceBinaryHouseholder_origin_column m n h pivots rs hp]
  simp only [sourceLabelFrame, Qatlib.Foundations.PureStateMath.Ket]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    have he : sourceLabelBits m n h a≠sourceLabelBits m n h b :=
      fun he => hba (sourceLabelBits_injective m n h he).symm
    simp [he]
  · intro ha
    exact False.elim (ha (Finset.mem_univ _))

/-- The explicit unselected-address or padding condition gives the stated coordinate behaviour. -/
theorem sourceBinaryHouseholder_origin_padding_zero (m n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hp : ∀ r∈rs,(r.1.val+1).testBit (pivots r.1).val=true)
    (x : Reg m) (hx : n+1≤(sourceLEEquiv m x).val) :
    sourceBinaryHouseholder m n h pivots rs x (fun _ => false)=0 := by
  rw [sourceBinaryHouseholder_origin_column m n h pivots rs hp]
  apply Finset.sum_eq_zero
  intro a _
  rw [sourceLabelFrame_padding_row m n h x hx a, zero_mul]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
