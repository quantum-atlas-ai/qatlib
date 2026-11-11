/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeWeightPair

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LchsSimulation.StaticLchs
/-! Refined one-qubit/CNOT PREP on the explicit source-layout frame.
The word uses the true adjoint of its refined V. Generic serialization of
Python's primitive inverse stream is a separate compiler obligation. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical Kronecker

/-- Construction for weight VWord in the native weight program model. -/
def weightVWord (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m) :
    List (Fin n × Circle) → List (ReflectionGate (weightWidth m w))
  | [] => []
  | r::rs => weightVWord m w n h pivots rs ++
      weightPairWord m w (pivots r.1) (sourceLabelBits m n h (some r.1)) r.2

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem weightVWord_legal (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hw : m-2≤w) : reflectionLegal (weightVWord m w n h pivots rs) := by
  induction rs with
  | nil => intro g hg; simp [weightVWord] at hg
  | cons r rs ih =>
    rw [weightVWord, reflectionLegal_append]
    exact ⟨ih,weightPairWord_legal m w _ _ _ hw⟩

/-- The actual native matrix satisfies the stated frame-transport identity. -/
theorem weightVWord_frame (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hw : m-2≤w) :
    reflectionProgramMatrix (weightVWord m w n h pivots rs) * weightFrame m w =
      weightFrame m w * sourceBinaryGivens m n h pivots rs := by
  induction rs with
  | nil => simp [weightVWord, reflectionProgramMatrix, sourceBinaryGivens]
  | cons r rs ih =>
    rw [weightVWord, reflectionProgramMatrix_append, Matrix.mul_assoc, ih,
      ← Matrix.mul_assoc, weightPairWord_frame m w _ _ _ hw, Matrix.mul_assoc]
    rfl

/-- Construction for weight Middle Word in the native weight program model. -/
def weightMiddleWord (m w : ℕ) : List (ReflectionGate (weightWidth m w)) :=
  nativeOriginWord (weightLift m w (List.finRange m)) (weightWorkWire m w)
    (weightSeedWire m w) (weightPool m w)

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem weightMiddleWord_legal (m w : ℕ) (hw : m-2≤w) : reflectionLegal (weightMiddleWord m w) := by
  apply nativeOriginWord_legal
  · exact weightAllocation m w _ (List.nodup_finRange m)
  · simpa [weightLift] using hw

/-- The actual native matrix satisfies the stated frame-transport identity. -/
theorem weightMiddleWord_frame (m w : ℕ) (hw : m-2≤w) :
    reflectionProgramMatrix (weightMiddleWord m w) * weightFrame m w =
      weightFrame m w * ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket (fun _ : Fin m => false))) := by
  apply Qatlib.Concepts.GateVocabulary.GateVocab.matrix_ext_on_kets
  intro x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, weightFrame_ket,
    sourceOrigin_reflect_ket, Matrix.mulVec_smul, weightFrame_ket]
  have hz : (List.finRange m).all (fun j => !x j)=true ↔ x=(fun _ => false) := by
    constructor
    · intro hh
      funext j
      exact Bool.eq_false_of_not_eq_true' (List.all_eq_true.mp hh j (by simp))
    · intro he
      subst x
      simp
  have hb := nativePredicateReflection_basis (nativeZeroPattern (weightLift m w (List.finRange m)))
    (weightWorkWire m w) (weightSeedWire m w) (weightPool m w)
    (by simpa [nativeZeroPattern, List.map_map, Function.comp_def] using
      weightAllocation m w (List.finRange m) (List.nodup_finRange m))
    (by simpa [nativeZeroPattern, weightLift] using hw) (weightInput m w x)
    (weightInput_pool m w x) (weightInput_work m w x) (weightInput_seed m w x)
  have hnot (b : Bool) : (b==false)=!b := by cases b <;> rfl
  change ApplyGate (reflectionProgramMatrix (weightMiddleWord m w)) (Qatlib.Foundations.PureStateMath.Ket (weightInput m w x)) = _
  rw [← run_reflectionCompile]
  simpa only [weightMiddleWord, nativeOriginWord, nativeZeroPattern, weightLift, List.all_map,
    Function.comp_def, weightInput_label, hnot, hz] using hb

/-- The actual native matrix satisfies the stated frame-transport identity. -/
theorem weightVWord_adjoint_frame (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hw : m-2≤w)
    (hp : ∀ r∈rs,(r.1.val+1).testBit (pivots r.1).val=true) :
    reflectionProgramMatrix (reflectionAdjoint (weightVWord m w n h pivots rs)) * weightFrame m w =
      weightFrame m w * (sourceBinaryGivens m n h pivots rs)ᴴ := by
  let U := reflectionProgramMatrix (weightVWord m w n h pivots rs)
  let J := weightFrame m w
  let B := sourceBinaryGivens m n h pivots rs
  have hu : Uᴴ*U=1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using
      reflectionProgramMatrix_unitary _ (weightVWord_legal m w n h pivots rs hw)
  have hb : B*Bᴴ=1 := by
    simpa only [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] using
      sourceBinaryGivens_unitary m n h pivots rs hp
  have hf : U*J=J*B := weightVWord_frame m w n h pivots rs hw
  rw [reflectionAdjoint_matrix _ (weightVWord_legal m w n h pivots rs hw)]
  change Uᴴ*J=J*Bᴴ
  calc
    Uᴴ*J = Uᴴ*(J*(B*Bᴴ)) := by rw [hb, Matrix.mul_one]
    _ = Uᴴ*((J*B)*Bᴴ) := by rw [Matrix.mul_assoc]
    _ = Uᴴ*((U*J)*Bᴴ) := by rw [hf]
    _ = J*Bᴴ := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hu, Matrix.one_mul]

/-- Construction for weight Refined Prep Word in the native weight program model. -/
def weightRefinedPrepWord (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) : List (ReflectionGate (weightWidth m w)) :=
  reflectionAdjoint (weightVWord m w n h pivots rs) ++ weightMiddleWord m w ++ weightVWord m w n h pivots rs

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem weightRefinedPrepWord_legal (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hw : m-2≤w) : reflectionLegal (weightRefinedPrepWord m w n h pivots rs) := by
  rw [weightRefinedPrepWord, reflectionLegal_append, reflectionLegal_append]
  exact ⟨⟨reflectionAdjoint_legal _ (weightVWord_legal m w n h pivots rs hw),weightMiddleWord_legal m w hw⟩,
    weightVWord_legal m w n h pivots rs hw⟩

/-- The actual native matrix satisfies the stated frame-transport identity. -/
theorem weightRefinedPrepWord_frame (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hw : m-2≤w)
    (hp : ∀ r∈rs,(r.1.val+1).testBit (pivots r.1).val=true) :
    reflectionProgramMatrix (weightRefinedPrepWord m w n h pivots rs) * weightFrame m w =
      weightFrame m w * sourceBinaryHouseholder m n h pivots rs := by
  let U := reflectionProgramMatrix (weightVWord m w n h pivots rs)
  let A := reflectionProgramMatrix (reflectionAdjoint (weightVWord m w n h pivots rs))
  let M := reflectionProgramMatrix (weightMiddleWord m w)
  let J := weightFrame m w
  let B := sourceBinaryGivens m n h pivots rs
  let R := ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket (fun _ : Fin m => false)))
  have hu : U*J=J*B := weightVWord_frame m w n h pivots rs hw
  have ha : A*J=J*Bᴴ := weightVWord_adjoint_frame m w n h pivots rs hw hp
  have hm : M*J=J*R := weightMiddleWord_frame m w hw
  rw [weightRefinedPrepWord, reflectionProgramMatrix_append, reflectionProgramMatrix_append]
  change (U*(M*A))*J=J*(B*R*Bᴴ)
  calc
    (U*(M*A))*J = U*(M*(A*J)) := by simp only [Matrix.mul_assoc]
    _ = U*(M*(J*Bᴴ)) := by rw [ha]
    _ = (U*J)*(R*Bᴴ) := by rw [← Matrix.mul_assoc M J, hm]; simp only [Matrix.mul_assoc]
    _ = J*(B*R*Bᴴ) := by rw [hu]; simp only [Matrix.mul_assoc]

/-- The actual native matrix satisfies the stated frame-transport identity. -/
theorem weightRefinedPrepWord_active_frame (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hw : m-2≤w)
    (hp : ∀ r∈rs,(r.1.val+1).testBit (pivots r.1).val=true) :
    reflectionProgramMatrix (weightRefinedPrepWord m w n h pivots rs) *
      (weightFrame m w * sourceLabelFrame m n h) =
      (weightFrame m w * sourceLabelFrame m n h) * tableHouseholder rs := by
  rw [← Matrix.mul_assoc, weightRefinedPrepWord_frame m w n h pivots rs hw hp,
    Matrix.mul_assoc, sourceBinaryHouseholder_frame m n h pivots rs hp, ← Matrix.mul_assoc]

/-- The same emitted program has the displayed exact query and elementary-gate counts. -/
theorem weightMiddleWord_counts (m w : ℕ) (hw : m-2≤w) :
    QueryCount (reflectionCompile (weightMiddleWord m w))=0 ∧
    GateCount (reflectionCompile (weightMiddleWord m w)) =
      2*(2*m+(if m≤1 then 1 else 15*(2*m-3)))+2 := by
  simpa [weightMiddleWord, weightLift] using nativeOriginWord_counts
    (weightLift m w (List.finRange m)) (weightWorkWire m w) (weightSeedWire m w) (weightPool m w)
      (by simpa [weightLift] using hw)

/-- The same emitted program has the displayed exact query and elementary-gate counts. -/
theorem weightRefinedPrepWord_counts (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) :
    QueryCount (reflectionCompile (weightRefinedPrepWord m w n h pivots rs))=0 ∧
    GateCount (reflectionCompile (weightRefinedPrepWord m w n h pivots rs)) =
      2*(weightVWord m w n h pivots rs).length+(weightMiddleWord m w).length := by
  refine ⟨queryCount_reflectionCompile _,?_⟩
  rw [gateCount_reflectionCompile]
  simp only [weightRefinedPrepWord, List.length_append, reflectionAdjoint_length]
  omega

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
