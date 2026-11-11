/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeKnownBuilders
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeWeightConsumer

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
/-! Canonical typed source V/middle/PREP constructors. The native reversed
inverse expands to the same full operator as the refined true adjoint,
although the elementary lists can differ. Python byte decoding and scalar
producer correspondence remain separate from this typed-source theorem. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical

/-- Construction for weight Native VOps in the native weight source ops model. -/
def weightNativeVOps (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m) :
    List (Fin n × Circle) → List (NativeKnown.Gate (weightWidth m w))
  | [] => []
  | r::rs => weightNativeVOps m w n h pivots rs ++
      NativeKnown.pairOps (weightLift m w (binaryPairControls (pivots r.1))) (weightWorkWire m w)
        (weightLabelWire m w (pivots r.1)) (weightPool m w)
        (weightLift m w (binaryPairTargets (pivots r.1) (sourceLabelBits m n h (some r.1)))) r.2

/-- Compiling the typed native constructors gives exactly the corresponding elementary word. -/
theorem weightNativeVOps_compile (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) :
    NativeKnown.wordCompile (weightNativeVOps m w n h pivots rs)=weightVWord m w n h pivots rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [weightNativeVOps, NativeKnown.wordCompile_append, ih, NativeKnown.pairOps_compile]
    rfl

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem weightNativeVOps_legal (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hw : m-2≤w) : NativeKnown.wordLegal (weightNativeVOps m w n h pivots rs) := by
  apply NativeKnown.wordLegal_of_compile
  rw [weightNativeVOps_compile]
  exact weightVWord_legal m w n h pivots rs hw

/-- Construction for weight Native Middle Ops in the native weight source ops model. -/
def weightNativeMiddleOps (m w : ℕ) : List (NativeKnown.Gate (weightWidth m w)) :=
  NativeKnown.middleOps (weightLift m w (List.finRange m)) (weightWorkWire m w)
    (weightSeedWire m w) (weightPool m w)

/-- Compiling the typed native constructors gives exactly the corresponding elementary word. -/
theorem weightNativeMiddleOps_compile (m w : ℕ) :
    NativeKnown.wordCompile (weightNativeMiddleOps m w)=weightMiddleWord m w :=
  NativeKnown.middleOps_compile _ _ _ _

/-- Global native-inverse/refined-adjoint equality, with no input-state
cleanliness condition. In particular, dirty work and seed are permitted. -/
theorem weightNativeVInverse_matrix (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hw : m-2≤w) :
    reflectionProgramMatrix (NativeKnown.wordCompile (NativeKnown.adjointWord (weightNativeVOps m w n h pivots rs))) =
      reflectionProgramMatrix (reflectionAdjoint (weightVWord m w n h pivots rs)) := by
  rw [NativeKnown.wordCompile_adjoint _ (weightNativeVOps_legal m w n h pivots rs hw),
    weightNativeVOps_compile, reflectionAdjoint_matrix _ (weightVWord_legal m w n h pivots rs hw)]

/-- Construction for weight Native Prep Ops in the native weight source ops model. -/
def weightNativePrepOps (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) : List (NativeKnown.Gate (weightWidth m w)) :=
  NativeKnown.adjointWord (weightNativeVOps m w n h pivots rs) ++ weightNativeMiddleOps m w ++
    weightNativeVOps m w n h pivots rs

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem weightNativePrepOps_legal (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hw : m-2≤w) : NativeKnown.wordLegal (weightNativePrepOps m w n h pivots rs) := by
  have hv := weightNativeVOps_legal m w n h pivots rs hw
  have hm : NativeKnown.wordLegal (weightNativeMiddleOps m w) := by
    apply NativeKnown.wordLegal_of_compile
    rw [weightNativeMiddleOps_compile]
    exact weightMiddleWord_legal m w hw
  intro g hg
  simp only [weightNativePrepOps, List.mem_append] at hg
  rcases hg with (ha|hmemb)|hvemb
  · exact NativeKnown.adjointWord_legal _ hv g ha
  · exact hm g hmemb
  · exact hv g hvemb

/-- Evaluation of the emitted native word equals the stated concrete matrix semantics. -/
theorem weightNativePrepOps_matrix (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hw : m-2≤w) :
    reflectionProgramMatrix (NativeKnown.wordCompile (weightNativePrepOps m w n h pivots rs)) =
      reflectionProgramMatrix (weightRefinedPrepWord m w n h pivots rs) := by
  simp only [weightNativePrepOps, NativeKnown.wordCompile_append, weightNativeVOps_compile,
    weightNativeMiddleOps_compile, weightRefinedPrepWord, reflectionProgramMatrix_append]
  rw [weightNativeVInverse_matrix m w n h pivots rs hw]

/-- Evaluation of the emitted native word equals the stated concrete matrix semantics. -/
theorem weightNativePrepOps_adjoint_matrix (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hw : m-2≤w) :
    reflectionProgramMatrix (NativeKnown.wordCompile (NativeKnown.adjointWord (weightNativePrepOps m w n h pivots rs))) =
      (reflectionProgramMatrix (weightRefinedPrepWord m w n h pivots rs))ᴴ := by
  rw [NativeKnown.wordCompile_adjoint _ (weightNativePrepOps_legal m w n h pivots rs hw),
    weightNativePrepOps_matrix m w n h pivots rs hw]

/-- The actual native program gives the displayed projected unitary encoding. -/
theorem weightNativePrepOps_encoding (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) (hw : m-2≤w)
    (hp : ∀ r∈rs,(r.1.val+1).testBit (pivots r.1).val=true) :
    ProjectedUnitaryEncoding (tableHouseholder rs)
      (reflectionProgramMatrix (NativeKnown.wordCompile (weightNativePrepOps m w n h pivots rs)))
      (weightFrame m w * sourceLabelFrame m n h) (weightFrame m w * sourceLabelFrame m n h) := by
  rw [weightNativePrepOps_matrix m w n h pivots rs hw]
  exact weightRefinedPrepWord_encoding m w n h pivots rs hw hp

/-- The same emitted program has the displayed exact query and elementary-gate counts. -/
theorem weightNativePrepOps_counts (m w n : ℕ) (h : n+1≤2^m) (pivots : Fin n → Fin m)
    (rs : List (Fin n × Circle)) :
    QueryCount (reflectionCompile (NativeKnown.wordCompile (weightNativePrepOps m w n h pivots rs)))=0 ∧
    GateCount (reflectionCompile (NativeKnown.wordCompile (weightNativePrepOps m w n h pivots rs))) =
      2*(weightVWord m w n h pivots rs).length+(weightMiddleWord m w).length := by
  refine ⟨queryCount_reflectionCompile _,?_⟩
  rw [gateCount_reflectionCompile]
  simp only [weightNativePrepOps, NativeKnown.wordCompile_append, List.length_append,
    NativeKnown.wordCompile_adjoint_length, weightNativeVOps_compile, weightNativeMiddleOps_compile]
  omega

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
