/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyControlledRotationCorrected
import Qatlib.Concepts.GateVocabulary.GateVocab.GateVocabulary

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.RiskEstimation.PolyRotation
/-! Native CCX triples of append_mcx, using the pinned exact fifteen-gate
table. In particular, reversing native CCXs is proved to be the adjoint;
it is not confused with reversing elementary gates without conjugation. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Abbreviation for Ccx Triple in the native and ladder model. -/
abbrev CcxTriple (N : ℕ) := Fin N × Fin N × Fin N

/-- Construction for ccx Triples Compile in the native and ladder model. -/
def ccxTriplesCompile {N : ℕ} (ts : List (CcxTriple N)) : List (ReflectionGate N) :=
  ts.flatMap (fun t => toffoliLocalSteps t.1 t.2.1 t.2.2)

/-- Construction for ccx Triples Legal in the native and ladder model. -/
def ccxTriplesLegal {N : ℕ} (ts : List (CcxTriple N)) : Prop :=
  ∀ t ∈ ts, t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

/-- Construction for native And Fold in the native and ladder model. -/
def nativeAndFold {N : ℕ} (flag : Fin N) : List (Fin N) → List (Fin N) → List (CcxTriple N)
  | c::cs,w::ws => (flag,c,w)::nativeAndFold w cs ws
  | _,_ => []

/-- Exact compute triples: use the first two controls once, then the rest. -/
def nativeAndLadder {N : ℕ} (S works : List (Fin N)) : List (CcxTriple N) :=
  match S,subsetActiveWorks S works with
  | a::b::cs,w::ws => (a,b,w)::nativeAndFold w cs ws
  | _,_ => []

/-- Compiling the emitted AND triples gives the existing elementary AND-fold table. -/
theorem nativeAndFold_compile {N : ℕ} (cs ws : List (Fin N)) (f : Fin N) :
    ccxTriplesCompile (nativeAndFold f cs ws) = subsetAndFold f cs ws := by
  induction cs generalizing ws f with
  | nil => cases ws <;> rfl
  | cons c cs ih =>
    cases ws with
    | nil => rfl
    | cons w ws =>
      simp only [nativeAndFold, ccxTriplesCompile, List.flatMap_cons, subsetAndFold]
      rw [← ih ws w]
      rfl

/-- Compiling the native compute ladder gives the corrected supported-wire AND table. -/
theorem nativeAndLadder_compile {N : ℕ} (S ws : List (Fin N)) :
    ccxTriplesCompile (nativeAndLadder S ws) = subsetAndLadderCorrected S ws := by
  cases S with
  | nil => rfl
  | cons a S =>
    cases S with
    | nil => rfl
    | cons b cs =>
      cases hw : subsetActiveWorks (a::b::cs) ws with
      | nil => simp [nativeAndLadder, subsetAndLadderCorrected, hw, ccxTriplesCompile]
      | cons w ww =>
        simp only [nativeAndLadder, subsetAndLadderCorrected, hw,
          ccxTriplesCompile, List.flatMap_cons]
        rw [← nativeAndFold_compile cs ww w]
        rfl

/-- Pairwise distinct wires in every triple make the expanded fifteen-gate tables legal. -/
theorem ccxTriplesCompile_legal {N : ℕ} (ts : List (CcxTriple N)) (h : ccxTriplesLegal ts) :
    reflectionLegal (ccxTriplesCompile ts) := by
  intro g hg
  obtain ⟨t,ht,hg⟩ := List.mem_flatMap.mp hg
  exact toffoliLocalSteps_legal t.1 t.2.1 t.2.2 (h t ht).1 (h t ht).2.1 (h t ht).2.2 g hg

/-- Legality of the expanded tables certifies all three wire inequalities of every triple. -/
theorem ccxTriplesLegal_of_compile {N : ℕ} (ts : List (CcxTriple N))
    (h : reflectionLegal (ccxTriplesCompile ts)) : ccxTriplesLegal ts := by
  intro t ht
  have hs : reflectionLegal (toffoliLocalSteps t.1 t.2.1 t.2.2) := by
    intro g hg
    exact h g (List.mem_flatMap.mpr ⟨t,ht,hg⟩)
  exact ⟨hs (.inr (t.1,t.2.1)) (by simp [toffoliLocalSteps]),
    hs (.inr (t.1,t.2.2)) (by simp [toffoliLocalSteps]),
    hs (.inr (t.2.1,t.2.2)) (by simp [toffoliLocalSteps])⟩

/-- The expanded table has exactly fifteen elementary instructions per CCX triple. -/
theorem ccxTriplesCompile_length {N : ℕ} (ts : List (CcxTriple N)) :
    (ccxTriplesCompile ts).length = 15*ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [ccxTriplesCompile, List.flatMap_cons, List.length_append,
      toffoliLocalSteps_length, List.length_cons] at *
    omega

/-- The exact Toffoli table is self-adjoint when its three wires are distinct. -/
private theorem ccx_table_adjoint {N : ℕ} (t : CcxTriple N)
    (h : t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2) :
    (reflectionProgramMatrix (toffoliLocalSteps t.1 t.2.1 t.2.2))ᴴ =
      reflectionProgramMatrix (toffoliLocalSteps t.1 t.2.1 t.2.2) := by
  rw [Qatlib.Concepts.GateVocabulary.GateVocab.toffoli_fifteen_matrix t.1 t.2.1 t.2.2 h.1 h.2.1 h.2.2]
  exact permMatrix_conjTranspose (Qatlib.Concepts.GateVocabulary.GateVocab.toffoliUpdate_involutive t.1 t.2.1 t.2.2 h.2.1 h.2.2)

/-- Source uncompute reuses each native CCX, in reversed triple order. -/
theorem ccxTriplesCompile_reverse_matrix {N : ℕ} (ts : List (CcxTriple N))
    (h : ccxTriplesLegal ts) :
    reflectionProgramMatrix (ccxTriplesCompile ts.reverse) =
      (reflectionProgramMatrix (ccxTriplesCompile ts))ᴴ := by
  induction ts with
  | nil => simp [ccxTriplesCompile, reflectionProgramMatrix]
  | cons t ts ih =>
    have ht := h t (by simp)
    have hs : ccxTriplesLegal ts := fun u hu => h u (by simp [hu])
    simp only [List.reverse_cons, ccxTriplesCompile, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, reflectionProgramMatrix_append, Matrix.conjTranspose_mul]
    rw [← ccxTriplesCompile, ih hs, ccx_table_adjoint t ht]
    rfl

/-- The corrected rotation frame makes every triple in the native AND ladder legal. -/
theorem nativeAndLadder_legal {N : ℕ} (S ws : List (Fin N)) (target : Fin N)
    (h : subsetRotationFrameCorrected S target ws) : ccxTriplesLegal (nativeAndLadder S ws) := by
  apply ccxTriplesLegal_of_compile
  rw [nativeAndLadder_compile]
  exact (subsetAndLadderCorrected_transport S ws target h).1

/-- Coordinates outside the allocated AND pool are untouched by compute. -/
theorem nativeLadder_preserves {N : ℕ} (S ws : List (Fin N)) (x : Reg N)
    (wire : Fin N) (hw : wire ∉ ws) : subsetLadderBasisCorrected S ws x wire = x wire := by
  cases S with
  | nil => rfl
  | cons a S =>
    cases S with
    | nil => rfl
    | cons b cs =>
      cases hx : subsetActiveWorks (a::b::cs) ws with
      | nil => simp [subsetLadderBasisCorrected, hx]
      | cons w ww =>
        have ht : wire ∉ ww := by
          intro ht
          apply hw
          apply List.mem_of_mem_take (i := (a::b::cs).length - 1)
          change wire ∈ subsetActiveWorks (a::b::cs) ws
          rw [hx]
          simp [ht]
        have hne : wire ≠ w := by
          intro he
          apply hw
          rw [he]
          apply List.mem_of_mem_take (i := (a::b::cs).length - 1)
          change w ∈ subsetActiveWorks (a::b::cs) ws
          rw [hx]
          simp
        simp only [subsetLadderBasisCorrected, hx]
        rw [subsetFoldBasis_preserves cs ww w _ wire ht]
        exact Function.update_of_ne hne _ _

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
