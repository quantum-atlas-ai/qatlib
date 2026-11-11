/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalSynthesis

/-!
# Local preparation of known frames and states

`coordinateKnownFrame` selects computational basis columns, and `knownFrame_unitary_completion`
extends an isometric rectangular frame to the action of a full unitary. The resulting frame
preparation and range reflection are implemented by legal local gates with arbitrary known
single-qubit matrices, following the circuit-synthesis setting of [BarencoEtAl1995].

The constructions use at most `128 * (n + 1)² * 4ⁿ` gates on the data and `n + 1` workspace
qubits, returning the workspace to zero. Empty frames and zero-qubit states are included, and
normalized complex states can be prepared exactly from the all-false basis state.

## Main statements

* `knownFrame_unitary_completion`: unitary transport from a coordinate frame to an isometric
  frame.
* `known_rectangular_frame_local_prepare_and_reflect`: bounded exact preparation and range
  reflection.
* `known_complex_state_actual_local_preparation`: bounded exact preparation of normalized
  states.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option autoImplicit false

/-- The coordinate frame whose columns are the computational basis vectors selected by the
embedding `e`. -/
noncomputable def coordinateKnownFrame (n m : ℕ) (e : Fin m ↪ Reg n) :
    Matrix (Reg n) (Fin m) ℂ := fun x j => if x = e j then 1 else 0

/-- Distinct coordinate basis columns form an isometric frame. -/
theorem coordinateKnownFrame_isometry (n m : ℕ) (e : Fin m ↪ Reg n) :
    IsIsometry (coordinateKnownFrame n m e) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, coordinateKnownFrame]
  rw [Finset.sum_eq_single (e i)]
  · simp [Matrix.one_apply, e.injective.eq_iff]
  · intro x _ hx
    simp [hx]
  · simp

set_option maxHeartbeats 800000 in

/-- Every isometric frame is the image of the selected coordinate frame under some unitary on
the full register. -/
theorem knownFrame_unitary_completion (n m : ℕ) (e : Fin m ↪ Reg n)
    (F : Matrix (Reg n) (Fin m) ℂ) (hF : IsIsometry F) :
    ∃ U : Matrix (Reg n) (Reg n) ℂ, U ∈ unitaryGroup (Reg n) ℂ ∧
      U * coordinateKnownFrame n m e = F := by
  classical
  let v : Reg n → EuclideanSpace ℂ (Reg n) := fun x =>
    if h : ∃ j, e j = x then WithLp.toLp 2 (fun i => F i (Classical.choose h)) else 0
  have ve (j : Fin m) : v (e j) = WithLp.toLp 2 (fun i => F i j) := by
    have hj : ∃ k, e k = e j := ⟨j, rfl⟩
    dsimp only [v]
    rw [dif_pos hj]
    have he : Classical.choose hj = j := e.injective (Classical.choose_spec hj)
    rw [he]
  have hv : Orthonormal ℂ ((Set.range e).restrict v) := by
    rw [orthonormal_iff_ite]
    intro ⟨x,hx⟩ ⟨y,hy⟩
    obtain ⟨j,rfl⟩ := hx
    obtain ⟨k,rfl⟩ := hy
    dsimp only [Set.restrict, Set.domRestrict]; rw [ve, ve, EuclideanSpace.inner_eq_star_dotProduct]
    have hh := congrArg (fun M : Matrix (Fin m) (Fin m) ℂ => M j k) hF
    simpa [IsIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      dotProduct, e.injective.eq_iff, Subtype.ext_iff, mul_comm, WithLp.ofLp_toLp] using! hh
  obtain ⟨b,hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (ι := Reg n) finrank_euclideanSpace
  let U : Matrix (Reg n) (Reg n) ℂ := fun x y => b y x
  refine ⟨U, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    ext x y
    have hbxy := orthonormal_iff_ite.mp b.orthonormal x y
    simpa [U, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using! hbxy
  · ext x j
    simp only [Matrix.mul_apply, coordinateKnownFrame]
    rw [Finset.sum_eq_single (e j)]
    · simp only [ite_true, mul_one]
      have hj := hb (e j) ⟨j,rfl⟩
      rw [ve] at hj
      exact congrArg (fun w : EuclideanSpace ℂ (Reg n) => w x) hj
    · intro y _ hy
      simp [hy]
    · simp

/-- For an isometric frame `F`, the reflection `I - 2 * F * Fᴴ` is unitary. -/
theorem knownFrame_reflector_unitary (n m : ℕ) (F : Matrix (Reg n) (Fin m) ℂ)
    (hF : IsIsometry F) : (1 - 2 • (F * Fᴴ)) ∈ unitaryGroup (Reg n) ℂ := by
  have hp := rangeProjector_isOrthogonalProjector hF
  have hh := reflectionAbout_unitary hp
  have heq : 1 - 2 • (F * Fᴴ) = -(ReflectionAbout (rangeProjector F)) := by
    simp [ReflectionAbout, rangeProjector, two_smul]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hh ⊢
  rw [heq, Matrix.conjTranspose_neg, neg_mul_neg, hh]

/-- An empty rectangular frame and its identity reflection each possess a legal local
implementation within `128 * (n + 1)² * 4ⁿ` gates, restoring the zero workspace. -/
theorem known_rectangular_frame_local_empty (n : ℕ) (e : Fin 0 ↪ Reg n)
    (F : Matrix (Reg n) (Fin 0) ℂ) :
    (∃ gs : List (ReflectionGate (n+(n+1))), reflectionLegal gs ∧
      gs.length ≤ 128*(n+1)^2*4^n ∧
      ∀ ψ : QState (Fin 0),
      Run 1 (reflectionCompile gs) (knownFrameEmbed n (coordinateKnownFrame n 0 e *ᵥ ψ)) =
        knownFrameEmbed n (F *ᵥ ψ)) ∧
    (∃ rs : List (ReflectionGate (n+(n+1))), reflectionLegal rs ∧
      rs.length ≤ 128*(n+1)^2*4^n ∧
      ∀ ψ : QState (Reg n), Run 1 (reflectionCompile rs) (knownFrameEmbed n ψ) =
        knownFrameEmbed n ((1 - 2 • (F * Fᴴ)) *ᵥ ψ)) := by
  constructor
  · refine ⟨[], by simp [reflectionLegal], by simp, ?_⟩
    intro ψ
    simp [reflectionCompile]
  · refine ⟨[], by simp [reflectionLegal], by simp, ?_⟩
    intro ψ
    have hf : F * Fᴴ = 0 := by
      ext x y
      simp [Matrix.mul_apply]
    simp [reflectionCompile, hf]

/-- Every normalized state on the zero-qubit register can be prepared, including its scalar
phase, with at most 128 legal gates and a restored zero workspace. -/
theorem known_complex_state_local_preparation_zero (ψ : QState (Reg 0)) (hψ : Normalized ψ) :
    ∃ gs : List (ReflectionGate 1), reflectionLegal gs ∧ gs.length ≤ 128 ∧
      Run 1 (reflectionCompile gs) (knownFrameEmbed 0 (Qatlib.Foundations.PureStateMath.Ket (fun _ => false))) =
        knownFrameEmbed 0 ψ := by
  let x : Reg 0 := fun _ => false
  have hz : star (ψ x) * ψ x = 1 := by
    have hh := (normalized_iff_inner_self ψ).mp hψ
    change (∑ u : Reg 0, star (ψ u) * ψ u) = 1 at hh
    rw [Finset.sum_eq_single x] at hh
    · exact hh
    · intro u _ hu; exact (hu (Subsingleton.elim _ _)).elim
    · intro hx; exact (hx (Finset.mem_univ x)).elim
  refine ⟨knownScalarPhaseSteps (ψ x), knownScalarPhaseSteps_legal (ψ x) hz,
    by simp [knownScalarPhaseSteps], ?_⟩
  rw [knownScalarPhaseSteps_run]
  congr 1
  funext u
  have hu : u = x := Subsingleton.elim _ _
  simp [hu, x, Qatlib.Foundations.PureStateMath.Ket, Pi.smul_apply, smul_eq_mul]

/-- An isometric rectangular frame can be prepared from its coordinate frame and its range
reflection can be implemented, each with at most `128 * (n + 1)² * 4ⁿ` legal local gates and
restored zero workspace. See [BarencoEtAl1995] for the circuit synthesis background. -/
theorem known_rectangular_frame_local_prepare_and_reflect
    (n m : ℕ) (e : Fin m ↪ Reg n) (F : Matrix (Reg n) (Fin m) ℂ) (hF : IsIsometry F) :
    (∃ gs : List (ReflectionGate (n+(n+1))), reflectionLegal gs ∧
      gs.length ≤ 128*(n+1)^2*4^n ∧
      ∀ ψ : QState (Fin m),
      Run 1 (reflectionCompile gs) (knownFrameEmbed n (coordinateKnownFrame n m e *ᵥ ψ)) =
        knownFrameEmbed n (F *ᵥ ψ)) ∧
    (∃ rs : List (ReflectionGate (n+(n+1))), reflectionLegal rs ∧
      rs.length ≤ 128*(n+1)^2*4^n ∧
      ∀ ψ : QState (Reg n), Run 1 (reflectionCompile rs) (knownFrameEmbed n ψ) =
        knownFrameEmbed n ((1 - 2 • (F * Fᴴ)) *ᵥ ψ)) := by
  obtain ⟨U,hU,hUF⟩ := knownFrame_unitary_completion n m e F hF
  obtain ⟨gs,hgs,hlen,_,_,hrun⟩ := known_unitary_actual_clean_local_synthesis n U hU
  constructor
  · refine ⟨gs,hgs,hlen,?_⟩
    intro ψ
    rw [hrun,Matrix.mulVec_mulVec,hUF]
  · obtain ⟨rs,hrs,hrlen,_,_,hrrun⟩ := known_unitary_actual_clean_local_synthesis n
      (1 - 2 • (F * Fᴴ)) (knownFrame_reflector_unitary n m F hF)
    exact ⟨rs,hrs,hrlen,hrrun⟩

/-- Every normalized `n`-qubit state can be prepared exactly from the all-false basis state with
at most `128 * (n + 1)² * 4ⁿ` legal local gates and `n + 1` workspace qubits returned to
zero. -/
theorem known_complex_state_actual_local_preparation
    (n : ℕ) (ψ : QState (Reg n)) (hψ : Normalized ψ) :
    ∃ gs : List (ReflectionGate (n+(n+1))), reflectionLegal gs ∧
      gs.length ≤ 128*(n+1)^2*4^n ∧
      Run 1 (reflectionCompile gs) (knownFrameEmbed n (Qatlib.Foundations.PureStateMath.Ket (fun _=>false))) =
        knownFrameEmbed n ψ := by
  let e : Fin 1 ↪ Reg n := ⟨fun _=>fun _=>false,fun _ _ _=>Subsingleton.elim _ _⟩
  let F : Matrix (Reg n) (Fin 1) ℂ := fun x _=>ψ x
  have hF : IsIsometry F := by
    have hn := (normalized_iff_inner_self ψ).mp hψ
    ext i j
    have hij : i=j := Subsingleton.elim _ _
    simpa [IsIsometry,F,Qatlib.Foundations.PureStateMath.Inner,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.one_apply,dotProduct,hij] using! hn
  obtain ⟨gs,hgs,hlen,hrun⟩ :=
    (known_rectangular_frame_local_prepare_and_reflect n 1 e F hF).1
  have hcoord : coordinateKnownFrame n 1 e *ᵥ (fun _=>1) = Qatlib.Foundations.PureStateMath.Ket (fun _=>false) := by
    funext x
    by_cases hx : x = fun _=>false <;>
      simp [coordinateKnownFrame,Matrix.mulVec,dotProduct,e,Qatlib.Foundations.PureStateMath.Ket,hx]
  have hf : F *ᵥ (fun _=>1) = ψ := by
    funext x
    simp [F,Matrix.mulVec,dotProduct]
  refine ⟨gs,hgs,hlen,?_⟩
  simpa only [hcoord,hf] using! hrun (fun _=>1)

end Qatlib.Concepts.MatrixAccess.KnownFrameSynth
