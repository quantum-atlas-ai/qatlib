/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SymmetryAdv10.MainResults.SourceModel
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # A normalized countermodel to the old PSD-only projection contract

Fixed source1012.2112v1 Lemma13 assumes an orthogonal projector.
The historical header instead assumes only positive semidefiniteness.
The unit instance below retains normalized targets and actual operator norms;
it refutes that weaker interface, without refuting the source lemma.
-/

set_option autoImplicit false
noncomputable section
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder MatrixOrder
namespace Qatlib.Papers.SymmetryAdv10.MainResults.ProjectorAudit
open Qatlib.Papers.SymmetryAdv10.MainResults

/-- The exact historical query-output coordinate projector. -/
def PiZ (P : Problem) (x : P.Hom) (z : P.Out) : Matrix P.F P.F ℂ :=
  fun f g => if f=g then (if P.funMap f x=z then 1 else 0) else 0

/-- A genuine one-input normalized state generation instance. -/
abbrev unitProblem : Problem where
  F := Unit
  Hom := Unit
  Out := Unit
  Tgt := Unit
  funMap := fun _ _ => ()
  target := fun _ _ => 1

/-- The selected target really has squared norm one. -/
theorem targetNorm (f : Unit) : ∑ t : Unit, ‖unitProblem.target f t‖^2=1 := by
  norm_num [unitProblem,Matrix.one_apply]

/-- The proposed bad matrix is PSD but is not a projection. -/
def halfBad : Matrix Unit Unit ℂ := (1/2 : ℝ) • 1

/-- Positivity alone admits the half identity. -/
theorem halfPositive : halfBad.PosSemidef :=
  Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ)≤1/2)

/-- On the unit instance, every junk matrix is exactly the identity. -/
theorem junkUnique (M : Matrix Unit Unit ℂ) (h : unitProblem.IsNoncoherentJunk M) : M=1 := by
  ext i j
  cases i; cases j
  simpa using h.2 ()

/-- The actual singleton target density is the identity. -/
theorem rhoOne : unitProblem.rhoDot=1 := by
  ext i j
  cases i; cases j
  simp [Problem.rhoDot,Problem.targetGram,unitProblem]

/-- The historical coordinate projection really is the identity here. -/
theorem piOne (x z : Unit) : PiZ unitProblem x z=1 := by
  cases x; cases z
  ext i j
  cases i; cases j
  simp [PiZ,unitProblem]

/-- The entire junk optimization reduces to the actual overlap one half. -/
theorem halfOverlap : unitProblem.badOverlap halfBad=1/2 := by
  have hset : {v : ℝ | ∃ M : Matrix Unit Unit ℂ,
      unitProblem.IsNoncoherentJunk M ∧
      v=(halfBad*Matrix.hadamard unitProblem.rhoDot M).trace.re}={1/2} := by
    ext v
    constructor
    · rintro ⟨M,hM,rfl⟩
      rw [junkUnique M hM,rhoOne]
      norm_num [halfBad,Matrix.hadamard,Matrix.trace,Matrix.mul_apply]
    · intro hv
      have hv' : v=1/2 := Set.mem_singleton_iff.mp hv
      refine ⟨1,⟨Matrix.PosSemidef.one,by intro f; simp⟩,?_⟩
      rw [hv',rhoOne]
      norm_num [halfBad,Matrix.hadamard,Matrix.trace,Matrix.mul_apply]
  rw [Problem.badOverlap,hset,csSup_singleton]

/-- The actual L2 operator norm premise holds at eta equal to one quarter. -/
theorem quarterBound (z : Unit) : ‖PiZ unitProblem () z*halfBad‖^2≤(1/4 : ℝ) := by
  rw [piOne,one_mul]
  norm_num [halfBad,norm_smul]

/-- The whole original universally quantified PSD-only target is false. -/
theorem oldTargetFalse : ¬ (∀ (P : Problem) (x : P.Hom)
    (Pibad : Matrix P.F P.F ℂ) (eta : ℝ),
    Pibad.PosSemidef → (∀ z : P.Out, ‖PiZ P x z*Pibad‖^2≤eta) →
    P.badOverlap Pibad≤eta) := by
  intro h
  have hf:=h unitProblem () halfBad (1/4) halfPositive quarterBound
  rw [halfOverlap] at hf
  norm_num at hf

/-- The missing idempotence excludes this normalized counterexample. -/
theorem halfNotProject : halfBad*halfBad≠halfBad := by
  intro h
  have he:=congrArg (fun M : Matrix Unit Unit ℂ => (M () ()).re) h
  norm_num [halfBad,Matrix.mul_apply] at he

end Qatlib.Papers.SymmetryAdv10.MainResults.ProjectorAudit
