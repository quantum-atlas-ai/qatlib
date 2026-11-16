/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SymmetryAdv10.MainResults.SourceModel
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # The old arbitrary-basis block target lacks representation hypotheses

Fixed source1012.2112v1 Lemma25 uses the canonical stabilizer decomposition
and an invariant adversary. The old header quantifies over arbitrary matrices
and every unitary basis. An actual normalized two-input instance disproves
that universal interface, without refuting the source decomposition theorem.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.SymmetryAdv10.MainResults.BlockAudit
open Qatlib.Papers.SymmetryAdv10.MainResults

/-- The exact historical dependent block-diagonal matrix. -/
def blockDiagSigma {ι : Type} [DecidableEq ι]
    (m : ι → Type)
    (D : ∀ i, Matrix (m i) (m i) ℂ) : Matrix (Σ i, m i) (Σ i, m i) ℂ :=
  fun p q => if h : p.1=q.1 then D p.1 p.2 (h ▸ q.2) else 0

/-- Two singleton blocks, with a normalized target for each actual input. -/
abbrev twoProblem : Problem where
  F := Σ _ : Fin 2, Unit
  Hom := Unit
  Out := Unit
  Tgt := Unit
  funMap := fun _ _ => ()
  target := fun _ _ => 1

/-- A real symmetric matrix mixing the two proposed blocks. -/
def swap : Matrix (Σ _ : Fin 2, Unit) (Σ _ : Fin 2, Unit) ℂ :=
  fun i j => if i.1=j.1 then 0 else 1

/-- The chosen target vectors have unit squared norm. -/
theorem targetNorm (f : twoProblem.F) :
    ∑ t : Unit, ‖twoProblem.target f t‖^2=1 := by
  norm_num [twoProblem]

/-- The mixing matrix is Hermitian, so failure is not caused by non-Hermiticity. -/
theorem swapHermitian : swap.IsHermitian := by
  ext i j
  by_cases h : i.1=j.1 <;> simp [swap,Matrix.conjTranspose_apply,h,eq_comm]

/-- Equal oracle outputs leave the actual restricted matrix unchanged. -/
theorem restriction : twoProblem.GammaX swap ()=swap := by
  ext i j
  simp [Problem.GammaX,Problem.D,Matrix.hadamard,twoProblem]

/-- The whole arbitrary-unitary historical block-decomposition contract is false. -/
theorem oldTargetFalse : ¬ (∀ (P : Problem) (l : Type) [Fintype l] [DecidableEq l]
    (m : l → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (Γ : Matrix P.F P.F ℂ) (x : P.Hom) (U : Matrix P.F (Σ i, m i) ℂ),
    (U*Matrix.conjTranspose U=1 ∧ Matrix.conjTranspose U*U=1) →
    ∃ D : ∀ i, Matrix (m i) (m i) ℂ,
      Matrix.conjTranspose U*P.GammaX Γ x*U=blockDiagSigma m D) := by
  intro h
  obtain ⟨D,hD⟩:=h twoProblem (Fin 2) (fun _ => Unit) swap () 1 (by simp)
  have he:=congrArg (fun M : Matrix (Σ _ : Fin 2, Unit) (Σ _ : Fin 2, Unit) ℂ =>
      M ⟨0,()⟩ ⟨1,()⟩) hD
  simp [restriction,blockDiagSigma,swap] at he

end Qatlib.Papers.SymmetryAdv10.MainResults.BlockAudit
