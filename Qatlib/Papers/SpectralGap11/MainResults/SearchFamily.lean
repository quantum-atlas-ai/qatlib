/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpectralGap11.MainResults.SourceTheorem1GapAmplification
public import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws

/-!
# A constant-term frustration-free search family

The input register has a branch bit and a search word. The first projector
requires the false branch to be uniform. The second requires the true branch
to vanish away from the marked word and fixes its ratio at that word.
Their common zero state has constant overlap with the known initial branch
and with the marked true-branch word. No preparation algorithm is postulated.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.SpectralGap11.MainResults.SearchFamily

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open scoped BigOperators

noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

/-- A controlled block matrix with the label preceding the system index. -/
def splitBlocks (B : K → Matrix I I ℂ) : Matrix (K × I) (K × I) ℂ :=
  fun row col => if row.1 = col.1 then B row.1 row.2 col.2 else 0

omit [DecidableEq I] in
/-- Controlled orthogonal projections are actual idempotent matrices. -/
theorem splitBlocks_sq (B : K → Matrix I I ℂ) (hB : ∀ k, B k * B k = B k) :
    splitBlocks B * splitBlocks B = splitBlocks B := by
  ext ⟨k, i⟩ ⟨l, j⟩
  simp only [splitBlocks, Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases hkl : k = l
  · subst l
    simp
    exact congrFun (congrFun (hB k) i) j
  · simp [hkl]

omit [Fintype I] [Fintype K] [DecidableEq I] in
/-- Controlled Hermitian blocks remain Hermitian. -/
theorem splitBlocks_hermitian (B : K → Matrix I I ℂ) (hB : ∀ k, (B k).IsHermitian) :
    (splitBlocks B).IsHermitian := by
  change (splitBlocks B)ᴴ = splitBlocks B
  ext ⟨k, i⟩ ⟨l, j⟩
  by_cases hkl : k = l
  · subst l
    simpa [splitBlocks, Matrix.conjTranspose_apply] using
      congrFun (congrFun (hB k).eq i) j
  · simp [splitBlocks, Matrix.conjTranspose_apply, hkl, Ne.symm hkl]

omit [DecidableEq I] in
/-- Every label branch is acted on by its actual controlled matrix. -/
theorem splitBlocks_mulVec (B : K → Matrix I I ℂ) (v : K × I → ℂ) (k : K) (i : I) :
    (splitBlocks B *ᵥ v) (k, i) = (B k *ᵥ (fun j => v (k, j))) i := by
  simp [splitBlocks, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

/-- The normalized two-branch constraint state at the marked word. -/
def markedState (M : ℕ) : Bool → ℂ :=
  fun b => (((if b then Real.sqrt M else 1) / Real.sqrt (M + 1) : ℝ) : ℂ)

omit [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] in
/-- The marked constraint state is normalized by its actual amplitudes. -/
theorem markedState_normalized (M : ℕ) : Normalized (markedState M) := by
  have hden : Real.sqrt (M + 1 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ M by positivity)
  have hd := Real.sq_sqrt (show (0 : ℝ) ≤ M + 1 by positivity)
  simp [Normalized, markedState,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  field_simp [hden]
  simp only [sq_abs, hs, hd]
  ring

/-- The known projection: uniform false branch, unconstrained true branch. -/
def freeP : Matrix (Bool × I) (Bool × I) ℂ :=
  splitBlocks (fun b : Bool => if b then 1 else outerProduct (Uniform I))

/-- The marked constraint projector is controlled by the actual word label. -/
def markedQ (x : I) : Matrix (Bool × I) (Bool × I) ℂ :=
  Matrix.blockDiagonal (fun y : I =>
    outerProduct (if y = x then markedState (Fintype.card I) else Ket false))

/-- The known projection is idempotent for a nonempty search space. -/
theorem freeP_sq (hI : 0 < Fintype.card I) : freeP (I := I) * freeP = freeP := by
  apply splitBlocks_sq
  intro b
  cases b
  · exact (isOrthogonalProjector_outerProduct (normalized_uniform hI)).1
  · simp

/-- The known projection is Hermitian. -/
theorem freeP_hermitian (hI : 0 < Fintype.card I) : (freeP (I := I)).IsHermitian := by
  apply splitBlocks_hermitian
  intro b
  cases b
  · exact (isOrthogonalProjector_outerProduct (normalized_uniform hI)).2
  · exact Matrix.isHermitian_one

/-- Each actual marked constraint is a projection. -/
theorem markedQ_sq (x : I) : markedQ x * markedQ x = markedQ x := by
  rw [markedQ, ← Matrix.blockDiagonal_mul]
  congr 1
  funext y
  by_cases hy : y = x
  · simp only [hy, ↓reduceIte]
    exact (isOrthogonalProjector_outerProduct (markedState_normalized _)).1
  · simp only [hy, ↓reduceIte]
    exact (isOrthogonalProjector_outerProduct (normalized_ket false)).1

/-- The actual marked constraint is Hermitian. -/
theorem markedQ_hermitian (x : I) : (markedQ x).IsHermitian := by
  change (Matrix.blockDiagonal _)ᴴ = _
  rw [Matrix.blockDiagonal_conjTranspose]
  congr 1
  funext y
  by_cases hy : y = x
  · simp only [hy, ↓reduceIte]
    exact (isOrthogonalProjector_outerProduct (markedState_normalized _)).2
  · simp only [hy, ↓reduceIte]
    exact (isOrthogonalProjector_outerProduct (normalized_ket false)).2

/-- The actual input Hamiltonian has two complementary projector terms. -/
def hardHamiltonian (x : I) : Matrix (Bool × I) (Bool × I) ℂ :=
  (1 - freeP) + (1 - markedQ x)

/-- The two input terms are specified explicitly. -/
def hardTerms (x : I) : Bool → Matrix (Bool × I) (Bool × I) ℂ :=
  fun b => if b then 1 - markedQ x else 1 - freeP

/-- Summing the specified two terms gives the actual hard-family Hamiltonian. -/
theorem hardTerms_sum (x : I) : ∑ b, hardTerms x b = hardHamiltonian x := by
  simp [hardTerms, hardHamiltonian]
  module

end

end Qatlib.Papers.SpectralGap11.MainResults.SearchFamily
