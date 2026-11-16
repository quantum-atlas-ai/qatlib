/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SymmetryAdv10.MainResults.FreeThreshold
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # A normalized actual two-input witness for the old hybrid collapse -/

set_option autoImplicit false
noncomputable section
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
namespace Qatlib.Papers.SymmetryAdv10.MainResults.SwapWitness
open Qatlib.Papers.SymmetryAdv10.MainResults

/-- A true binary oracle whose target states are the corresponding orthogonal basis vectors. -/
abbrev binaryProblem : Problem where
  F := Fin 2
  Hom := Unit
  Out := Fin 2
  Tgt := Fin 2
  funMap := fun f _ => f
  target := fun f t => if t=f then 1 else 0

/-- The nonzero swap adversary with uniform fixed vector. -/
def swap : Matrix (Fin 2) (Fin 2) ℂ := fun i j => if i=j then 0 else 1

/-- The actual targets are normalized rather than degenerate zero states. -/
theorem targetNorm (f : Fin 2) : ∑ t : Fin 2, ‖binaryProblem.target f t‖^2=1 := by
  fin_cases f <;> norm_num [binaryProblem,Fin.sum_univ_two]

/-- The swap is a Hermitian matrix fixing the actual uniform vector. -/
theorem adversary : binaryProblem.IsAdversaryMatrix swap := by
  constructor
  · ext i j
    by_cases h : i=j <;> simp [swap,Matrix.conjTranspose_apply,h,eq_comm]
  · ext i
    fin_cases i <;> simp [Problem.deltaVec,Matrix.mulVec,dotProduct,Fin.sum_univ_two,swap]

/-- The additive upper constraint is the actual Gram matrix of the vector one minus one. -/
theorem upperPSD : (1-swap).PosSemidef := by
  let r : Matrix Unit (Fin 2) ℂ := fun _ j => if j=0 then 1 else -1
  have he : 1-swap=Matrix.conjTranspose r*r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply,Matrix.conjTranspose_apply]
      <;> norm_num [r,swap,Matrix.one_apply]
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self r

/-- The additive lower constraint is the actual Gram matrix of the all-ones vector. -/
theorem lowerPSD : (1+swap).PosSemidef := by
  let r : Matrix Unit (Fin 2) ℂ := fun _ _ => 1
  have he : 1+swap=Matrix.conjTranspose r*r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply,Matrix.conjTranspose_apply]
      <;> norm_num [r,swap,Matrix.one_apply]
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self r

/-- All actual additive feasibility conditions are proved. -/
theorem additive : binaryProblem.IsAdditiveAdversary swap :=
  ⟨adversary,upperPSD,lowerPSD⟩

/-- The distinguishing query annihilates the off-diagonal swap entries. -/
theorem restriction : binaryProblem.GammaX swap ()=0 := by
  ext i j
  by_cases h : i=j <;> simp [Problem.GammaX,Problem.D,Matrix.hadamard,swap,binaryProblem,h,eq_comm]

/-- The actual denominator is strictly positive, witnessed by an off-diagonal entry. -/
theorem positiveDen : 0<binaryProblem.maxGammaDiff swap := by
  have he : binaryProblem.maxGammaDiff swap=‖swap‖ := by
    have hr : ∀ x : Unit, binaryProblem.GammaX swap x=0 := by
      intro x
      cases x
      exact restriction
    simp [Problem.maxGammaDiff,hr]
  rw [he]
  apply norm_pos_iff.mpr
  intro hz
  have hc:=congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) hz
  norm_num [swap] at hc

/-- The old hybrid functional really collapses on this normalized, nonzero actual instance. -/
theorem actualCollapse (eps : ℝ) (heps : eps<1) : binaryProblem.advHat eps=0 :=
  FreeThreshold.boundCollapse binaryProblem swap additive positiveDen eps heps

/-- The exact historical marked-item search problem on its entire dimension domain. -/
abbrev searchProblem (n : ℕ) : Problem where
  F := Fin n
  Hom := Fin n
  Out := Bool
  Tgt := Fin n
  funMap := fun f x => decide (f=x)
  target := fun f t => if t=f then 1 else 0

/-- The actual marked-item search query separates both inputs in dimension two. -/
theorem searchRestrict (x : Fin 2) : (searchProblem 2).GammaX swap x=0 := by
  ext i j
  fin_cases x <;> fin_cases i <;> fin_cases j <;>
    norm_num [Problem.GammaX,Problem.D,Matrix.hadamard,swap,searchProblem]

/-- The same genuine additive witness is feasible for the actual search problem. -/
theorem searchAdditive : (searchProblem 2).IsAdditiveAdversary swap := by
  change binaryProblem.IsAdditiveAdversary swap
  exact additive

/-- The actual search denominator is positive. -/
theorem searchDen : 0<(searchProblem 2).maxGammaDiff swap := by
  have he : (searchProblem 2).maxGammaDiff swap=binaryProblem.maxGammaDiff swap := by
    simp [Problem.maxGammaDiff,searchRestrict,show ∀ x : Unit,
      binaryProblem.GammaX swap x=0 from fun x => by cases x; exact restriction]
  rw [he]
  exact positiveDen

/-- The historical hybrid functional vanishes on actual search with two marked-item inputs. -/
theorem searchCollapse (eps : ℝ) (heps : eps<1) : (searchProblem 2).advHat eps=0 :=
  FreeThreshold.boundCollapse (searchProblem 2) swap searchAdditive searchDen eps heps

/-- The complete old hybrid search lower-bound interface fails at n two and epsilon one quarter. -/
theorem oldSearchFalse : ¬ (∀ (n : ℕ), 0<n → ∀ eps : ℝ, 0<eps → eps<1-1/(n : ℝ) →
    ∃ c : ℝ, 0<c ∧ c*(Real.sqrt (1-eps)-1/Real.sqrt n)^2*Real.sqrt n≤
      (searchProblem n).advHat eps) := by
  intro h
  obtain ⟨c,hc,hbound⟩:=h 2 (by norm_num) (1/4) (by norm_num) (by norm_num)
  rw [searchCollapse (1/4) (by norm_num)] at hbound
  have hs : 1/Real.sqrt 2<Real.sqrt (1-(1/4 : ℝ)) := by
    rw [one_div,← Real.sqrt_inv]
    apply Real.sqrt_lt_sqrt <;> norm_num
  have hsq : 0<(Real.sqrt (1-(1/4 : ℝ))-1/Real.sqrt 2)^2 :=
    sq_pos_of_pos (sub_pos.mpr hs)
  have hp : 0<c*(Real.sqrt (1-(1/4 : ℝ))-1/Real.sqrt 2)^2*Real.sqrt 2 :=
    mul_pos (mul_pos hc hsq) (Real.sqrt_pos.mpr (by norm_num))
  exact (not_le_of_gt hp) hbound

end Qatlib.Papers.SymmetryAdv10.MainResults.SwapWitness
