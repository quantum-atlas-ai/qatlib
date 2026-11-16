/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SparseNetwork13.MainResults.Model.SpectralModel
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ext

@[expose] public section


/-! A two-vertex counterexample to the unrestricted modified-gap contract. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.SparseNetwork13.MainResults.Spectral.ContractProbe
open Matrix BigOperators
open Qatlib.Papers.SparseNetwork13.MainResults.Model

/-- Two vertices joined by an edge of conductance one quarter. -/
def smallEdge : ElecNetwork (Fin 2) (Fin 1) where
  tail _ := 0
  head _ := 1
  w _ := 1 / 4
  w_pos _ := by norm_num
  nonloop _ := by decide

/-- The two-dimensional Laplacian with scalar diagonal coefficient. -/
def pairMat (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a,-a;-a,a]

/-- The nonconstant line on two vertices. -/
def pairOrth : Set (Fin 2 → ℝ) := {x | x 0 + x 1 = 0}

/-- Every nonzero vector on the nonconstant line has the same Rayleigh quotient. -/
theorem pairRayleigh (a : ℝ) (x : Fin 2 → ℝ)
    (hx : x ∈ pairOrth) (hne : x ≠ 0) : rayleigh (pairMat a) x = 2 * a := by
  have hx1 : x 1 = -x 0 := by change x 0 + x 1 = 0 at hx; linarith
  have hx0 : x 0 ≠ 0 := by
    intro h
    apply hne
    funext i
    fin_cases i <;> simp_all
  have hd : x 0 * x 0 + x 1 * x 1 ≠ 0 := by
    have hp := sq_pos_of_ne_zero hx0
    nlinarith [sq_nonneg (x 1)]
  unfold rayleigh
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  apply (div_eq_iff hd).mpr
  simp [pairMat, hx1]
  ring

/-- The entire constrained Rayleigh range is a singleton, so its infimum is exact. -/
theorem pairRange (a : ℝ) : rayleighRange (pairMat a) pairOrth = {2 * a} := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hn⟩, rfl⟩
    exact pairRayleigh a x hx hn
  · intro hy
    have hy' : y = 2 * a := hy
    subst y
    refine ⟨![1,-1], ⟨?_, ?_⟩, ?_⟩
    · norm_num [pairOrth]
    · intro h
      have hh := congrFun h (0 : Fin 2)
      norm_num at hh
    · exact pairRayleigh a _ (by norm_num [pairOrth]) (by
        intro h
        have hh := congrFun h (0 : Fin 2)
        norm_num at hh)

/-- The constrained variational infimum of the two-point matrix is its nonzero eigenvalue. -/
theorem pairMin (a : ℝ) : rayleighMinOver (pairMat a) pairOrth = 2 * a := by
  unfold rayleighMinOver
  rw [pairRange, csInf_singleton]

/-- Both original vertex degrees are one quarter. -/
theorem smallDegree (v : Fin 2) : weightedDegree smallEdge v = 1 / 4 := by
  fin_cases v <;> norm_num [weightedDegree, smallEdge, Fin.sum_univ_one]

/-- The original normalized Laplacian is the unit two-point Laplacian. -/
theorem smallMatrix : normalizedLaplacian smallEdge = pairMat 1 := by
  funext u v
  fin_cases u <;> fin_cases v <;>
    norm_num [normalizedLaplacian, smallDegree, weightedDegree, laplacian, Matrix.mul_apply,
      Fin.sum_univ_one, incident, weightMatrix, smallEdge, pairMat]

/-- Adding degree two while taking zero external current rescales the Laplacian by one ninth. -/
theorem modifiedMatrix : normalizedModifiedLaplacian smallEdge 2 (fun _ => 0) =
    pairMat (1 / 9) := by
  funext u v
  fin_cases u <;> fin_cases v <;>
    norm_num [normalizedModifiedLaplacian, modifiedLaplacian, weightedDegreeMod,
      smallDegree, weightedDegree, laplacian, Matrix.mul_apply, Fin.sum_univ_one,
      incident, weightMatrix, smallEdge, pairMat]

/-- The original degree-weighted orthogonal subspace is exactly the nonconstant line. -/
theorem smallOrth : degreeOrthogonal smallEdge = pairOrth := by
  ext x
  simp only [degreeOrthogonal, pairOrth, Set.mem_ofPred_eq, Fin.sum_univ_two, smallDegree]
  norm_num
  constructor <;> intro h <;> linarith

/-- The modified degree-weighted orthogonal subspace is the same nonconstant line. -/
theorem modifiedOrth : degreeModOrthogonal smallEdge 2 = pairOrth := by
  ext x
  simp only [degreeModOrthogonal, pairOrth, Set.mem_ofPred_eq, Fin.sum_univ_two,
    weightedDegreeMod, smallDegree]
  norm_num
  constructor <;> intro h <;> linarith

/-- The actual original variational normalized gap is two. -/
theorem originalGap : lambda2Normalized smallEdge = 2 := by
  unfold lambda2Normalized
  rw [smallMatrix, smallOrth, pairMin]
  norm_num

/-- The actual modified variational normalized gap is two ninths. -/
theorem modifiedGap : lambda2NormalizedMod smallEdge 2 (fun _ => 0) = 2 / 9 := by
  unfold lambda2NormalizedMod
  rw [modifiedMatrix, modifiedOrth, pairMin]
  norm_num

/-- The literal legacy Lemma 7 contract fails on a positive-weight two-vertex network.
This refutes the missing-hypothesis formalization, not the source theorem. -/
theorem legacyGapFalse :
    ¬ (∀ (G : ElecNetwork (Fin 2) (Fin 1)) (lam : ℝ) (iext : Fin 2 → ℝ),
      0 < lam → lam ≤ lambda2Normalized G →
      lam / 3 ≤ lambda2NormalizedMod G lam iext) := by
  intro h
  have hh := h smallEdge 2 (fun _ => 0) (by norm_num) (by simpa only [originalGap] using (le_refl (2 : ℝ)))
  rw [modifiedGap] at hh
  norm_num at hh
end Qatlib.Papers.SparseNetwork13.MainResults.Spectral.ContractProbe
