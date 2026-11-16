/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QSDPBinOpt19.MainResults.SourceMainResults

@[expose] public section


open Matrix MatrixOrder
open scoped ComplexOrder MatrixOrder BigOperators
open Qatlib.Papers.QSDPBinOpt19.MainResults

set_option autoImplicit false

namespace Qatlib.Papers.QSDPBinOpt19.MainResults

noncomputable section

/-- The abstract update record permits a permanently rejecting, feasible initial state. -/
def stagnantHU : HUInstance (Fin 1) where
  m := 0
  state := fun _ => uniformDiag (Fin 1)
  sepOK := fun _ => False
  infeasible := False
  initial := rfl

/-- No positive tolerance can make the unrestricted abstract update record converge. -/
theorem hu_convergence_counterexample (ε : ℝ) :
    ¬ (stagnantHU.infeasible ∨ ∃ t : ℕ,
      t ≤ huIterationBound (Fintype.card (Fin 1)) ε ∧
        stagnantHU.sepOK (stagnantHU.state t)) := by
  simp [stagnantHU]

/-- A real diagonal matrix has trace norm equal to the sum of absolute entries. -/
private theorem diagonal_trace_norm {I : Type*} [Fintype I] [DecidableEq I]
    (x : I → ℝ) :
    Matrix.traceNorm (Matrix.diagonal (fun j => (x j : ℂ))) = ∑ j, |x j| := by
  have hs : CFC.sqrt ((Matrix.diagonal fun i => (x i : ℂ))ᴴ *
      (Matrix.diagonal fun i => (x i : ℂ))) =
      Matrix.diagonal fun i => ((|x i| : ℝ) : ℂ) := by
    apply CFC.sqrt_unique
    · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal,
        ← Complex.ofReal_mul]
      congr 1
      nlinarith [sq_abs (x i)]
    · apply Matrix.PosSemidef.nonneg
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      exact_mod_cast abs_nonneg (x i)
  unfold Matrix.traceNorm
  rw [hs]
  simp

/-- A trace-one positive matrix may have a zero diagonal entry. -/
def singularState : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![1, 0]

/-- The old diagonal normalization drops the zero coordinate and loses half the trace. -/
theorem diagonal_normalization_counterexample :
    singularState.PosSemidef ∧ Matrix.trace singularState = 1 ∧
      0 < (1 : ℝ) ∧
      Matrix.traceNorm (diagPartC singularState - uniformDiagC (Fin 2)) ≤ (1 : ℝ)^4 ∧
      Matrix.trace (normalizeCorrelation singularState) ≠ 1 := by
  have hp : singularState.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num
  have hd : diagPartC singularState - uniformDiagC (Fin 2) =
      Matrix.diagonal (fun i : Fin 2 => ((![(1 / 2 : ℝ), -(1 / 2 : ℝ)] i : ℝ) : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [diagPartC, uniformDiagC, ncard, singularState, Matrix.diagonal]
  refine ⟨hp, ?_, one_pos, ?_, ?_⟩
  · norm_num [singularState, Matrix.trace, Fin.sum_univ_two]
  · rw [hd, diagonal_trace_norm]
    norm_num [Fin.sum_univ_two]
  · norm_num [normalizeCorrelation, normFactor, ncard, singularState,
      Matrix.trace, Fin.sum_univ_two]

end
end Qatlib.Papers.QSDPBinOpt19.MainResults
