/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Qatlib Contributors
-/
module

public import Qatlib.Papers.VarTimeAmpAmp10.MainTheorem.CostAssembly
public import Qatlib.Papers.VarTimeAmpAmp10.MainTheorem.MainReadout
public import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.Algo5Readout
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# MiscFill VarTimeAmpAmp10 concrete instances

Concrete satisfiable instances for the Theorem 3 cost-assembly lemmas
(`vtRatioBound`, `vtDominate`, `thm3DerivedCost`) and the Algorithm 5 Fourier
readout (`readoutZeroEntry`, `idealErasure`), with numeric checks of the
`1/m` zero-outcome mass and the label-independent zero block.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
noncomputable section

open Qatlib.Papers.VarTimeAmpAmp10.MainTheorem.CostAssembly
open Qatlib.Papers.VarTimeAmpAmp10.MainTheorem.MainReadout
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.Algo5Readout

namespace QatlibTests.MiscFillVarTimeAmpAmp10

/-- Numeric instance of the shared-sum ratio cancellation. -/
example : (4 : ℝ) / Real.sqrt (1 / 2) ≤ Real.sqrt (32 / 1) * (2 / 1) * |1| := by
  have h := vtRatioBound 2 1 32 1 (1 / 2) 4 (1 / 2) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by nlinarith [sq_nonneg 4])
    (by norm_num)
  exact h

/-- The domination step on concrete numbers. -/
example (tmax total : ℝ) (htmax1 : 1 ≤ tmax)
    (htmax : tmax ≤ 3 / Real.sqrt (1 / 2)) (htmaxle : tmax ≤ 5 * 2 / 1)
    (hvt : total ≤ 1 * (tmax * Real.sqrt (Real.log tmax)
        + (3 / Real.sqrt (1 / 2)) * (Real.log (5 * 2 / 1)
          * Real.sqrt (Real.log (5 * 2 / 1))))) :
    total ≤ 2 * 1 * (3 / Real.sqrt (1 / 2) * (Real.log (5 * 2 / 1)
      * Real.sqrt (Real.log (5 * 2 / 1)))) := by
  refine vtDominate 1 tmax 3 (1 / 2) 5 2 1 (by norm_num) (by norm_num)
    htmax1 htmax htmaxle ?_ total hvt
  exact le_of_lt (lt_of_lt_of_le Real.exp_one_lt_three (by norm_num))

/-- The zero block of an ideal amplified state with two register states and
step labels `1` and `2`: independent of the labels, equal to `β/√3`. -/
example : ∀ i : Fin 2,
    zeroBlock 3 (idealState 3 ![Complex.ofReal 1, Complex.ofReal 1]
        ![⟨1, by omega⟩, ⟨2, by omega⟩]) i
      = Complex.ofReal 1 * invSqrtM 3 := by
  intro i
  have h := (idealErasure 3 ![Complex.ofReal 1, Complex.ofReal 1]
    ![⟨1, by omega⟩, ⟨2, by omega⟩]).2 i
  fin_cases i <;> simpa using h

/-- The zero-outcome mass for the same state is exactly `2/3`: the source's
`1/m` success factor scaled by the explicitly unnormalized input mass `2`. -/
example : (∑ i : Fin 2, Complex.normSq (zeroBlock 3
      (idealState 3 ![Complex.ofReal 1, Complex.ofReal 1]
        ![⟨1, by omega⟩, ⟨2, by omega⟩]) i)) = 2 / 3 := by
  have h := (idealErasure 3 ![Complex.ofReal 1, Complex.ofReal 1]
    ![⟨1, by omega⟩, ⟨2, by omega⟩]).1
  rw [h]
  have hns : (∑ i : Fin 2, Complex.normSq (![Complex.ofReal 1, Complex.ofReal 1] i))
      = (2 : ℝ) := by
    simp
    norm_num
  rw [hns]
  norm_num

/-- Negative instance: a label-concentrated step state strictly loses mass in
the zero-outcome readout — the probability is `1/2 < 1 = ∑ ‖a j‖²`, so the
`1/m` factor of `readoutSingle` is a genuine loss, not a relabeling. -/
theorem notMassPreserv :
    readoutProb 2 (fun j : Fin 2 => if j = 0 then (1 : ℂ) else 0)
      < ∑ j : Fin 2, ‖(if j = 0 then (1 : ℂ) else 0)‖ ^ 2 := by
  rw [readoutSingle 2 0 1]
  have h1 : ∑ j : Fin 2, ‖(if j = 0 then (1 : ℂ) else 0)‖ ^ 2 = 1 := by
    have e1 : ((1 : Fin 2) = 0) = False := by decide
    simp [Fin.sum_univ_two, e1]
  rw [h1]
  rw [show ‖(1 : ℂ)‖ = 1 by simp]
  norm_num

end QatlibTests.MiscFillVarTimeAmpAmp10
