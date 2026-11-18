/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamLCUSim12.TaylorBounds.DefectOrder
public import Qatlib.Papers.HamLCUSim12.FullSimulation.Lemma8Bound
public import Qatlib.Papers.HamLCUSim12.FullSimulation.Lemma10Inverse
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! Concrete satisfiable instances of the conditional multiproduct estimates.

The two nodes have nonzero low-order defects that cancel with signed weights,
while the common fifth-order residual is nonzero. A reflection supplies a
nonidentity correction map with an exact inverse. Zero correction is the
negative example: normalization alone does not establish the source inverse
bound. These tests do not construct a Hamiltonian or a Suzuki integrator.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QatlibTests.HamLCUSim12DefectRegression

open scoped BigOperators
open Qatlib.Papers.HamLCUSim12.TaylorBounds.DefectOrder
open Qatlib.Papers.HamLCUSim12.FullSimulation.Lemma8Bound
open Qatlib.Papers.HamLCUSim12.FullSimulation.Lemma10Inverse

/-- The first-order extrapolation coefficients at nodes one and two. -/
def coeff (q : Fin 2) : ℝ := if q = 0 then -1 / 3 else 4 / 3

/-- Two distinct positive integrator repetition parameters. -/
def node (q : Fin 2) : ℝ := if q = 0 then 1 else 2

/-- A nonconstant reference curve for the scalar defect test. -/
def evolution (s : ℝ) : ℝ := 1 + s

/-- An explicit node word with nonzero cubic defect and fifth-order residual. -/
def nodeWord (q : Fin 2) (s : ℝ) : ℝ :=
  evolution s + s ^ 3 / node q ^ 2 * 3 + s ^ 5 / 100

/-- The signed coefficients satisfy the zeroth moment row. -/
private theorem coeff_sum : ∑ q : Fin 2, coeff q = 1 := by
  norm_num [coeff, Fin.sum_univ_two]

/-- The signed coefficients cancel the first inverse-square moment. -/
private theorem moment_zero : ∑ q : Fin 2, coeff q / node q ^ 2 = 0 := by
  norm_num [coeff, node, Fin.sum_univ_two]

/-- All required positive-order moment rows reduce to the first row at `k = 1`. -/
private theorem moment_row (j : ℕ) (hj : j < 1) :
    (∑ q : Fin 2, coeff q / node q ^ (2 * 1 + 2 * j)) = 0 := by
  have hj0 : j = 0 := by omega
  subst j
  simpa using moment_zero

-- The residual is positive, so this fixture does not merely use exact words.
example : (∑ q, coeff q * nodeWord q (1 / 10)) - evolution (1 / 10) =
    (1 / 10 : ℝ) ^ 5 / 100 := by
  norm_num [coeff, node, nodeWord, evolution, Fin.sum_univ_two]

-- The conditional Eq.(39) bound accepts an explicitly satisfied node defect.
example : ‖(∑ q, coeff q • nodeWord q (1 / 10)) - evolution (1 / 10)‖ ≤
    (2 * (1 : ℝ) * (5 / 3) ^ (1 - 1 : ℕ) * 1 * (1 / 10)) ^ (4 * 1 + 1) := by
  apply lemma8_multiproduct_bound 1 (by omega) 1 1 (1 / 10)
    (by norm_num) (by norm_num) (by norm_num) coeff node
    coeff_sum moment_row
    evolution nodeWord (fun _ => 3)
    (by
      intro q
      fin_cases q <;> norm_num [coeff])
  intro q
  fin_cases q <;>
    norm_num [nodeWord, evolution, node, Fin.sum_univ_one, Real.norm_eq_abs]

-- The bundled cancellation theorem also has a concrete nonzero remainder.
example : ‖(∑ q, coeff q • nodeWord q (1 / 10)) - evolution (1 / 10)‖ ≤
    (∑ q, |coeff q|) * 1 * (1 / 10 : ℝ) ^ (2 * (1 + 1) + 1) := by
  apply multiproduct_order_at 1 1 coeff node
    coeff_sum moment_row
    evolution nodeWord (fun _ => 3) 1 (1 / 10)
  intro q
  fin_cases q <;>
    norm_num [nodeWord, evolution, node, Fin.sum_univ_one, Real.norm_eq_abs]

-- A nonunit-length vector exercises the normalization adjustment.
example : ‖(1 : ℝ) - (‖(9 / 8 : ℝ)‖)⁻¹ • (9 / 8 : ℝ)‖ ≤ 2 * (1 / 8) := by
  apply norm_div_two (9 / 8 : ℝ) 1 (1 / 8)
    (by norm_num) (by norm_num) (by norm_num)

/-- The reflection is a nonidentity continuous linear map with inverse itself. -/
def reflection (_ : ℝ) : ℝ →L[ℝ] ℝ := -ContinuousLinearMap.id ℝ ℝ

-- All premises of the conditional inverse estimate hold with positive step
-- and positive Hamiltonian-scale parameters; the correction is not identity.
example : ‖(1 : ℝ) - ekMap reflection (-(1 / 4))
    (ekMap reflection (1 / 4) 1)‖ ≤
      (2 * (1 : ℝ) * 1 * (5 / 3) ^ (1 - 1 : ℕ) * 1 * (1 / 4)) ^ (4 * 1 + 2) := by
  have hbound := lemma10_inverse_defect (E := ℝ) 1 (by omega) 1 1 (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) reflection
    (by
      intro φ _
      simp only [reflection, neg_apply, ContinuousLinearMap.id_apply,
        neg_neg, sub_self, norm_zero]
      positivity)
    (1 : ℝ) (by norm_num)
  simpa only [Nat.cast_one] using hbound

example : reflection 0 (1 : ℝ) ≠ 1 := by
  norm_num [reflection]

-- A zero aggregate normalizes to zero and has inverse defect one, hence it
-- cannot satisfy the small-error premise at zero step.
example : ‖(1 : ℝ) - ekMap (fun _ => (0 : ℝ →L[ℝ] ℝ)) 0
    (ekMap (fun _ => (0 : ℝ →L[ℝ] ℝ)) 0 1)‖ = 1 := by
  norm_num [ekMap]

example : ¬ ‖(0 : ℝ →L[ℝ] ℝ) ((0 : ℝ →L[ℝ] ℝ) 1) - 1‖ ≤ (0 : ℝ) ^ 6 := by
  norm_num

/-- A positive aggregate with a genuine nonzero single-step error. -/
def stretch : ℝ →L[ℝ] ℝ := (9 / 8 : ℝ) • ContinuousLinearMap.id ℝ ℝ

/-- This aggregate is exactly one eighth away from the reference in operator norm. -/
private theorem stretch_error : ‖stretch - ContinuousLinearMap.id ℝ ℝ‖ = 1 / 8 := by
  have h : stretch - ContinuousLinearMap.id ℝ ℝ =
      (1 / 8 : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro x
    change (9 / 8 : ℝ) * x - x = (1 / 8 : ℝ) * x
    ring
  rw [h, norm_smul, ContinuousLinearMap.norm_id]
  norm_num

-- The new composition estimate has a nonzero numerator, attaining 2ε+ε².
example : ‖stretch (stretch 1) - (1 : ℝ)‖ = 17 / 64 := by
  norm_num [stretch]

example : ‖stretch (stretch 1) - (1 : ℝ)‖ ≤ 2 * (1 / 8 : ℝ) + (1 / 8 : ℝ) ^ 2 := by
  apply composition_defect_of_approx stretch stretch
    (ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ) (1 / 8)
    (by norm_num) stretch_error.le stretch_error.le
    ContinuousLinearMap.norm_id_le ContinuousLinearMap.norm_id_le 1 (by norm_num)
  simp

-- The denominator-free composition identity also covers a zero first map.
example : ekMap (fun _ => (0 : ℝ →L[ℝ] ℝ)) (-1)
    (ekMap (fun _ => (0 : ℝ →L[ℝ] ℝ)) 1 1) = 0 := by
  rw [ek_composition_all]
  simp

-- A nonidentity reference pair satisfies the new operator-error interface.
example : ‖(1 : ℝ) - ekMap reflection (-1) (ekMap reflection 1 1)‖ ≤ 5 * (1 / 8) := by
  apply normalized_inverse_of_approx reflection 1 (reflection 0) (reflection 0) (1 / 8)
    (by norm_num) (by norm_num)
    (by norm_num [reflection]) (by norm_num [reflection])
    (by simpa only [reflection, norm_neg] using
      (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ)))
    (by simpa only [reflection, norm_neg] using
      (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ)))
    1 (by norm_num)
  norm_num [reflection]

end QatlibTests.HamLCUSim12DefectRegression
