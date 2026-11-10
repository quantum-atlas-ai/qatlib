/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.CyclicRecovery.AlgebraicOracle
import Qatlib.Concepts.WalkFind.UniformThree.ConventionBridge
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
set_option warningAsError false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement

open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Foundations.BornMetrics.EventProbability

namespace Qatlib.Concepts.WalkFind.UniformThree

open Matrix
open scoped Classical

variable {G R : Type*}
  [AddCommGroup G] [Fintype G] [DecidableEq G]
  [AddCommGroup R] [Fintype R] [DecidableEq R]

def HidesSubgroup (f : G → R) (H : AddSubgroup G) : Prop :=
  ∀ x y, f x = f y ↔ x - y ∈ H

noncomputable def addOracleLabelBranch (f : G → R) (ψ : QState G) (z : R) : QState G :=
  fun x => Run (AddOracle f) [Step.query] (TensorState ψ (Ket 0)) (x, z)

omit [AddCommGroup G] in

theorem addOracleLabelBranch_apply (f : G → R) (ψ : QState G) (z : R) (x : G) :
    addOracleLabelBranch f ψ z x = if z = f x then ψ x else 0 :=
  run_addOracle_zero_apply f ψ x z

omit [AddCommGroup G] in

theorem measureProb_addOracleLabelBranch_univ (f : G → R) (ψ : QState G) (z : R) :
    MeasureProb (addOracleLabelBranch f ψ z) Finset.univ =
      MarginalProbRight
        (Run (AddOracle f) [Step.query] (TensorState ψ (Ket 0))) {z} := by
  rw [addOracle_label_weight]
  unfold MeasureProb
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  rw [BornProb, addOracleLabelBranch_apply]
  by_cases h : f x = z
  · rw [if_pos h.symm, if_pos h]
    rfl
  · have hz : z ≠ f x := fun hz => h hz.symm
    rw [if_neg hz, if_neg h]
    simp

omit [AddCommGroup G] in

theorem collapse_addOracle_output_label (f : G → R) (ψ : QState G) (z : R) :
    Collapse (Run (AddOracle f) [Step.query] (TensorState ψ (Ket 0)))
        (Finset.univ ×ˢ {z}) =
      TensorState (addOracleLabelBranch f ψ z) (Ket z) := by
  funext p
  rcases p with ⟨x, y⟩
  by_cases hy : y = z
  · subst y
    simp [collapse_apply, TensorState, Ket, addOracleLabelBranch]
  · simp [collapse_apply, TensorState, Ket, hy, Ne.symm hy]

noncomputable def cosetBranchScale (H : AddSubgroup G) : ℂ :=
  (Real.sqrt (Fintype.card H : ℝ) : ℂ) *
    (Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹

omit [DecidableEq G] in

theorem norm_cosetBranchScale_sq (H : AddSubgroup G) :
    ‖cosetBranchScale H‖ ^ 2 =
      (Fintype.card H : ℝ) / (Fintype.card G : ℝ) := by
  simp [cosetBranchScale, mul_pow, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg _), div_eq_mul_inv]

theorem addOracleLabelBranch_uniform_eq_smul_coset
    (f : G → R) (H : AddSubgroup G) (hf : HidesSubgroup f H) (s : G) :
    addOracleLabelBranch f (Uniform G) (f s) =
      cosetBranchScale H • abelianCosetState H s := by
  funext x
  rw [addOracleLabelBranch_apply]
  simp only [Uniform, Pi.smul_apply, smul_eq_mul, abelianCosetState]
  by_cases hx : x - s ∈ H
  · have hfx : f x = f s := (hf x s).2 hx
    have hz : f s = f x := hfx.symm
    simp only [if_pos hz, if_pos hx]
    have hH : (Real.sqrt (Fintype.card H : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < Fintype.card H by
        exact_mod_cast Fintype.card_pos)).ne'
    change (Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹ =
      ((Real.sqrt (Fintype.card H : ℝ) : ℂ) *
        (Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹) *
          (Real.sqrt (Fintype.card H : ℝ) : ℂ)⁻¹
    symm
    calc
      _ = (Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹ *
          ((Real.sqrt (Fintype.card H : ℝ) : ℂ) *
            (Real.sqrt (Fintype.card H : ℝ) : ℂ)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hH, mul_one]
  · have hfx : f x ≠ f s := fun h => hx ((hf x s).1 h)
    have hz : f s ≠ f x := fun h => hfx h.symm
    simp [hz, hx]

theorem addOracle_hidden_label_weight
    (f : G → R) (H : AddSubgroup G) (hf : HidesSubgroup f H) (s : G) :
    MarginalProbRight
        (Run (AddOracle f) [Step.query] (TensorState (Uniform G) (Ket 0))) {f s} =
      (Fintype.card H : ℝ) / (Fintype.card G : ℝ) := by
  rw [← measureProb_addOracleLabelBranch_univ,
    addOracleLabelBranch_uniform_eq_smul_coset f H hf s,
    measureProb_smul, measureProb_univ (normalized_abelianCosetState H s),
    norm_cosetBranchScale_sq, mul_one]

theorem conditionalState_addOracle_hidden_label
    (f : G → R) (H : AddSubgroup G) (hf : HidesSubgroup f H) (s : G) :
    ConditionalState (addOracleLabelBranch f (Uniform G) (f s)) =
      some (abelianCosetState H s) := by
  have hprob : MeasureProb (addOracleLabelBranch f (Uniform G) (f s)) Finset.univ =
      (Fintype.card H : ℝ) / (Fintype.card G : ℝ) := by
    rw [measureProb_addOracleLabelBranch_univ, addOracle_hidden_label_weight f H hf s]
  have hpos : (0 : ℝ) < (Fintype.card H : ℝ) / (Fintype.card G : ℝ) :=
    div_pos (by exact_mod_cast Fintype.card_pos) (by exact_mod_cast Fintype.card_pos)
  have hscale : cosetBranchScale H =
      (Real.sqrt ((Fintype.card H : ℝ) / (Fintype.card G : ℝ)) : ℂ) := by
    rw [Real.sqrt_div (Nat.cast_nonneg _), Complex.ofReal_div, div_eq_mul_inv]
    rfl
  have hsqrt : (Real.sqrt ((Fintype.card H : ℝ) / (Fintype.card G : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  unfold ConditionalState
  rw [hprob, if_pos hpos]
  congr 1
  funext x
  change (Real.sqrt (MeasureProb (addOracleLabelBranch f (Uniform G) (f s))
      Finset.univ) : ℂ)⁻¹ *
      Collapse (addOracleLabelBranch f (Uniform G) (f s)) Finset.univ x = _
  rw [hprob, collapse_apply, if_pos (Finset.mem_univ x),
    addOracleLabelBranch_uniform_eq_smul_coset f H hf s]
  change (Real.sqrt ((Fintype.card H : ℝ) / (Fintype.card G : ℝ)) : ℂ)⁻¹ *
      (cosetBranchScale H * abelianCosetState H s x) = _
  rw [hscale, ← mul_assoc, inv_mul_cancel₀ hsqrt, one_mul]

theorem conditionalState_addOracle_hidden_label_exists
    (f : G → R) (H : AddSubgroup G) (hf : HidesSubgroup f H) (s : G) :
    ∃ φ : QState G,
      ConditionalState (addOracleLabelBranch f (Uniform G) (f s)) = some φ ∧
        Normalized φ := by
  exact ⟨abelianCosetState H s, conditionalState_addOracle_hidden_label f H hf s,
    normalized_abelianCosetState H s⟩

omit [AddCommGroup G] in

theorem addOracleLabelBranch_eq_zero_of_unused
    (f : G → R) (z : R) (hz : ∀ x, f x ≠ z) :
    addOracleLabelBranch f (Uniform G) z = 0 := by
  funext x
  rw [addOracleLabelBranch_apply]
  have hzx : z ≠ f x := fun h => hz x h.symm
  simp [hzx]

omit [AddCommGroup G] in

theorem conditionalState_addOracleLabelBranch_eq_none_of_unused
    (f : G → R) (z : R) (hz : ∀ x, f x ≠ z) :
    ConditionalState (addOracleLabelBranch f (Uniform G) z) = none := by
  rw [addOracleLabelBranch_eq_zero_of_unused f z hz]
  exact conditionalState_zero

end Qatlib.Concepts.WalkFind.UniformThree
