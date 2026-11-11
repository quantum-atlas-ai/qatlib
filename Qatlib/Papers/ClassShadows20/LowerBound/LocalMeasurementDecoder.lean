/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClassShadows20.LowerBound.LocalMeasurementLowerBoundSubgoalStat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Qatlib.Papers.ClassShadows20.LowerBound.LocalShotPauliMomentSubgoalHuan
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Decoding local measurement predictions

Uniformly accurate predictions of a single elevated coordinate determine that coordinate by
maximization. The remaining lemmas bound local Pauli overlaps, prove nonnegativity of the
code-state shot values, and establish trace and measurement normalization identities used in
local measurement lower bounds.

These constructions support the treatment in [HuangKuengPreskill2020].

## Main statements

* `local_good_prediction_decodes`: recovers the distinguished coordinate from an accurate
  maximizing prediction.
* `local_shot_sum`: normalizes shot values from measurement completeness and unit trace.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdversaryBounds.AdvDuality

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
namespace Qatlib.Papers.ClassShadows20.LowerBound
open Matrix
open scoped Classical BigOperators ComplexOrder

/-- Predictions within `ε` of a vector with value `3 * ε` at `x` and zero elsewhere have a
strict maximum at `x` when `ε > 0`. -/
lemma local_good_prediction_unique_max {M : ℕ} (ε : ℝ) (hε : 0 < ε)
    (v : Fin M → ℝ) (x : Fin M)
    (hv : ∀ i, |v i - 3 * ε * (if i = x then (1 : ℝ) else 0)| ≤ ε) :
    ∀ i, i ≠ x → v i < v x := by
  intro i hi
  have hx := (abs_le.mp (hv x)).1
  have hii := (abs_le.mp (hv i)).2
  simp at hx
  simp only [if_neg hi, mul_zero, sub_zero] at hii
  linarith

/-- A maximizing coordinate of predictions within `ε` of the distinguished-coordinate signal
must equal its index `x` when `ε > 0`. -/
lemma local_good_prediction_decodes {M : ℕ} (ε : ℝ) (hε : 0 < ε)
    (v : Fin M → ℝ) (x d : Fin M)
    (hmax : ∀ i, v i ≤ v d)
    (hv : ∀ i, |v i - 3 * ε * (if i = x then (1 : ℝ) else 0)| ≤ ε) : d = x := by
  by_contra h
  exact (not_le_of_gt (local_good_prediction_unique_max ε hε v x hv d h)) (hmax x)

/-- The local Pauli overlap has absolute value at most one for a pure density operator and a
unitary conjugation. -/
lemma local_wire_overlap_abs {J : Type} (Uf : J → Operator 2) (P : Operator 2)
    (hP : IsPureDensityOperator P) (a : Option (Fin 3)) (u : J)
    (hU : Uf u ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    |localPauliOverlap Uf P a u| ≤ 1 := by
  cases a with
  | none => simp [localPauliOverlap]
  | some b =>
    let Q := (Uf u)ᴴ * P * Uf u
    have hQ : IsDensityOperator Q := by
      refine ⟨hP.1.1.conjTranspose_mul_mul_same _, ?_⟩
      have hu : Uf u * (Uf u)ᴴ = 1 := by
        simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hU
      dsimp [Q]
      rw [Matrix.trace_mul_cycle, hu, Matrix.one_mul, hP.1.2]
    have ht : (Matrix.trace (pauliMatrix b * Q)).re = localPauliOverlap Uf P (some b) u := by
      simp only [localPauliOverlap, Q, Matrix.mul_assoc]
    have hpos : ∀ s : Bool, 0 ≤ (Matrix.trace (PauliProjector b s * Q)).re := by
      intro s
      have hn := (pauliRecordDist Q hQ).nonneg (b,s)
      have he := (pauli_record_kraus_and_mass.2 Q (b,s)).2
      change 0 ≤ instrumentProb pauliShadowRecordInstrument Q (b,s) at hn
      rw [he] at hn
      linarith
    have hp := hpos true
    have hm := hpos false
    simp only [PauliProjector, Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul,
      Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul,
      Complex.add_re, Complex.mul_re, Complex.one_re,
      hQ.2, ht] at hp hm
    norm_num at hp hm
    rw [abs_le]
    constructor <;> linarith

/-- A code-state local shot value is nonnegative for nonnegative weight, pure local factors,
unitary rotations, and `0 < 3 * ε ≤ 1`. -/
lemma local_shot_nonneg {n : ℕ} {J : Type} (Uf : J → Operator 2)
    (w : ℝ) (hw : 0 ≤ w) (ψ : Fin n → Operator 2) (hψ : ∀ j, IsPureDensityOperator (ψ j))
    (uw : Fin n → J) (hU : ∀ j, Uf (uw j) ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (a : Fin n → Option (Fin 3)) (ε : ℝ) (hε : 0 < ε) (hε1 : 3*ε ≤ 1) :
    0 ≤ localShotValue Uf w ψ uw (theorem6CodeState n ε a) := by
  rw [localShotValue_factor Uf w ψ uw hψ hU]
  apply mul_nonneg hw
  have habs : |∏ j, localPauliOverlap Uf (ψ j) (a j) (uw j)| ≤ 1 := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _j : Fin n, (1 : ℝ) := Finset.prod_le_prod₀
        (fun _ _ => abs_nonneg _) (fun j _ => local_wire_overlap_abs Uf (ψ j) (hψ j) (a j) (uw j) (hU j))
      _ = 1 := by simp
  have hlo := (abs_le.mp habs).1
  have hmul := mul_le_mul_of_nonneg_left hlo (show 0 ≤ 3*ε by positivity)
  linarith

/-- The code operator has trace one when its Pauli word has positive weight `k`. -/
lemma local_code_trace {n k : ℕ} (ε : ℝ) (a : Fin n → Option (Fin 3))
    (hk : 1 ≤ k) (hS : tensorPauliWeight a = k) :
    Matrix.trace (theorem6CodeState n ε a) = 1 := by
  have hs : ∃ j b, a j = some b := by
    by_contra hn
    have hz : ∀ j, a j = none := by
      intro j
      cases h : a j with
      | none => rfl
      | some b => exact False.elim (hn ⟨j,b,h⟩)
    have hh : tensorPauliWeight a = 0 := by simp [tensorPauliWeight, hz]
    omega
  have ht : Matrix.trace (tensorPauliWord n a) = 0 := by
    rw [tensorPauliWord, tensorPauliProduct_trace]
    obtain ⟨j,b,h⟩ := hs
    exact Finset.prod_eq_zero (Finset.mem_univ j)
        (by rw [h, tensorPauliWordFactor, trace_pauliMatrix])
  rw [theorem6CodeState, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, ht]
  simp only [smul_zero, add_zero, Matrix.trace_one, Fintype.card_fin, Complex.real_smul]
  have hd : (2 ^ n : ℝ) ≠ 0 := by positivity
  norm_cast
  field_simp

/-- If the weighted tensor measurement operators sum to the identity, local shot values for a
trace-one input sum to one under unitary local rotations. -/
lemma local_shot_sum {n : ℕ} {J O : Type} [Fintype O]
    (Uf : J → Operator 2) (uw : Fin n → J)
    (hU : ∀ j, Uf (uw j) ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (w : O → ℝ) (ψ : O → Fin n → Operator 2)
    (hsum : (∑ o, (w o * (2^n : ℝ)) • tensorPauliProduct n (ψ o)) = 1)
    (ρ : Operator (2^n)) (hρ : Matrix.trace ρ = 1) :
    ∑ o, localShotValue Uf (w o) (ψ o) uw ρ = 1 := by
  let T := tensorPauliProduct n (fun j => Uf (uw j))
  have hu : Tᴴ * T = 1 := by
    rw [tensorPauliProduct_conjTranspose, tensorPauliProduct_mul]
    have hj : ∀ j, (Uf (uw j))ᴴ * Uf (uw j) = 1 := by
      intro j
      simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp (hU j)
    simp_rw [hj]
    exact tensorPauliProduct_one n
  have ht : Matrix.trace (T * ρ * Tᴴ) = 1 := by
    rw [Matrix.trace_mul_cycle, hu, Matrix.one_mul, hρ]
  have hs : (∑ o, Matrix.trace ((w o * (2^n : ℝ)) • tensorPauliProduct n (ψ o) *
      (T * ρ * Tᴴ))) = 1 := by
    rw [← Matrix.trace_sum, ← Finset.sum_mul, hsum, Matrix.one_mul, ht]
  have hr := congrArg Complex.re hs
  simpa only [localShotValue, T, Complex.re_sum, Matrix.smul_mul, Matrix.trace_smul,
    Complex.smul_re, smul_eq_mul, Complex.one_re] using hr
end Qatlib.Papers.ClassShadows20.LowerBound
