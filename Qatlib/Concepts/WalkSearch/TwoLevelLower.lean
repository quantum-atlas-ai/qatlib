/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws

/-!
# Transition kernels and Szegedy walk primitives

This module defines transition matrices, stationary distributions, and reversibility through
detailed balance. It constructs `SzegedyIsometry`, its range reflection, the register swap, and
`SzegedyWalk`, and proves their normalization and unitarity properties under the
transition-kernel hypotheses.

`SzegedyEmbedState` lifts square-root weights to the pair space, where detailed balance gives a
walk fixed vector. The module also provides the Metropolis acceptance formula and a
two-dimensional coin with its unitary and Born-weight identities, supplying primitives for the
walk construction [Szegedy2004].

## Main statements

* `reversible_stationary`: detailed balance gives stationarity for a probability vector.
* `szegedyWalk_unitary`: unitarity of the reflection-product walk.
* `szegedyWalk_fixes_stationary`: invariance of the embedded detailed-balance vector.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.WalkSearch.TwoLevelLower

open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A nonnegative real kernel whose rows each sum to one. -/
def IsTransitionMatrix (P : I → I → ℝ) : Prop :=
  (∀ x y, 0 ≤ P x y) ∧ ∀ x, ∑ y, P x y = 1

/-- A nonnegative probability vector preserved by right multiplication with the transition
kernel. -/
def IsStationary (P : I → I → ℝ) (π : I → ℝ) : Prop :=
  (∀ x, 0 ≤ π x) ∧ ∑ x, π x = 1 ∧ ∀ y, ∑ x, π x * P x y = π y

/-- The detailed-balance equations `π x * P x y = π y * P y x` for every pair of states. -/
def IsReversible (P : I → I → ℝ) (π : I → ℝ) : Prop :=
  ∀ x y, π x * P x y = π y * P y x

omit [DecidableEq I] in

/-- A nonnegative normalized vector satisfying detailed balance for a transition matrix is
stationary. -/
theorem reversible_stationary {P : I → I → ℝ} (hP : IsTransitionMatrix P) {π : I → ℝ}
    (hπ : (∀ x, 0 ≤ π x) ∧ ∑ x, π x = 1) (hrev : IsReversible P π) :
    IsStationary P π := by
  refine ⟨hπ.1, hπ.2, fun y => ?_⟩
  have hstep : ∀ x : I, π x * P x y = π y * P y x := fun x => hrev x y
  rw [Finset.sum_congr rfl (fun x _ => hstep x), ← Finset.mul_sum, hP.2 y, mul_one]

/-- The frame whose column at `x` has amplitudes `sqrt (P x y)` on basis pairs `(x, y)` and zero
elsewhere. -/
noncomputable def SzegedyIsometry (P : I → I → ℝ) : Matrix (I × I) I ℂ :=
  Matrix.of fun p x => if p.1 = x then ((Real.sqrt (P x p.2) : ℂ)) else 0

/-- The Szegedy frame has orthonormal columns for a transition matrix. -/
theorem szegedyIsometry_conjTranspose_mul (P : I → I → ℝ) (hP : IsTransitionMatrix P) :
    (SzegedyIsometry P)ᴴ * SzegedyIsometry P = 1 := by
  ext x x'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
    SzegedyIsometry, Matrix.of_apply, Matrix.one_apply]
  by_cases hxx' : x = x'
  · subst hxx'
    have hkey : ∀ p : I × I,
        (starRingEnd ℂ) (if p.1 = x then ((Real.sqrt (P x p.2) : ℂ)) else 0)
            * (if p.1 = x then ((Real.sqrt (P x p.2) : ℂ)) else 0)
          = if p.1 = x then ((P x p.2 : ℂ)) else 0 := by
      intro p
      by_cases hp : p.1 = x
      · rw [ite_eq_left hp, ite_eq_left hp, Complex.conj_ofReal, ← Complex.ofReal_mul, ← sq,
          Real.sq_sqrt (hP.1 x p.2)]
      · rw [ite_eq_right hp, ite_eq_right hp, map_zero, zero_mul]
    rw [Finset.sum_congr rfl (fun p _ => hkey p), Fintype.sum_prod_type,
      Finset.sum_eq_single x]
    · simp only [ite_true]
      exact_mod_cast hP.2 x
    · intro a _ ha
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [ite_eq_right (fun e : (a, y).1 = x => ha e)]
    · intro hcon
      exact absurd (Finset.mem_univ x) hcon
  · have hzero : ∀ p : I × I,
        (starRingEnd ℂ) (if p.1 = x then ((Real.sqrt (P x p.2) : ℂ)) else 0)
            * (if p.1 = x' then ((Real.sqrt (P x' p.2) : ℂ)) else 0) = 0 := by
      intro p
      by_cases hp : p.1 = x
      · simp only [ite_eq_left hp,
          ite_eq_right (show ¬(p.1 = x') from fun e => hxx' (hp.symm.trans e)), mul_zero]
      · simp only [ite_eq_right hp, map_zero, zero_mul]
    rw [Finset.sum_eq_zero (fun p _ => hzero p), ite_eq_right hxx']

/-- For a transition matrix, the Szegedy frame times its adjoint is an orthogonal projector. -/
theorem isStarProjection_szegedy (P : I → I → ℝ) (hP : IsTransitionMatrix P) :
    IsOrthogonalProjector (SzegedyIsometry P * (SzegedyIsometry P)ᴴ) := by
  refine ⟨?_, ?_⟩
  · show (SzegedyIsometry P * (SzegedyIsometry P)ᴴ)
        * (SzegedyIsometry P * (SzegedyIsometry P)ᴴ)
        = SzegedyIsometry P * (SzegedyIsometry P)ᴴ
    have hcalc : (SzegedyIsometry P * (SzegedyIsometry P)ᴴ)
        * (SzegedyIsometry P * (SzegedyIsometry P)ᴴ)
        = SzegedyIsometry P * ((SzegedyIsometry P)ᴴ * SzegedyIsometry P)
          * (SzegedyIsometry P)ᴴ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc]
    rw [hcalc, szegedyIsometry_conjTranspose_mul P hP, Matrix.mul_one]
  · show star (SzegedyIsometry P * (SzegedyIsometry P)ᴴ)
        = SzegedyIsometry P * (SzegedyIsometry P)ᴴ
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]

/-- The reflection about the range matrix of the Szegedy frame. -/
noncomputable def SzegedyReflection (P : I → I → ℝ) : Matrix (I × I) (I × I) ℂ :=
  ReflectionAbout (SzegedyIsometry P * (SzegedyIsometry P)ᴴ)

/-- The Szegedy reflection is unitary for a transition matrix. -/
theorem szegedyReflection_unitary (P : I → I → ℝ) (hP : IsTransitionMatrix P) :
    SzegedyReflection P ∈ Matrix.unitaryGroup (I × I) ℂ :=
  reflectionAbout_unitary (isStarProjection_szegedy P hP)

/-- The permutation matrix exchanging the two state registers. -/
noncomputable def SwapGate : Matrix (I × I) (I × I) ℂ := permMatrix Prod.swap

/-- The register swap gate is unitary. -/
theorem swapGate_unitary : SwapGate ∈ Matrix.unitaryGroup (I × I) ℂ :=
  permMatrix_unitary Prod.swap_swap

/-- The swap gate acts on state amplitudes by exchanging the pair coordinates. -/
theorem applyGate_swapGate (Φ : QState (I × I)) :
    SwapGate *ᵥ Φ = fun p => Φ (Prod.swap p) := by
  funext q
  rw [SwapGate]
  exact applyGate_permMatrix Prod.swap_swap Φ q

/-- The product of the Szegedy reflection and its conjugate by the register swap, with the
conjugated reflection acting last. -/
noncomputable def SzegedyWalk (P : I → I → ℝ) : Matrix (I × I) (I × I) ℂ :=
  (SwapGate * SzegedyReflection P * SwapGate) * SzegedyReflection P

/-- The Szegedy walk is unitary for a transition matrix. -/
theorem szegedyWalk_unitary (P : I → I → ℝ) (hP : IsTransitionMatrix P) :
    SzegedyWalk P ∈ Matrix.unitaryGroup (I × I) ℂ := by
  unfold SzegedyWalk
  exact Submonoid.mul_mem _
    (Submonoid.mul_mem _ (Submonoid.mul_mem _ swapGate_unitary
      (szegedyReflection_unitary P hP)) swapGate_unitary)
    (szegedyReflection_unitary P hP)

/-- The Szegedy frame applied to the vector of square roots of the real weights `v`. -/
noncomputable def SzegedyEmbedState (P : I → I → ℝ) (v : I → ℝ) : QState (I × I) :=
  SzegedyIsometry P *ᵥ fun x => ((Real.sqrt (v x) : ℂ))

/-- The embedded state has amplitude `sqrt (P x y) * sqrt (v x)` at `(x, y)`. -/
theorem szegedyEmbedState_apply (P : I → I → ℝ) (v : I → ℝ) (x y : I) :
    SzegedyEmbedState P v (x, y)
      = ((Real.sqrt (P x y) * Real.sqrt (v x) : ℂ)) := by
  simp only [SzegedyEmbedState, Matrix.mulVec, dotProduct, SzegedyIsometry,
    Matrix.of_apply]
  rw [Finset.sum_eq_single x]
  · rw [ite_eq_left rfl, ← Complex.ofReal_mul]
  · intro a _ ha
    simp [show x ≠ a from fun e => ha e.symm]
  · intro hcon
    exact absurd (Finset.mem_univ x) hcon

/-- Embedding a nonnegative probability vector through the Szegedy frame gives a normalized
state. -/
theorem normalized_szegedyEmbedState (P : I → I → ℝ) (hP : IsTransitionMatrix P)
    {v : I → ℝ} (hv : ∀ x, 0 ≤ v x) (hsum : ∑ x, v x = 1) :
    Normalized (SzegedyEmbedState P v) := by
  unfold Normalized
  have hkey : ∀ p : I × I, ‖SzegedyEmbedState P v p‖ ^ 2 = P p.1 p.2 * v p.1 := by
    intro p
    obtain ⟨x, y⟩ := p
    have hnn : 0 ≤ P x y * v x := mul_nonneg (hP.1 x y) (hv x)
    have hentry : ((Real.sqrt (P x y * v x) : ℂ))
        = ((Real.sqrt (P x y) * Real.sqrt (v x) : ℂ)) := by
      rw [← Complex.ofReal_mul, Real.sqrt_mul (hP.1 x y) (v x)]
    rw [szegedyEmbedState_apply P v x y, ← hentry, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hnn]
  have hsplit : ∑ p : I × I, ‖SzegedyEmbedState P v p‖ ^ 2
      = ∑ x, ∑ y, (P x y * v x) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      hkey (x, y)
  rw [hsplit]
  have hswap : ∑ x : I, ∑ y : I, P x y * v x = ∑ x : I, v x * ∑ y : I, P x y := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => mul_comm _ _
  rw [hswap, Finset.sum_congr rfl (fun x _ => by rw [hP.2 x, mul_one])]
  exact_mod_cast hsum

/-- If the detailed-balance equations hold, the Szegedy walk fixes the embedded square-root
vector [Szegedy2004]. -/
theorem szegedyWalk_fixes_stationary (P : I → I → ℝ) (hP : IsTransitionMatrix P)
    {π : I → ℝ}
    (hrev : IsReversible P π) :
    SzegedyWalk P *ᵥ SzegedyEmbedState P π = SzegedyEmbedState P π := by
  set Φ : QState (I × I) := SzegedyEmbedState P π with hΦ

  have hswapfix : SwapGate *ᵥ Φ = Φ := by
    funext p
    obtain ⟨x, y⟩ := p
    have h1 : (SwapGate *ᵥ Φ) (x, y) = Φ (y, x) := by
      rw [applyGate_swapGate Φ]
      exact congrArg Φ Prod.swap_prod_mk
    rw [h1, hΦ, szegedyEmbedState_apply P π y x, szegedyEmbedState_apply P π x y]
    have hrev' : π y * P y x = π x * P x y := (hrev x y).symm
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_inj,
      ← Real.sqrt_mul (hP.1 y x) (π y), ← Real.sqrt_mul (hP.1 x y) (π x),
      mul_comm (P y x) (π y), hrev', mul_comm (P x y) (π x)]

  have hRfix : SzegedyReflection P *ᵥ Φ = Φ := by
    have hpre : (SzegedyIsometry P * (SzegedyIsometry P)ᴴ) *ᵥ Φ = Φ := by
      rw [hΦ, SzegedyEmbedState]
      have eq1 : (SzegedyIsometry P * (SzegedyIsometry P)ᴴ) *ᵥ
          (SzegedyIsometry P *ᵥ (fun x => ((Real.sqrt (π x) : ℂ))))
          = SzegedyIsometry P *ᵥ (((SzegedyIsometry P)ᴴ * SzegedyIsometry P) *ᵥ
            (fun x => ((Real.sqrt (π x) : ℂ)))) := by
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rw [eq1, szegedyIsometry_conjTranspose_mul P hP, Matrix.one_mulVec]
    have h2 : ApplyGate (ReflectionAbout (SzegedyIsometry P * (SzegedyIsometry P)ᴴ)) Φ
        = Φ :=
      applyGate_reflectionAbout_of_fixed (by exact hpre)
    exact h2

  rw [SzegedyWalk]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hRfix, hswapfix, hRfix, hswapfix]

/-- The Metropolis acceptance ratio `min 1 (π y * P y x / (π x * P x y))`, using real division. -/
noncomputable def MetropolisAcceptance (P : I → I → ℝ) (π : I → ℝ) (x y : I) : ℝ :=
  min 1 (π y * P y x / (π x * P x y))

omit [DecidableEq I] in

/-- For nonnegative target weights and a transition matrix, the Metropolis-adjusted off-diagonal
flow satisfies detailed balance. -/
theorem metropolisAcceptance_detailed_balance (P : I → I → ℝ) (hP : IsTransitionMatrix P)
    {π : I → ℝ} (hπ : ∀ x, 0 ≤ π x) (x y : I) :
    π x * (P x y * MetropolisAcceptance P π x y)
      = π y * (P y x * MetropolisAcceptance P π y x) := by
  have hnn : ∀ a b : I, 0 ≤ π a * P a b := fun a b => mul_nonneg (hπ a) (hP.1 a b)
  have hmin : ∀ a b : I, π a * (P a b * MetropolisAcceptance P π a b)
      = min (π a * P a b) (π b * P b a) := by
    intro a b
    rw [MetropolisAcceptance, ← mul_assoc]
    by_cases h0 : π a * P a b = 0
    · rw [h0, zero_mul, min_eq_left (hnn b a)]
    · have hpos : 0 < π a * P a b := lt_of_le_of_ne' (hnn a b) h0
      by_cases hba : π b * P b a ≤ π a * P a b
      · rw [min_eq_right (div_le_one_of_le₀ hba (hnn a b)), ← mul_div_assoc,
          mul_div_cancel_left₀ _ hpos.ne', min_eq_right hba]
      · have hlt : π a * P a b < π b * P b a := lt_of_not_ge hba
        rw [min_eq_left ((one_le_div hpos).mpr hlt.le), mul_one, min_eq_left hlt.le]
  rw [hmin x y, hmin y x, min_comm]

/-- The two-dimensional real-amplitude coin with entries determined by `sqrt a` and `sqrt (1 -
a)`. -/
noncomputable def MetropolisCoin (a : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((Real.sqrt (1 - a) : ℝ) : ℂ), ((Real.sqrt a : ℝ) : ℂ);
     ((Real.sqrt a : ℝ) : ℂ), (-(Real.sqrt (1 - a)) : ℂ)]

/-- The Metropolis coin is unitary when its parameter lies in `[0, 1]`. -/
theorem metropolisCoin_unitary {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    MetropolisCoin a ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hsq0 : ((Real.sqrt (1 - a) : ℂ)) * ((Real.sqrt (1 - a) : ℂ)) = ((1 - a : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← sq, Real.sq_sqrt (sub_nonneg_of_le h1)]
  have hsq1 : ((Real.sqrt a : ℂ)) * ((Real.sqrt a : ℂ)) = ((a : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← sq, Real.sq_sqrt h0]
  have hreal : ∀ r : ℝ, (starRingEnd ℂ) ((r : ℂ)) = ((r : ℂ)) := fun r => by simp
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MetropolisCoin, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, hreal, hsq0, hsq1] <;>
    ring

/-- For nonnegative `a`, applying `MetropolisCoin a` to basis state zero gives Born weight `a`
at basis state one. -/
theorem metropolisCoin_accept_prob {a : ℝ} (h0 : 0 ≤ a) :
    BornProb (MetropolisCoin a *ᵥ Ket 0) 1 = a := by
  rw [BornProb]
  have hcol : (MetropolisCoin a *ᵥ Ket 0) 1 = ((Real.sqrt a : ℝ) : ℂ) := by
    simp [Matrix.mulVec, dotProduct, Ket, MetropolisCoin]
  rw [hcol, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal,
    Real.mul_self_sqrt h0]

end Qatlib.Concepts.WalkSearch.TwoLevelLower
