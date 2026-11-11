/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Ring
import Qatlib.Foundations.PureStateMath.Tensor

/-!
# Prepare-select-unprepare linear combinations

`IsPrepare` specifies a unitary preparing square roots of real weights. `LCUWorkspace`
conjugates controlled selection by this preparation, and `lcu_corner_apply` identifies its
designated ancilla corner with the weighted sum acting on a system state.

The mathematical background is described in [GilyenSuLowWiebe2019].

## Main statements

* `select_unitary`: unitarity of controlled selection.
* `lcu_corner_apply`: the prepared workspace corner applies the weighted sum.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Concepts.BlockEncoding.LinearCombination

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Matrix

variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

/-- Applying a matrix to the basis vector at `j₀` extracts column `j₀`. -/
theorem mulVec_ket_apply (A : Matrix J J ℂ) (j₀ j : J) : (A *ᵥ Ket j₀) j = A j j₀ := by
  simp only [Matrix.mulVec, dotProduct, Ket]
  rw [Finset.sum_eq_single j₀]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hcon
    exact absurd (Finset.mem_univ j₀) hcon

/-- A tensor product gate acts on a tensor product state by applying each factor separately. -/
theorem mulVec_tensorGate (A : Matrix J J ℂ) (B : Matrix I I ℂ) (φ : QState J)
    (ψ : QState I) :
    TensorGate A B *ᵥ TensorState φ ψ = TensorState (A *ᵥ φ) (B *ᵥ ψ) := by
  funext p
  obtain ⟨x, y⟩ := p
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, TensorGate, TensorState,
    Matrix.kronecker_apply]
  have key : ∀ x1 : J, ∑ x2 : I, (A x x1 * B y x2) * (φ x1 * ψ x2)
      = (A x x1 * φ x1) * ∑ x2 : I, B y x2 * ψ x2 := by
    intro x1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl (fun x1 _ => key x1), Finset.sum_mul]

/-- The controlled matrix applying `U j` on the system for ancilla label `j`. -/
noncomputable def Select (U : J → Matrix I I ℂ) : Matrix (J × I) (J × I) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then U q.1 p.2 q.2 else 0

/-- The controlled matrix `Select U` is unitary if each `U j` is unitary. -/
theorem select_unitary (U : J → Matrix I I ℂ) (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) :
    Select U ∈ Matrix.unitaryGroup (J × I) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext p p'
  obtain ⟨a, i⟩ := p
  obtain ⟨a', i'⟩ := p'
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
    Select, Matrix.of_apply, RCLike.star_def, Matrix.one_apply]
  rcases eq_or_ne a a' with h | h
  · subst h
    have hent : ∀ (A : Matrix I I ℂ) (i i' : I),
        (∑ b : I, (starRingEnd ℂ) (A b i) * A b i') = (Aᴴ * A) i i' := by
      intro A i i''
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun b _ => by
        rw [Matrix.conjTranspose_apply, RCLike.star_def]
    rw [Finset.sum_eq_single a]
    · simp only [if_true]
      rw [hent, ← Matrix.star_eq_conjTranspose (U a),
        (Matrix.mem_unitaryGroup_iff' (A := U a)).mp (hU a)]
      by_cases hii : i = i' <;> simp [Matrix.one_apply, hii]
    · intro m _ hm
      simp [hm]
    · intro hcon
      exact absurd (Finset.mem_univ a) hcon
  · rw [if_neg (fun e => h (congrArg Prod.fst e))]
    exact Finset.sum_eq_zero fun m _ => by
      by_cases hma : m = a
      · simp [hma, h]
      · simp [hma]

/-- The condition that `P` is unitary and sends the chosen basis state to the square roots of
the weights `w`. -/
def IsPrepare (P : Matrix J J ℂ) (w : J → ℝ) (j₀ : J) : Prop :=
  P ∈ Matrix.unitaryGroup J ℂ ∧ P *ᵥ Ket j₀ = fun j => ((Real.sqrt (w j) : ℂ))

/-- The workspace matrix applying preparation, controlled selection, and inverse preparation. -/
noncomputable def LCUWorkspace (U : J → Matrix I I ℂ) (P : Matrix J J ℂ) :
    Matrix (J × I) (J × I) ℂ :=
  TensorGate Pᴴ 1 * (Select U * TensorGate P 1)

/-- For nonnegative weights prepared by `P`, the designated ancilla component of `LCUWorkspace U
P` equals the weighted matrix sum applied to `ψ`. See [GilyenSuLowWiebe2019]. -/
theorem lcu_corner_apply (U : J → Matrix I I ℂ) {w : J → ℝ} (hw : ∀ j, 0 ≤ w j)
    {P : Matrix J J ℂ} {j₀ : J} (hP : IsPrepare P w j₀) (ψ : QState I) :
    (fun i' => (LCUWorkspace U P *ᵥ TensorState (Ket j₀) ψ) (j₀, i'))
      = (∑ j, w j • U j) *ᵥ ψ := by
  have hcol : ∀ j : J, P j j₀ = ((Real.sqrt (w j) : ℂ)) := by
    intro j
    rw [← mulVec_ket_apply P j₀ j, ← congrFun hP.2 j]

  have hstep1 : Select U *ᵥ TensorState (fun j => ((Real.sqrt (w j) : ℂ))) ψ
      = fun p => ((Real.sqrt (w p.1) : ℂ)) • (U p.1 *ᵥ ψ) p.2 := by
    funext p
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Select, Matrix.of_apply,
      TensorState]
    rw [Finset.sum_eq_single p.1]
    · simp only [if_true]
      have hsum : (∑ j : I, (U p.1) p.2 j * (((Real.sqrt (w p.1) : ℂ)) * ψ j))
          = ((Real.sqrt (w p.1) : ℂ)) * ((U p.1 *ᵥ ψ) p.2) := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      simpa only [smul_eq_mul] using! hsum
    · intro m _ hm
      have hne : ¬(p.1 = m) := fun e => hm e.symm
      rw [Finset.sum_eq_zero]
      intro j _
      rw [if_neg hne]
      ring
    · intro hcon
      exact absurd (Finset.mem_univ p.1) hcon

  have hentry : ∀ (A : Matrix J J ℂ) (Ξ : QState (J × I)) (x : J) (y : I),
      (TensorGate A 1 *ᵥ Ξ) (x, y) = ∑ m : J, A x m * Ξ (m, y) := by
    intro A Ξ x y
    have hexp : ∀ m : J, ∀ k : I,
        TensorGate A (1 : Matrix I I ℂ) (x, y) (m, k)
          = A x m * (if y = k then (1 : ℂ) else 0) := by
      intro m k
      simp [TensorGate, Matrix.one_apply]
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, hexp]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_eq_single y]
    · rw [if_pos rfl]
      ring
    · intro k _ hk
      rw [if_neg (show ¬(y = k) from fun e => hk e.symm)]
      ring
    · intro hcon
      exact absurd (Finset.mem_univ y) hcon
  funext i'
  have h2 : (LCUWorkspace U P *ᵥ TensorState (Ket j₀) ψ) (j₀, i')
      = ∑ j : J, (Pᴴ j₀ j) * (((Real.sqrt (w j) : ℂ)) * (U j *ᵥ ψ) i') := by
    rw [LCUWorkspace, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mulVec_tensorGate,
      hP.2, Matrix.one_mulVec, hstep1, hentry]
    simp only [smul_eq_mul]
  have hcoef : ∀ j : J, (Pᴴ j₀ j) * ((Real.sqrt (w j) : ℂ)) = ((w j : ℂ)) := by
    intro j
    have h2r : ((Real.sqrt (w j) : ℂ)) * ((Real.sqrt (w j) : ℂ)) = ((w j : ℂ)) := by
      rw [← Complex.ofReal_mul, ← sq, Real.sq_sqrt (hw j)]
    rw [Matrix.conjTranspose_apply, hcol j, RCLike.star_def, Complex.conj_ofReal, h2r]
  have hdist : (∑ j, w j • U j) *ᵥ ψ
      = fun i' => ∑ j : J, ((w j : ℂ)) * (U j *ᵥ ψ) i' := by
    funext i'
    simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.mul_sum,
      Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.real_smul]
    ring
  rw [h2, hdist]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, hcoef j]

end Qatlib.Concepts.BlockEncoding.LinearCombination
