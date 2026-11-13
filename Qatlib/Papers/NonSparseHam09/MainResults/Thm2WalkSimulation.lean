/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonSparseHam09.MainResults.Defs
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Matrix evolution and zero-time walk simulation

`timeEvolution` satisfies the additive time law and equals the identity at time zero. For a
Hermitian matrix, its generator is skew-Hermitian and its evolution is unitary. The module also
constructs the zero-time case of `WalkSimulates`. This development accompanies
[ChildsKothari2010].

## Main statements

* `timeEvolution_add`: composition of evolutions adds their times.
* `timeEvolution_mem_unitaryGroup`: Hermitian evolution belongs to the unitary group.
* `walkSimulates_zero`: zero walk steps simulate time zero with any nonnegative error bound.

## References

* [Childs and Kothari, 2010][ChildsKothari2010]
-/

set_option autoImplicit false
noncomputable section

open Matrix Finset
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonSparseHam09.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The scalar coefficients of the evolution generators add according to the sum of the real
times. -/
lemma timeEvo_scalar_add (t s : ℝ) :
    (-(Complex.I * (t : ℂ))) + (-(Complex.I * (s : ℂ)))
      = -(Complex.I * ((t + s : ℝ) : ℂ)) := by
  push_cast
  ring

omit [Nonempty ι] in

/-- Matrix time evolution satisfies `timeEvolution H t * timeEvolution H s = timeEvolution H (t
+ s)`. This identity supports the simulation framework of [ChildsKothari2010]. -/
theorem timeEvolution_add (H : Matrix ι ι ℂ) (t s : ℝ) :
    timeEvolution H t * timeEvolution H s = timeEvolution H (t + s) := by
  unfold timeEvolution
  calc NormedSpace.exp (-(Complex.I * (t : ℂ)) • H)
        * NormedSpace.exp (-(Complex.I * (s : ℂ)) • H)
      = NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H + (-(Complex.I * (s : ℂ))) • H) :=
        (Matrix.exp_add_of_commute _ _ (by
          exact ((Commute.refl H).smul_left _).smul_right _)).symm
    _ = NormedSpace.exp (-(Complex.I * ((t + s : ℝ) : ℂ)) • H) := by
        congr 1
        rw [← add_smul, timeEvo_scalar_add]

omit [Nonempty ι] in

/-- Time evolution at time zero is the identity matrix. -/
theorem timeEvolution_zero (H : Matrix ι ι ℂ) : timeEvolution H 0 = 1 := by
  unfold timeEvolution
  simp

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in

/-- For Hermitian `H`, the conjugate transpose of the generator obtained by scaling `H` by −i t
is its negative. -/
lemma timeEvo_gen_conjTranspose (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (t : ℝ) :
    ((-(Complex.I * (t : ℂ))) • H)ᴴ = - ((-(Complex.I * (t : ℂ))) • H) := by
  rw [Matrix.conjTranspose_smul, hH]
  simp [Complex.conj_ofReal]

omit [Nonempty ι] in

/-- For Hermitian `H`, time evolution multiplied by its conjugate transpose is the identity. See
[ChildsKothari2010]. -/
theorem timeEvolution_unitary (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (t : ℝ) :
    timeEvolution H t * (timeEvolution H t)ᴴ = 1 := by
  unfold timeEvolution
  set A : Matrix ι ι ℂ := (-(Complex.I * (t : ℂ))) • H with hAdef
  have hcomm : Commute A (-A) := by
    have hx : -A = (-1 : ℂ) • A := by simp
    rw [hx]
    exact (Commute.refl A).smul_right (-1)
  have hstar : Aᴴ = -A := by
    rw [hAdef, Matrix.conjTranspose_smul, hH]
    simp [Complex.conj_ofReal]
  have h : NormedSpace.exp A * (NormedSpace.exp A)ᴴ = 1 := by
    calc NormedSpace.exp A * (NormedSpace.exp A)ᴴ
        = NormedSpace.exp A * NormedSpace.exp Aᴴ := by rw [Matrix.exp_conjTranspose]
      _ = NormedSpace.exp A * NormedSpace.exp (-A) := by rw [hstar]
      _ = NormedSpace.exp (A + -A) := (Matrix.exp_add_of_commute A (-A) hcomm).symm
      _ = NormedSpace.exp 0 := by rw [add_neg_cancel]
      _ = 1 := NormedSpace.exp_zero
  simpa [hAdef] using h

/-- The time evolution of a Hermitian matrix belongs to `Matrix.unitaryGroup`. See
[ChildsKothari2010]. -/
theorem timeEvolution_mem_unitaryGroup (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (t : ℝ) :
    timeEvolution H t ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  exact timeEvolution_unitary H hH t

/-- Zero walk steps simulate evolution for time zero with any nonnegative error tolerance. See
[ChildsKothari2010]. -/
theorem walkSimulates_zero (H : Matrix ι ι ℂ) {δ : ℝ} (hδ : 0 ≤ δ) :
    WalkSimulates H 0 δ 0 := by
  refine ⟨{ size := Fintype.card ι
            step := 1
            step_unitary := Submonoid.one_mem _
            vertexState := fun i => Fintype.equivFin ι i }, ?_, ?_⟩
  · intro a b hab
    change (1 : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) a b ≠ 0 at hab
    rw [Matrix.one_apply] at hab
    split_ifs at hab with h
    · refine ⟨(Fintype.equivFin ι).symm a, (Fintype.equivFin ι).symm a, ?_, ?_, Or.inl rfl⟩
      · simp
      · simp [h]
    · exact absurd rfl hab
  · intro i j
    rw [pow_zero, timeEvolution_zero]
    simp only [Matrix.one_apply]
    by_cases h : i = j
    · subst h; simp [hδ]
    · have hv : Fintype.equivFin ι i ≠ Fintype.equivFin ι j :=
        fun he => h ((Fintype.equivFin ι).injective he)
      simp [h, hv, hδ]

end Qatlib.Papers.NonSparseHam09.MainResults
