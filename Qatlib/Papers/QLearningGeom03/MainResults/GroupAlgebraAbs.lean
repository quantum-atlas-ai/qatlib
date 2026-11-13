/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Qatlib.Papers.QLearningGeom03.MainResults.GroupAlgebraZN
import Qatlib.Papers.QLearningGeom03.MainResults.Battleship
import Qatlib.Papers.QLearningGeom03.MainResults.CriticalMax

/-!
# Spectral absolute values in the cyclic group algebra

This module constructs `absGroupAlgebra v` by replacing the Fourier eigenvalues of a cyclic
group-algebra matrix with their complex norms. It proves Fourier diagonalization, a
factorization as `Cᴴ * C`, and the constant-diagonal property.

The module also gives the common diagonal entry as the mean absolute eigenvalue and proves
maximality of `diagNormSqZ` under the stated unitary and constant-diagonal constraints. These
results implement the cyclic case of Proposition 5.4 in [HunzikerEtAl2003].

## Main statements

* `fourier_absGroupAlgebra`: Fourier diagonalization with nonnegative eigenvalues.
* `absGroupAlgebra_psd`: A factorization proving positivity.
* `absGroupAlgebra_max`: Constrained maximality of the diagonal squared norm.

## References

* [Hunziker et al., 2003][HunzikerEtAl2003]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QLearningGeom03.MainResults

open Matrix
open scoped Matrix

variable {N : ℕ} [NeZero N]

/-- The inverse cyclic Fourier transform of the prescribed eigenvalues `g`, using normalization
1/N. -/
noncomputable def invFourierVec (g : ZMod N → ℂ) (k : ZMod N) : ℂ :=
  ((N : ℂ))⁻¹ * ∑ j, g j * chiN k (-j)

/-- The Fourier coefficient of `invFourierVec g` at `j` is `g j`. -/
lemma eigen_invFourierVec (g : ZMod N → ℂ) (j : ZMod N) :
    (∑ x, invFourierVec g x * chiN j x) = g j := by
  have h1 : (∑ x, invFourierVec g x * chiN j x)
      = (N : ℂ)⁻¹ * ∑ x, ∑ j', (g j' * chiN x (-j')) * chiN j x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold invFourierVec
    rw [mul_assoc, Finset.sum_mul]
  rw [h1, Finset.sum_comm]
  have h2 : ∀ j' x : ZMod N,
      (g j' * chiN x (-j')) * chiN j x = g j' * chiN (j - j') x := by
    intro j' x
    have hneg : chiN x (-j') = star (chiN j' x) := by
      unfold chiN
      rw [stdAddChar_star]
      congr 1
      ring
    calc (g j' * chiN x (-j')) * chiN j x
        = g j' * (chiN j x * chiN x (-j')) := by ring
      _ = g j' * chiN x (j - j') := by
          rw [hneg, chiN_mul_star j j' x]
      _ = g j' * chiN (j - j') x := by rw [chiN_comm x (j - j')]
  rw [Finset.sum_congr rfl (fun j' _ => Finset.sum_congr rfl (fun x _ => h2 j' x))]
  have h3 : ∀ j' : ZMod N, (∑ x, g j' * chiN (j - j') x)
      = g j' * (∑ x, chiN (j - j') x) := fun j' => by rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun j' _ => h3 j')]
  rw [Finset.sum_eq_single j]
  · rw [chiN_sum_left, ite_eq_left (sub_self j)]
    have hNc : ((N : ℂ)) ≠ 0 := by exact_mod_cast NeZero.ne N
    field_simp
  · intro j' _ hne
    rw [chiN_sum_left, ite_eq_right]
    · ring
    · intro h0
      exact hne (sub_eq_zero.mp h0).symm
  · intro hmem
    exact absurd (Finset.mem_univ j) hmem

/-- Every complex diagonal matrix is the Fourier conjugate of some cyclic group-algebra matrix. -/
theorem fourier_surjective_diagonal (g : ZMod N → ℂ) :
    ∃ w, fourier N * groupAlgebraElem w * (fourier N)ᴴ = Matrix.diagonal g := by
  refine ⟨invFourierVec g, ?_⟩
  rw [fourier_conj_groupAlgebraElem (Nat.pos_of_neZero N)]
  congr 1
  funext j
  exact eigen_invFourierVec g j

/-- For positive N, the conjugate transpose of the normalized Fourier matrix is a left inverse. -/
lemma fourier_conjTranspose_mul (hN : 0 < N) : (fourier N)ᴴ * fourier N = 1 := by
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hstar : star ((((Real.sqrt N : ℝ) : ℂ)⁻¹)) = (((Real.sqrt N : ℝ) : ℂ)⁻¹) := by simp
  have hstarchi : ∀ x : ZMod N, star (chiN x j) = chiN x (-j) := by
    intro x
    unfold chiN
    rw [stdAddChar_star]
    congr 1
    ring
  have hterm : ∀ x : ZMod N, (fourier N)ᴴ j x * fourier N x k
      = ((((Real.sqrt N : ℝ) : ℂ)⁻¹) * (((Real.sqrt N : ℝ) : ℂ)⁻¹)) * chiN x (k - j) := by
    intro x
    rw [Matrix.conjTranspose_apply]
    unfold fourier
    rw [star_mul, hstar, hstarchi x]
    calc chiN x (-j) * (((Real.sqrt N : ℝ) : ℂ)⁻¹)
          * ((((Real.sqrt N : ℝ) : ℂ)⁻¹) * chiN x k)
        = ((((Real.sqrt N : ℝ) : ℂ)⁻¹) * (((Real.sqrt N : ℝ) : ℂ)⁻¹))
          * (chiN x (-j) * chiN x k) := by ring
      _ = ((((Real.sqrt N : ℝ) : ℂ)⁻¹) * (((Real.sqrt N : ℝ) : ℂ)⁻¹))
          * chiN x (k - j) := by
          rw [← chiN_add_right]
          congr 1
          abel
  rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum]
  rw [show (∑ x : ZMod N, chiN x (k - j)) = ((if k - j = 0 then N else 0 : ℕ) : ℂ) from by
    rw [chiN_sum, ZMod.card]]
  by_cases hjk : k - j = 0
  · have hjk' : j = k := (sub_eq_zero.mp hjk).symm
    rw [ite_eq_left hjk, ite_eq_left hjk', sqrt_inv_mul_self hN]
  · have hjk' : j ≠ k := fun h => hjk (by rw [h]; abel)
    rw [ite_eq_right hjk, ite_eq_right hjk']
    simp

/-- The Fourier eigenvalue of the cyclic group-algebra matrix with coefficient vector `v` at
frequency `j`. -/
noncomputable def eigen (v : ZMod N → ℂ) (j : ZMod N) : ℂ :=
  ∑ x, v x * chiN j x

/-- The complex norm of the Fourier eigenvalue at frequency `j`. -/
noncomputable def absEigen (v : ZMod N → ℂ) (j : ZMod N) : ℝ := ‖eigen v j‖

/-- Every absolute Fourier eigenvalue is nonnegative. -/
lemma absEigen_nonneg (v : ZMod N → ℂ) (j : ZMod N) : 0 ≤ absEigen v j :=
  norm_nonneg (eigen v j)

/-- The cyclic group-algebra matrix whose Fourier eigenvalues are `absEigen v`. -/
noncomputable def absGroupAlgebra (v : ZMod N → ℂ) : Matrix (ZMod N) (ZMod N) ℂ :=
  groupAlgebraElem (invFourierVec (fun j => ((absEigen v j : ℝ) : ℂ)))

/-- Fourier conjugation diagonalizes `absGroupAlgebra v` with diagonal entries `absEigen v`, as
in [Hunziker et al., Proposition 5.4][HunzikerEtAl2003]. -/
theorem fourier_absGroupAlgebra (v : ZMod N → ℂ) :
    fourier N * absGroupAlgebra v * (fourier N)ᴴ
      = Matrix.diagonal (fun j => ((absEigen v j : ℝ) : ℂ)) := by
  unfold absGroupAlgebra
  rw [fourier_conj_groupAlgebraElem (Nat.pos_of_neZero N)]
  congr 1
  funext j
  exact eigen_invFourierVec (fun j => ((absEigen v j : ℝ) : ℂ)) j

/-- The spectral absolute-value matrix belongs to the cyclic group algebra, as in [Hunziker et
al., Proposition 5.4][HunzikerEtAl2003]. -/
theorem absGroupAlgebra_mem (v : ZMod N → ℂ) :
    ∃ w, absGroupAlgebra v = groupAlgebraElem w :=
  ⟨_, rfl⟩

/-- Every diagonal entry of `absGroupAlgebra v` equals its entry at (0, 0), as in [Hunziker et
al., Proposition 5.4][HunzikerEtAl2003]. -/
theorem absGroupAlgebra_constant_diag (v : ZMod N → ℂ) (i : ZMod N) :
    absGroupAlgebra v i i = absGroupAlgebra v 0 0 := by
  unfold absGroupAlgebra
  rw [cyclic_diag, cyclic_diag]

/-- The spectral absolute-value matrix has a factorization `Cᴴ * C`, proving its positivity as
in [Hunziker et al., Proposition 5.4][HunzikerEtAl2003]. -/
theorem absGroupAlgebra_psd (v : ZMod N → ℂ) :
    ∃ C, absGroupAlgebra v = Cᴴ * C := by
  have hN : 0 < N := Nat.pos_of_neZero N
  have hF' : (fourier N)ᴴ * fourier N = 1 := fourier_conjTranspose_mul hN
  refine ⟨Matrix.diagonal (fun j => ((Real.sqrt (absEigen v j) : ℝ) : ℂ)) * fourier N, ?_⟩
  have hspec : absGroupAlgebra v
      = (fourier N)ᴴ * Matrix.diagonal (fun j => ((absEigen v j : ℝ) : ℂ)) * fourier N := by
    have hD := fourier_absGroupAlgebra (N := N) v
    calc absGroupAlgebra v
        = (fourier N)ᴴ * (fourier N * absGroupAlgebra v * (fourier N)ᴴ) * fourier N := by
          simp only [Matrix.mul_assoc]
          rw [hF', Matrix.mul_one, ← Matrix.mul_assoc, hF', Matrix.one_mul]
      _ = (fourier N)ᴴ * Matrix.diagonal (fun j => ((absEigen v j : ℝ) : ℂ)) * fourier N := by
          rw [hD]
  have hdiag : (Matrix.diagonal (fun j => ((Real.sqrt (absEigen v j) : ℝ) : ℂ)))ᴴ
      = Matrix.diagonal (fun j => ((Real.sqrt (absEigen v j) : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose]
    ext j k
    by_cases hjk : j = k
    · subst hjk
      simp [Complex.conj_ofReal]
    · simp [hjk]
  have hfun : (fun j => ((Real.sqrt (absEigen v j) : ℝ) : ℂ)
        * ((Real.sqrt (absEigen v j) : ℝ) : ℂ))
      = (fun j => ((absEigen v j : ℝ) : ℂ)) := by
    funext j
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (absEigen_nonneg v j)]
  have hCC : (Matrix.diagonal (fun j => ((Real.sqrt (absEigen v j) : ℝ) : ℂ)) * fourier N)ᴴ
        * (Matrix.diagonal (fun j => ((Real.sqrt (absEigen v j) : ℝ) : ℂ)) * fourier N)
      = (fourier N)ᴴ * Matrix.diagonal (fun j => ((absEigen v j : ℝ) : ℂ)) * fourier N := by
    rw [Matrix.conjTranspose_mul, hdiag]
    calc ((fourier N)ᴴ * Matrix.diagonal (fun j => ((Real.sqrt (absEigen v j) : ℝ) : ℂ)))
          * (Matrix.diagonal (fun j => ((Real.sqrt (absEigen v j) : ℝ) : ℂ)) * fourier N)
        = (fourier N)ᴴ
            * (Matrix.diagonal (fun j => ((Real.sqrt (absEigen v j) : ℝ) : ℂ))
              * (Matrix.diagonal (fun j => ((Real.sqrt (absEigen v j) : ℝ) : ℂ)) * fourier N)) :=
          Matrix.mul_assoc _ _ _
      _ = (fourier N)ᴴ
            * ((Matrix.diagonal (fun j => ((Real.sqrt (absEigen v j) : ℝ) : ℂ))
              * Matrix.diagonal (fun j => ((Real.sqrt (absEigen v j) : ℝ) : ℂ))) * fourier N) := by
          rw [← Matrix.mul_assoc (Matrix.diagonal (fun j => ((Real.sqrt (absEigen v j) : ℝ) : ℂ)))
            (Matrix.diagonal (fun j => ((Real.sqrt (absEigen v j) : ℝ) : ℂ))) (fourier N)]
      _ = (fourier N)ᴴ
            * (Matrix.diagonal (fun j => ((Real.sqrt (absEigen v j) : ℝ) : ℂ)
              * ((Real.sqrt (absEigen v j) : ℝ) : ℂ)) * fourier N) := by
          rw [Matrix.diagonal_mul_diagonal]
      _ = (fourier N)ᴴ
            * (Matrix.diagonal (fun j => ((absEigen v j : ℝ) : ℂ)) * fourier N) := by
          rw [hfun]
      _ = (fourier N)ᴴ * Matrix.diagonal (fun j => ((absEigen v j : ℝ) : ℂ)) * fourier N :=
          (Matrix.mul_assoc _ _ _).symm
  exact hspec.trans hCC.symm

/-- The common diagonal entry of `absGroupAlgebra v` is 1/N times the sum of the absolute
Fourier eigenvalues. This is used in the learning bounds of [HunzikerEtAl2003]. -/
theorem absGroupAlgebra_diag (v : ZMod N → ℂ) :
    absGroupAlgebra v 0 0
      = ((N : ℂ))⁻¹ * ((∑ j, absEigen v j : ℝ) : ℂ) := by
  unfold absGroupAlgebra
  rw [groupAlgebraElem_apply, sub_self, invFourierVec]
  have hsum : (∑ j : ZMod N, ((absEigen v j : ℝ) : ℂ) * chiN (0 : ZMod N) (-j))
      = ((∑ j, absEigen v j : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [chiN_comm (0 : ZMod N) (-j), chiN_zero_right, mul_one]
  rw [hsum]

/-- The sum of the squared complex norms of the diagonal entries of a matrix indexed by `ZMod
N`. -/
noncomputable def diagNormSqZ (B : Matrix (ZMod N) (ZMod N) ℂ) : ℝ :=
  ∑ i, Complex.normSq (B i i)

/-- Reindexing a cyclic matrix by `Fin N` identifies `diagNormSqZ` with `diagNormSq`. -/
lemma diagNormSqZ_eq (B : Matrix (ZMod N) (ZMod N) ℂ) :
    diagNormSqZ (N := N) B
      = diagNormSq (Matrix.reindex (ZMod.finEquiv N).toEquiv.symm
          (ZMod.finEquiv N).toEquiv.symm B) := by
  simp only [diagNormSqZ, diagNormSq, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact (Equiv.sum_comp (ZMod.finEquiv N).toEquiv
    (fun j : ZMod N => Complex.normSq (B j j))).symm

/-- For `U * Uᴴ = 1`, if `U * absGroupAlgebra v` has constant diagonal, its diagonal squared
norm is at most that of `absGroupAlgebra v`, as in [Hunziker et al., Proposition
5.4][HunzikerEtAl2003]. -/
theorem absGroupAlgebra_max (v : ZMod N → ℂ) {U : Matrix (ZMod N) (ZMod N) ℂ}
    (hU : U * Uᴴ = 1)
    (hdiagU : ∀ i, (U * absGroupAlgebra v) i i = (U * absGroupAlgebra v) 0 0) :
    diagNormSqZ (U * absGroupAlgebra v) ≤ diagNormSqZ (absGroupAlgebra v) := by
  let e : ZMod N ≃ Fin N := (ZMod.finEquiv N).toEquiv.symm
  obtain ⟨C, hC⟩ := absGroupAlgebra_psd v
  have hmul : ∀ A B : Matrix (ZMod N) (ZMod N) ℂ,
      Matrix.reindex e e (A * B) = Matrix.reindex e e A * Matrix.reindex e e B :=
    fun A B => (Matrix.reindexAlgEquiv ℝ ℂ e).map_mul A B
  have hone : Matrix.reindex e e (1 : Matrix (ZMod N) (ZMod N) ℂ) = 1 :=
    (Matrix.reindexAlgEquiv ℝ ℂ e).map_one
  have hU' : Matrix.reindex e e U * (Matrix.reindex e e U)ᴴ = 1 := by
    rw [Matrix.conjTranspose_reindex, ← hmul, hU, hone]
  have hA' : Matrix.reindex e e (absGroupAlgebra v)
      = (Matrix.reindex e e C)ᴴ * Matrix.reindex e e C := by
    rw [hC, hmul, ← Matrix.conjTranspose_reindex]
  have hdiagA' : ∀ i : Fin N, Matrix.reindex e e (absGroupAlgebra v) i i
      = Matrix.reindex e e (absGroupAlgebra v) 0 0 := by
    intro i
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [absGroupAlgebra_constant_diag v (e.symm i),
      absGroupAlgebra_constant_diag v (e.symm 0)]
  have hdiagC' : ∀ i : Fin N, ((Matrix.reindex e e C)ᴴ * Matrix.reindex e e C) i i
      = ((Matrix.reindex e e C)ᴴ * Matrix.reindex e e C) 0 0 := by
    intro i
    rw [← hA']
    exact hdiagA' i
  have hdiagU'' : ∀ i : Fin N, Matrix.reindex e e (U * absGroupAlgebra v) i i
      = Matrix.reindex e e (U * absGroupAlgebra v) 0 0 := by
    intro i
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [hdiagU (e.symm i), hdiagU (e.symm 0)]
  have hdiagU' : ∀ i : Fin N,
      (Matrix.reindex e e U * ((Matrix.reindex e e C)ᴴ * Matrix.reindex e e C)) i i
        = (Matrix.reindex e e U * ((Matrix.reindex e e C)ᴴ * Matrix.reindex e e C)) 0 0 := by
    intro i
    rw [← hA', ← hmul]
    exact hdiagU'' i
  have hle := diagNormSq_mul_unitary_le (n := N) hdiagC' hU' hdiagU'
  rw [diagNormSqZ_eq, diagNormSqZ_eq]
  have hleft : Matrix.reindex e e (U * absGroupAlgebra v)
      = Matrix.reindex e e U * ((Matrix.reindex e e C)ᴴ * Matrix.reindex e e C) := by
    rw [hmul, hA']
  rw [hleft, hA']
  exact hle

end Qatlib.Papers.QLearningGeom03.MainResults
