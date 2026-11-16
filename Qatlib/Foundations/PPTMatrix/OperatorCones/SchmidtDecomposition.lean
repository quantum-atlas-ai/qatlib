/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.ForMathlib.SchmidtBridges
public import Qatlib.Foundations.PPTMatrix.OperatorCones.ForMathlib.ThinSingularValueDecomposition
public import Qatlib.Foundations.PPTMatrix.OperatorCones.SchmidtNumber
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section




/-!
# Schmidt decompositions with exactly the coefficient-matrix rank many terms.

The thin singular expansion of a bipartite vector's coefficient matrix is transported to an actual Schmidt expansion. The number of strictly positive terms equals the coefficient-matrix rank, and both local families are orthonormal. Rank-zero and empty ambient types remain covered.
-/

open Matrix
open scoped Kronecker

namespace Qatlib.Foundations.PPTMatrix.OperatorCones.ManuscriptSchmidt

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq n] in
/-- Entrywise conjugation preserves orthonormality in finite complex
coordinate space; it is not asserted to be a complex-linear operation. -/
theorem orthonormal_conjugate_coordinates {r : Type*}
    (b : r → EuclideanSpace ℂ n) (hb : Orthonormal ℂ b) :
    Orthonormal ℂ (fun j => WithLp.toLp 2 (fun k => star (b j k))) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro i j
  have h := congrArg star (orthonormal_iff_ite.mp hb i j)
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    WithLp.ofLp_toLp, Pi.star_apply, star_sum, star_mul, star_star,
    apply_ite, star_one, star_zero, mul_comm] using h

omit [DecidableEq m] in
/-- Every bipartite vector has an actual Schmidt expansion indexed by its
coefficient-matrix rank, including rank zero and empty ambient index types. -/
theorem exists_schmidt_decomposition (v : m × n → ℂ) :
    ∃ (a : Fin (schmidtRank v) → EuclideanSpace ℂ m)
      (b : Fin (schmidtRank v) → EuclideanSpace ℂ n)
      (s : Fin (schmidtRank v) → ℝ),
      Orthonormal ℂ a ∧ Orthonormal ℂ b ∧ (∀ i, 0 < s i) ∧
      v = fun ij : m × n => ∑ k, (s k : ℂ) * a k ij.1 * b k ij.2 := by
  classical
  obtain ⟨r, a, bRight, s, ha, hbRight, hs, hT⟩ :=
    ManuscriptSVD.exists_thin_singular_expansion (coeffMatrix v).toEuclideanLin
  let b : Fin r → EuclideanSpace ℂ n :=
    fun k => WithLp.toLp 2 (fun j => star (bRight k j))
  have hb : Orthonormal ℂ b := orthonormal_conjugate_coordinates bRight hbRight
  have hv : v = fun ij : m × n => ∑ k, (s k : ℂ) * a k ij.1 * b k ij.2 := by
    funext ij
    obtain ⟨i, j⟩ := ij
    calc
      v (i, j) = ((coeffMatrix v).toEuclideanLin (EuclideanSpace.single j 1)) i := by
        change (coeffMatrix v) i j = ((coeffMatrix v) *ᵥ Pi.single j 1) i
        exact (congrFun (Matrix.mulVec_single_one (coeffMatrix v) j) i).symm
      _ = (∑ k, ((s k : ℂ) * inner ℂ (bRight k) (EuclideanSpace.single j 1)) • a k) i :=
        congrArg (fun x : EuclideanSpace ℂ m => x i) (hT (EuclideanSpace.single j 1))
      _ = ∑ k, (s k : ℂ) * a k i * b k j := by
        simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
          EuclideanSpace.inner_single_right, one_mul, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro k _
        change ((s k : ℂ) * star (bRight k j)) * a k i =
          (s k : ℂ) * a k i * star (bRight k j)
        ring
  have hr : schmidtRank v = r := by
    rw [hv, schmidtRank_eq_nonzero_terms a b s ha hb]
    let e : {j : Fin r // s j ≠ 0} ≃ Fin r :=
      Equiv.subtypeUnivEquiv (fun j => ne_of_gt (hs j))
    exact (Fintype.card_congr e).trans (Fintype.card_fin r)
  subst r
  exact ⟨a, b, s, ha, hb, hs, hv⟩

omit [DecidableEq m] in
/-- The manuscript's orthonormal reference realization, obtained from its
Schmidt decomposition rather than an arbitrary rank factorization. -/
theorem exists_reference_isometry_of_schmidt (v : m × n → ℂ) :
    ∃ (U : Matrix m (Fin (schmidtRank v)) ℂ)
      (w : Fin (schmidtRank v) × n → ℂ),
      Uᴴ * U = 1 ∧ v = (U ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ w := by
  classical
  obtain ⟨a, b, s, ha, _, _, hv⟩ := exists_schmidt_decomposition v
  let U : Matrix m (Fin (schmidtRank v)) ℂ := fun i k => a k i
  let w : Fin (schmidtRank v) × n → ℂ := fun kj => (s kj.1 : ℂ) * b kj.1 kj.2
  have hU : Uᴴ * U = 1 := by
    apply (orthonormal_columns_iff U).mp
    change Orthonormal ℂ a
    exact ha
  have hfactor : coeffMatrix v = U * coeffMatrix w := by
    ext i j
    rw [Matrix.mul_apply]
    change v (i, j) = ∑ k, a k i * ((s k : ℂ) * b k j)
    rw [congrFun hv (i, j)]
    apply Finset.sum_congr rfl
    intro k _
    ring
  refine ⟨U, w, hU, ?_⟩
  have hcoeff : coeffMatrix v = coeffMatrix ((U ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ w) := by
    rw [coeffMatrix_kronecker_mulVec, Matrix.transpose_one, Matrix.mul_one]
    exact hfactor
  funext ij
  exact congrFun (congrFun hcoeff ij.1) ij.2

end Qatlib.Foundations.PPTMatrix.OperatorCones.ManuscriptSchmidt
