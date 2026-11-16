/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.Defs
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section




/-!
# Rectangular singular expansions on the nonzero singular subspace.

For a rectangular operator, singular vectors in the codomain form an orthonormal family only on the nonzero-singular-value support. This construction keeps the zero slots explicit, then restricts to the finite nonzero subtype to obtain an exact thin expansion.
-/

open Module
open scoped ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones.ManuscriptSVD

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Rectangular singular-vector existence without a false full-basis claim on
the codomain. Restricting both families to the nonzero singular indices yields
the thin decomposition; all zero slots are explicitly retained here. -/
theorem exists_rectangular_singular_family (T : E →ₗ[ℂ] F) :
    ∃ (v : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E)
      (s : Fin (finrank ℂ E) → ℝ) (u : Fin (finrank ℂ E) → F),
      (∀ i, 0 ≤ s i) ∧
      Orthonormal ℂ ({i | s i ≠ 0}.domRestrict u) ∧
      (∀ i, s i = 0 → u i = 0) ∧
      (∀ i, T (v i) = (s i : ℂ) • u i) := by
  classical
  let hP := T.isPositive_adjoint_comp_self
  let v := hP.isSymmetric.eigenvectorBasis (n := finrank ℂ E) rfl
  let s : Fin (finrank ℂ E) → ℝ :=
    fun i => Real.sqrt (hP.isSymmetric.eigenvalues rfl i)
  let u : Fin (finrank ℂ E) → F :=
    fun i => (((s i)⁻¹ : ℝ) : ℂ) • T (v i)
  have hs2 (i : Fin (finrank ℂ E)) :
      (s i : ℂ) ^ 2 = (hP.isSymmetric.eigenvalues rfl i : ℂ) := by
    have h := Real.sq_sqrt (hP.nonneg_eigenvalues rfl i)
    change (Real.sqrt (hP.isSymmetric.eigenvalues rfl i) : ℂ) ^ 2 = _
    exact_mod_cast h
  have hg (i j : Fin (finrank ℂ E)) :
      inner ℂ (T (v i)) (T (v j)) =
        (s j : ℂ) ^ 2 * (if i = j then 1 else 0) := by
    rw [← LinearMap.adjoint_inner_right T]
    change inner ℂ (v i) ((LinearMap.adjoint T ∘ₗ T) (v j)) = _
    have hj : (LinearMap.adjoint T ∘ₗ T) (v j) =
        (hP.isSymmetric.eigenvalues rfl j : ℂ) • v j :=
      hP.isSymmetric.apply_eigenvectorBasis rfl j
    rw [hj, inner_smul_right, v.inner_eq_ite, hs2]
  have hu : Orthonormal ℂ ({i | s i ≠ 0}.domRestrict u) := by
    apply orthonormal_iff_ite.mpr
    intro i j
    change inner ℂ ((((s i.val)⁻¹ : ℝ) : ℂ) • T (v i.val))
      ((((s j.val)⁻¹ : ℝ) : ℂ) • T (v j.val)) = if i = j then 1 else 0
    rw [inner_smul_left, inner_smul_right, hg]
    simp only [map_inv₀, Complex.conj_ofReal, Complex.ofReal_inv]
    by_cases hij : i = j
    · subst j
      have hi : s i.val ≠ 0 := i.property
      have hiC : (s i.val : ℂ) ≠ 0 := by exact_mod_cast hi
      simp only [ite_true, mul_one]
      field_simp [hiC]
    · have hval : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      simp only [ite_eq_right hij, ite_eq_right hval, mul_zero]
  refine ⟨v, s, u, fun _ => Real.sqrt_nonneg _, hu, ?_, ?_⟩
  · intro i hi
    simp only [u, hi, inv_zero, Complex.ofReal_zero, zero_smul]
  · intro i
    by_cases hi : s i = 0
    · have hTi : T (v i) = 0 := (inner_self_eq_zero (𝕜 := ℂ)).mp (by
        simpa only [hi, Complex.ofReal_zero, zero_pow (by decide : 2 ≠ 0),
          ite_true, zero_mul] using hg i i)
      simp only [hTi, hi, Complex.ofReal_zero, zero_smul]
    · dsimp [u]
      rw [smul_smul, mul_inv_cancel₀ hi, one_smul]

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
/-- Expansion over the domain singular basis. Zero coefficients vanish,
so restriction to the nonzero subtype retains exactly the same operator. -/
theorem rectangular_singular_family_expansion
    (T : E →ₗ[ℂ] F) {ι : Type*} [Fintype ι]
    (v : OrthonormalBasis ι ℂ E) (s : ι → ℝ) (u : ι → F)
    (hT : ∀ i, T (v i) = (s i : ℂ) • u i) (x : E) :
    T x = ∑ i, ((s i : ℂ) * inner ℂ (v i) x) • u i := by
  calc
    T x = T (∑ i, inner ℂ (v i) x • v i) :=
      congrArg T (v.sum_repr' x).symm
    _ = ∑ i, inner ℂ (v i) x • T (v i) := by
      rw [map_sum]
      simp only [map_smul]
    _ = ∑ i, ((s i : ℂ) * inner ℂ (v i) x) • u i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hT, smul_smul, mul_comm]

/-- The finite thin singular expansion has orthonormal factors on both sides
and strictly positive coefficients. The zero map is represented with `r = 0`.
The identification of `r` with rank is the separate algebraic rank/count lemma. -/
theorem exists_thin_singular_expansion (T : E →ₗ[ℂ] F) :
    ∃ (r : ℕ) (a : Fin r → F) (b : Fin r → E) (s : Fin r → ℝ),
      Orthonormal ℂ a ∧ Orthonormal ℂ b ∧ (∀ i, 0 < s i) ∧
      ∀ x, T x = ∑ i, ((s i : ℂ) * inner ℂ (b i) x) • a i := by
  classical
  obtain ⟨v, s, u, hs, hu, _, hT⟩ := exists_rectangular_singular_family T
  let S : Set (Fin (finrank ℂ E)) := {i | s i ≠ 0}
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  have ha : Orthonormal ℂ (fun i : Fin (Fintype.card S) => u (e i).val) :=
    hu.comp e e.injective
  have hb : Orthonormal ℂ (fun i : Fin (Fintype.card S) => v (e i).val) :=
    v.orthonormal.comp (fun i => (e i).val) (Subtype.val_injective.comp e.injective)
  refine ⟨Fintype.card S, fun i => u (e i).val, fun i => v (e i).val,
    fun i => s (e i).val, ha, hb, ?_, ?_⟩
  · intro i
    exact lt_of_le_of_ne (hs _) (Ne.symm (e i).property)
  · intro x
    calc
      T x = ∑ i, ((s i : ℂ) * inner ℂ (v i) x) • u i :=
        rectangular_singular_family_expansion T v s u hT x
      _ = ∑ i : S, ((s i.val : ℂ) * inner ℂ (v i.val) x) • u i.val := by
        apply Finset.sum_congr_set S
        · intro i hi
          rfl
        · intro i hi
          have hi0 : s i = 0 := by
            simpa only [S, Set.mem_ofPred_eq, not_not] using hi
          simp only [hi0, Complex.ofReal_zero, zero_mul, zero_smul]
      _ = ∑ i : Fin (Fintype.card S),
          ((s (e i).val : ℂ) * inner ℂ (v (e i).val) x) • u (e i).val :=
        (e.sum_comp _).symm

end Qatlib.Foundations.PPTMatrix.OperatorCones.ManuscriptSVD
