/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnstrRandom10.MainResults.StoquasticGroundTransform

set_option backward.isDefEq.respectTransparency false

/-!
# UnstrRandom10.MainResults: stoquastic variational bounds (Lemma 1, Theorem 4)

Farhi--Goldstone--Gosset--Shor, *Unstructured Randomness, Small Gaps and
Localization*, fixed arXiv:1010.0009v1, Section II.1.

The paper proves its variational lower bound for stoquastic Hamiltonians in two
steps.

* Lemma 1 (extracted-text line 142): if `H` is Hermitian and stoquastic in the
  `|z⟩` basis with `H|ψ⟩ = E|ψ⟩` and `⟨z|ψ⟩ > 0` for all `z`, then `E` is the
  ground state energy `E_g` of `H`. The paper proves this by flipping the signs of
  the amplitudes of a ground state `|ψ_g⟩`, observing that the stoquasticity of `H`
  can only lower the expectation, and deriving a contradiction with the orthogonality
  of the eigenspaces from the strict positivity of `ψ` (extracted-text lines
  143--200).

* Theorem 4 (extracted-text lines 132--138): for any state `|φ⟩` with
  `⟨z|φ⟩ > 0` for all `z`, the ground state energy satisfies
  `E_g ≥ min_z ⟨z|H|φ⟩ / ⟨z|φ⟩`. The proof shifts `H` by the diagonal
  `diag_z (⟨z|H|φ⟩/⟨z|φ⟩)`, so that `|φ⟩` becomes a zero eigenvector, applies
  Lemma 1 to the shifted matrix, and compares quadratic forms.

Both results are stated below for the real symmetric matrix representing the
paper's real-entry Hermitian operator. Lemma 1 is stated as "`E` is an eigenvalue
and no eigenvalue is smaller" (`IsLowestEigenvalue`), and Theorem 4 is stated for
every eigenvalue `E` of `H`, which is the same statement applied to `E_g`.

The Lean proofs replace the paper's sign-flip comparison for `|ψ_g⟩` by the
equivalent ground-state transform proved in `StoquasticGroundTransform`: after
shifting by the relevant multiple of the identity or by the relevant diagonal, the
shifted matrix is stoquastic with the positive kernel vector and is therefore
positive semidefinite. The Rayleigh quotients of `H` and of the shifted matrix then
give the claimed inequalities.

Boundary: the random permutation `π`, the Hamiltonian family `H_π(s)`, and the
asymptotic probability statements of Theorems 1--3 and Lemma 3 are not covered by
this module.
-/

set_option autoImplicit false

noncomputable section

open Matrix

namespace Qatlib.Papers.UnstrRandom10.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lemma 1 of arXiv:1010.0009v1 (extracted-text line 142): a pointwise positive
eigenvector of a stoquastic matrix realizes the lowest eigenvalue. -/
theorem stoquastic_positive_eigenvector_lowest (H : Matrix ι ι ℝ) (hH : IsStoquastic H)
    [Nonempty ι] (ψ : ι → ℝ) (hψ : ∀ i, 0 < ψ i) (E : ℝ) (hEig : H *ᵥ ψ = E • ψ) :
    IsLowestEigenvalue H E := by
  refine ⟨⟨ψ, ?_, hEig⟩, ?_⟩
  · intro h0
    obtain ⟨i0⟩ := ‹Nonempty ι›
    have : ψ i0 = 0 := by rw [h0]; rfl
    linarith [hψ i0]
  · obtain ⟨hHsym, hHoff⟩ := hH
    intro mu v hv hveig
    have hstoq : IsStoquastic (H - E • (1 : Matrix ι ι ℝ)) := by
      refine ⟨fun i j => ?_, fun i j hij => ?_⟩
      · by_cases hij : i = j
        · subst hij
          rfl
        · have hji : ¬ j = i := fun h => hij h.symm
          simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, hij,
            hji, if_false, mul_zero, sub_zero]
          exact hHsym i j
      · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, hij,
          if_false, mul_zero, sub_zero]
        exact hHoff i j hij
    have hker : (H - E • (1 : Matrix ι ι ℝ)) *ᵥ ψ = 0 := by
      rw [sub_mulVec, smul_mulVec, one_mulVec, hEig, sub_self]
    have hpsd := posSemidef_of_stoquastic_kernel _ hstoq ψ hψ hker
    have hqK : 0 ≤ qform (H - E • (1 : Matrix ι ι ℝ)) v := by
      have := Matrix.PosSemidef.dotProduct_mulVec_nonneg hpsd v
      simpa only [qform, star_trivial] using this
    have hsplit := qform_sub_smul_one H E v
    have hqH := qform_of_eigenvector H v mu hveig
    have hvv : 0 < v ⬝ᵥ v := by
      have hne : v ⬝ᵥ v ≠ 0 := fun h => hv (dotProduct_self_eq_zero.mp h)
      exact lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)) (Ne.symm hne)
    have : E * (v ⬝ᵥ v) ≤ mu * (v ⬝ᵥ v) := by
      nlinarith [hqK, hsplit, hqH]
    exact le_of_mul_le_mul_right this hvv

/-- Theorem 4 of arXiv:1010.0009v1 (extracted-text lines 132--138): every
eigenvalue `E` of a stoquastic matrix, and in particular its lowest eigenvalue
`E_g`, is at least `min_z ⟨z|H|φ⟩ / ⟨z|φ⟩` for any pointwise positive state `|φ⟩`. -/
theorem stoquastic_eigenvalue_ge_min_quotient (H : Matrix ι ι ℝ) (hH : IsStoquastic H)
    [Nonempty ι] (φ : ι → ℝ) (hφ : ∀ i, 0 < φ i) (E : ℝ) (v : ι → ℝ) (hv : v ≠ 0)
    (hveig : H *ᵥ v = E • v) :
    (Finset.univ.inf' Finset.univ_nonempty (fun z => (H *ᵥ φ) z / φ z)) ≤ E := by
  obtain ⟨hHsym, hHoff⟩ := hH
  set d : ι → ℝ := fun z => (H *ᵥ φ) z / φ z with hd
  have hstoq : IsStoquastic (H - diagonal d) := by
    refine ⟨fun i j => ?_, fun i j hij => ?_⟩
    · by_cases hij : i = j
      · subst hij
        rfl
      · have hji : ¬ j = i := fun h => hij h.symm
        simp only [Matrix.sub_apply, diagonal_apply, hij, hji, if_false, sub_zero]
        exact hHsym i j
    · simp only [Matrix.sub_apply, diagonal_apply, hij, if_false, sub_zero]
      exact hHoff i j hij
  have hker : (H - diagonal d) *ᵥ φ = 0 := by
    ext z
    have hz : φ z ≠ 0 := ne_of_gt (hφ z)
    simp only [sub_mulVec, Pi.sub_apply, Pi.zero_apply, mulVec_diagonal, hd]
    rw [div_mul_cancel₀ _ hz, sub_self]
  have hpsd := posSemidef_of_stoquastic_kernel _ hstoq φ hφ hker
  have hqK : 0 ≤ qform (H - diagonal d) v := by
    have := Matrix.PosSemidef.dotProduct_mulVec_nonneg hpsd v
    simpa only [qform, star_trivial] using this
  have hsplit := qform_sub_diagonal H d v
  have hqH := qform_of_eigenvector H v E hveig
  have hvv : 0 < v ⬝ᵥ v := by
    have hne : v ⬝ᵥ v ≠ 0 := fun h => hv (dotProduct_self_eq_zero.mp h)
    exact lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)) (Ne.symm hne)
  have hterm : ∀ z, (Finset.univ.inf' Finset.univ_nonempty d) * (v z * v z)
      ≤ v z * (d z * v z) := by
    intro z
    have h1 : Finset.univ.inf' Finset.univ_nonempty d ≤ d z :=
      Finset.inf'_le _ (Finset.mem_univ z)
    nlinarith [mul_self_nonneg (v z)]
  have hsum : (Finset.univ.inf' Finset.univ_nonempty d) * (v ⬝ᵥ v)
      ≤ ∑ z, v z * (d z * v z) := by
    have h := Finset.sum_le_sum fun z (_ : z ∈ Finset.univ) => hterm z
    rw [show (Finset.univ.inf' Finset.univ_nonempty d) * (v ⬝ᵥ v)
        = ∑ z, (Finset.univ.inf' Finset.univ_nonempty d) * (v z * v z) from by
      rw [dotProduct, Finset.mul_sum]]
    exact h
  have hE : (Finset.univ.inf' Finset.univ_nonempty d) * (v ⬝ᵥ v) ≤ E * (v ⬝ᵥ v) := by
    calc (Finset.univ.inf' Finset.univ_nonempty d) * (v ⬝ᵥ v)
        ≤ ∑ z, v z * (d z * v z) := hsum
      _ ≤ qform H v := by linarith [hqK, hsplit]
      _ = E * (v ⬝ᵥ v) := hqH
  exact le_of_mul_le_mul_right hE hvv

/-- Theorem 4 of arXiv:1010.0009v1 in the paper's own wording: if `E_g` is the
lowest eigenvalue of the stoquastic `H`, then `E_g ≥ min_z ⟨z|H|φ⟩ / ⟨z|φ⟩` for any
pointwise positive state `|φ⟩`. -/
theorem stoquastic_groundEnergy_ge_min_quotient (H : Matrix ι ι ℝ) (hH : IsStoquastic H)
    [Nonempty ι] (Eg : ℝ) (hEg : IsLowestEigenvalue H Eg) (φ : ι → ℝ)
    (hφ : ∀ i, 0 < φ i) :
    (Finset.univ.inf' Finset.univ_nonempty (fun z => (H *ᵥ φ) z / φ z)) ≤ Eg := by
  obtain ⟨⟨v, hv, hveig⟩, _⟩ := hEg
  exact stoquastic_eigenvalue_ge_min_quotient H hH φ hφ Eg v hv hveig

end Qatlib.Papers.UnstrRandom10.MainResults
