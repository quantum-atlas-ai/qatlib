/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.LocalCircuits.LocalGateCosts.Costs
public import Qatlib.Papers.QCircApprox95.MainResults.Unitary
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

/-!
# Conjugating a phase into any site, and assembling the product form of Theorem 3.1

The phase gate `Qatlib.Concepts.LocalCircuits.LocalGateCosts.phaseGate` acts on the coordinate
`0` only. Conjugating it by the permutation matrix of the transposition `0 ↔ i` moves the phase to
the coordinate `i` without changing the phase or the unitary class, so a diagonal unitary whose
coordinates are single phases is the product of the conjugated phase gates at those coordinates.

Applied to a diagonalisation `U = W * D * W*` of a unitary, this gives the product form
`U = V_k I_{w_k} V_k* ⋯ V_1 I_{w_1} V_1*` used in the proof of [Knill1995], Theorem 3.1, with
`V_i = W * P_i`. The module proves the algebraic assembly. It does not prove the diagonalisation
itself: the existence of a unitary eigenbasis for a unitary matrix with a fixed subspace is the
analytic input that remains open, so the product form is proved here for a unitary that is already
presented in diagonalised form.

## Main statements

* `permMatrix_conj_diagonal`: conjugating a diagonal matrix by a permutation matrix permutes its
  diagonal.
* `prod_ofFn_conj`: a product of conjugates telescopes into the conjugate of the product.
* `prod_ofFn_diagonal`: a product of diagonal matrices is the diagonal of the pointwise product.
* `unitary_eq_conj_phase_product_of_diagonal`: a unitary presented as `W * D * W*` with `D`
  diagonal is a product of conjugated phase gates.

## References

* [Knill, 1995][Knill1995]
-/

set_option autoImplicit false
noncomputable section
open Matrix
namespace Qatlib.Papers.QCircApprox95.MainResults

open Qatlib.Concepts.LocalCircuits.LocalGateCosts

/-- The matrix whose row `a` is the standard basis vector at the coordinate `σ a`, i.e. the entry
in row `a`, column `b` is one exactly when `b = σ a`. -/
def permMatrix {N : ℕ} (σ : Equiv.Perm (Fin N)) : Matrix (Fin N) (Fin N) ℂ :=
  fun a b => if b = σ a then 1 else 0

/-- Left multiplication by the permutation matrix of `σ` permutes the rows by `σ`. -/
theorem permMatrix_mul {N : ℕ} (σ : Equiv.Perm (Fin N)) (M : Matrix (Fin N) (Fin N) ℂ) :
    permMatrix σ * M = M.submatrix σ id := by
  ext a c
  rw [Matrix.mul_apply, Matrix.submatrix_apply, id_eq]
  rw [Finset.sum_eq_single (σ a)]
  · rw [permMatrix, ite_eq_left rfl, one_mul]
  · intro x _ hx
    rw [permMatrix, ite_eq_right hx, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Right multiplication by the permutation matrix of `σ` permutes the columns by `σ⁻¹`. -/
theorem mul_permMatrix {N : ℕ} (σ : Equiv.Perm (Fin N)) (M : Matrix (Fin N) (Fin N) ℂ) :
    M * permMatrix σ = M.submatrix id σ.symm := by
  ext a c
  rw [Matrix.mul_apply, Matrix.submatrix_apply, id_eq]
  rw [Finset.sum_eq_single (σ.symm c)]
  · rw [permMatrix, σ.apply_symm_apply, ite_eq_left rfl, mul_one]
  · intro x _ hx
    rw [permMatrix]
    have hcx : ¬ (c = σ x) := by
      intro h
      exact hx (by rw [h, Equiv.symm_apply_apply])
    rw [ite_eq_right hcx, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The conjugate transpose of a permutation matrix is the permutation matrix of the inverse
permutation. -/
theorem conjTranspose_permMatrix {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (permMatrix σ)ᴴ = permMatrix σ.symm := by
  ext a b
  rw [Matrix.conjTranspose_apply, permMatrix, permMatrix]
  by_cases h : a = σ b
  · rw [ite_eq_left h, star_one, ite_eq_left (by rw [h, Equiv.symm_apply_apply])]
  · rw [ite_eq_right h, star_zero, ite_eq_right]
    intro hb
    exact h (by rw [hb, Equiv.apply_symm_apply])

/-- Conjugating a diagonal matrix by the permutation matrix of `σ` permutes its diagonal entries
by `σ`. -/
theorem permMatrix_conj_diagonal {N : ℕ} (σ : Equiv.Perm (Fin N)) (d : Fin N → ℂ) :
    permMatrix σ * Matrix.diagonal d * (permMatrix σ)ᴴ = Matrix.diagonal (fun a => d (σ a)) := by
  rw [conjTranspose_permMatrix, Matrix.mul_assoc, permMatrix_mul, mul_permMatrix,
    Matrix.submatrix_submatrix]
  ext a b
  simp only [Matrix.submatrix_apply, Function.comp_apply, id_eq, Equiv.symm_symm]
  by_cases h : a = b
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne d (fun he => h (σ.injective he)), Matrix.diagonal_apply_ne _ h]

/-- The permutation matrix of `σ` is unitary. -/
theorem permMatrix_mem_unitaryGroup {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    permMatrix σ ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hstar : star (permMatrix σ) = permMatrix σ.symm := by
    rw [Matrix.star_eq_conjTranspose]
    exact conjTranspose_permMatrix σ
  rw [Matrix.mem_unitaryGroup_iff', hstar, permMatrix_mul]
  ext a b
  rw [Matrix.submatrix_apply, id_eq, permMatrix, Matrix.one_apply, Equiv.apply_symm_apply]
  by_cases h : a = b <;> simp [h, eq_comm]

/-- A product of matrices conjugated by the same unitary is the conjugate of their product. -/
theorem prod_ofFn_conj {N : ℕ} (W : Matrix (Fin N) (Fin N) ℂ) (hWW : W * Wᴴ = 1)
    (hW'W : Wᴴ * W = 1) (k : ℕ) (D : Fin k → Matrix (Fin N) (Fin N) ℂ) :
    (List.ofFn (fun i => W * D i * Wᴴ)).prod = W * (List.ofFn D).prod * Wᴴ := by
  revert D
  induction k with
  | zero =>
    intro D
    rw [List.ofFn_zero, List.prod_nil, List.ofFn_zero, List.prod_nil, mul_one, hWW]
  | succ k ih =>
    intro D
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
      ih (fun i => D (Fin.succ i))]
    calc (W * D 0 * Wᴴ) * (W * (List.ofFn fun i => D (Fin.succ i)).prod * Wᴴ)
        = W * D 0 * (Wᴴ * W) * (List.ofFn fun i => D (Fin.succ i)).prod * Wᴴ := by noncomm_ring
      _ = W * D 0 * (List.ofFn fun i => D (Fin.succ i)).prod * Wᴴ := by rw [hW'W, mul_one]
      _ = W * (D 0 * (List.ofFn fun i => D (Fin.succ i)).prod) * Wᴴ := by noncomm_ring

/-- A product of diagonal matrices is the diagonal matrix of the pointwise product. -/
theorem prod_ofFn_diagonal {M : ℕ} (k : ℕ) (g : Fin k → Fin M → ℂ) :
    (List.ofFn (fun i => Matrix.diagonal (g i))).prod =
      Matrix.diagonal (fun a => (List.ofFn (fun i => g i a)).prod) := by
  revert g
  induction k with
  | zero =>
    intro g
    ext a b
    simp
  | succ k ih =>
    intro g
    rw [List.ofFn_succ, List.prod_cons, ih (fun i => g (Fin.succ i)),
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    rw [List.ofFn_succ, List.prod_cons]

/-- **Product form of Theorem 3.1, given a diagonalisation.** If a unitary `U` is presented as
`W * D * W*` with `W` unitary and `D` diagonal with entries `exp (I * φ a)` on the coordinate
`a`, then `U` is a product of conjugated phase gates at the coordinates, each conjugated by the
unitary `W * P_i` obtained from the permutation matrix swapping the phase coordinate `0` with the
coordinate `i`. This is the algebraic part of the proof of [Knill1995], Theorem 3.1. The
diagonalisation itself, and hence the paper's hypothesis of a fixed subspace of dimension `2 ^ n -
k`, is not proved here, and no cost bound is asserted: the gate count is only identified as a
product of `2 ^ n` factors. -/
theorem unitary_eq_conj_phase_product_of_diagonal {n : ℕ}
    (W U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (φ : Fin (2 ^ n) → ℝ)
    (hU : U = W * Matrix.diagonal (fun a => Complex.exp (Complex.I * (φ a : ℂ))) * Wᴴ) :
    ∃ (V : Fin (2 ^ n) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (w : Fin (2 ^ n) → ℝ),
      (∀ i, V i ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) ∧
      U = (List.ofFn (fun i => V i * phaseGate n (w i) * (V i)ᴴ)).prod := by
  classical
  have hN : 0 < 2 ^ n := Nat.two_pow_pos n
  have hW'W : Wᴴ * W = 1 := Matrix.mem_unitaryGroup_iff'.mp hW
  have hWW : W * Wᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hW
    simpa only [Matrix.star_eq_conjTranspose] using h
  -- the reference coordinate of the phase gate
  let z : Fin (2 ^ n) := ⟨0, hN⟩
  have hz : z = (0 : Fin (2 ^ n)) := Fin.ext rfl
  -- the transposition moving the phase coordinate onto the site `i`
  let σ : Fin (2 ^ n) → Equiv.Perm (Fin (2 ^ n)) := fun i => Equiv.swap z i
  -- the phase gate with its phase moved to the site `i`
  let siteDiag : Fin (2 ^ n) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
    fun i => Matrix.diagonal (fun a => if a = i then Complex.exp (Complex.I * (φ i : ℂ)) else 1)
  have hsite : ∀ i : Fin (2 ^ n),
      permMatrix (σ i) * phaseGate n (φ i) * (permMatrix (σ i))ᴴ = siteDiag i := by
    intro i
    have hphase : phaseGate n (φ i) =
        Matrix.diagonal (fun b => if b = z then Complex.exp (Complex.I * (φ i : ℂ)) else 1) := by
      unfold phaseGate
      rw [hz]
    rw [hphase, permMatrix_conj_diagonal]
    congr 1
    funext a
    by_cases ha : a = i
    · have hza : σ i a = z := by rw [ha, Equiv.swap_apply_right]
      rw [hza, ha, ite_eq_left rfl, ite_eq_left rfl]
    · have hne : σ i a ≠ z := by
        intro h
        have h1 : σ i a = σ i i := by rw [h, Equiv.swap_apply_right]
        exact ha (Equiv.injective _ h1)
      rw [ite_eq_right hne, ite_eq_right ha]
  refine ⟨fun i => W * permMatrix (σ i), φ, ?_, ?_⟩
  · intro i
    exact Submonoid.mul_mem _ hW (permMatrix_mem_unitaryGroup (σ i))
  · have hfactor : ∀ i : Fin (2 ^ n),
        (W * permMatrix (σ i)) * phaseGate n (φ i) * (W * permMatrix (σ i))ᴴ =
          W * siteDiag i * Wᴴ := by
      intro i
      rw [Matrix.conjTranspose_mul]
      rw [show W * permMatrix (σ i) * phaseGate n (φ i) * ((permMatrix (σ i))ᴴ * Wᴴ)
          = W * (permMatrix (σ i) * phaseGate n (φ i) * (permMatrix (σ i))ᴴ) * Wᴴ from by
            noncomm_ring,
        hsite i]
    have hstep : (List.ofFn
          (fun i => (W * permMatrix (σ i)) * phaseGate n (φ i) * (W * permMatrix (σ i))ᴴ)) =
        List.ofFn (fun i => W * siteDiag i * Wᴴ) := by
      rw [List.ofFn_inj]
      funext i
      exact hfactor i
    have hprod := prod_ofFn_conj W hWW hW'W (2 ^ n) siteDiag
    have hdiag : (List.ofFn siteDiag).prod =
        Matrix.diagonal (fun a => Complex.exp (Complex.I * (φ a : ℂ))) := by
      have hsiteD : siteDiag = (fun i => Matrix.diagonal
          (fun a => if a = i then Complex.exp (Complex.I * (φ i : ℂ)) else 1)) := rfl
      rw [hsiteD, prod_ofFn_diagonal (2 ^ n)]
      congr 1
      funext a
      rw [Fin.prod_ofFn]
      rw [Finset.prod_eq_single a ?_ ?_]
      · rw [ite_eq_left rfl]
      · intro b _ hb
        rw [ite_eq_right]
        rintro rfl
        exact hb rfl
      · intro h
        exact absurd (Finset.mem_univ a) h
    rw [hU, hstep, hprod, hdiag]

end Qatlib.Papers.QCircApprox95.MainResults
