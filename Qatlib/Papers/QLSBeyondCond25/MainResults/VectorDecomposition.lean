/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse

set_option backward.isDefEq.respectTransparency false

/-! Vector decomposition for
"A New Quantum Linear System Algorithm Beyond the Condition Number and
Its Application to Solving Multivariate Polynomial Systems"
(arXiv:2510.05588, 2025), Section 2.

The paper solves `A x = b` by phase estimation on the augmented matrix
`H = [A, -b]`: the initial state `psi_0 = [0,...,0,1]^T` splits as a
null-space plus a row-space component of `H`, and the null component
encodes the minimum-norm solution `x = A^+ b`.

This block proves the two Section 2 cores over the Moore–Penrose
pseudoinverse `matrixPseudoinverse` of the Concepts layer:

- `exists_unique_decomposition` (**c004**, Lemma 2.6): every vector
  admits a unique decomposition `psi = u + v` with `u` in the null
  space of `H`, `v` in the row space of `H` and `u` orthogonal to `v`.
- `vectorDecomposition` (**c005**, Theorem 2.7, Vector Decomposition
  Theorem): for `x = A^+ b` with `b` in the range of `A`, the special
  vector `psi_0 = [0,...,0,1]^T` equals
  `(1/(1+‖x‖²)) (theta - theta^perp)` with `theta = [x; 1]` in the
  null space of `H` and `theta^perp = [x; -‖x‖²]` in the row space of
  `H`; moreover `x` solves the system, has minimum norm among all
  solutions, and lies in the row space of `A` (there is `p` with
  `A^H p = x`).

Everything is over `ℂ` (the real case of the paper embeds); the
pairing is the conjugate-sesquilinear `sip` and the squared norm is
`sqN`. The augmented matrix is `augMatrix A b : Matrix M (N ⊕ Unit) ℂ`.

Restricted: the phase-estimation/walk layers of Section 3 are outside;
`b` in the range of `A` (consistency) is an explicit hypothesis, which
the paper assumes by taking `x` to be a solution.

No axiom beyond the three standard ones, no `sorry`. -/
set_option autoImplicit false

namespace Qatlib.Papers.QLSBeyondCond25.MainResults

open Matrix Qatlib.Concepts.CoherentSim.CoherentOAA

/-! ## Sesquilinear pairing and squared norm -/

section Helpers

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- Conjugate-sesquilinear pairing `⟨u, v⟩ = ∑ star (u i) * v i`,
linear in the second argument. -/
noncomputable def sip (u v : X → ℂ) : ℂ := ∑ i, star (u i) * v i

/-- The pairing vanishes when the first argument is zero. -/
theorem sip_zero_left (v : X → ℂ) : sip 0 v = 0 := by
  simp [sip]

/-- Hermitian symmetry up to conjugation. -/
theorem sip_conj (u v : X → ℂ) : sip u v = star (sip v u) := by
  simp only [sip, star_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [star_mul, star_star]

/-- Additivity in the first argument. -/
theorem sip_add_left (u v w : X → ℂ) : sip (u + v) w = sip u w + sip v w := by
  rw [sip, sip, sip, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Pi.add_apply, star_add]
  ring

/-- Additivity in the second argument. -/
theorem sip_add_right (u v w : X → ℂ) : sip u (v + w) = sip u v + sip u w := by
  rw [sip, sip, sip, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Pi.add_apply]
  ring

/-- Conjugate transpose moves across the pairing:
`⟨A u, v⟩ = ⟨u, A^H v⟩`. -/
theorem sip_conjTranspose_mulVec (A : Matrix Y Z ℂ) (u : Z → ℂ) (v : Y → ℂ) :
    sip (A *ᵥ u) v = sip u (Aᴴ *ᵥ v) := by
  have hL : sip (A *ᵥ u) v = ∑ i, ∑ j, (star (u j) * star (A i j)) * v i := by
    simp only [sip, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [star_mul]
  have hR : sip u (Aᴴ *ᵥ v) = ∑ i, ∑ j, (star (u j) * star (A i j)) * v i := by
    simp only [sip, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hL, hR]

/-- Squared Euclidean norm of a complex vector. -/
def sqN (v : X → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

/-- Squared norms are nonnegative. -/
theorem sqN_nonneg (v : X → ℂ) : 0 ≤ sqN v :=
  Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

/-- The squared norm is the pairing of a vector with itself. -/
theorem sqN_cast_eq_sip (v : X → ℂ) : ((sqN v : ℝ) : ℂ) = sip v v := by
  simp only [sqN, sip, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply]

/-- A vector of vanishing norm is zero. -/
theorem sqN_eq_zero {v : X → ℂ} (h : sqN v = 0) : v = 0 := by
  have hmem : ∀ i ∈ Finset.univ, Complex.normSq (v i) = 0 :=
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _) |>.mp h
  funext i
  simpa using (Complex.normSq_eq_zero).mp (hmem i (Finset.mem_univ i))

/-- Pythagoras for orthogonal vectors: if `⟨u, v⟩ = 0` then
`‖u + v‖² = ‖u‖² + ‖v‖²`. -/
theorem sqN_add_orth {u v : X → ℂ} (huv : sip u v = 0) :
    sqN (u + v) = sqN u + sqN v := by
  have hvu : sip v u = 0 := (star_eq_zero).mp (by rw [← sip_conj, huv])
  have key : ((sqN (u + v) : ℝ) : ℂ) = ((sqN u + sqN v : ℝ) : ℂ) := by
    rw [Complex.ofReal_add, sqN_cast_eq_sip, sqN_cast_eq_sip, sqN_cast_eq_sip]
    rw [sip_add_left, sip_add_right, sip_add_right, huv, hvu]
    simp
  exact Complex.ofReal_inj.mp key

end Helpers

/-! ## The augmented matrix and its two subspaces -/

section Augmented

variable {M N : Type*} [Fintype M] [Fintype N]

/-- The augmented column `[x; c]` of a vector `x` and a scalar `c`. -/
def vecAppend (x : N → ℂ) (c : ℂ) : N ⊕ Unit → ℂ :=
  Sum.elim x (fun _ => c)

omit [Fintype N] in
/-- Componentwise addition on augmented columns. -/
theorem vecAppend_add (x y : N → ℂ) (c d : ℂ) :
    vecAppend x c + vecAppend y d = vecAppend (x + y) (c + d) := by
  funext j
  cases j <;> simp [vecAppend]

omit [Fintype N] in
/-- Componentwise subtraction on augmented columns. -/
theorem vecAppend_sub (x y : N → ℂ) (c d : ℂ) :
    vecAppend x c - vecAppend y d = vecAppend (x - y) (c - d) := by
  funext j
  cases j <;> simp [vecAppend]

omit [Fintype N] in
/-- Scalar multiplication on augmented columns. -/
theorem vecAppend_smul (r : ℂ) (x : N → ℂ) (c : ℂ) :
    r • vecAppend x c = vecAppend (r • x) (r * c) := by
  funext j
  cases j <;> simp [vecAppend, Pi.smul_apply, smul_eq_mul]

/-- The augmented matrix `H = [A, -b]` of the linear system
`A x = b`, acting on `N ⊕ Unit` columns. -/
def augMatrix (A : Matrix M N ℂ) (b : M → ℂ) : Matrix M (N ⊕ Unit) ℂ :=
  Matrix.of fun i j => Sum.elim (fun k => A i k) (fun _ => -b i) j

omit [Fintype M] in
/-- Action of the augmented matrix on an augmented column:
`[A, -b] [x; c] = A x - c • b`. -/
theorem augMatrix_mulVec (A : Matrix M N ℂ) (b : M → ℂ) (x : N → ℂ) (c : ℂ) :
    augMatrix A b *ᵥ vecAppend x c = A *ᵥ x - c • b := by
  funext i
  simp only [augMatrix, Matrix.of_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, vecAppend,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hU : ∑ _j : Unit, (-b i) * c = -b i * c := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_unit]
    simp
  rw [hU]
  ring

omit [Fintype N] in
/-- Action of the adjoint of the augmented matrix:
`[A, -b]^H p = [A^H p; -⟨b, p⟩]`. -/
theorem augMatrix_conjTranspose_mulVec (A : Matrix M N ℂ) (b : M → ℂ) (p : M → ℂ) :
    (augMatrix A b)ᴴ *ᵥ p = vecAppend (Aᴴ *ᵥ p) (-(sip b p)) := by
  funext j
  rcases j with k | u
  · simp only [augMatrix, Matrix.conjTranspose_apply, Matrix.mulVec,
      dotProduct, vecAppend, Sum.elim_inl, Matrix.of_apply]
  · simp only [augMatrix, Matrix.conjTranspose_apply, Matrix.mulVec,
      dotProduct, vecAppend, Sum.elim_inr, Matrix.of_apply]
    have hstep : ∑ i, star (-(b i)) * p i = -(∑ i, star (b i) * p i) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => by rw [star_neg, neg_mul])
    rw [hstep]
    rfl

/-- The null space of a matrix as a submodule. -/
noncomputable def nullSpaceOf {K : Type*} [Fintype K] (H : Matrix M K ℂ) :
    Submodule ℂ (K → ℂ) :=
  LinearMap.ker H.mulVecLin

/-- The row space of a matrix as a submodule (range of the adjoint). -/
noncomputable def rowSpaceOf {K : Type*} [Fintype K] (H : Matrix M K ℂ) :
    Submodule ℂ (K → ℂ) :=
  LinearMap.range Hᴴ.mulVecLin

omit [Fintype M] in
/-- Null-space membership is vanishing of the action. -/
theorem mem_nullSpaceOf_iff {K : Type*} [Fintype K] {H : Matrix M K ℂ} {v : K → ℂ} :
    v ∈ nullSpaceOf H ↔ H *ᵥ v = 0 := by
  rw [nullSpaceOf, LinearMap.mem_ker, Matrix.mulVecLin_apply]

/-- Row-space membership is being an adjoint image. -/
theorem mem_rowSpaceOf_iff {K : Type*} [Fintype K] {H : Matrix M K ℂ} {v : K → ℂ} :
    v ∈ rowSpaceOf H ↔ ∃ w : M → ℂ, Hᴴ *ᵥ w = v := by
  rw [rowSpaceOf, LinearMap.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    rw [Matrix.mulVecLin_apply] at hw
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, by rw [Matrix.mulVecLin_apply, hw]⟩

/-- Null-space vectors are orthogonal to row-space vectors. -/
theorem ortho_null_row {K : Type*} [Fintype K] {H : Matrix M K ℂ} {u v : K → ℂ}
    (hu : u ∈ nullSpaceOf H) (hv : v ∈ rowSpaceOf H) : sip u v = 0 := by
  obtain ⟨w, hw⟩ := mem_rowSpaceOf_iff.mp hv
  rw [← hw, ← sip_conjTranspose_mulVec, mem_nullSpaceOf_iff.mp hu, sip_zero_left]

/-- The null space and the row space intersect trivially. -/
theorem eq_zero_of_mem_null_and_row {K : Type*} [Fintype K] {H : Matrix M K ℂ} {u : K → ℂ}
    (h1 : u ∈ nullSpaceOf H) (h2 : u ∈ rowSpaceOf H) : u = 0 := by
  have hz : sip u u = 0 := ortho_null_row h1 h2
  have hc : ((sqN u : ℝ) : ℂ) = 0 := by rw [sqN_cast_eq_sip, hz]
  exact sqN_eq_zero (Complex.ofReal_inj.mp hc)

end Augmented

/-! ## c004: the unique null/row decomposition (Lemma 2.6) -/

/-- **c004 (Lemma 2.6)**: every vector `ψ` admits a unique
decomposition `ψ = u + v` with `u` in the null space of `H`, `v` in
the row space of `H` and `u` orthogonal to `v`. Existence is via the
orthogonal projector `H^+ H`; uniqueness via the trivial intersection
of the two subspaces. -/
theorem exists_unique_decomposition {M K : Type*} [Fintype M] [Fintype K] [DecidableEq K]
    (H : Matrix M K ℂ) (ψ : K → ℂ) :
    ∃ u v : K → ℂ, u ∈ nullSpaceOf H ∧ v ∈ rowSpaceOf H ∧ ψ = u + v ∧ sip u v = 0 ∧
      ∀ u' v' : K → ℂ, u' ∈ nullSpaceOf H → v' ∈ rowSpaceOf H → ψ = u' + v' →
        sip u' v' = 0 → u' = u ∧ v' = v := by
  have hproj : matrixPseudoinverse H * H = Hᴴ * (matrixPseudoinverse H)ᴴ := by
    rw [← Matrix.conjTranspose_mul, matrixPseudoinverse_mul_adjoint H]
  have hHit : H *ᵥ ((matrixPseudoinverse H * H) *ᵥ ψ) = H *ᵥ ψ := by
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, mul_matrixPseudoinverse_mul H]
  have hker : ψ - (matrixPseudoinverse H * H) *ᵥ ψ ∈ nullSpaceOf H := by
    rw [mem_nullSpaceOf_iff, Matrix.mulVec_sub, hHit]
    simp
  have hrow : (matrixPseudoinverse H * H) *ᵥ ψ ∈ rowSpaceOf H := by
    rw [mem_rowSpaceOf_iff]
    refine ⟨(matrixPseudoinverse H)ᴴ *ᵥ ψ, ?_⟩
    rw [Matrix.mulVec_mulVec, ← hproj]
  have hsum : ψ - (matrixPseudoinverse H * H) *ᵥ ψ
      + (matrixPseudoinverse H * H) *ᵥ ψ = ψ := by
    rw [sub_add_cancel]
  refine ⟨ψ - (matrixPseudoinverse H * H) *ᵥ ψ, (matrixPseudoinverse H * H) *ᵥ ψ,
    hker, hrow, hsum.symm, ortho_null_row hker hrow, ?_⟩
  intro u' v' hu1 hv1 hψ _
  have h1 : u' + v' = ψ - (matrixPseudoinverse H * H) *ᵥ ψ
      + (matrixPseudoinverse H * H) *ᵥ ψ := by
    rw [hsum]; exact hψ.symm
  have hd : u' - (ψ - (matrixPseudoinverse H * H) *ᵥ ψ)
      = (matrixPseudoinverse H * H) *ᵥ ψ - v' := by
    have h2 : (u' - (ψ - (matrixPseudoinverse H * H) *ᵥ ψ))
        + ((ψ - (matrixPseudoinverse H * H) *ᵥ ψ) + v')
        = ((matrixPseudoinverse H * H) *ᵥ ψ - v')
          + ((ψ - (matrixPseudoinverse H * H) *ᵥ ψ) + v') := by
      calc (u' - (ψ - (matrixPseudoinverse H * H) *ᵥ ψ))
          + ((ψ - (matrixPseudoinverse H * H) *ᵥ ψ) + v')
          = u' + v' := by abel
        _ = ψ - (matrixPseudoinverse H * H) *ᵥ ψ
            + (matrixPseudoinverse H * H) *ᵥ ψ := h1
        _ = ((matrixPseudoinverse H * H) *ᵥ ψ - v')
            + ((ψ - (matrixPseudoinverse H * H) *ᵥ ψ) + v') := by abel
    exact add_right_cancel h2
  have hdu : u' - (ψ - (matrixPseudoinverse H * H) *ᵥ ψ) ∈ nullSpaceOf H := by
    rw [mem_nullSpaceOf_iff, Matrix.mulVec_sub,
      mem_nullSpaceOf_iff.mp hu1, mem_nullSpaceOf_iff.mp hker]
    simp
  have hdv : u' - (ψ - (matrixPseudoinverse H * H) *ᵥ ψ) ∈ rowSpaceOf H := by
    rw [hd]
    exact Submodule.sub_mem _ hrow hv1
  have hzero : u' - (ψ - (matrixPseudoinverse H * H) *ᵥ ψ) = 0 :=
    eq_zero_of_mem_null_and_row hdu hdv
  constructor
  · linear_combination hzero
  · have hzz : (matrixPseudoinverse H * H) *ᵥ ψ - v' = 0 := by rw [← hd, hzero]
    exact (sub_eq_zero.mp hzz).symm

/-! ## c005: the Vector Decomposition Theorem (Theorem 2.7) -/

section Main

variable {M N : Type*} [Fintype M] [Fintype N] [DecidableEq N]

/-- The pseudoinverse solution of a consistent system, vector form. -/
theorem pseudoinverse_solves_vec (A : Matrix M N ℂ) {b : M → ℂ}
    (hb : ∃ y : N → ℂ, A *ᵥ y = b) :
    A *ᵥ (matrixPseudoinverse A *ᵥ b) = b := by
  obtain ⟨y, hy⟩ := hb
  have h1 : (A * matrixPseudoinverse A) *ᵥ b = b := by
    calc (A * matrixPseudoinverse A) *ᵥ b
        = (A * matrixPseudoinverse A) *ᵥ (A *ᵥ y) := by rw [hy]
      _ = ((A * matrixPseudoinverse A) * A) *ᵥ y := Matrix.mulVec_mulVec y _ _
      _ = A *ᵥ y := by rw [mul_matrixPseudoinverse_mul A]
      _ = b := hy
  calc A *ᵥ (matrixPseudoinverse A *ᵥ b)
      = (A * matrixPseudoinverse A) *ᵥ b := Matrix.mulVec_mulVec b A (matrixPseudoinverse A)
    _ = b := h1

/-- The pseudoinverse solution lies in the row space of `A`. -/
theorem pseudoinverse_mem_rowSpace (A : Matrix M N ℂ) (b : M → ℂ) :
    ∃ p : M → ℂ, Aᴴ *ᵥ p = matrixPseudoinverse A *ᵥ b := by
  refine ⟨(matrixPseudoinverse A)ᴴ *ᵥ (matrixPseudoinverse A *ᵥ b), ?_⟩
  have hproj : matrixPseudoinverse A * A = Aᴴ * (matrixPseudoinverse A)ᴴ := by
    rw [← Matrix.conjTranspose_mul, matrixPseudoinverse_mul_adjoint A]
  calc Aᴴ *ᵥ ((matrixPseudoinverse A)ᴴ *ᵥ (matrixPseudoinverse A *ᵥ b))
      = (Aᴴ * (matrixPseudoinverse A)ᴴ) *ᵥ (matrixPseudoinverse A *ᵥ b) :=
        Matrix.mulVec_mulVec _ _ _
    _ = (matrixPseudoinverse A * A) *ᵥ (matrixPseudoinverse A *ᵥ b) := by rw [← hproj]
    _ = ((matrixPseudoinverse A * A) * matrixPseudoinverse A) *ᵥ b :=
        Matrix.mulVec_mulVec _ _ _
    _ = matrixPseudoinverse A *ᵥ b := by rw [matrixPseudoinverse_mul_self A]

/-- Minimum norm: the pseudoinverse solution minimizes the norm among
all solutions of a consistent system. -/
theorem pseudoinverse_minNorm (A : Matrix M N ℂ) {b : M → ℂ}
    (hb : ∃ y : N → ℂ, A *ᵥ y = b) (y : N → ℂ) (hy : A *ᵥ y = b) :
    Real.sqrt (sqN (matrixPseudoinverse A *ᵥ b)) ≤ Real.sqrt (sqN y) := by
  have hx : A *ᵥ (matrixPseudoinverse A *ᵥ b) = b := pseudoinverse_solves_vec A hb
  obtain ⟨p, hp⟩ := pseudoinverse_mem_rowSpace A b
  have hrow : matrixPseudoinverse A *ᵥ b ∈ rowSpaceOf A :=
    mem_rowSpaceOf_iff.mpr ⟨p, hp⟩
  have hker : y - matrixPseudoinverse A *ᵥ b ∈ nullSpaceOf A := by
    rw [mem_nullSpaceOf_iff, Matrix.mulVec_sub, hy, hx]
    simp
  have horth0 : sip (y - matrixPseudoinverse A *ᵥ b) (matrixPseudoinverse A *ᵥ b) = 0 :=
    ortho_null_row hker hrow
  have horth : sip (matrixPseudoinverse A *ᵥ b) (y - matrixPseudoinverse A *ᵥ b) = 0 := by
    refine (star_eq_zero).mp ?_
    rw [← sip_conj, horth0]
  have hpy : sqN y
      = sqN (matrixPseudoinverse A *ᵥ b + (y - matrixPseudoinverse A *ᵥ b)) := by
    rw [add_sub_cancel]
  rw [hpy, sqN_add_orth horth]
  refine Real.sqrt_le_sqrt ?_
  linarith [sqN_nonneg (y - matrixPseudoinverse A *ᵥ b)]

/-- **c005 (Theorem 2.7, Vector Decomposition Theorem)**: with
`x = A^+ b` the minimum-norm solution of the consistent system
`A x = b`, the special vector `psi_0 = [0,...,0,1]^T` decomposes as
`psi_0 = (1/(1+‖x‖²)) (theta - theta^perp)` with
`theta = [x; 1]` in the null space of `H = [A, -b]` and
`theta^perp = [x; -‖x‖²]` in the row space of `H`. Moreover `x`
solves the system with minimum norm, and there is `p` with
`A^H p = x = A^+ b`. -/
theorem vectorDecomposition (A : Matrix M N ℂ) (b : M → ℂ)
    (hb : ∃ y : N → ℂ, A *ᵥ y = b) :
    vecAppend (matrixPseudoinverse A *ᵥ b) 1 ∈ nullSpaceOf (augMatrix A b)
    ∧ vecAppend (matrixPseudoinverse A *ᵥ b)
        (-((sqN (matrixPseudoinverse A *ᵥ b) : ℝ) : ℂ)) ∈ rowSpaceOf (augMatrix A b)
    ∧ vecAppend 0 1 =
        (((1 : ℝ) + sqN (matrixPseudoinverse A *ᵥ b)) : ℂ)⁻¹ •
          (vecAppend (matrixPseudoinverse A *ᵥ b) 1 -
            vecAppend (matrixPseudoinverse A *ᵥ b)
              (-((sqN (matrixPseudoinverse A *ᵥ b) : ℝ) : ℂ)))
    ∧ A *ᵥ (matrixPseudoinverse A *ᵥ b) = b
    ∧ (∀ y : N → ℂ, A *ᵥ y = b →
        Real.sqrt (sqN (matrixPseudoinverse A *ᵥ b)) ≤ Real.sqrt (sqN y))
    ∧ ∃ p : M → ℂ, Aᴴ *ᵥ p = matrixPseudoinverse A *ᵥ b := by
  have hx : A *ᵥ (matrixPseudoinverse A *ᵥ b) = b := pseudoinverse_solves_vec A hb
  obtain ⟨p₀, hp₀⟩ := pseudoinverse_mem_rowSpace A b
  have htheta : vecAppend (matrixPseudoinverse A *ᵥ b) 1 ∈ nullSpaceOf (augMatrix A b) := by
    rw [mem_nullSpaceOf_iff, augMatrix_mulVec, hx, one_smul, sub_self]
  have hsipb : sip b p₀ = ((sqN (matrixPseudoinverse A *ᵥ b) : ℝ) : ℂ) := by
    have hb' : sip (A *ᵥ (matrixPseudoinverse A *ᵥ b)) p₀ = sip b p₀ := by rw [hx]
    rw [← hb', sip_conjTranspose_mulVec, hp₀, sqN_cast_eq_sip]
  have hperp : vecAppend (matrixPseudoinverse A *ᵥ b)
      (-((sqN (matrixPseudoinverse A *ᵥ b) : ℝ) : ℂ)) ∈ rowSpaceOf (augMatrix A b) := by
    rw [mem_rowSpaceOf_iff]
    refine ⟨p₀, ?_⟩
    rw [augMatrix_conjTranspose_mulVec, hsipb, hp₀]
  have hpsi : vecAppend 0 1 =
      (((1 : ℝ) + sqN (matrixPseudoinverse A *ᵥ b)) : ℂ)⁻¹ •
        (vecAppend (matrixPseudoinverse A *ᵥ b) 1 -
          vecAppend (matrixPseudoinverse A *ᵥ b)
            (-((sqN (matrixPseudoinverse A *ᵥ b) : ℝ) : ℂ))) := by
    have hpos : (0 : ℝ) < 1 + sqN (matrixPseudoinverse A *ᵥ b) := by
      have := sqN_nonneg (matrixPseudoinverse A *ᵥ b)
      linarith
    have hne : (((1 : ℝ) + sqN (matrixPseudoinverse A *ᵥ b)) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hpos)
    rw [vecAppend_sub, vecAppend_smul, sub_self, smul_zero]
    have h1 : (1 : ℂ) - (-((sqN (matrixPseudoinverse A *ᵥ b) : ℝ) : ℂ))
        = (((1 : ℝ) + sqN (matrixPseudoinverse A *ᵥ b)) : ℂ) := by
      rw [sub_neg_eq_add]
      push_cast
      ring
    rw [h1, inv_mul_cancel₀ hne]
  exact ⟨htheta, hperp, hpsi, hx,
    fun y hy => pseudoinverse_minNorm A hb y hy, ⟨p₀, hp₀⟩⟩

end Main

end Qatlib.Papers.QLSBeyondCond25.MainResults
