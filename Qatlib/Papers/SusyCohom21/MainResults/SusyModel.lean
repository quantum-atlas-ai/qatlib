/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# SusyCohom21 — finite-dimensional model of the N = 2 supersymmetry algebra
and the cohomology (Hodge) Laplacian

Cade--Crichigno, *Complexity of Supersymmetric Systems and the Cohomology
Problem*, fixed arXiv:2107.00011v2 (accepted Quantum 2023-05-11).

This file provides the concrete matrix model used by the paper-layer statements:
complex states on a finite index type, the supercharge `Q` with `Q² = 0` and
`H = {Q,Q†} = QQ† + Q†Q` (Eq. (3.1)), the coboundary Laplacian
`Δ = dd† + d†d`, graded complexes, the site penalty of Eq. (3.12), and the
spectral mapping `H = B²` used in Theorems 5 and 6.

Boundary: all results are finite-dimensional linear algebra over `ℂ`.  The
complexity-class statements of the paper (QMA, DQC1, #P, ...) are not formalised
here; the claim files state their concrete mathematical content, as in the
`Papers/LocalHam06` precedent.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.SusyCohom21.MainResults.SusyModel

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Complex vector indexed by a finite type. -/
abbrev State (ι : Type) := ι → ℂ

/-- Squared Euclidean norm of a state, written as the real part of `⟨ψ|ψ⟩`. -/
def normSqVec (ψ : State ι) : ℝ := (star ψ ⬝ᵥ ψ).re

/-- A normalized state. -/
def Normalized (ψ : State ι) : Prop := normSqVec ψ = 1

/-- Energy `⟨ψ|H|ψ⟩` of a Hermitian matrix `H` in state `ψ`. -/
def energy (H : Matrix ι ι ℂ) (ψ : State ι) : ℝ := (star ψ ⬝ᵥ (H *ᵥ ψ)).re

/-- The inner product is conjugate-symmetric: `⟨y, x⟩ = conj ⟨x, y⟩`. -/
lemma star_dotProduct_swap (x y : State ι) :
    star y ⬝ᵥ x = star (star x ⬝ᵥ y) := by
  simpa using star_dotProduct (v := y) (w := x)

/-- The squared norm is nonnegative. -/
lemma normSqVec_nonneg (ψ : State ι) : 0 ≤ normSqVec ψ :=
  (RCLike.nonneg_iff.mp (dotProduct_star_self_nonneg ψ)).1

/-- The squared norm vanishes exactly on the zero state. -/
lemma normSqVec_eq_zero_iff (ψ : State ι) : normSqVec ψ = 0 ↔ ψ = 0 := by
  constructor
  · intro h
    have hself : star (star ψ ⬝ᵥ ψ) = star ψ ⬝ᵥ ψ :=
      (star_dotProduct (v := ψ) (w := ψ)).symm
    have him : (star ψ ⬝ᵥ ψ).im = 0 := Complex.conj_eq_iff_im.mp hself
    have hz : star ψ ⬝ᵥ ψ = 0 := by
      apply Complex.ext
      · simpa [normSqVec, Complex.zero_re] using h
      · simpa [Complex.zero_im] using him
    exact dotProduct_star_self_eq_zero.mp hz
  · intro h
    subst h
    simp [normSqVec]

/-- Pythagoras: if `x` and `y` are orthogonal, the squared norm of `x + y` is
the sum of the squared norms. -/
lemma normSqVec_add_of_dotProduct_zero {x y : State ι}
    (h : star x ⬝ᵥ y = 0) : normSqVec (x + y) = normSqVec x + normSqVec y := by
  have hswap : star y ⬝ᵥ x = 0 := by
    rw [star_dotProduct_swap, h, star_zero]
  unfold normSqVec
  rw [star_add, add_dotProduct, dotProduct_add, dotProduct_add, h, hswap, add_zero, zero_add,
    Complex.add_re]

/-- The Laplacian `Δ = dd† + d†d` of a coboundary operator `d`. -/
def laplacian (d : Matrix ι ι ℂ) : Matrix ι ι ℂ := d * dᴴ + dᴴ * d

/-- The quadratic form of `A†A` is the squared norm of `Aψ`. -/
lemma qform_conjTranspose_mul_self (A : Matrix ι ι ℂ) (ψ : State ι) :
    star ψ ⬝ᵥ ((Aᴴ * A) *ᵥ ψ) = star (A *ᵥ ψ) ⬝ᵥ (A *ᵥ ψ) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]

/-- The quadratic form of `AA†` is the squared norm of `A†ψ`. -/
lemma qform_mul_conjTranspose_self (A : Matrix ι ι ℂ) (ψ : State ι) :
    star ψ ⬝ᵥ ((A * Aᴴ) *ᵥ ψ) = star (Aᴴ *ᵥ ψ) ⬝ᵥ (Aᴴ *ᵥ ψ) := by
  simpa using qform_conjTranspose_mul_self Aᴴ ψ

/-- The Laplacian `dd† + d†d` is positive semidefinite. -/
lemma laplacian_posSemidef (d : Matrix ι ι ℂ) : (laplacian d).PosSemidef := by
  unfold laplacian
  exact (Matrix.posSemidef_self_mul_conjTranspose d).add
    (Matrix.posSemidef_conjTranspose_mul_self d)

/-- The Laplacian kills `ψ` exactly when both `d` and `d†` kill `ψ` (Hodge
kernel characterisation). -/
lemma laplacian_mulVec_eq_zero_iff (d : Matrix ι ι ℂ) (ψ : State ι) :
    laplacian d *ᵥ ψ = 0 ↔ d *ᵥ ψ = 0 ∧ dᴴ *ᵥ ψ = 0 := by
  constructor
  · intro h
    have hq : star ψ ⬝ᵥ (laplacian d *ᵥ ψ) = 0 := by rw [h, dotProduct_zero]
    have hexp : star ψ ⬝ᵥ (laplacian d *ᵥ ψ)
        = star (d *ᵥ ψ) ⬝ᵥ (d *ᵥ ψ) + star (dᴴ *ᵥ ψ) ⬝ᵥ (dᴴ *ᵥ ψ) := by
      rw [laplacian, Matrix.add_mulVec, dotProduct_add, qform_mul_conjTranspose_self,
        qform_conjTranspose_mul_self, add_comm]
    rw [hexp] at hq
    have hre : normSqVec (d *ᵥ ψ) + normSqVec (dᴴ *ᵥ ψ) = 0 := by
      have := congrArg Complex.re hq
      simpa [normSqVec, Complex.zero_re] using this
    have h1 : 0 ≤ normSqVec (d *ᵥ ψ) := normSqVec_nonneg _
    have h2 : 0 ≤ normSqVec (dᴴ *ᵥ ψ) := normSqVec_nonneg _
    have hd : normSqVec (d *ᵥ ψ) = 0 := by linarith
    have hdd : normSqVec (dᴴ *ᵥ ψ) = 0 := by linarith
    exact ⟨normSqVec_eq_zero_iff _ |>.mp hd, normSqVec_eq_zero_iff _ |>.mp hdd⟩
  · rintro ⟨h1, h2⟩
    rw [laplacian, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      h1, h2, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]

/-! ### The N = 2 supersymmetry algebra -/

/-- A nilpotent supercharge `Q` with `Q² = 0`. -/
structure Supercharge (ι : Type) [Fintype ι] where
  Q : Matrix ι ι ℂ
  sq_zero : Q * Q = 0

namespace Supercharge

variable (S : Supercharge ι)

/-- The supersymmetric Hamiltonian `H = {Q, Q†} = QQ† + Q†Q`. -/
def hamiltonian : Matrix ι ι ℂ := S.Q * S.Qᴴ + S.Qᴴ * S.Q

/-- The Hermitian operator `Q + Q†`. -/
def shift : Matrix ι ι ℂ := S.Q + S.Qᴴ

/-- The adjoint of a nilpotent matrix is nilpotent. -/
lemma adjoint_sq_zero : S.Qᴴ * S.Qᴴ = 0 := by
  rw [← Matrix.conjTranspose_mul, S.sq_zero, Matrix.conjTranspose_zero]

/-- `Q + Q†` is Hermitian. -/
lemma shift_isHermitian : S.shift.IsHermitian := by
  show S.shiftᴴ = S.shift
  unfold shift
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]

/-- `H = {Q,Q†}` equals `(Q + Q†)²` when `Q² = 0`. -/
lemma hamiltonian_eq_shift_sq : S.hamiltonian = S.shift * S.shift := by
  unfold hamiltonian shift
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, S.sq_zero, S.adjoint_sq_zero,
    zero_add, add_zero]

/-- The SUSY Hamiltonian is Hermitian. -/
lemma hamiltonian_isHermitian : S.hamiltonian.IsHermitian := by
  rw [S.hamiltonian_eq_shift_sq]
  show (S.shift * S.shift)ᴴ = S.shift * S.shift
  rw [Matrix.conjTranspose_mul, S.shift_isHermitian.eq]

/-- The SUSY Hamiltonian is positive semidefinite. -/
lemma hamiltonian_posSemidef : S.hamiltonian.PosSemidef := by
  rw [S.hamiltonian_eq_shift_sq]
  have hp := Matrix.posSemidef_conjTranspose_mul_self S.shift
  rwa [S.shift_isHermitian.eq] at hp

/-- The quadratic form of `H` is the squared norm of `(Q + Q†)ψ`. -/
lemma qform_hamiltonian (ψ : State ι) :
    star ψ ⬝ᵥ (S.hamiltonian *ᵥ ψ) = star (S.shift *ᵥ ψ) ⬝ᵥ (S.shift *ᵥ ψ) := by
  rw [S.hamiltonian_eq_shift_sq, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← S.shift_isHermitian.eq, Matrix.vecMul_conjTranspose, star_star,
    S.shift_isHermitian.eq]

/-- The energy of `H` is `‖(Q + Q†)ψ‖²`. -/
lemma energy_hamiltonian_eq_normSq (ψ : State ι) :
    (star ψ ⬝ᵥ (S.hamiltonian *ᵥ ψ)).re = normSqVec (S.shift *ᵥ ψ) := by
  rw [S.qform_hamiltonian]
  rfl

/-- The kernel of `H` is the kernel of `Q + Q†`. -/
lemma hamiltonian_mulVec_eq_zero_iff (ψ : State ι) :
    S.hamiltonian *ᵥ ψ = 0 ↔ S.shift *ᵥ ψ = 0 := by
  constructor
  · intro h
    have h' : (star ψ ⬝ᵥ (S.hamiltonian *ᵥ ψ)).re = 0 := by rw [h, dotProduct_zero]; simp
    rw [S.energy_hamiltonian_eq_normSq] at h'
    exact normSqVec_eq_zero_iff _ |>.mp h'
  · intro h
    rw [S.hamiltonian_eq_shift_sq, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

/-- The eigenvectors of `Q + Q†` are eigenvectors of `H = (Q + Q†)²` with the
squared eigenvalues. -/
lemma shift_sq_eigen (i : ι) :
    (S.shift * S.shift) *ᵥ ⇑(S.shift_isHermitian.eigenvectorBasis i)
      = ((S.shift_isHermitian.eigenvalues i) *
          (S.shift_isHermitian.eigenvalues i) : ℝ) •
          ⇑(S.shift_isHermitian.eigenvectorBasis i) := by
  have h := S.shift_isHermitian.mulVec_eigenvectorBasis i
  rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, h, smul_smul]

end Supercharge

/-! ### Spectral mapping for `H = B²` -/

/-- The square of a Hermitian matrix is Hermitian. -/
lemma mul_self_isHermitian {B : Matrix ι ι ℂ} (hB : B.IsHermitian) : (B * B).IsHermitian := by
  show (B * B)ᴴ = B * B
  rw [Matrix.conjTranspose_mul, hB.eq]

/-- The characteristic polynomial of `B²` for Hermitian `B` is the product of
`X - μᵢ²` over the eigenvalues `μᵢ` of `B`.  Hence the eigenvalues of `B²` are
exactly the squares of the eigenvalues of `B` (with multiplicity). -/
lemma charpoly_mul_self_of_isHermitian (B : Matrix ι ι ℂ) (hB : B.IsHermitian) :
    (B * B).charpoly
      = ∏ i, (Polynomial.X - Polynomial.C
          ((hB.eigenvalues i : ℂ) * (hB.eigenvalues i : ℂ))) := by
  let u : Matrix ι ι ℂ := (hB.eigenvectorUnitary : Matrix ι ι ℂ)
  let D : Matrix ι ι ℂ := Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues)
  have hspec : B = u * D * star u := by
    simpa only [u, D, Unitary.conjStarAlgAut_apply] using hB.spectral_theorem
  have hU : star u * u = 1 := Unitary.coe_star_mul_self hB.eigenvectorUnitary
  have hsq : (u * D * star u) * (u * D * star u) = u * (D * D) * star u := by
    calc (u * D * star u) * (u * D * star u)
        = u * D * (star u * u) * D * star u := by noncomm_ring
      _ = u * D * 1 * D * star u := by rw [hU]
      _ = u * (D * D) * star u := by noncomm_ring
  have hcyc : (u * (D * D) * star u).charpoly = (D * D).charpoly := by
    rw [Matrix.charpoly_mul_comm (u * (D * D)) (star u), ← mul_assoc, hU, one_mul]
  have hDD : D * D = Matrix.diagonal
      (fun i => (hB.eigenvalues i : ℂ) * (hB.eigenvalues i : ℂ)) := by
    simp only [D]
    rw [Matrix.diagonal_mul_diagonal]
    rfl
  have hbb : B * B = u * (D * D) * star u := by
    conv_lhs => rw [hspec]
    exact hsq
  rw [hbb, hcyc, hDD, Matrix.charpoly_diagonal]

/-! ### Penalty term of the SUSY hardness reduction -/

/-- The site penalty `n_a n_b + (n_a - 1)(n_b - 1)` of Eq. (3.12) evaluated on
occupation numbers `n_a, n_b ∈ {0,1}`. -/
def occPenalty (na nb : Bool) : ℤ :=
  (if na then 1 else 0) * (if nb then 1 else 0)
    + ((if na then 1 else 0) - 1) * ((if nb then 1 else 0) - 1)

/-- Eq. (3.15): the penalty vanishes exactly when the two modes at a site are
occupied in different amounts, i.e. exactly one fermion sits at the site. -/
lemma occPenalty_eq_zero_iff (na nb : Bool) : occPenalty na nb = 0 ↔ na ≠ nb := by
  cases na <;> cases nb <;> simp [occPenalty]

/-- The penalty equals one exactly when the two occupation numbers agree. -/
lemma occPenalty_eq_one_iff (na nb : Bool) : occPenalty na nb = 1 ↔ na = nb := by
  cases na <;> cases nb <;> simp [occPenalty]

/-- The site penalty is nonnegative. -/
lemma occPenalty_nonneg (na nb : Bool) : 0 ≤ occPenalty na nb := by
  cases na <;> cases nb <;> simp [occPenalty]

/-- Equation (3.16): the promise gap transforms as `b' - a' = (b-a)(b+a)` with
`a' = a²`, `b' = b²`. -/
lemma gap_square (a b : ℝ) : b ^ 2 - a ^ 2 = (b - a) * (b + a) := by ring

/-- For `0 ≤ a ≤ b` the squared-gap is at least the square of the original gap. -/
lemma gap_square_ge (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (b - a) ^ 2 ≤ b ^ 2 - a ^ 2 := by
  have h : b ^ 2 - a ^ 2 = (b - a) * (b + a) := gap_square a b
  have h1 : 0 ≤ b - a := sub_nonneg.mpr hab
  have h2 : b - a ≤ b + a := by linarith
  rw [h]
  calc (b - a) ^ 2 = (b - a) * (b - a) := by ring
    _ ≤ (b - a) * (b + a) := by exact mul_le_mul_of_nonneg_left h2 h1

/-- Eq. (3.16) in strict form: a strict inverse-polynomial gap survives squaring. -/
lemma gap_square_gt (a b c : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 < c)
    (hgap : c < b - a) : c ^ 2 < b ^ 2 - a ^ 2 := by
  have h1 : 0 < b - a := lt_trans hc hgap
  have h2 : c < b + a := by linarith
  have h3 : c ^ 2 < (b - a) * (b + a) := by
    calc c ^ 2 < c * (b - a) := by nlinarith
      _ < (b - a) * (b + a) := by nlinarith
  rwa [gap_square]

/-- An inverse-polynomial promise gap `1/q` with `q ≥ 1` stays inverse
polynomial after squaring: it becomes `1/q²`. -/
lemma inverse_polynomial_gap_sq (a b q : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hq : 1 ≤ q) (hgap : 1 / q ≤ b - a) : 1 / q ^ 2 ≤ b ^ 2 - a ^ 2 := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have h1 : 0 ≤ b - a := le_trans (by positivity) hgap
  have h2 : 1 / q ≤ b + a := by
    have : b - a ≤ b + a := by linarith
    exact le_trans hgap this
  rw [gap_square]
  calc 1 / q ^ 2 = (1 / q) * (1 / q) := by field_simp
    _ ≤ (b - a) * (b + a) := by
      exact mul_le_mul hgap h2 (by positivity) h1

/-! ### Graded cochain complexes and the Hodge decomposition -/

/-- A finite graded cochain complex: `d` raises the grade by one and squares to zero. -/
structure GradedComplex (ι : Type) [Fintype ι] where
  grade : ι → ℕ
  d : Matrix ι ι ℂ
  sq_zero : d * d = 0
  raises : ∀ i j, d i j ≠ 0 → grade i = grade j + 1

namespace GradedComplex

variable (C : GradedComplex ι)

/-- Vectors supported in a single grade. -/
def SupportedIn (l : ℕ) (ψ : State ι) : Prop := ∀ i, C.grade i ≠ l → ψ i = 0

/-- The adjoint `d†` lowers the grade by one. -/
lemma dagger_lowers (i j : ι) (h : C.dᴴ i j ≠ 0) : C.grade i + 1 = C.grade j := by
  have h' : C.d j i ≠ 0 := by
    intro h0
    exact h (by simp [Matrix.conjTranspose_apply, h0])
  have := C.raises j i h'
  omega

/-- `d` raises the grade of the support by one. -/
lemma mulVec_supported_succ {l : ℕ} {ψ : State ι} (hψ : C.SupportedIn l ψ) :
    C.SupportedIn (l + 1) (C.d *ᵥ ψ) := by
  intro a ha
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hdj : C.d a j = 0
  · simp [hdj]
  · have hnj : C.grade j ≠ l := by
      have hr := C.raises a j hdj
      omega
    simp [hψ j hnj]

/-- `d†` lowers the grade of the support by one. -/
lemma mulVec_dagger_supported_pred {l : ℕ} {ψ : State ι} (hψ : C.SupportedIn l ψ) :
    C.SupportedIn (l - 1) (C.dᴴ *ᵥ ψ) := by
  intro a ha
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hpsij : ψ j = 0
  · simp [hpsij]
  · have hgj : C.grade j = l := by
      by_contra hne
      exact hpsij (hψ j hne)
    by_cases hdja : C.d j a = 0
    · simp [Matrix.conjTranspose_apply, hdja]
    · exfalso
      have hg : C.grade j = C.grade a + 1 := C.raises j a hdja
      apply ha
      omega

/-- Orthogonality of `dψ` and `d†ψ` for `ψ` supported in a single grade. -/
lemma cross_term_zero {l : ℕ} {ψ : State ι} (hψ : C.SupportedIn l ψ) :
    star (C.d *ᵥ ψ) ⬝ᵥ (C.dᴴ *ᵥ ψ) = 0 := by
  rw [dotProduct]
  apply Finset.sum_eq_zero
  intro a _
  have hd_supp := C.mulVec_supported_succ hψ
  have hdd_supp := C.mulVec_dagger_supported_pred hψ
  by_cases h1 : (C.d *ᵥ ψ) a = 0
  · simp [h1]
  · have h2 : (C.dᴴ *ᵥ ψ) a = 0 := by
      by_contra hne
      have hg1 : C.grade a = l + 1 := by
        by_contra hne1
        exact h1 (hd_supp a hne1)
      have hg2 : C.grade a = l - 1 := by
        by_contra hne2
        exact hne (hdd_supp a hne2)
      omega
    simp [h2]

/-- For a state supported in grade `l`, the Laplacian energy equals the norm
squared of `(d + d†)ψ`; the two cross terms vanish by graded orthogonality. -/
lemma laplacian_energy_eq_shift_normSq {l : ℕ} {ψ : State ι} (hψ : C.SupportedIn l ψ) :
    (star ψ ⬝ᵥ (laplacian C.d *ᵥ ψ)).re = normSqVec ((C.d + C.dᴴ) *ᵥ ψ) := by
  have hlap : star ψ ⬝ᵥ (laplacian C.d *ᵥ ψ)
      = star (C.d *ᵥ ψ) ⬝ᵥ (C.d *ᵥ ψ) + star (C.dᴴ *ᵥ ψ) ⬝ᵥ (C.dᴴ *ᵥ ψ) := by
    rw [laplacian, Matrix.add_mulVec, dotProduct_add, qform_mul_conjTranspose_self,
      qform_conjTranspose_mul_self]
    exact add_comm _ _
  have hshift : (C.d + C.dᴴ) *ᵥ ψ = C.d *ᵥ ψ + C.dᴴ *ᵥ ψ := Matrix.add_mulVec _ _ _
  rw [hlap, hshift, normSqVec_add_of_dotProduct_zero (C.cross_term_zero hψ)]
  rfl

/-- A state supported in a single grade has Laplacian energy zero iff it is
simultaneously closed and co-closed (Eq. (4.15) restricted to that grade). -/
lemma laplacian_energy_zero_iff {l : ℕ} {ψ : State ι} (hψ : C.SupportedIn l ψ) :
    (star ψ ⬝ᵥ (laplacian C.d *ᵥ ψ)).re = 0 ↔ C.d *ᵥ ψ = 0 ∧ C.dᴴ *ᵥ ψ = 0 := by
  rw [C.laplacian_energy_eq_shift_normSq hψ, normSqVec_eq_zero_iff]
  constructor
  · intro h
    -- (d + d†)ψ = 0 with graded orthogonality gives each piece zero
    have hzero : C.d *ᵥ ψ + C.dᴴ *ᵥ ψ = 0 := by
      rwa [Matrix.add_mulVec] at h
    have hcross := C.cross_term_zero hψ
    have hsplit := normSqVec_add_of_dotProduct_zero hcross
    have hnorm : normSqVec (C.d *ᵥ ψ) + normSqVec (C.dᴴ *ᵥ ψ) = 0 := by
      rw [← hsplit, hzero]; simp [normSqVec]
    have h1 : normSqVec (C.d *ᵥ ψ) = 0 := by
      have h0 := normSqVec_nonneg (C.d *ᵥ ψ)
      have h0' := normSqVec_nonneg (C.dᴴ *ᵥ ψ)
      linarith
    have h2 : normSqVec (C.dᴴ *ᵥ ψ) = 0 := by
      have h0 := normSqVec_nonneg (C.d *ᵥ ψ)
      have h0' := normSqVec_nonneg (C.dᴴ *ᵥ ψ)
      linarith
    exact ⟨normSqVec_eq_zero_iff _ |>.mp h1, normSqVec_eq_zero_iff _ |>.mp h2⟩
  · rintro ⟨h1, h2⟩
    rw [Matrix.add_mulVec, h1, h2, add_zero]

end GradedComplex

/-! ### Kernel dimension of Hermitian squares -/

/-- Dimension of the kernel of a matrix acting on `ι → ℂ`. -/
def kernelDim (M : Matrix ι ι ℂ) : ℕ := Module.finrank ℂ (LinearMap.ker M.mulVecLin)

/-- For Hermitian `B`, `ker (B²) = ker B`; this is the spectral fact behind
`β_{n+2} = #zero eigenvalues` of Theorem 5. -/
lemma kernelDim_mul_self_of_isHermitian (B : Matrix ι ι ℂ) (hB : B.IsHermitian) :
    kernelDim (B * B) = kernelDim B := by
  have h1 : ∀ v : State ι, (B * B) *ᵥ v = 0 ↔ B *ᵥ v = 0 := by
    intro v
    simpa [hB.eq] using Matrix.self_mul_conjTranspose_mulVec_eq_zero B v
  have hk : LinearMap.ker ((B * B).mulVecLin) = LinearMap.ker B.mulVecLin := by
    apply Submodule.ext
    intro v
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact h1 v
  unfold kernelDim
  rw [hk]


/-! ### Laplacian as a square, Betti numbers, and the Hodge kernel -/

/-- If `d² = 0` then `(d†)² = 0`. -/
lemma conjTranspose_sq_zero {d : Matrix ι ι ℂ} (h : d * d = 0) : dᴴ * dᴴ = 0 := by
  rw [← Matrix.conjTranspose_mul, h, Matrix.conjTranspose_zero]

/-- `d + d†` is Hermitian. -/
lemma add_conjTranspose_isHermitian (d : Matrix ι ι ℂ) : (d + dᴴ).IsHermitian := by
  show (d + dᴴ)ᴴ = d + dᴴ
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]

/-- Eq. (5.6): for a coboundary `d` with `d² = 0`, the Laplacian is the square
`Δ = (d + d†)²`. -/
lemma laplacian_eq_shift_sq {d : Matrix ι ι ℂ} (h : d * d = 0) :
    laplacian d = (d + dᴴ) * (d + dᴴ) := by
  have h' := conjTranspose_sq_zero h
  unfold laplacian
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h, h', zero_add, add_zero]

/-- The `l`-th Betti number, represented as the dimension of the zero-eigenspace
of the Laplacian (Theorem 5: `β_l = dim ker Δ_l`). -/
def bettiNumber (C : GradedComplex ι) : ℕ := kernelDim (laplacian C.d)

/-- Theorem 5, kernel form: `β` equals the kernel dimension of `d + d†`, hence of
the squared Hamiltonian `(d + d†)²` of Theorem 6. -/
lemma bettiNumber_eq_kernelDim_shift (C : GradedComplex ι) :
    bettiNumber C = kernelDim (C.d + C.dᴴ) := by
  unfold bettiNumber
  rw [laplacian_eq_shift_sq C.sq_zero]
  exact kernelDim_mul_self_of_isHermitian _ (add_conjTranspose_isHermitian _)

/-- Eq. (4.15): `Δv = 0` iff `dv = d†v = 0`. -/
lemma hodge_kernel_characterization (C : GradedComplex ι) (ψ : State ι) :
    laplacian C.d *ᵥ ψ = 0 ↔ C.d *ᵥ ψ = 0 ∧ C.dᴴ *ᵥ ψ = 0 :=
  laplacian_mulVec_eq_zero_iff C.d ψ

/-- Nonnegativity of the energy of a positive semidefinite Hamiltonian. -/
lemma energy_nonneg_of_posSemidef {H : Matrix ι ι ℂ} (h : H.PosSemidef) (ψ : State ι) :
    0 ≤ energy H ψ := by
  simpa [energy] using h.re_dotProduct_nonneg ψ

/-- Energy of the SUSY Hamiltonian is nonnegative. -/
lemma energy_hamiltonian_nonneg (S : Supercharge ι) (ψ : State ι) :
    0 ≤ energy S.hamiltonian ψ :=
  energy_nonneg_of_posSemidef S.hamiltonian_posSemidef ψ

/-- Zero energy of the SUSY Hamiltonian iff the state lies in `ker (Q + Q†)`
(the perfect-completeness witness condition). -/
lemma energy_hamiltonian_eq_zero_iff (S : Supercharge ι) (ψ : State ι) :
    energy S.hamiltonian ψ = 0 ↔ S.hamiltonian *ᵥ ψ = 0 := by
  unfold energy
  rw [S.energy_hamiltonian_eq_normSq]
  constructor
  · intro h
    exact (S.hamiltonian_mulVec_eq_zero_iff ψ).mpr
      ((normSqVec_eq_zero_iff _).mp h)
  · intro h
    rw [(S.hamiltonian_mulVec_eq_zero_iff ψ).mp h]
    simp [normSqVec]

/-- Theorem 6 / Eq. (5.6): the SUSY Hamiltonian `H = (Q + Q†)²` has the squared
eigenvalues of the Hermitian operator `Q + Q†`, with the same eigenvectors; its
characteristic polynomial is the product of `X - λᵢ·λᵢ`. -/
theorem hamiltonian_spectrum_square (S : Supercharge ι) :
    (∀ i, S.hamiltonian *ᵥ ⇑(S.shift_isHermitian.eigenvectorBasis i)
        = ((S.shift_isHermitian.eigenvalues i) *
            (S.shift_isHermitian.eigenvalues i) : ℝ) •
            ⇑(S.shift_isHermitian.eigenvectorBasis i)) ∧
    S.hamiltonian.charpoly
      = ∏ i, (Polynomial.X - Polynomial.C
          ((S.shift_isHermitian.eigenvalues i : ℂ) *
            (S.shift_isHermitian.eigenvalues i : ℂ))) := by
  constructor
  · intro i
    rw [S.hamiltonian_eq_shift_sq]
    exact S.shift_sq_eigen i
  · rw [S.hamiltonian_eq_shift_sq]
    exact charpoly_mul_self_of_isHermitian S.shift S.shift_isHermitian

/-! ### Spectral density of a Hermitian matrix -/

/-- Definition 6/7 shadow: the spectral density `N_A(b)` of a Hermitian matrix,
i.e. the fraction of eigenvalues at most `b` (Eq. (5.2)). -/
def spectralDensity (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (b : ℝ) : ℚ :=
  ((Finset.univ.filter (fun i => hA.eigenvalues i ≤ b)).card : ℚ) /
    (Fintype.card ι : ℚ)

/-- The spectral density is nonnegative. -/
lemma spectralDensity_nonneg {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (b : ℝ) :
    0 ≤ spectralDensity A hA b := by
  unfold spectralDensity
  positivity

/-- The spectral density is at most one on a nonempty index set. -/
lemma spectralDensity_le_one [Nonempty ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (b : ℝ) :
    spectralDensity A hA b ≤ 1 := by
  unfold spectralDensity
  have hcard : ((Finset.univ.filter (fun i => hA.eigenvalues i ≤ b)).card : ℚ)
      ≤ (Fintype.card ι : ℚ) := by
    exact_mod_cast Finset.card_filter_le _ _
  have hpos : (0 : ℚ) < (Fintype.card ι : ℚ) := by
    exact_mod_cast Fintype.card_pos
  rw [div_le_one hpos]
  exact hcard

/-- The spectral density is monotone in the threshold `b`; this is the counting
fact behind QBNE `= LLSD` in Theorem 7. -/
lemma spectralDensity_mono [Nonempty ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    {b b' : ℝ} (hbb : b ≤ b') :
    spectralDensity A hA b ≤ spectralDensity A hA b' := by
  unfold spectralDensity
  have hsub : (Finset.univ.filter (fun i => hA.eigenvalues i ≤ b)) ⊆
      (Finset.univ.filter (fun i => hA.eigenvalues i ≤ b')) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact le_trans hi hbb
  have hcard : ((Finset.univ.filter (fun i => hA.eigenvalues i ≤ b)).card : ℚ)
      ≤ ((Finset.univ.filter (fun i => hA.eigenvalues i ≤ b')).card : ℚ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hpos : (0 : ℚ) < (Fintype.card ι : ℚ) := by
    exact_mod_cast Fintype.card_pos
  exact div_le_div_of_nonneg_right hcard hpos.le

/-- Row sparsity: each row has at most `s` nonzeros (the sparse-access hypothesis
of Proposition 1). -/
def RowSparse (s : ℕ) (A : Matrix ι ι ℂ) : Prop :=
  ∀ i, (Finset.univ.filter (fun j => A i j ≠ 0)).card ≤ s

/-- A graded complex is a supercharge with `Q = d`. -/
def GradedComplex.toSupercharge (C : GradedComplex ι) : Supercharge ι :=
  ⟨C.d, C.sq_zero⟩

/-- The cohomology Laplacian is the SUSY Hamiltonian of the associated
supercharge. -/
@[simp] lemma GradedComplex.laplacian_eq_hamiltonian (C : GradedComplex ι) :
    laplacian C.d = C.toSupercharge.hamiltonian := rfl

/-- The shift of the associated supercharge is `d + d†`. -/
@[simp] lemma GradedComplex.shift_toSupercharge (C : GradedComplex ι) :
    C.toSupercharge.shift = C.d + C.dᴴ := rfl

/-- For `d² = 0` the Laplacian is Hermitian. -/
lemma laplacian_isHermitian {d : Matrix ι ι ℂ} (h : d * d = 0) :
    (laplacian d).IsHermitian := by
  rw [laplacian_eq_shift_sq h]
  exact mul_self_isHermitian (add_conjTranspose_isHermitian d)

/-- For `d² = 0` the Laplacian is positive semidefinite. -/
lemma laplacian_posSemidef_of_sq_zero {d : Matrix ι ι ℂ} (h : d * d = 0) :
    (laplacian d).PosSemidef := by
  have hp := (Supercharge.mk d h).hamiltonian_posSemidef
  simpa only [Supercharge.hamiltonian, laplacian] using hp

/-- For `d² = 0` the Laplacian energy is `‖(d + d†)ψ‖²`. -/
lemma energy_laplacian_eq_normSq {d : Matrix ι ι ℂ} (h : d * d = 0) (ψ : State ι) :
    energy (laplacian d) ψ = normSqVec ((d + dᴴ) *ᵥ ψ) := by
  have h' := (Supercharge.mk d h).energy_hamiltonian_eq_normSq ψ
  simpa only [Supercharge.hamiltonian, Supercharge.shift, laplacian, energy] using h'

/-- For `d² = 0`, zero Laplacian energy is equivalent to lying in the Laplacian
kernel. -/
lemma laplacian_energy_eq_zero_iff {d : Matrix ι ι ℂ} (h : d * d = 0) (ψ : State ι) :
    energy (laplacian d) ψ = 0 ↔ laplacian d *ᵥ ψ = 0 := by
  have h' := energy_hamiltonian_eq_zero_iff (Supercharge.mk d h) ψ
  simpa only [Supercharge.hamiltonian, laplacian] using h'

/-! ### Promise gaps and squared gaps -/

/-- An inverse-polynomial spectral gap above the zero ground space: every
normalized state has zero energy or energy at least `1/q`. -/
def SpectralGap (H : Matrix ι ι ℂ) (q : ℕ) : Prop :=
  ∀ ψ, Normalized ψ → energy H ψ = 0 ∨ (1 / (q : ℝ)) ≤ energy H ψ

/-- Under an inverse-polynomial gap, energies below the threshold are exactly the
zero-energy (Betti) states; this is the promise used for #P-completeness in
Theorem 5. -/
lemma spectralGap_energy_zero (H : Matrix ι ι ℂ) {q : ℕ}
    (h : SpectralGap H q) {ψ : State ι} (hψ : Normalized ψ)
    (hlt : energy H ψ < 1 / (q : ℝ)) : energy H ψ = 0 := by
  rcases h ψ hψ with h0 | hge
  · exact h0
  · linarith

/-- Eq. (3.16), multiplication form: `b² - a² = (b - a)(b + a)`. -/
lemma gap_square_mul (a b : ℝ) : b * b - a * a = (b - a) * (b + a) := by ring

/-- Eq. (3.16): squaring preserves a strict inverse-polynomial gap. -/
lemma gap_square_gt_mul (a b c : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 < c)
    (hgap : c < b - a) : c * c < b * b - a * a := by
  simpa only [pow_two] using gap_square_gt a b c ha hab hc hgap

/-- Squaring is monotone for nonnegative `a ≤ b`: `(b - a)² ≤ b² - a²`. -/
lemma gap_square_ge_mul (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (b - a) * (b - a) ≤ b * b - a * a := by
  simpa only [pow_two] using gap_square_ge a b ha hab

end Qatlib.Papers.SusyCohom21.MainResults.SusyModel
