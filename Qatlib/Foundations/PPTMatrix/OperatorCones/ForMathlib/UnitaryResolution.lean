/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.ForMathlib.PseudoInverse

@[expose] public section




/-!
# Positive semidefinite resolutions of unitary matrices

This file extends the explicit spectral calculus of `PseudoInverse.lean` (additivity, scalars,
the rank-one expansion `cfc_eq_sum`, the commutant statement `commute_cfc` and the converse
positivity statement `nonneg_of_posSemidef_cfc`) and uses it to write a unitary matrix as a
combination `∑ k, c k • Q k` of positive semidefinite matrices `Q k` summing to `1`, with
coefficients of modulus at most `1` (`exists_psd_resolution_of_unitary`).
-/

open Matrix
open scoped ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones

/-! ### More spectral calculus -/

section Calculus

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- `cfc_eq_mul` with the diagonal entries given up to a pointwise equality. -/
theorem cfc_eq_mul_of_eq (hA : A.IsHermitian) (f : ℝ → ℝ) (d : n → ℂ)
    (hd : ∀ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) = d i) :
    hA.cfc f = (hA.eigenvectorUnitary : Matrix n n ℂ) * diagonal d *
      star (hA.eigenvectorUnitary : Matrix n n ℂ) :=
  (cfc_eq_mul hA f).trans (congrArg (fun d : n → ℂ => (hA.eigenvectorUnitary : Matrix n n ℂ) *
    diagonal d * star (hA.eigenvectorUnitary : Matrix n n ℂ)) (funext hd))

/-- The eigenvector unitary `U` of a Hermitian matrix satisfies `U * U⋆ = 1`. -/
theorem eigenvectorUnitary_mul_star_self (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℂ) * star (hA.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
  Unitary.coe_mul_star_self hA.eigenvectorUnitary

/-- Establishes `conj_diagonal_add`: `U * diagonal (fun i => d i + e i) * star U = U * diagonal d * star U + U * diagonal e * star U`, for the stated parameters. -/
theorem conj_diagonal_add (U : Matrix n n ℂ) (d e : n → ℂ) :
    U * diagonal (fun i => d i + e i) * star U =
      U * diagonal d * star U + U * diagonal e * star U := by
  rw [← Matrix.diagonal_add, Matrix.mul_add, Matrix.add_mul]

/-- Establishes `conj_diagonal_sub`: `U * diagonal (fun i => d i - e i) * star U = U * diagonal d * star U - U * diagonal e * star U`, for the stated parameters. -/
theorem conj_diagonal_sub (U : Matrix n n ℂ) (d e : n → ℂ) :
    U * diagonal (fun i => d i - e i) * star U =
      U * diagonal d * star U - U * diagonal e * star U := by
  rw [← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]

/-- Establishes `conj_diagonal_smul`: `U * diagonal (fun i => c * d i) * star U = c • (U * diagonal d * star U)`, for the stated parameters. -/
theorem conj_diagonal_smul (U : Matrix n n ℂ) (c : ℂ) (d : n → ℂ) :
    U * diagonal (fun i => c * d i) * star U = c • (U * diagonal d * star U) := by
  have h : diagonal (fun i => c * d i) = c • diagonal d := Matrix.diagonal_smul c d
  rw [h, Matrix.mul_smul, Matrix.smul_mul]

/-- The spectral calculus is additive. -/
theorem cfc_add (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    hA.cfc (fun x => f x + g x) = hA.cfc f + hA.cfc g := by
  rw [cfc_eq_mul hA f, cfc_eq_mul hA g, ← conj_diagonal_add]
  exact cfc_eq_mul_of_eq hA (fun x => f x + g x)
    (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ) + ((g (hA.eigenvalues i) : ℝ) : ℂ))
    (fun i => Complex.ofReal_add _ _)

/-- The spectral calculus is subtractive. -/
theorem cfc_sub (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    hA.cfc (fun x => f x - g x) = hA.cfc f - hA.cfc g := by
  rw [cfc_eq_mul hA f, cfc_eq_mul hA g, ← conj_diagonal_sub]
  exact cfc_eq_mul_of_eq hA (fun x => f x - g x)
    (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ) - ((g (hA.eigenvalues i) : ℝ) : ℂ))
    (fun i => Complex.ofReal_sub _ _)

/-- The spectral calculus commutes with real scalars. -/
theorem cfc_smul (hA : A.IsHermitian) (r : ℝ) (f : ℝ → ℝ) :
    hA.cfc (fun x => r * f x) = (r : ℂ) • hA.cfc f := by
  rw [cfc_eq_mul hA f, ← conj_diagonal_smul]
  exact cfc_eq_mul_of_eq hA (fun x => r * f x)
    (fun i => (r : ℂ) * ((f (hA.eigenvalues i) : ℝ) : ℂ))
    (fun i => Complex.ofReal_mul _ _)

/-- The spectral calculus of the constant function `1` is the identity matrix. -/
theorem cfc_one (hA : A.IsHermitian) : hA.cfc (fun _ => 1) = 1 := by
  rw [cfc_eq_mul_of_eq hA (fun _ => 1) (fun _ => 1) (fun _ => Complex.ofReal_one),
    Matrix.diagonal_one, Matrix.mul_one]
  exact eigenvectorUnitary_mul_star_self hA

/-- The spectral calculus of the constant function `0` is the zero matrix. -/
theorem cfc_zero (hA : A.IsHermitian) : hA.cfc (fun _ => 0) = 0 := by
  rw [cfc_eq_mul_of_eq hA (fun _ => 0) (fun _ => 0) (fun _ => Complex.ofReal_zero),
    Matrix.diagonal_zero, Matrix.mul_zero, Matrix.zero_mul]

/-- The spectral calculus as a combination of the rank-one eigenprojectors. -/
theorem cfc_eq_sum (hA : A.IsHermitian) (f : ℝ → ℝ) :
    hA.cfc f = ∑ j, ((f (hA.eigenvalues j) : ℝ) : ℂ) •
      Matrix.vecMulVec (fun i => (hA.eigenvectorUnitary : Matrix n n ℂ) i j)
        (star fun i => (hA.eigenvectorUnitary : Matrix n n ℂ) i j) := by
  rw [cfc_eq_mul hA f]
  ext i k
  rw [Matrix.mul_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Matrix.mul_diagonal, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.star_apply,
    Pi.star_apply, smul_eq_mul]
  ring

/-- A matrix commuting with `U * diagonal d * U⋆` commutes with `U * diagonal e * U⋆` whenever
`e` is constant on the level sets of `d`. -/
theorem commute_conj_diagonal {U : Matrix n n ℂ} (hU1 : star U * U = 1) (hU2 : U * star U = 1)
    (B : Matrix n n ℂ) (d e : n → ℂ) (hde : ∀ j k, d j = d k → e j = e k)
    (h : B * (U * diagonal d * star U) = U * diagonal d * star U * B) :
    B * (U * diagonal e * star U) = U * diagonal e * star U * B := by
  have hB' : star U * B * U * diagonal d = diagonal d * (star U * B * U) := by
    calc star U * B * U * diagonal d
        = star U * (B * (U * diagonal d * star U)) * U := by
          simp only [Matrix.mul_assoc]
          rw [hU1, Matrix.mul_one]
      _ = star U * (U * diagonal d * star U * B) * U := by rw [h]
      _ = diagonal d * (star U * B * U) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (star U) U, hU1, Matrix.one_mul]
  have hent : ∀ j k, (star U * B * U) j k * d k = d j * (star U * B * U) j k := by
    intro j k
    have hjk : (star U * B * U * diagonal d) j k = (diagonal d * (star U * B * U)) j k := by
      rw [hB']
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hjk
    exact hjk
  have hent' : ∀ j k, (star U * B * U) j k * e k = e j * (star U * B * U) j k := by
    intro j k
    by_cases h0 : (star U * B * U) j k = 0
    · rw [h0, zero_mul, mul_zero]
    · have hd : d k = d j := mul_left_cancel₀ h0 ((hent j k).trans (mul_comm _ _))
      rw [hde k j hd]
      exact mul_comm _ _
  have hB'e : star U * B * U * diagonal e = diagonal e * (star U * B * U) := by
    ext j k
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    exact hent' j k
  calc B * (U * diagonal e * star U)
      = U * (star U * B * U * diagonal e) * star U := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc U (star U), hU2, Matrix.one_mul]
    _ = U * (diagonal e * (star U * B * U)) * star U := by rw [hB'e]
    _ = U * diagonal e * star U * B := by
        simp only [Matrix.mul_assoc]
        rw [hU2, Matrix.mul_one]

/-- A matrix commuting with a Hermitian matrix commutes with its whole spectral calculus. -/
theorem commute_cfc (hA : A.IsHermitian) (B : Matrix n n ℂ) (hAB : B * A = A * B)
    (f : ℝ → ℝ) : B * hA.cfc f = hA.cfc f * B := by
  have hAeq : A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ) :=
    (cfc_id hA).symm.trans (cfc_eq_mul hA (fun x => x))
  have h : B * ((hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ)) =
      (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ) * B := by
    rw [← hAeq]
    exact hAB
  rw [cfc_eq_mul hA f]
  exact commute_conj_diagonal (star_eigenvectorUnitary_mul_self hA)
    (eigenvectorUnitary_mul_star_self hA) B
    (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ))
    (fun j k hjk => congrArg (fun x : ℝ => ((f x : ℝ) : ℂ)) (Complex.ofReal_injective hjk)) h

/-- If the spectral calculus of `f` is positive semidefinite, then `f` is nonnegative on the
eigenvalues. -/
theorem nonneg_of_posSemidef_cfc (hA : A.IsHermitian) {f : ℝ → ℝ}
    (h : (hA.cfc f).PosSemidef) : ∀ j, 0 ≤ f (hA.eigenvalues j) := by
  have hU1 := star_eigenvectorUnitary_mul_self hA
  have he : (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * hA.cfc f *
      (hA.eigenvectorUnitary : Matrix n n ℂ) =
      diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) := by
    rw [cfc_eq_mul hA f, ← Matrix.star_eq_conjTranspose]
    calc star (hA.eigenvectorUnitary : Matrix n n ℂ) *
          ((hA.eigenvectorUnitary : Matrix n n ℂ) *
            diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) *
            star (hA.eigenvectorUnitary : Matrix n n ℂ)) *
          (hA.eigenvectorUnitary : Matrix n n ℂ)
        = star (hA.eigenvectorUnitary : Matrix n n ℂ) * (hA.eigenvectorUnitary : Matrix n n ℂ) *
            diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) *
            (star (hA.eigenvectorUnitary : Matrix n n ℂ) *
              (hA.eigenvectorUnitary : Matrix n n ℂ)) := by
          simp only [Matrix.mul_assoc]
      _ = diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) := by
          rw [hU1, Matrix.one_mul, Matrix.mul_one]
  have hd : (diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ))).PosSemidef := by
    have h2 := h.conjTranspose_mul_mul_same (hA.eigenvectorUnitary : Matrix n n ℂ)
    rw [he] at h2
    exact h2
  intro j
  exact Complex.zero_le_real.mp (Matrix.posSemidef_diagonal_iff.mp hd j)

/-- Establishes `cfc_mul_mul`: `hA.cfc f * hA.cfc g * hA.cfc h = hA.cfc (fun x => f x * g x * h x)`, for the stated parameters. -/
theorem cfc_mul_mul (hA : A.IsHermitian) (f g h : ℝ → ℝ) :
    hA.cfc f * hA.cfc g * hA.cfc h = hA.cfc (fun x => f x * g x * h x) := by
  rw [cfc_mul_cfc hA f g, cfc_mul_cfc hA (fun x => f x * g x) h]

/-- Establishes `cfc_one_sub_sq`: `hA.cfc (fun x => 1 - x * x) = 1 - A * A`, for the stated parameters. -/
theorem cfc_one_sub_sq (hA : A.IsHermitian) : hA.cfc (fun x => 1 - x * x) = 1 - A * A := by
  calc hA.cfc (fun x => 1 - x * x)
      = hA.cfc (fun _ => 1) - hA.cfc (fun x => x * x) :=
        cfc_sub hA (fun _ => 1) (fun x => x * x)
    _ = 1 - hA.cfc (fun x => x) * hA.cfc (fun x => x) := by
        rw [cfc_one hA, cfc_mul_cfc hA (fun x => x) (fun x => x)]
    _ = 1 - A * A := by rw [cfc_id hA]

end Calculus

/-! ### Scalar functions on `[-1, 1]` -/

/-- `√(1 - x²)`. -/
private noncomputable def sinPart (x : ℝ) : ℝ := Real.sqrt (1 - x * x)

/-- The pseudo-inverse of `sinPart`. -/
private noncomputable def sinPartInv (x : ℝ) : ℝ := (sinPart x)⁻¹

/-- The indicator of `sinPart x ≠ 0`. -/
private noncomputable def sinPartSupp (x : ℝ) : ℝ := sinPart x * (sinPart x)⁻¹

/-- Establishes `sinPart_cases`: `(sinPartSupp x = 0 ∧ sinPartInv x = 0 ∧ 1 - x * x = 0) ∨ (sinPartSupp x = 1 ∧ sinPartInv x * sinPartInv x * (1 - x * x) = 1)`, for the stated parameters. -/
private theorem sinPart_cases {x : ℝ} (hx : 0 ≤ 1 - x * x) :
    (sinPartSupp x = 0 ∧ sinPartInv x = 0 ∧ 1 - x * x = 0) ∨
      (sinPartSupp x = 1 ∧ sinPartInv x * sinPartInv x * (1 - x * x) = 1) := by
  have hss : sinPart x * sinPart x = 1 - x * x := Real.mul_self_sqrt hx
  by_cases h0 : sinPart x = 0
  · left
    refine ⟨?_, ?_, ?_⟩
    · unfold sinPartSupp
      rw [h0, zero_mul]
    · unfold sinPartInv
      rw [h0, _root_.inv_zero]
    · rw [← hss, h0, zero_mul]
  · right
    refine ⟨mul_inv_cancel₀ h0, ?_⟩
    unfold sinPartInv
    rw [← hss, mul_mul_mul_comm, inv_mul_cancel₀ h0, one_mul]

/-- Establishes `norm_add_mul_I_le_one`: `‖(x : ℂ) + (y : ℂ) * Complex.I‖ ≤ 1`, for the stated parameters. -/
private theorem norm_add_mul_I_le_one (x y : ℝ) (h : x * x + y * y ≤ 1) :
    ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ≤ 1 := by
  have h0 : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  have h1 := Real.sqrt_nonneg (x ^ 2 + y ^ 2)
  have h2 := Real.sq_sqrt h0
  rw [Complex.norm_add_mul_I]
  nlinarith [h1, h2, h, sq_nonneg (Real.sqrt (x ^ 2 + y ^ 2) - 1)]

/-- Establishes `norm_ofReal_le_one`: `‖(x : ℂ)‖ ≤ 1`, for the stated parameters. -/
private theorem norm_ofReal_le_one (x y : ℝ) (h : x * x + y * y ≤ 1) : ‖(x : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;>
    nlinarith [mul_self_nonneg y, mul_self_nonneg (x - 1), mul_self_nonneg (x + 1)]

/-! ### Matrix algebra not involving the identity matrix -/

section Algebra

variable {n : Type*} [Fintype n]

/-- Establishes `sandwich_aux`: `(F + G * B) * H * (F + G * B) = F * H * F + G * H * G * (B * B) + (F * H * G + G * H * F) * B`, for the stated parameters. -/
private theorem sandwich_aux (F G H B : Matrix n n ℂ) (hBF : B * F = F * B)
    (hBG : B * G = G * B) (hBH : B * H = H * B) :
    (F + G * B) * H * (F + G * B) =
      F * H * F + G * H * G * (B * B) + (F * H * G + G * H * F) * B := by
  have hBF' : ∀ Y : Matrix n n ℂ, B * (F * Y) = F * (B * Y) := fun Y => by
    rw [← Matrix.mul_assoc B F Y, hBF, Matrix.mul_assoc F B Y]
  have hBG' : ∀ Y : Matrix n n ℂ, B * (G * Y) = G * (B * Y) := fun Y => by
    rw [← Matrix.mul_assoc B G Y, hBG, Matrix.mul_assoc G B Y]
  have hBH' : ∀ Y : Matrix n n ℂ, B * (H * Y) = H * (B * Y) := fun Y => by
    rw [← Matrix.mul_assoc B H Y, hBH, Matrix.mul_assoc H B Y]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hBF, hBG', hBH]
  abel

/-- Establishes `mul_mul_mul_comm_of_commute`: `F * B * (F * B) = F * F * (B * B)`, for the stated parameters. -/
private theorem mul_mul_mul_comm_of_commute (F B : Matrix n n ℂ) (h : B * F = F * B) :
    F * B * (F * B) = F * F * (B * B) := by
  rw [Matrix.mul_assoc F B (F * B), ← Matrix.mul_assoc B F B, h, Matrix.mul_assoc F B B,
    ← Matrix.mul_assoc F F (B * B)]

/-- Establishes `smul_mul_smul'`: `(a • M) * (b • P) = (a * b) • (M * P)`, for the stated parameters. -/
private theorem smul_mul_smul' (a b : ℂ) (M P : Matrix n n ℂ) :
    (a • M) * (b • P) = (a * b) • (M * P) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- Establishes `sum_smul_sandwich`: `∑ j, c j • (Q * E j * Q) = Q * (∑ j, c j • E j) * Q`, for the stated parameters. -/
private theorem sum_smul_sandwich {ι : Type*} [Fintype ι] (Q : Matrix n n ℂ) (c : ι → ℂ)
    (E : ι → Matrix n n ℂ) : ∑ j, c j • (Q * E j * Q) = Q * (∑ j, c j • E j) * Q := by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.mul_smul, Matrix.smul_mul]

omit [Fintype n] in
/-- The Hermitian part of a matrix is Hermitian. -/
private theorem isHermitian_cartesian_re (W : Matrix n n ℂ) :
    ((1 / 2 : ℂ) • (W + Wᴴ)).IsHermitian := by
  have hstar : star (1 / 2 : ℂ) = 1 / 2 := by simp
  show ((1 / 2 : ℂ) • (W + Wᴴ))ᴴ = (1 / 2 : ℂ) • (W + Wᴴ)
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
    hstar, add_comm Wᴴ W]

omit [Fintype n] in
/-- The skew-Hermitian part of a matrix, divided by `I`, is Hermitian. -/
private theorem isHermitian_cartesian_im (W : Matrix n n ℂ) :
    ((-Complex.I / 2) • (W - Wᴴ)).IsHermitian := by
  have hstar : star (-Complex.I / 2) = Complex.I / 2 := by simp
  show ((-Complex.I / 2) • (W - Wᴴ))ᴴ = (-Complex.I / 2) • (W - Wᴴ)
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
    hstar]
  module

omit [Fintype n] in
/-- Cartesian decomposition of a matrix. -/
private theorem cartesian_add (W : Matrix n n ℂ) :
    (1 / 2 : ℂ) • (W + Wᴴ) + Complex.I • ((-Complex.I / 2) • (W - Wᴴ)) = W := by
  have hI : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
  rw [smul_smul, hI]
  module

end Algebra

/-! ### Sandwich identities for the spectral calculus -/

section Sandwich

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- Establishes `sandwich_cfc`: `(hA.cfc f + hA.cfc g * B) * hA.cfc h * (hA.cfc f + hA.cfc g * B) = hA.cfc (fun x => f x * h x * f x) + hA.cfc (fun x => g x * h x * g x) * (B * B) + hA.cfc (fun x => f x * h x * g x + g x * h x * f x) * B`, for the stated parameters. -/
private theorem sandwich_cfc (hA : A.IsHermitian) (B : Matrix n n ℂ) (hAB : B * A = A * B)
    (f g h : ℝ → ℝ) :
    (hA.cfc f + hA.cfc g * B) * hA.cfc h * (hA.cfc f + hA.cfc g * B) =
      hA.cfc (fun x => f x * h x * f x) + hA.cfc (fun x => g x * h x * g x) * (B * B) +
        hA.cfc (fun x => f x * h x * g x + g x * h x * f x) * B := by
  rw [sandwich_aux (hA.cfc f) (hA.cfc g) (hA.cfc h) B (commute_cfc hA B hAB f)
    (commute_cfc hA B hAB g) (commute_cfc hA B hAB h), cfc_mul_mul hA f h f,
    cfc_mul_mul hA g h g, cfc_mul_mul hA f h g, cfc_mul_mul hA g h f,
    ← cfc_add hA (fun x => f x * h x * g x) (fun x => g x * h x * f x)]

/-- Establishes `conjTranspose_cfc_add_cfc_mul`: `(hA.cfc f + hA.cfc g * B)ᴴ = hA.cfc f + hA.cfc g * B`, for the stated parameters. -/
private theorem conjTranspose_cfc_add_cfc_mul (hA : A.IsHermitian) (B : Matrix n n ℂ)
    (hBh : B.IsHermitian) (hAB : B * A = A * B) (f g : ℝ → ℝ) :
    (hA.cfc f + hA.cfc g * B)ᴴ = hA.cfc f + hA.cfc g * B := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, (isHermitian_cfc hA f).eq,
    (isHermitian_cfc hA g).eq, hBh.eq, commute_cfc hA B hAB g]

/-- Establishes `half_sandwich`: `(hA.cfc (fun x => sinPartSupp x / 2) + hA.cfc (fun x => sinPartInv x / 2) * B) * hA.cfc h * (hA.cfc (fun x => sinPartSupp x / 2) + hA.cfc (fun x => sinPartInv x / 2) * B) = hA.cfc (fun x => h x * sinPartSupp x / 2) + hA.cfc (fun x => h x * sinPartInv x / 2) * B`, for the stated parameters. -/
private theorem half_sandwich (hA : A.IsHermitian)
    (hN : ∀ j, 0 ≤ 1 - hA.eigenvalues j * hA.eigenvalues j) (B : Matrix n n ℂ)
    (hAB : B * A = A * B) (hBB : B * B = hA.cfc (fun x => 1 - x * x)) (h : ℝ → ℝ) :
    (hA.cfc (fun x => sinPartSupp x / 2) + hA.cfc (fun x => sinPartInv x / 2) * B) * hA.cfc h *
        (hA.cfc (fun x => sinPartSupp x / 2) + hA.cfc (fun x => sinPartInv x / 2) * B) =
      hA.cfc (fun x => h x * sinPartSupp x / 2) +
        hA.cfc (fun x => h x * sinPartInv x / 2) * B := by
  rw [sandwich_cfc hA B hAB (fun x => sinPartSupp x / 2) (fun x => sinPartInv x / 2) h, hBB,
    cfc_mul_cfc, ← cfc_add]
  congr 1
  · refine cfc_congr_eigenvalues hA (fun i => ?_)
    rcases sinPart_cases (hN i) with ⟨he, hr, hq⟩ | ⟨he, hr⟩
    · simp only [he, hr, hq]
      ring
    · simp only [he]
      linear_combination (h (hA.eigenvalues i) / 4) * hr
  · congr 1
    refine cfc_congr_eigenvalues hA (fun i => ?_)
    rcases sinPart_cases (hN i) with ⟨he, hr, -⟩ | ⟨he, -⟩
    · simp only [he, hr]
      ring
    · simp only [he]
      ring

/-- Establishes `compl_sandwich`: `hA.cfc (fun x => 1 - sinPartSupp x) * hA.cfc h * hA.cfc (fun x => 1 - sinPartSupp x) = hA.cfc (fun x => h x * (1 - sinPartSupp x))`, for the stated parameters. -/
private theorem compl_sandwich (hA : A.IsHermitian)
    (hN : ∀ j, 0 ≤ 1 - hA.eigenvalues j * hA.eigenvalues j) (h : ℝ → ℝ) :
    hA.cfc (fun x => 1 - sinPartSupp x) * hA.cfc h * hA.cfc (fun x => 1 - sinPartSupp x) =
      hA.cfc (fun x => h x * (1 - sinPartSupp x)) := by
  rw [cfc_mul_mul hA (fun x => 1 - sinPartSupp x) h (fun x => 1 - sinPartSupp x)]
  refine cfc_congr_eigenvalues hA (fun i => ?_)
  rcases sinPart_cases (hN i) with ⟨he, -, -⟩ | ⟨he, -⟩
  · simp only [he]
    ring
  · simp only [he]
    ring

/-- Establishes `cfc_sinPartSupp_mul`: `hA.cfc sinPartSupp * B = B`, for the stated parameters. -/
private theorem cfc_sinPartSupp_mul (hA : A.IsHermitian)
    (hN : ∀ j, 0 ≤ 1 - hA.eigenvalues j * hA.eigenvalues j) (B : Matrix n n ℂ)
    (hBh : B.IsHermitian) (hAB : B * A = A * B) (hBB : B * B = hA.cfc (fun x => 1 - x * x)) :
    hA.cfc sinPartSupp * B = B := by
  have hcomm : B * hA.cfc (fun x => 1 - sinPartSupp x) =
      hA.cfc (fun x => 1 - sinPartSupp x) * B := commute_cfc hA B hAB _
  have hZ : (hA.cfc (fun x => 1 - sinPartSupp x) * B)ᴴ *
      (hA.cfc (fun x => 1 - sinPartSupp x) * B) = 0 := by
    rw [Matrix.conjTranspose_mul, hBh.eq, (isHermitian_cfc hA _).eq, hcomm]
    calc hA.cfc (fun x => 1 - sinPartSupp x) * B * (hA.cfc (fun x => 1 - sinPartSupp x) * B)
        = hA.cfc (fun x => 1 - sinPartSupp x) * hA.cfc (fun x => 1 - sinPartSupp x) * (B * B) :=
          mul_mul_mul_comm_of_commute _ B hcomm
      _ = hA.cfc (fun x => (1 - sinPartSupp x) * (1 - sinPartSupp x) * (1 - x * x)) := by
          rw [hBB, cfc_mul_cfc, cfc_mul_cfc]
      _ = hA.cfc (fun _ => 0) := by
          refine cfc_congr_eigenvalues hA (fun i => ?_)
          rcases sinPart_cases (hN i) with ⟨-, -, hq⟩ | ⟨he, -⟩
          · simp only [hq]
            ring
          · simp only [he]
            ring
      _ = 0 := cfc_zero hA
  have hZ0 : hA.cfc (fun x => 1 - sinPartSupp x) * B = 0 :=
    Matrix.conjTranspose_mul_self_eq_zero.mp hZ
  have hsplit : hA.cfc (fun x => 1 - sinPartSupp x) = 1 - hA.cfc sinPartSupp := by
    rw [cfc_sub hA (fun _ => 1) sinPartSupp, cfc_one hA]
  rw [hsplit, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hZ0
  exact hZ0.symm

/-- The rank-one eigenprojector onto the `j`-th eigenvector of a Hermitian matrix. -/
private noncomputable def eigenProj (hA : A.IsHermitian) (j : n) : Matrix n n ℂ :=
  Matrix.vecMulVec (fun i => (hA.eigenvectorUnitary : Matrix n n ℂ) i j)
    (star fun i => (hA.eigenvectorUnitary : Matrix n n ℂ) i j)

/-- Establishes `posSemidef_eigenProj`: `(eigenProj hA j).PosSemidef`, for the stated parameters. -/
private theorem posSemidef_eigenProj (hA : A.IsHermitian) (j : n) : (eigenProj hA j).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (fun i => (hA.eigenvectorUnitary : Matrix n n ℂ) i j)

/-- Establishes `cfc_eq_sum_eigenProj`: `hA.cfc f = ∑ j, ((f (hA.eigenvalues j) : ℝ) : ℂ) • eigenProj hA j`, for the stated parameters. -/
private theorem cfc_eq_sum_eigenProj (hA : A.IsHermitian) (f : ℝ → ℝ) :
    hA.cfc f = ∑ j, ((f (hA.eigenvalues j) : ℝ) : ℂ) • eigenProj hA j :=
  cfc_eq_sum hA f

/-- Establishes `sum_smul_eigenProj_sandwich`: `∑ j, ((f (hA.eigenvalues j) : ℝ) : ℂ) • (Q * eigenProj hA j * Q) = Q * hA.cfc f * Q`, for the stated parameters. -/
private theorem sum_smul_eigenProj_sandwich (hA : A.IsHermitian) (Q : Matrix n n ℂ) (f : ℝ → ℝ) :
    ∑ j, ((f (hA.eigenvalues j) : ℝ) : ℂ) • (Q * eigenProj hA j * Q) = Q * hA.cfc f * Q := by
  rw [cfc_eq_sum_eigenProj hA f]
  exact sum_smul_sandwich Q (fun j => ((f (hA.eigenvalues j) : ℝ) : ℂ)) (eigenProj hA)

/-- Establishes `sum_eigenProj_sandwich`: `∑ j, Q * eigenProj hA j * Q = Q * hA.cfc (fun _ => 1) * Q`, for the stated parameters. -/
private theorem sum_eigenProj_sandwich (hA : A.IsHermitian) (Q : Matrix n n ℂ) :
    ∑ j, Q * eigenProj hA j * Q = Q * hA.cfc (fun _ => 1) * Q := by
  rw [← sum_smul_eigenProj_sandwich hA Q (fun _ => 1)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Complex.ofReal_one, one_smul]

/-- Establishes `sum_add_mul_smul_eigenProj_sandwich`: `∑ j, (((f (hA.eigenvalues j) : ℝ) : ℂ) + ((g (hA.eigenvalues j) : ℝ) : ℂ) * z) • (Q * eigenProj hA j * Q) = Q * hA.cfc f * Q + z • (Q * hA.cfc g * Q)`, for the stated parameters. -/
private theorem sum_add_mul_smul_eigenProj_sandwich (hA : A.IsHermitian) (Q : Matrix n n ℂ)
    (f g : ℝ → ℝ) (z : ℂ) :
    ∑ j, (((f (hA.eigenvalues j) : ℝ) : ℂ) + ((g (hA.eigenvalues j) : ℝ) : ℂ) * z) •
        (Q * eigenProj hA j * Q) = Q * hA.cfc f * Q + z • (Q * hA.cfc g * Q) := by
  rw [← sum_smul_eigenProj_sandwich hA Q f, ← sum_smul_eigenProj_sandwich hA Q g,
    Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [add_smul, mul_comm ((g (hA.eigenvalues j) : ℝ) : ℂ) z, mul_smul]

end Sandwich

/-! ### Positive semidefinite resolutions -/

section Resolution

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

omit [Fintype n] in
/-- Transport a resolution indexed by a finite type to one indexed by `Fin N`. -/
private theorem exists_fin_of_fintype {ι : Type*} [Fintype ι] {W : Matrix n n ℂ} (c : ι → ℂ)
    (Q : ι → Matrix n n ℂ) (hc : ∀ k, ‖c k‖ ≤ 1) (hQ : ∀ k, (Q k).PosSemidef)
    (h1 : ∑ k, Q k = 1) (hW : ∑ k, c k • Q k = W) :
    ∃ (N : ℕ) (c : Fin N → ℂ) (Q : Fin N → Matrix n n ℂ), (∀ k, ‖c k‖ ≤ 1) ∧
      (∀ k, (Q k).PosSemidef) ∧ ∑ k, Q k = 1 ∧ ∑ k, c k • Q k = W :=
  ⟨Fintype.card ι, fun k => c ((Fintype.equivFin ι).symm k),
    fun k => Q ((Fintype.equivFin ι).symm k), fun _ => hc _, fun _ => hQ _,
    (Equiv.sum_comp (Fintype.equivFin ι).symm Q).trans h1,
    (Equiv.sum_comp (Fintype.equivFin ι).symm (fun k => c k • Q k)).trans hW⟩

/-- Assembly step: three Hermitian matrices `Q₀ Q₁ Q₂` whose sandwiches resolve the spectral
calculus of `A` give a positive semidefinite resolution of `A + I • X`. -/
private theorem exists_psd_resolution_of_sandwich (hA : A.IsHermitian) (Q₀ Q₁ Q₂ X : Matrix n n ℂ)
    (hQ₀ : Q₀ᴴ = Q₀) (hQ₁ : Q₁ᴴ = Q₁) (hQ₂ : Q₂ᴴ = Q₂) (g : ℝ → ℝ)
    (hg : ∀ j, hA.eigenvalues j * hA.eigenvalues j +
      g (hA.eigenvalues j) * g (hA.eigenvalues j) ≤ 1)
    (hsum : ∀ h : ℝ → ℝ,
      Q₀ * hA.cfc h * Q₀ + Q₁ * hA.cfc h * Q₁ + Q₂ * hA.cfc h * Q₂ = hA.cfc h)
    (hdiff : Q₀ * hA.cfc g * Q₀ - Q₁ * hA.cfc g * Q₁ = X) :
    ∃ (N : ℕ) (c : Fin N → ℂ) (Q : Fin N → Matrix n n ℂ), (∀ k, ‖c k‖ ≤ 1) ∧
      (∀ k, (Q k).PosSemidef) ∧ ∑ k, Q k = 1 ∧ ∑ k, c k • Q k = A + Complex.I • X := by
  have key : ∀ P₀ R₀ P₁ R₁ P₂ : Matrix n n ℂ,
      P₀ + Complex.I • R₀ + (P₁ + (-Complex.I) • R₁) + P₂ =
        P₀ + P₁ + P₂ + Complex.I • (R₀ - R₁) := by
    intro P₀ R₀ P₁ R₁ P₂
    rw [neg_smul, smul_sub]
    abel
  refine exists_fin_of_fintype (ι := (n ⊕ n) ⊕ n)
    (Sum.elim (Sum.elim
      (fun j => ((hA.eigenvalues j : ℝ) : ℂ) + ((g (hA.eigenvalues j) : ℝ) : ℂ) * Complex.I)
      (fun j => ((hA.eigenvalues j : ℝ) : ℂ) + ((g (hA.eigenvalues j) : ℝ) : ℂ) * (-Complex.I)))
      (fun j => ((hA.eigenvalues j : ℝ) : ℂ)))
    (Sum.elim (Sum.elim (fun j => Q₀ * eigenProj hA j * Q₀) (fun j => Q₁ * eigenProj hA j * Q₁))
      (fun j => Q₂ * eigenProj hA j * Q₂)) ?_ ?_ ?_ ?_
  · rintro ((j | j) | j)
    · show ‖((hA.eigenvalues j : ℝ) : ℂ) + ((g (hA.eigenvalues j) : ℝ) : ℂ) * Complex.I‖ ≤ 1
      exact norm_add_mul_I_le_one _ _ (hg j)
    · show ‖((hA.eigenvalues j : ℝ) : ℂ) + ((g (hA.eigenvalues j) : ℝ) : ℂ) * (-Complex.I)‖ ≤ 1
      have hneg : ((hA.eigenvalues j : ℝ) : ℂ) + ((g (hA.eigenvalues j) : ℝ) : ℂ) * (-Complex.I) =
          ((hA.eigenvalues j : ℝ) : ℂ) + ((-g (hA.eigenvalues j) : ℝ) : ℂ) * Complex.I := by
        rw [Complex.ofReal_neg, neg_mul, mul_neg]
      rw [hneg]
      refine norm_add_mul_I_le_one _ _ ?_
      rw [neg_mul_neg]
      exact hg j
    · show ‖((hA.eigenvalues j : ℝ) : ℂ)‖ ≤ 1
      exact norm_ofReal_le_one _ _ (hg j)
  · rintro ((j | j) | j)
    · have h := (posSemidef_eigenProj hA j).mul_mul_conjTranspose_same Q₀
      rw [hQ₀] at h
      exact h
    · have h := (posSemidef_eigenProj hA j).mul_mul_conjTranspose_same Q₁
      rw [hQ₁] at h
      exact h
    · have h := (posSemidef_eigenProj hA j).mul_mul_conjTranspose_same Q₂
      rw [hQ₂] at h
      exact h
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [sum_eigenProj_sandwich hA Q₀, sum_eigenProj_sandwich hA Q₁, sum_eigenProj_sandwich hA Q₂,
      hsum (fun _ => 1)]
    exact cfc_one hA
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [sum_add_mul_smul_eigenProj_sandwich hA Q₀ (fun x => x) g Complex.I,
      sum_add_mul_smul_eigenProj_sandwich hA Q₁ (fun x => x) g (-Complex.I),
      sum_smul_eigenProj_sandwich hA Q₂ (fun x => x), key, hsum (fun x => x), hdiff, cfc_id hA]

/-- A commuting pair of Hermitian matrices with `X₁² + X₂² = 1` gives a positive semidefinite
resolution of `X₁ + I • X₂`. -/
theorem exists_psd_resolution_of_commuting_pair {X₁ X₂ : Matrix n n ℂ} (h₁ : X₁.IsHermitian)
    (h₂ : X₂.IsHermitian) (hc : X₂ * X₁ = X₁ * X₂) (hs : X₁ * X₁ + X₂ * X₂ = 1) :
    ∃ (N : ℕ) (c : Fin N → ℂ) (Q : Fin N → Matrix n n ℂ), (∀ k, ‖c k‖ ≤ 1) ∧
      (∀ k, (Q k).PosSemidef) ∧ ∑ k, Q k = 1 ∧ ∑ k, c k • Q k = X₁ + Complex.I • X₂ := by
  have hq : X₂ * X₂ = h₁.cfc (fun x => 1 - x * x) :=
    (eq_sub_of_add_eq' hs).trans (cfc_one_sub_sq h₁).symm
  have hN : ∀ j, 0 ≤ 1 - h₁.eigenvalues j * h₁.eigenvalues j := by
    refine nonneg_of_posSemidef_cfc h₁ (f := fun x => 1 - x * x) ?_
    rw [← hq]
    have h := Matrix.posSemidef_conjTranspose_mul_self X₂
    rw [h₂.eq] at h
    exact h
  have h₂' : (-X₂).IsHermitian := by
    show (-X₂)ᴴ = -X₂
    rw [Matrix.conjTranspose_neg, h₂.eq]
  have hc' : -X₂ * X₁ = X₁ * -X₂ := by rw [Matrix.neg_mul, Matrix.mul_neg, hc]
  have hq' : -X₂ * -X₂ = h₁.cfc (fun x => 1 - x * x) := by
    rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, hq]
  have key : ∀ D K C : Matrix n n ℂ, D + K + (D + -K) + C = D + D + C := by
    intro D K C
    abel
  have key2 : ∀ D K : Matrix n n ℂ, D + K - (D + -K) = K + K := by
    intro D K
    abel
  have hsr : h₁.cfc (fun x => sinPart x * sinPartInv x / 2 + sinPart x * sinPartInv x / 2) =
      h₁.cfc sinPartSupp := by
    refine cfc_congr_eigenvalues h₁ (fun i => ?_)
    unfold sinPartSupp sinPartInv
    ring
  refine exists_psd_resolution_of_sandwich h₁
    (h₁.cfc (fun x => sinPartSupp x / 2) + h₁.cfc (fun x => sinPartInv x / 2) * X₂)
    (h₁.cfc (fun x => sinPartSupp x / 2) + h₁.cfc (fun x => sinPartInv x / 2) * -X₂)
    (h₁.cfc (fun x => 1 - sinPartSupp x)) X₂
    (conjTranspose_cfc_add_cfc_mul h₁ X₂ h₂ hc _ _)
    (conjTranspose_cfc_add_cfc_mul h₁ (-X₂) h₂' hc' _ _)
    (isHermitian_cfc h₁ _).eq sinPart ?_ ?_ ?_
  · intro j
    have h : sinPart (h₁.eigenvalues j) * sinPart (h₁.eigenvalues j) =
        1 - h₁.eigenvalues j * h₁.eigenvalues j := Real.mul_self_sqrt (hN j)
    linarith
  · intro h
    rw [half_sandwich h₁ hN X₂ hc hq h, half_sandwich h₁ hN (-X₂) hc' hq' h,
      compl_sandwich h₁ hN h, Matrix.mul_neg, key, ← cfc_add, ← cfc_add]
    refine cfc_congr_eigenvalues h₁ (fun i => ?_)
    ring
  · rw [half_sandwich h₁ hN X₂ hc hq sinPart, half_sandwich h₁ hN (-X₂) hc' hq' sinPart,
      Matrix.mul_neg, key2, ← Matrix.add_mul, ← cfc_add, hsr,
      cfc_sinPartSupp_mul h₁ hN X₂ h₂ hc hq]

/-- Establishes `cartesian_commute`: `((-Complex.I / 2) • (W - Wᴴ)) * ((1 / 2 : ℂ) • (W + Wᴴ)) = ((1 / 2 : ℂ) • (W + Wᴴ)) * ((-Complex.I / 2) • (W - Wᴴ))`, for the stated parameters. -/
private theorem cartesian_commute (W : Matrix n n ℂ) (hW : Wᴴ * W = 1) (hW' : W * Wᴴ = 1) :
    ((-Complex.I / 2) • (W - Wᴴ)) * ((1 / 2 : ℂ) • (W + Wᴴ)) =
      ((1 / 2 : ℂ) • (W + Wᴴ)) * ((-Complex.I / 2) • (W - Wᴴ)) := by
  have hMP : (W - Wᴴ) * (W + Wᴴ) = (W + Wᴴ) * (W - Wᴴ) := by
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
      Matrix.mul_sub, hW, hW']
    abel
  rw [smul_mul_smul', smul_mul_smul', hMP, mul_comm (1 / 2 : ℂ) (-Complex.I / 2)]

/-- Establishes `cartesian_sq_add_sq`: `((1 / 2 : ℂ) • (W + Wᴴ)) * ((1 / 2 : ℂ) • (W + Wᴴ)) + ((-Complex.I / 2) • (W - Wᴴ)) * ((-Complex.I / 2) • (W - Wᴴ)) = 1`, for the stated parameters. -/
private theorem cartesian_sq_add_sq (W : Matrix n n ℂ) (hW : Wᴴ * W = 1) (hW' : W * Wᴴ = 1) :
    ((1 / 2 : ℂ) • (W + Wᴴ)) * ((1 / 2 : ℂ) • (W + Wᴴ)) +
      ((-Complex.I / 2) • (W - Wᴴ)) * ((-Complex.I / 2) • (W - Wᴴ)) = 1 := by
  have hI2 : (-Complex.I / 2) * (-Complex.I / 2) = -(1 / 4 : ℂ) := by
    linear_combination (1 / 4 : ℂ) * Complex.I_mul_I
  have hPP : (W + Wᴴ) * (W + Wᴴ) = W * W + 1 + (1 + Wᴴ * Wᴴ) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hW, hW']
  have hMM : (W - Wᴴ) * (W - Wᴴ) = W * W - 1 - (1 - Wᴴ * Wᴴ) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hW, hW']
  rw [smul_mul_smul', smul_mul_smul', hI2, hPP, hMM]
  module

/-- **Positive semidefinite resolution of a unitary matrix**: a unitary `W` is a combination
`∑ k, c k • Q k` of positive semidefinite matrices `Q k` with `∑ k, Q k = 1` and coefficients of
modulus at most `1`. -/
theorem exists_psd_resolution_of_unitary (W : Matrix n n ℂ) (hW : Wᴴ * W = 1) :
    ∃ (N : ℕ) (c : Fin N → ℂ) (Q : Fin N → Matrix n n ℂ), (∀ k, ‖c k‖ ≤ 1) ∧
      (∀ k, (Q k).PosSemidef) ∧ ∑ k, Q k = 1 ∧ ∑ k, c k • Q k = W := by
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  have h := exists_psd_resolution_of_commuting_pair (isHermitian_cartesian_re W)
    (isHermitian_cartesian_im W) (cartesian_commute W hW hW') (cartesian_sq_add_sq W hW hW')
  rw [cartesian_add W] at h
  exact h

end Resolution

end Qatlib.Foundations.PPTMatrix.OperatorCones
