/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLogicSynth04.MainResults.QubitRotations
import Qatlib.Concepts.MixedFidelity.FidelityMetric.SimultaneousDiagonalization
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Quantum Shannon decomposition from cosine-sine data

The Hermitian components `hermPart` and `skewPart` lead to a unitary diagonalization used by
`theorem12_demultiplex`. A selector of two unitary blocks then factors through a Z-rotation
multiplexor.

Given a cosine-sine factorization, `theorem13_qsd_of_csd` decomposes both selectors and obtains
the corresponding quantum Shannon factorization. See [ShendeBullockMarkov2006] for the paper's
setting.

## Main statements

* `star_negI_half`: The complex conjugate of `-I / 2` is `I / 2`.
* `theorem13_qsd_of_csd`: Given the stated cosine-sine factorization with unitary outer blocks,
  `U` has a quantum Shannon factorization with two Z-rotation multiplexors surrounding the given
  Y-rotation multiplexor and four repeated unitary blocks.

## References

* [Shende et al., 2006][ShendeBullockMarkov2006]
-/

set_option backward.isDefEq.respectTransparency false

open scoped Matrix
open Matrix
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLogicSynth04.MainResults

open Qatlib.Concepts.MixedFidelity.FidelityMetric

/-- The complex conjugate of `-I / 2` is `I / 2`. -/
theorem star_negI_half : star (-Complex.I / 2 : ℂ) = Complex.I / 2 := by
  rw [star_div₀, star_neg, star_ofNat, Complex.star_def, Complex.conj_I]
  ring

/-- The complex number `1 / 2` is fixed by conjugation. -/
theorem star_half : star ((1 / 2 : ℂ)) = 1 / 2 := by
  rw [star_div₀, star_one, star_ofNat]

/-- The Hermitian part `(U + Uᴴ) / 2` of a complex matrix. -/
def hermPart {M : Type*} (U : Matrix M M ℂ) : Matrix M M ℂ :=
  (1 / 2 : ℂ) • (U + Uᴴ)

/-- The Hermitian matrix `(-I / 2) • (U - Uᴴ)` representing the imaginary component of `U`. -/
def skewPart {M : Type*} (U : Matrix M M ℂ) : Matrix M M ℂ :=
  (-Complex.I / 2 : ℂ) • (U - Uᴴ)

/-- The matrix `hermPart U` is Hermitian. -/
theorem hermPart_isHermitian {M : Type*} (U : Matrix M M ℂ) : (hermPart U).IsHermitian := by
  unfold hermPart
  exact (isHermitian_add_transpose_self U).smul (by rw [isSelfAdjoint_iff, star_half])

/-- The matrix `skewPart U` is Hermitian. -/
theorem skewPart_isHermitian {M : Type*} (U : Matrix M M ℂ) : (skewPart U).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  unfold skewPart
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.conjTranspose_apply]
  rw [star_mul, star_negI_half, star_sub, star_star]
  ring

/-- The decomposition `hermPart U + I • skewPart U` recovers `U`. -/
theorem hermPart_add_I_smul_skewPart {M : Type*} (U : Matrix M M ℂ) :
    hermPart U + Complex.I • skewPart U = U := by
  ext i j
  simp only [hermPart, skewPart, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.conjTranspose_apply, smul_eq_mul]
  have hI : Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) := by
    rw [show Complex.I * (-Complex.I / 2) = -(Complex.I * Complex.I) / 2 by ring]
    rw [Complex.I_mul_I]
    ring
  rw [show Complex.I * ((-Complex.I / 2) * (U i j - star (U j i)))
        = (Complex.I * (-Complex.I / 2)) * (U i j - star (U j i)) by ring, hI]
  ring

/-- For a unitary matrix, its Hermitian and imaginary Hermitian components commute. -/
theorem hermPart_comm_skewPart {M : Type*} [Fintype M] [DecidableEq M]
    (U : Matrix M M ℂ) (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1) :
    hermPart U * skewPart U = skewPart U * hermPart U := by
  have hmat : (U + Uᴴ) * (U - Uᴴ) = (U - Uᴴ) * (U + Uᴴ) := by
    have e1 : (U + Uᴴ) * (U - Uᴴ) = U * U - Uᴴ * Uᴴ := by
      calc (U + Uᴴ) * (U - Uᴴ)
          = U * U - U * Uᴴ + (Uᴴ * U - Uᴴ * Uᴴ) := by noncomm_ring
        _ = U * U - Uᴴ * Uᴴ := by rw [hU, hU']; abel
    have e2 : (U - Uᴴ) * (U + Uᴴ) = U * U - Uᴴ * Uᴴ := by
      calc (U - Uᴴ) * (U + Uᴴ)
          = U * U + U * Uᴴ - (Uᴴ * U + Uᴴ * Uᴴ) := by noncomm_ring
        _ = U * U - Uᴴ * Uᴴ := by rw [hU, hU']; abel
    rw [e1, e2]
  unfold hermPart skewPart
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul,
    hmat]
  have hcoef : (-Complex.I / 2) * (1 / 2 : ℂ) = (1 / 2 : ℂ) * (-Complex.I / 2) := mul_comm _ _
  rw [hcoef]

/-- If a unitary conjugate of a diagonal matrix is unitary, every diagonal entry has squared
norm one. -/
theorem diag_normSq_of_unitary {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ)
    (hVl : V * Vᴴ = 1) (hVr : Vᴴ * V = 1)
    (hU : (V * Matrix.diagonal d * Vᴴ) * (V * Matrix.diagonal d * Vᴴ)ᴴ = 1) :
    ∀ j, Complex.normSq (d j) = 1 := by
  have hconj : (V * Matrix.diagonal d * Vᴴ)ᴴ = V * (Matrix.diagonal d)ᴴ * Vᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hconj] at hU
  have hDD : Matrix.diagonal d * (Matrix.diagonal d)ᴴ = 1 := by
    have key : (Matrix.diagonal d) * (Matrix.diagonal d)ᴴ
        = Vᴴ * ((V * Matrix.diagonal d * Vᴴ) * (V * (Matrix.diagonal d)ᴴ * Vᴴ)) * V := by
      calc (Matrix.diagonal d) * (Matrix.diagonal d)ᴴ
          = (Vᴴ * V) * Matrix.diagonal d * (Vᴴ * V) * (Matrix.diagonal d)ᴴ * (Vᴴ * V) := by
            rw [hVr]; noncomm_ring
        _ = Vᴴ * ((V * Matrix.diagonal d * Vᴴ) * (V * (Matrix.diagonal d)ᴴ * Vᴴ)) * V := by
            noncomm_ring
    rw [key, hU]
    simp [hVr]
  have hDD' : Matrix.diagonal (fun j => d j * star (d j)) = 1 := by
    have h := hDD
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal] at h
    exact h
  intro j
  have h : d j * star (d j) = 1 := by
    have hh := congrArg (fun X : Matrix (Fin n) (Fin n) ℂ => X j j) hDD'
    simpa [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] using! hh
  have hns : (Complex.normSq (d j) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    rw [mul_comm]
    rw [Complex.star_def] at h
    exact h
  rwa [← Complex.ofReal_one, Complex.ofReal_inj] at hns

/-- Every finite unitary matrix has a unitary diagonalization whose diagonal entries have
squared norm one. -/
theorem unitary_diag {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ (V : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℂ),
      V ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      (∀ j, Complex.normSq (lam j) = 1) ∧
      U = V * Matrix.diagonal lam * Vᴴ := by
  have hU1 : U * Uᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff.mp hU)
  have hU2 : Uᴴ * U = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff'.mp hU)
  let C : Bool → Matrix (Fin n) (Fin n) ℂ :=
    fun b => if b then skewPart U else hermPart U
  have hHerm : ∀ a, (C a).IsHermitian := by
    intro a
    cases a
    · simpa [C] using! hermPart_isHermitian U
    · simpa [C] using! skewPart_isHermitian U
  have hComm : ∀ a b, C a * C b = C b * C a := by
    intro a b
    cases a <;> cases b <;> simp [C, hermPart_comm_skewPart U hU1 hU2]
  obtain ⟨V, diag, hVl, hVr, hdiag⟩ :=
    exists_simultaneous_unitary_diagonalization C hHerm hComm
  have hVun : V ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    exact hVl
  let lam : Fin n → ℂ := fun j => (diag false j : ℂ) + Complex.I * (diag true j : ℂ)
  have h0 : hermPart U = V * Matrix.diagonal (fun i => (diag false i : ℂ)) * Vᴴ := by
    simpa [C] using! hdiag false
  have h1 : skewPart U = V * Matrix.diagonal (fun i => (diag true i : ℂ)) * Vᴴ := by
    simpa [C] using! hdiag true
  have hd1 : (fun i => Complex.I * (diag true i : ℂ))
      = Complex.I • (fun i => (diag true i : ℂ)) := by
    funext i; simp
  have hsmul : V * Matrix.diagonal (fun i => Complex.I * (diag true i : ℂ)) * Vᴴ
      = Complex.I • (V * Matrix.diagonal (fun i => (diag true i : ℂ)) * Vᴴ) := by
    rw [hd1, Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hUeq : U = V * Matrix.diagonal lam * Vᴴ := by
    have hdiagsum : Matrix.diagonal (fun i => (diag false i : ℂ))
        + Matrix.diagonal (fun i => Complex.I * (diag true i : ℂ)) = Matrix.diagonal lam := by
      rw [← Matrix.diagonal_add]
    rw [← hermPart_add_I_smul_skewPart U, h0, h1, ← hsmul]
    rw [← Matrix.add_mul, ← Matrix.mul_add, hdiagsum]
  refine ⟨V, lam, hVun, ?_, hUeq⟩
  have hdiagU : (V * Matrix.diagonal lam * Vᴴ) * (V * Matrix.diagonal lam * Vᴴ)ᴴ = 1 := by
    rw [← hUeq]; exact hU1
  exact diag_normSq_of_unitary V lam hVl hVr hdiagU

/-- The matrix selecting `U0` on the false Boolean sector and `U1` on the true sector. -/
def selectBlock {M : Type*} (U0 U1 : Matrix M M ℂ) : Matrix (Bool × M) (Bool × M) ℂ :=
  fun p q => if p.1 = q.1 then (if p.1 then U1 else U0) p.2 q.2 else 0

/-- Multiplication of two selector matrices multiplies the corresponding selected blocks. -/
theorem selectBlock_mul {M : Type*} [Fintype M]
    (A0 A1 B0 B1 : Matrix M M ℂ) :
    selectBlock A0 A1 * selectBlock B0 B1 = selectBlock (A0 * B0) (A1 * B1) := by
  ext ⟨s, i⟩ ⟨s', j⟩
  simp only [selectBlock, Matrix.mul_apply, Fintype.sum_prod_type]
  rcases s with _ | _ <;> rcases s' with _ | _ <;>
    simp [Fintype.sum_bool, Matrix.mul_apply]

/-- Selecting the diagonal phases `exp (-φ*I/2)` and `exp (φ*I/2)` equals the multiplexor of
`paperRz (φ c)`. See [ShendeBullockMarkov2006]. -/
theorem selectBlock_rz {M : Type*} [Fintype M] [DecidableEq M] (φ : M → ℝ) :
    selectBlock
        (Matrix.diagonal (fun c => Complex.exp (((-(φ c / 2) : ℝ) : ℂ) * Complex.I)))
        (Matrix.diagonal (fun c => Complex.exp ((((φ c / 2) : ℝ) : ℂ) * Complex.I)))
      = Matrix.blockDiagonal (fun c : M => paperRz (φ c)) := by
  ext ⟨s, i⟩ ⟨s', j⟩
  rcases s with _ | _ <;> rcases s' with _ | _ <;>
    by_cases hij : i = j <;>
    simp [selectBlock, Matrix.blockDiagonal_apply, paperRz, qubitEulerPhase_apply, hij]
  all_goals (congr 1; ring)

/-- A selector of two unitary matrices factors into repeated unitary blocks, a Z-rotation
multiplexor, and repeated unitary blocks. See [ShendeBullockMarkov2006]. -/
theorem theorem12_demultiplex {n : ℕ}
    (U0 U1 : Matrix (Fin n) (Fin n) ℂ)
    (hU0 : U0 ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hU1 : U1 ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ (V W : Matrix (Fin n) (Fin n) ℂ) (φ : Fin n → ℝ),
      V ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ W ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      selectBlock U0 U1 =
        selectBlock V V *
          Matrix.blockDiagonal (fun c : Fin n => paperRz (φ c)) *
          selectBlock W W := by
  have hU1' : U1ᴴ * U1 = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff'.mp hU1)
  have hU1c : U1ᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
    exact hU1'
  have hA : U0 * U1ᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    mul_mem_unitaryGroup hU0 hU1c
  obtain ⟨V, lam, hVun, hlam, hAeq⟩ := unitary_diag (U0 * U1ᴴ) hA

  have hlamnorm : ∀ j, ‖lam j‖ = 1 := by
    intro j
    have hsq : ‖lam j‖ ^ 2 = 1 := by
      have h := Complex.normSq_eq_norm_sq (lam j)
      rw [hlam j] at h
      linarith
    rcases sq_eq_one_iff.mp hsq with h | h
    · exact h
    · have hnn := norm_nonneg (lam j)
      rw [h] at hnn
      linarith
  have hz : ∀ j, lam j ∈ Metric.sphere (0 : ℂ) 1 := by
    intro j
    rw [Metric.mem_sphere, dist_zero_right]
    exact hlamnorm j
  set ψ : Fin n → ℝ := fun j => Complex.arg (lam j) with hψdef
  have hψ : ∀ j, Complex.exp ((ψ j : ℂ) * Complex.I) = lam j := by
    intro j
    have h := Circle.exp_arg (⟨lam j, hz j⟩ : Circle)
    have hc : (Circle.exp (ψ j) : ℂ) = lam j := by
      rw [h]
    exact hc

  set μ : Fin n → ℂ := fun j => Complex.exp (((ψ j / 2 : ℝ) : ℂ) * Complex.I) with hμdef
  have hμc : ∀ j, μ j = Complex.exp (((ψ j / 2 : ℝ) : ℂ) * Complex.I) := by
    intro j; simp only [hμdef]
  have hμsq : ∀ j, μ j * μ j = lam j := by
    intro j
    have ha : (((ψ j / 2 : ℝ) : ℂ) * Complex.I) + (((ψ j / 2 : ℝ) : ℂ) * Complex.I)
        = ((ψ j : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hμc j, ← Complex.exp_add, ha, hψ j]
  have hμnorm : ∀ j, ‖μ j‖ = 1 := by
    intro j
    rw [hμc j]
    exact Complex.norm_exp_ofReal_mul_I (ψ j / 2)
  have hμns : ∀ j, Complex.normSq (μ j) = 1 := by
    intro j
    rw [Complex.normSq_eq_norm_sq, hμnorm j]
    norm_num
  have hD : Matrix.diagonal μ * Matrix.diagonal μ = Matrix.diagonal lam := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    exact hμsq j
  have hμstar : ∀ j, μ j * star (μ j) = 1 := by
    intro j
    have h : (Complex.normSq (μ j) : ℂ) = 1 := by rw [hμns j]; norm_num
    rw [Complex.normSq_eq_conj_mul_self, mul_comm] at h
    rw [Complex.star_def]
    exact h
  have hμstar' : ∀ j, star (μ j) * μ j = 1 := by
    intro j
    have h : (Complex.normSq (μ j) : ℂ) = 1 := by rw [hμns j]; norm_num
    rw [Complex.normSq_eq_conj_mul_self] at h
    rw [Complex.star_def]
    exact h
  have hDU : Matrix.diagonal μ * (Matrix.diagonal μ)ᴴ = 1 := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    rw [show (fun i => μ i * star μ i) = (fun _ => (1 : ℂ)) from funext hμstar,
      Matrix.diagonal_one]
  have hUD : (Matrix.diagonal μ)ᴴ * Matrix.diagonal μ = 1 := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    rw [show (fun i => star μ i * μ i) = (fun _ => (1 : ℂ)) from funext hμstar',
      Matrix.diagonal_one]
  have hVl : V * Vᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff.mp hVun)
  have hVr : Vᴴ * V = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff'.mp hVun)
  refine ⟨V, Matrix.diagonal μ * Vᴴ * U1, fun j => -ψ j, hVun, ?_, ?_⟩
  · refine mul_mem_unitaryGroup (mul_mem_unitaryGroup ?_ ?_) hU1
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]; exact hDU
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose]; exact hVr
  · have hAB : selectBlock U0 U1
        = selectBlock (V * Matrix.diagonal μ * (Matrix.diagonal μ * Vᴴ * U1))
            (V * (Matrix.diagonal μ)ᴴ * (Matrix.diagonal μ * Vᴴ * U1)) := by
      congr 1
      · calc U0 = U0 * (U1ᴴ * U1) := by rw [hU1', Matrix.mul_one]
          _ = (U0 * U1ᴴ) * U1 := by rw [Matrix.mul_assoc]
          _ = (V * Matrix.diagonal μ * Matrix.diagonal μ * Vᴴ) * U1 := by
            rw [hAeq, ← hD]; simp only [Matrix.mul_assoc]
          _ = V * Matrix.diagonal μ * (Matrix.diagonal μ * Vᴴ * U1) := by
            simp only [Matrix.mul_assoc]
      · calc U1 = (V * Vᴴ) * U1 := by rw [hVl, Matrix.one_mul]
          _ = V * (Vᴴ * U1) := by rw [Matrix.mul_assoc]
          _ = V * (((Matrix.diagonal μ)ᴴ * Matrix.diagonal μ) * (Vᴴ * U1)) := by
            rw [hUD, Matrix.one_mul]
          _ = V * (Matrix.diagonal μ)ᴴ * (Matrix.diagonal μ * Vᴴ * U1) := by
            simp only [Matrix.mul_assoc]
    have hsecond : (Matrix.diagonal μ)ᴴ
        = Matrix.diagonal (fun c : Fin n => Complex.exp ((((-ψ c) / 2 : ℝ) : ℂ) * Complex.I)) := by
      rw [Matrix.diagonal_conjTranspose]
      congr 1
      funext c
      show star (μ c) = Complex.exp ((((-ψ c) / 2 : ℝ) : ℂ) * Complex.I)
      have hμc' : μ c = Complex.exp (((ψ c / 2 : ℝ) : ℂ) * Complex.I) := by
        simp only [hμdef]
      rw [hμc', Complex.star_def, ← Complex.exp_conj]
      congr 1
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    have hfirst : Matrix.diagonal μ
        = Matrix.diagonal (fun c : Fin n => Complex.exp (((-((-ψ c) / 2) : ℝ) : ℂ) * Complex.I)) := by
      congr 1
      funext c
      rw [hμc c]
      congr 1
      push_cast
      ring
    rw [hAB, ← selectBlock_rz (fun j => -ψ j), ← hfirst, ← hsecond,
      selectBlock_mul, selectBlock_mul]

/-- Given the stated cosine-sine factorization with unitary outer blocks, `U` has a quantum
Shannon factorization with two Z-rotation multiplexors surrounding the given Y-rotation
multiplexor and four repeated unitary blocks. See [ShendeBullockMarkov2006]. -/
theorem theorem13_qsd_of_csd {n : ℕ}
    (U : Matrix (Bool × Fin n) (Bool × Fin n) ℂ)
    (A1 B1 A2 B2 : Matrix (Fin n) (Fin n) ℂ) (ψ : Fin n → ℝ)
    (hA1 : A1 ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hB1 : B1 ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hA2 : A2 ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hB2 : B2 ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hCSD : U = selectBlock A1 B1 *
        Matrix.blockDiagonal (fun c : Fin n => paperRy (ψ c)) *
        selectBlock A2 B2) :
    ∃ (V1 W1 V2 W2 : Matrix (Fin n) (Fin n) ℂ) (φ1 φ2 : Fin n → ℝ),
      V1 ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ W1 ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      V2 ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ W2 ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      U = selectBlock V1 V1 *
            Matrix.blockDiagonal (fun c : Fin n => paperRz (φ1 c)) *
            selectBlock W1 W1 *
            Matrix.blockDiagonal (fun c : Fin n => paperRy (ψ c)) *
            selectBlock V2 V2 *
            Matrix.blockDiagonal (fun c : Fin n => paperRz (φ2 c)) *
            selectBlock W2 W2 := by
  obtain ⟨V1, W1, φ1, hV1, hW1, h1⟩ := theorem12_demultiplex A1 B1 hA1 hB1
  obtain ⟨V2, W2, φ2, hV2, hW2, h2⟩ := theorem12_demultiplex A2 B2 hA2 hB2
  refine ⟨V1, W1, V2, W2, φ1, φ2, hV1, hW1, hV2, hW2, ?_⟩
  rw [hCSD, h1, h2]
  noncomm_ring

end Qatlib.Papers.QLogicSynth04.MainResults
