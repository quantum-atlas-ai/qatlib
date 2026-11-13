/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Matrix

set_option backward.isDefEq.respectTransparency false

/-!
# Continuous Hermitianization of line-gapped non-Hermitian matrices

This file formalizes Theorem 5.1 (p. 112; Appendix D, Eqs. (D1)–(D13), pp. 159–160) of
[Ashida, Gong, and Ueda, 2020][AshidaGongUeda2020] at a fixed momentum point:

* If a complex matrix `H` has a **real line gap** (`∀ μ ∈ Λ(H), Re μ ≠ 0`), then `H` can be
  connected to a Hermitian matrix by a continuous path `path : ℝ → Matrix ι ι ℂ` with
  `path 0 = H`, `(path 1).IsHermitian`, and `RealLineGap ι (path t)` for all `t ∈ [0, 1]`.
* If `H` has an **imaginary line gap** (`∀ μ ∈ Λ(H), Im μ ≠ 0`), then `H` can be connected to an
  anti-Hermitian matrix (`Aᴴ = -A`) by a continuous path preserving `ImagLineGap` on `[0, 1]`.

We construct the deformation explicitly via Schur unitary upper-triangularization `H = U T Uᴴ`:
linearly interpolating off-diagonal entries of `T` to `0` and diagonal entries `Tᵢᵢ` to
`Re(Tᵢᵢ)` preserves upper-triangularity and keeps `Re(T(t)ᵢᵢ) = Re(Tᵢᵢ) ≠ 0` constant for all
`t ∈ [0, 1]`, reaching the Hermitian endpoint `U diag(Re Tᵢᵢ) Uᴴ` at `t = 1`.

## Main statements

* `RealLineGap` / `ImagLineGap` / `AntiHermitian`: spectral line-gap and anti-Hermitian predicates.
* `theorem_5_1_line_gap_hermitianization`: continuous gap-preserving deformation to a Hermitian
  (resp. anti-Hermitian) matrix (Theorem 5.1).

## References

* [Ashida, Gong, and Ueda, 2020][AshidaGongUeda2020]
-/

set_option autoImplicit false
noncomputable section

open Matrix Module
open scoped BigOperators

namespace Qatlib.Papers.NonHermitian20.GapClassify

/-- A real line gap: no eigenvalue of `A` has zero real part. -/
def RealLineGap (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : Prop :=
  ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' A) μ → μ.re ≠ 0

/-- An imaginary line gap: no eigenvalue of `A` has zero imaginary part. -/
def ImagLineGap (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : Prop :=
  ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' A) μ → μ.im ≠ 0

/-- Anti-Hermitian matrix predicate: `Aᴴ = -A`. -/
def AntiHermitian (ι : Type) (A : Matrix ι ι ℂ) : Prop :=
  Matrix.conjTranspose A = -A

/-- Schur unitary upper-triangularization on `Fin n`: every complex `n × n` matrix `A` factors as
`U * T * Uᴴ` with `Uᴴ * U = 1`, `U * Uᴴ = 1`, and `T` upper triangular. -/
private theorem schur_fin : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
    ∃ (U T : Matrix (Fin n) (Fin n) ℂ),
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ T.IsUpperTriangular ∧ A = U * T * Uᴴ
  | 0, A => by
    refine ⟨1, 0, by simp, by simp, fun i _ _ => i.elim0, ?_⟩
    ext i j
    exact i.elim0
  | n + 1, A => by
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' A)
    obtain ⟨v, hv_mem, hv_ne⟩ := (Submodule.ne_bot_iff _).mp hμ
    have hv_eig : A *ᵥ v = μ • v := Module.End.mem_eigenspace_iff.mp hv_mem
    let v_lp : EuclideanSpace ℂ (Fin (n + 1)) := WithLp.toLp 2 v
    have hv_lp_ne : v_lp ≠ 0 := by
      intro h0
      apply hv_ne
      ext k
      exact congrFun (congrArg WithLp.ofLp h0) k
    have hv_pos : 0 < ‖v_lp‖ := norm_pos_iff.mpr hv_lp_ne
    let u₀ : EuclideanSpace ℂ (Fin (n + 1)) := ((‖v_lp‖⁻¹ : ℝ) : ℂ) • v_lp
    have hu₀_norm : ‖u₀‖ = 1 := by
      simp only [u₀, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hv_pos.le)]
      exact inv_mul_cancel₀ hv_pos.ne'
    have hu₀_eig : A *ᵥ u₀.ofLp = μ • u₀.ofLp := by
      change A *ᵥ (((‖v_lp‖⁻¹ : ℝ) : ℂ) • v) = μ • (((‖v_lp‖⁻¹ : ℝ) : ℂ) • v)
      rw [Matrix.mulVec_smul, hv_eig, smul_comm]
    let s0 : Set (Fin (n + 1)) := {0}
    have hon : Orthonormal ℂ (s0.domRestrict (fun _ : Fin (n + 1) => u₀)) :=
      ⟨fun ⟨_, _⟩ => hu₀_norm, fun ⟨_, hi⟩ ⟨_, hj⟩ hij =>
        False.elim (hij (Subtype.ext (hi.trans hj.symm)))⟩
    obtain ⟨b, hb0⟩ := hon.exists_orthonormalBasis_extension_of_card_eq
      (finrank_euclideanSpace (𝕜 := ℂ) (ι := Fin (n + 1)))
    have hb_zero : b 0 = u₀ := hb0 0 (Set.mem_singleton 0)
    let V₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun i j => (b j).ofLp i
    have hV₁_iso : V₁ᴴ * V₁ = 1 := by
      ext i j
      have hinner : (V₁ᴴ * V₁) i j = inner ℂ (b i) (b j) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp only [V₁, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Pi.star_apply]
        refine Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [hinner, orthonormal_iff_ite.mp b.orthonormal, Matrix.one_apply]
    have hV₁_coiso : V₁ * V₁ᴴ = 1 := mul_eq_one_comm.mp hV₁_iso
    let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := V₁ᴴ * A * V₁
    have hB_col0 : ∀ i : Fin n, B i.succ 0 = 0 := by
      intro i
      have hcol : (A * V₁) = fun r c => (A *ᵥ (fun k => V₁ k c)) r := by
        ext r c
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      have hAv0 : (fun k => V₁ k 0) = u₀.ofLp := by
        ext k
        simp [V₁, hb_zero]
      have h1 : B i.succ 0 = ∑ k : Fin (n + 1), star ((b i.succ).ofLp k) * (A *ᵥ u₀.ofLp) k := by
        simp only [B, Matrix.mul_assoc, Matrix.mul_apply, Matrix.conjTranspose_apply]
        rw [← hAv0]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [Matrix.mulVec, dotProduct, V₁]
      rw [h1, hu₀_eig]
      have horth : inner ℂ (b i.succ) (b 0) = 0 :=
        b.orthonormal.2 (Fin.succ_ne_zero i)
      rw [hb_zero, EuclideanSpace.inner_eq_star_dotProduct] at horth
      have hsum : (∑ k : Fin (n + 1), star ((b i.succ).ofLp k) * (μ • u₀.ofLp) k) =
          μ * (u₀.ofLp ⬝ᵥ star (b i.succ).ofLp) := by
        simp only [Pi.smul_apply, smul_eq_mul, dotProduct, Pi.star_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [hsum, horth, mul_zero]
    let A' : Matrix (Fin n) (Fin n) ℂ := fun i j => B i.succ j.succ
    obtain ⟨U', T', hU'_iso, hU'_coiso, hT'_ut, hA'_eq⟩ := schur_fin n A'
    let V₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun i j =>
      Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => U' i' j') j) i
    have hV₂_iso : V₂ᴴ * V₂ = 1 := by
      ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_succ]
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
      · simp [V₂]
      · simp [V₂, (Fin.succ_ne_zero j').symm]
      · simp [V₂]
      · simp only [V₂, Matrix.conjTranspose_apply, Fin.cases_zero, Fin.cases_succ, mul_zero,
          zero_add, Matrix.one_apply, Fin.succ_inj]
        exact congrFun (congrFun hU'_iso i') j'
    have hV₂_coiso : V₂ * V₂ᴴ = 1 := mul_eq_one_comm.mp hV₂_iso
    let U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := V₁ * V₂
    let T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := V₂ᴴ * B * V₂
    have hU_iso : Uᴴ * U = 1 := by
      dsimp [U]
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc V₁ᴴ, hV₁_iso,
        Matrix.one_mul, hV₂_iso]
    have hU_coiso : U * Uᴴ = 1 := mul_eq_one_comm.mp hU_iso
    have hT_ut : T.IsUpperTriangular := by
      intro i j hij
      refine Fin.cases (fun h => (Fin.not_lt_zero j h).elim) (fun i' hij' => ?_) i hij
      refine Fin.cases ?_ (fun j' hij'' => ?_) j hij'
      · -- `T i'.succ 0 = 0`
        simp only [T, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, V₂,
          Fin.cases_zero, Fin.cases_succ, mul_one, mul_zero, add_zero, Finset.sum_const_zero]
        -- Expand `∑ x : Fin n, star (U' x i') * B x.succ 0`
        simp [hB_col0]
      · -- `T i'.succ j'.succ = T' i' j' = 0`
        have hjlt : j' < i' := Fin.succ_lt_succ_iff.mp hij''
        have hblock : T i'.succ j'.succ = (U'ᴴ * A' * U') i' j' := by
          simp only [T, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, V₂,
            Fin.cases_zero, Fin.cases_succ, star_zero, zero_mul, mul_zero, zero_add, A']
        have hT'_eq : U'ᴴ * A' * U' = T' := by
          rw [hA'_eq]
          calc U'ᴴ * (U' * T' * U'ᴴ) * U'
              = (U'ᴴ * U') * T' * (U'ᴴ * U') := by simp [Matrix.mul_assoc]
            _ = T' := by rw [hU'_iso, Matrix.one_mul, Matrix.mul_one]
        rw [hblock, hT'_eq]
        exact hT'_ut hjlt
    have hA_eq : A = U * T * Uᴴ := by
      dsimp [U, T, B]
      calc A = (V₁ * V₁ᴴ) * A * (V₁ * V₁ᴴ) := by rw [hV₁_coiso, Matrix.one_mul, Matrix.mul_one]
        _ = V₁ * (V₂ * V₂ᴴ) * (V₁ᴴ * A * V₁) * (V₂ * V₂ᴴ) * V₁ᴴ := by
            rw [hV₂_coiso]
            simp [Matrix.mul_assoc]
        _ = (V₁ * V₂) * (V₂ᴴ * (V₁ᴴ * A * V₁) * V₂) * (V₁ * V₂)ᴴ := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    exact ⟨U, T, hU_iso, hU_coiso, hT_ut, hA_eq⟩

/-- Eigenvalues of an upper-triangular matrix on `Fin n` are precisely its diagonal entries. -/
private lemma hasEigenvalue_of_isUpperTriangular {n : ℕ} {S : Matrix (Fin n) (Fin n) ℂ}
    (hS : S.IsUpperTriangular) (μ : ℂ) :
    Module.End.HasEigenvalue (Matrix.toLin' S) μ ↔ ∃ i : Fin n, S i i = μ := by
  have hequiv : Module.End.HasEigenvalue (Matrix.toLin' S) μ ↔
      ∃ v : Fin n → ℂ, v ≠ 0 ∧ (S - μ • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v = 0 := by
    rw [Module.End.HasEigenvalue, Module.End.HasUnifEigenvalue, Submodule.ne_bot_iff]
    constructor
    · rintro ⟨v, hv_mem, hv_ne⟩
      have hv : S *ᵥ v = μ • v := Module.End.mem_eigenspace_iff.mp hv_mem
      refine ⟨v, hv_ne, ?_⟩
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hv, sub_self]
    · rintro ⟨v, hv_ne, hv0⟩
      refine ⟨v, Module.End.mem_eigenspace_iff.mpr ?_, hv_ne⟩
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hv0
      exact sub_eq_zero.mp hv0
  have hut_sub : (S - μ • (1 : Matrix (Fin n) (Fin n) ℂ)).IsUpperTriangular := by
    intro i j hij
    have hne : i ≠ j := ne_of_gt hij
    simp [hS hij, hne]
  rw [hequiv]
  have hdet : (∃ v : Fin n → ℂ, v ≠ 0 ∧ (S - μ • 1) *ᵥ v = 0) ↔
      (S - μ • (1 : Matrix (Fin n) (Fin n) ℂ)).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
  rw [hdet, Matrix.det_of_isUpperTriangular hut_sub, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

/-- Eigenvalues are invariant under unitary similarity + index equivalence `e : ι ≃ Fin n`. -/
private lemma hasEigenvalue_conj_submatrix {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (e : ι ≃ Fin n) {U S : Matrix (Fin n) (Fin n) ℂ} (hU_iso : Uᴴ * U = 1) (hU_coiso : U * Uᴴ = 1)
    (μ : ℂ) :
    Module.End.HasEigenvalue (Matrix.toLin' ((U * S * Uᴴ).submatrix e e)) μ ↔
      Module.End.HasEigenvalue (Matrix.toLin' S) μ := by
  have hvec : ∀ M : Matrix ι ι ℂ,
      Module.End.HasEigenvalue (Matrix.toLin' M) μ ↔ ∃ v : ι → ℂ, v ≠ 0 ∧ M *ᵥ v = μ • v := by
    intro M
    rw [Module.End.HasEigenvalue, Module.End.HasUnifEigenvalue, Submodule.ne_bot_iff]
    constructor
    · rintro ⟨v, hv, hne⟩
      exact ⟨v, hne, Module.End.mem_eigenspace_iff.mp hv⟩
    · rintro ⟨v, hne, hv⟩
      exact ⟨v, Module.End.mem_eigenspace_iff.mpr hv, hne⟩
  have hvec_fin : Module.End.HasEigenvalue (Matrix.toLin' S) μ ↔
      ∃ w : Fin n → ℂ, w ≠ 0 ∧ S *ᵥ w = μ • w := by
    rw [Module.End.HasEigenvalue, Module.End.HasUnifEigenvalue, Submodule.ne_bot_iff]
    constructor
    · rintro ⟨w, hw, hne⟩
      exact ⟨w, hne, Module.End.mem_eigenspace_iff.mp hw⟩
    · rintro ⟨w, hne, hw⟩
      exact ⟨w, Module.End.mem_eigenspace_iff.mpr hw, hne⟩
  rw [hvec, hvec_fin]
  constructor
  · rintro ⟨v, hv_ne, hv_eig⟩
    let v' : Fin n → ℂ := v ∘ e.symm
    have hv'_eig : (U * S * Uᴴ) *ᵥ v' = μ • v' := by
      ext i
      have h := congrFun hv_eig (e.symm i)
      simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.smul_apply, v',
        Function.comp_apply, e.apply_symm_apply] at h ⊢
      rw [← h]
      have hsum := Equiv.sum_comp e (fun x => (U * S * Uᴴ) i x * v (e.symm x))
      simp only [e.symm_apply_apply] at hsum
      exact hsum.symm
    let w : Fin n → ℂ := Uᴴ *ᵥ v'
    have hw_ne : w ≠ 0 := by
      intro hw0
      apply hv_ne
      ext x
      have hv'0 : v' = 0 := by
        calc v' = (U * Uᴴ) *ᵥ v' := by rw [hU_coiso, Matrix.one_mulVec]
          _ = U *ᵥ w := (Matrix.mulVec_mulVec v' U Uᴴ).symm
          _ = 0 := by rw [hw0, Matrix.mulVec_zero]
      have hx := congrFun hv'0 (e x)
      simpa [v'] using hx
    refine ⟨w, hw_ne, ?_⟩
    calc S *ᵥ w = ((Uᴴ * U) * (S * Uᴴ)) *ᵥ v' := by
          rw [hU_iso, Matrix.one_mul]
          dsimp [w]
          exact Matrix.mulVec_mulVec v' S Uᴴ
      _ = Uᴴ *ᵥ ((U * S * Uᴴ) *ᵥ v') := by
          rw [Matrix.mulVec_mulVec]
          simp [Matrix.mul_assoc]
      _ = μ • w := by rw [hv'_eig, Matrix.mulVec_smul]
  · rintro ⟨w, hw_ne, hw_eig⟩
    let u : Fin n → ℂ := U *ᵥ w
    have hu_eig : (U * S * Uᴴ) *ᵥ u = μ • u := by
      calc (U * S * Uᴴ) *ᵥ u = U *ᵥ (S *ᵥ ((Uᴴ * U) *ᵥ w)) := by
            simp [u, Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = μ • u := by rw [hU_iso, Matrix.one_mulVec, hw_eig, Matrix.mulVec_smul]
    let v : ι → ℂ := u ∘ e
    have hv_ne : v ≠ 0 := by
      intro hv0
      apply hw_ne
      have hu0 : u = 0 := by
        ext i
        simpa [v, e.apply_symm_apply] using congrFun hv0 (e.symm i)
      calc w = (Uᴴ * U) *ᵥ w := by rw [hU_iso, Matrix.one_mulVec]
        _ = Uᴴ *ᵥ u := (Matrix.mulVec_mulVec w Uᴴ U).symm
        _ = 0 := by rw [hu0, Matrix.mulVec_zero]
    refine ⟨v, hv_ne, ?_⟩
    ext x
    have h := congrFun hu_eig (e x)
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.smul_apply, v,
      Function.comp_apply] at h ⊢
    rw [← h]
    exact Equiv.sum_comp e (fun j => (U * S * Uᴴ) (e x) j * u j)

/-- **Theorem 5.1** ([Ashida, Gong, and Ueda, 2020][AshidaGongUeda2020], p. 112; Appendix D,
Eqs. (D1)–(D13)): every complex matrix with a real (resp. imaginary) line gap admits a continuous
deformation to a Hermitian (resp. anti-Hermitian) matrix that preserves the real (resp. imaginary)
line gap throughout `t ∈ [0, 1]`. -/
theorem theorem_5_1_line_gap_hermitianization (ι : Type) [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) :
    (RealLineGap ι H →
        ∃ path : ℝ → Matrix ι ι ℂ,
          Continuous path ∧ path 0 = H ∧ (path 1).IsHermitian ∧
            ∀ t ∈ Set.Icc (0 : ℝ) 1, RealLineGap ι (path t)) ∧
      (ImagLineGap ι H →
        ∃ path : ℝ → Matrix ι ι ℂ,
          Continuous path ∧ path 0 = H ∧ AntiHermitian ι (path 1) ∧
            ∀ t ∈ Set.Icc (0 : ℝ) 1, ImagLineGap ι (path t)) := by
  have hreal_part : ∀ M : Matrix ι ι ℂ, RealLineGap ι M →
      ∃ path : ℝ → Matrix ι ι ℂ,
        Continuous path ∧ path 0 = M ∧ (path 1).IsHermitian ∧
          ∀ t ∈ Set.Icc (0 : ℝ) 1, RealLineGap ι (path t) := by
    intro M hgap
    let n : ℕ := Fintype.card ι
    let e : ι ≃ Fin n := Fintype.equivFin ι
    let A : Matrix (Fin n) (Fin n) ℂ := M.submatrix e.symm e.symm
    have hM_re : M = A.submatrix e e := by
      ext x y
      simp [A]
    obtain ⟨U, T, hU_iso, hU_coiso, hT_ut, hA_eq⟩ := schur_fin n A
    have hM_schur : M = (U * T * Uᴴ).submatrix e e := by
      rw [hM_re, hA_eq]
    have hdiag_re_ne : ∀ i : Fin n, (T i i).re ≠ 0 := by
      intro i
      apply hgap (T i i)
      rw [hM_schur, hasEigenvalue_conj_submatrix e hU_iso hU_coiso,
        hasEigenvalue_of_isUpperTriangular hT_ut]
      exact ⟨i, rfl⟩
    let S : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t i j =>
      if i = j then ((1 - t : ℝ) : ℂ) * T i i + (t : ℂ) * ((T i i).re : ℂ)
      else ((1 - t : ℝ) : ℂ) * T i j
    let path : ℝ → Matrix ι ι ℂ := fun t => (U * S t * Uᴴ).submatrix e e
    have hS_cont : Continuous S := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      dsimp [S]
      by_cases hij : i = j
      · simp only [hij, ↓reduceIte]
        exact ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).mul
          continuous_const).add (Complex.continuous_ofReal.mul continuous_const)
      · simp only [hij, ↓reduceIte]
        exact (Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).mul
          continuous_const
    have hpath_cont : Continuous path := by
      refine continuous_pi fun x => continuous_pi fun y => ?_
      simp only [path, Matrix.submatrix_apply, Matrix.mul_apply]
      refine continuous_finsetSum _ fun k _ => ?_
      refine (continuous_finsetSum _ fun l _ => ?_).mul continuous_const
      exact continuous_const.mul
        (show Continuous (fun t => S t l k) from
          (continuous_apply k).comp ((continuous_apply l).comp hS_cont))
    have hpath0 : path 0 = M := by
      have hS0 : S 0 = T := by
        ext i j
        by_cases hij : i = j <;> simp [S, hij]
      simp [path, hS0, hM_schur]
    have hpath1 : (path 1).IsHermitian := by
      have hS1_herm : (S 1).IsHermitian := by
        ext i j
        by_cases hij : i = j
        · subst hij
          simp [S]
        · have hji : j ≠ i := Ne.symm hij
          simp [S, hij, hji]
      ext x y
      have hU_herm : (U * S 1 * Uᴴ)ᴴ = U * S 1 * Uᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          hS1_herm.eq, Matrix.mul_assoc]
      exact congrFun (congrFun hU_herm (e x)) (e y)
    have hpath_gap : ∀ t ∈ Set.Icc (0 : ℝ) 1, RealLineGap ι (path t) := by
      intro t _ μ hμ
      have hSt_ut : (S t).IsUpperTriangular := by
        intro i j hij
        have hne : i ≠ j := ne_of_gt hij
        simp [S, hT_ut hij, hne]
      rw [hasEigenvalue_conj_submatrix e hU_iso hU_coiso,
        hasEigenvalue_of_isUpperTriangular hSt_ut] at hμ
      obtain ⟨i, rfl⟩ := hμ
      have hre : (S t i i).re = (T i i).re := by
        simp only [S, ↓reduceIte, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero]
        ring
      rw [hre]
      exact hdiag_re_ne i
    exact ⟨path, hpath_cont, hpath0, hpath1, hpath_gap⟩
  refine ⟨hreal_part H, ?_⟩
  intro himag
  let M : Matrix ι ι ℂ := (-Complex.I) • H
  have hM_gap : RealLineGap ι M := by
    intro μ hμ
    obtain ⟨v, hv_mem, hv_ne⟩ := (Submodule.ne_bot_iff _).mp hμ
    have hv_eig : ((-Complex.I) • H) *ᵥ v = μ • v := Module.End.mem_eigenspace_iff.mp hv_mem
    have hH_eig : H *ᵥ v = (Complex.I * μ) • v := by
      rw [Matrix.smul_mulVec] at hv_eig
      calc H *ᵥ v = (Complex.I * (-Complex.I)) • (H *ᵥ v) := by simp
        _ = Complex.I • ((-Complex.I) • (H *ᵥ v)) := mul_smul _ _ _
        _ = Complex.I • (μ • v) := by rw [hv_eig]
        _ = (Complex.I * μ) • v := (mul_smul _ _ _).symm
    have hH_has : Module.End.HasEigenvalue (Matrix.toLin' H) (Complex.I * μ) :=
      (Submodule.ne_bot_iff _).mpr ⟨v, Module.End.mem_eigenspace_iff.mpr hH_eig, hv_ne⟩
    have him := himag (Complex.I * μ) hH_has
    simpa [Complex.mul_im] using him
  obtain ⟨path', hcont', h0', hherm1', hgap'⟩ := hreal_part M hM_gap
  refine ⟨fun t => Complex.I • path' t, hcont'.const_smul Complex.I, ?_, ?_, ?_⟩
  · dsimp only
    rw [h0']
    dsimp [M]
    rw [← mul_smul]
    simp
  · unfold AntiHermitian
    rw [Matrix.conjTranspose_smul, hherm1'.eq]
    ext x y
    simp
  · intro t ht μ hμ
    obtain ⟨v, hv_mem, hv_ne⟩ := (Submodule.ne_bot_iff _).mp hμ
    have hv_eig : (Complex.I • path' t) *ᵥ v = μ • v := Module.End.mem_eigenspace_iff.mp hv_mem
    have hp_eig : path' t *ᵥ v = ((-Complex.I) * μ) • v := by
      rw [Matrix.smul_mulVec] at hv_eig
      calc path' t *ᵥ v = ((-Complex.I) * Complex.I) • (path' t *ᵥ v) := by simp
        _ = (-Complex.I) • (Complex.I • (path' t *ᵥ v)) := mul_smul _ _ _
        _ = (-Complex.I) • (μ • v) := by rw [hv_eig]
        _ = ((-Complex.I) * μ) • v := (mul_smul _ _ _).symm
    have hp_has : Module.End.HasEigenvalue (Matrix.toLin' (path' t)) ((-Complex.I) * μ) :=
      (Submodule.ne_bot_iff _).mpr ⟨v, Module.End.mem_eigenspace_iff.mpr hp_eig, hv_ne⟩
    have hre := hgap' t ht ((-Complex.I) * μ) hp_has
    simpa [Complex.mul_re] using hre

end Qatlib.Papers.NonHermitian20.GapClassify
