/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceTensorUpdate — the variational step as a generalized eigenvalue problem

Fixed source: F. Verstraete and J. I. Cirac, *Renormalization algorithms for
Quantum-Many Body Systems in two and higher dimensions*, arXiv:cond-mat/0407066v1
(2 Jul 2004), p. 3, Eq. (6):

  `E = x† H_eff x / x† N_eff x`  ("This expression can readily be minimized as it is
  equivalent to a generalized eigenvalue problem.")

PDF SHA-256 `397e011bc798dbb6aa2d4bf93f6d2e666a12f77fd0655e1168d03037d0af4da7`.

The optimization variable `x` collects the components of the single tensor
`A^{s}_{h̄,c̄}` being optimized, with all other tensors fixed.  The source claims
that stationarity of the energy quotient is the generalized eigenvalue equation
`H_eff x = λ N_eff x` with `λ = E(x)`.  Here we prove both directions at the level
of the first variation of the quotient, for arbitrary complex matrices `H_eff`,
`N_eff` (Hermiticity is not needed for the algebraic equivalence; for Hermitian
matrices the real part of the first variation is exactly the derivative of the
real energy).

Boundary: finite-dimensional matrix algebra only; we do not formalize how
`H_eff, N_eff` are assembled from the surrounding PEPS tensors (that is the
separate double-layer contraction claim), nor the sweeping order.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.RenormAlg04.MainResults.EigenUpdate

variable {m : ℕ}

/-- Matrix-vector product, written out to avoid notation imports. -/
def mv (M : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → ℂ) : Fin m → ℂ :=
  fun i => ∑ j, M i j * x j

/-- The identity matrix acts as the identity on vectors. -/
@[simp] theorem mv_one (x : Fin m → ℂ) :
    mv (1 : Matrix (Fin m) (Fin m) ℂ) x = x := by
  funext i
  unfold mv
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Ne.symm hji]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The quadratic form `x† M x` of Eq. (6). -/
noncomputable def qform (M : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → ℂ) : ℂ :=
  ∑ i, star (x i) * mv M x i

/-- Pairing `δ† w` of a vector `w` with a test direction `δ`. -/
noncomputable def qδ (w : Fin m → ℂ) (δ : Fin m → ℂ) : ℂ :=
  ∑ i, star (δ i) * w i

/-- The generalized eigenvalue equation `H_eff x = λ N_eff x` of Eq. (6). -/
def IsGenEigen (H N : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → ℂ) (lam : ℂ) : Prop :=
  ∀ i, mv H x i = lam * mv N x i

/-- The (complexified) first variation of the energy quotient `(x†Hx)/(x†Nx)` in the
direction `δ`; its real part is the derivative of the real quotient along `δ`. -/
noncomputable def firstVariation (H N : Matrix (Fin m) (Fin m) ℂ) (x δ : Fin m → ℂ) : ℂ :=
  qδ (mv H x) δ * qform N x - qform H x * qδ (mv N x) δ

/-- The quadratic form is the pairing of a vector with its matrix image. -/
@[simp] theorem qform_apply (M : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → ℂ) :
    qform M x = qδ (mv M x) x := rfl

/-- The pairing is additive in its vector argument. -/
theorem qδ_sub (w v : Fin m → ℂ) (δ : Fin m → ℂ) :
    qδ (fun i => w i - v i) δ = qδ w δ - qδ v δ := by
  unfold qδ
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib]

/-- The pairing is conjugate-linear in the test direction. -/
theorem qδ_smul_test (w δ : Fin m → ℂ) (c : ℂ) :
    qδ w (fun i => c * δ i) = star c * qδ w δ := by
  unfold qδ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [star_mul]
  ring

/-- The pairing is linear in its vector argument. -/
theorem qδ_mul_left (w δ : Fin m → ℂ) (c : ℂ) :
    qδ (fun i => c * w i) δ = c * qδ w δ := by
  unfold qδ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Testing the pairing against the coordinate direction at `k` reads off the `k`-th
component; this is how the generalized eigenvector equation is extracted. -/
theorem qδ_single (w : Fin m → ℂ) (k : Fin m) :
    qδ w (fun i => if i = k then (1 : ℂ) else 0) = w k := by
  unfold qδ
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hi
    simp [hi]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- A complex number whose real part vanishes, as does the real part after
multiplication by `I`, must be zero. -/
private theorem eq_zero_of_re_and_re_I_mul {z : ℂ} (h1 : z.re = 0)
    (h2 : (Complex.I * z).re = 0) : z = 0 := by
  apply Complex.ext
  · simpa using h1
  · have hIm : (Complex.I * z).re = -z.im := by
      rw [Complex.mul_re]
      simp
    rw [hIm] at h2
    simpa using neg_eq_zero.mp h2

/-- Source p. 3, Eq. (6): a direction is stationary for the energy quotient
`E(x) = x†Hx / x†Nx` (`x ≠ 0`, `x†Nx ≠ 0`) exactly when `x` satisfies the
generalized eigenvalue equation `H x = E(x) N x`. -/
theorem stationarity_iff_generalized_eigen
    (H N : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → ℂ)
    (hx : x ≠ 0) (hNx : qform N x ≠ 0) :
    (∀ δ : Fin m → ℂ, (firstVariation H N x δ).re = 0) ↔
      IsGenEigen H N x (qform H x / qform N x) := by
  set lam : ℂ := qform H x / qform N x with hlamdef
  have hlam_mul : lam * qform N x = qform H x := by
    rw [hlamdef, div_mul_cancel₀ _ hNx]
  constructor
  · intro hstat i
    -- Stationarity in every complex direction: the whole first variation vanishes.
    have hZall : ∀ δ : Fin m → ℂ, firstVariation H N x δ = 0 := by
      intro δ
      have hre : (firstVariation H N x δ).re = 0 := hstat δ
      have him : (Complex.I * firstVariation H N x δ).re = 0 := by
        have h2' : (firstVariation H N x (fun j => Complex.I * δ j)).re = 0 :=
          hstat (fun j => Complex.I * δ j)
        have hvar : firstVariation H N x (fun j => Complex.I * δ j)
            = (-Complex.I) * firstVariation H N x δ := by
          unfold firstVariation
          rw [qδ_smul_test, qδ_smul_test, Complex.star_def, Complex.conj_I]
          ring
        rw [hvar] at h2'
        rw [neg_mul] at h2'
        have h3 : -((Complex.I * firstVariation H N x δ).re) = 0 := by
          simpa using h2'
        exact neg_eq_zero.mp h3
      exact eq_zero_of_re_and_re_I_mul hre him
    -- Hence the ratio identity holds in every test direction.
    have hdiv : ∀ δ : Fin m → ℂ, qδ (mv H x) δ = lam * qδ (mv N x) δ := by
      intro δ
      have hZ : firstVariation H N x δ = 0 := hZall δ
      have hZ' : qδ (mv H x) δ * qform N x = qform H x * qδ (mv N x) δ := by
        have h := hZ
        unfold firstVariation at h
        exact sub_eq_zero.mp h
      rw [hlamdef]
      rw [div_mul_eq_mul_div]
      exact (eq_div_iff hNx).mpr hZ'
    -- Test with the coordinate direction at `i` to read off the `i`-th component.
    have hcoord : qδ (fun j => mv H x j - lam * mv N x j)
        (fun j => if j = i then (1 : ℂ) else 0) = 0 := by
      rw [qδ_sub, qδ_mul_left, hdiv]
      ring
    have hsingle := hcoord
    rw [qδ_single] at hsingle
    exact sub_eq_zero.mp hsingle
  · intro heig δ
    have hmv : mv H x = fun i => lam * mv N x i := funext heig
    have hH : qδ (mv H x) δ = lam * qδ (mv N x) δ := by
      rw [hmv, qδ_mul_left]
    unfold firstVariation
    have hid : qδ (mv H x) δ * qform N x - qform H x * qδ (mv N x) δ = 0 := by
      rw [hH, ← hlam_mul]
      ring
    rw [hid]
    simp

/-- Source p. 3, Eq. (6): a generalized eigenvector `H x = λ N x` with `x†Nx ≠ 0`
has quotient value exactly the eigenvalue `λ`; this is why minimizing the quotient
may be replaced by the generalized eigenvalue problem. -/
theorem energyQuotient_eq_eigenvalue
    (H N : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → ℂ) (lam : ℂ)
    (heig : IsGenEigen H N x lam) (hNx : qform N x ≠ 0) :
    qform H x / qform N x = lam := by
  have hq : qform H x = lam * qform N x := by
    unfold qform
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [heig i]
    ring
  rw [hq]
  exact mul_div_cancel_right₀ lam hNx

/-- With `N_eff` the identity the generalized eigenvalue problem of Eq. (6) reduces
to an ordinary eigenvalue problem `H x = λ x`. -/
theorem genEigen_one_iff (H : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → ℂ) (lam : ℂ) :
    IsGenEigen H 1 x lam ↔ mv H x = fun i => lam * x i := by
  unfold IsGenEigen
  constructor
  · intro h; funext i; rw [h i, mv_one]
  · intro h i; simpa using congrFun h i

/-- Source p. 3, Eq. (6) with a normalized state (`N_eff = 1`): stationarity in
every real direction is equivalent to the ordinary eigenvalue equation
`H x = E(x) x` with `E(x) = x†Hx / x†x`. -/
theorem stationarity_iff_ordinary_eigen (H : Matrix (Fin m) (Fin m) ℂ)
    (x : Fin m → ℂ) (hx : x ≠ 0) (h1 : qform (1 : Matrix (Fin m) (Fin m) ℂ) x ≠ 0) :
    (∀ δ : Fin m → ℂ, (firstVariation H 1 x δ).re = 0) ↔
      mv H x = fun i => (qform H x / qform (1 : Matrix (Fin m) (Fin m) ℂ) x) * x i := by
  rw [stationarity_iff_generalized_eigen H 1 x hx h1]
  exact genEigen_one_iff H x (qform H x / qform (1 : Matrix (Fin m) (Fin m) ℂ) x)

end Qatlib.Papers.RenormAlg04.MainResults.EigenUpdate
