/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.QueryComplexity.DegreeMethod.LocalCapability

/-!
# Fourier matrices and exact phase estimation

This module builds `QFTMatrix` from complex roots of unity and proves its unitarity and its
action on `PhaseState`. It defines the block-diagonal operator `ControlledPowers` and proves
exact phase kickback and readout when an eigenphase lies on the Fourier grid, following
[Kitaev1995].

The final lemmas express roots of unity as complex exponentials and establish the integer
periodicity identities used in phase readout.

## Main statements

* `qftMatrix_unitary`: unitarity of the normalized Fourier matrix for positive size.
* `controlledPowers_kickback`: creation of an eigenphase state from a uniform control state.
* `qpe_exact_readout`: exact grid-label readout with probability one.
* `qpe_exact_readout_linear`: exact readout extended to finite eigenstate combinations.

## References

* [Kitaev, 1995][Kitaev1995]
* [Magniez et al., 2011, Theorem 5][MagniezNayakRolandSantha2011]
-/

set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.SpectralFilter.PhaseReadout

open Matrix

variable {M : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

/-- The complex exponential `exp(2*π*I/M)` used as the Fourier root of unity. -/
noncomputable def primRoot (M : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (M : ℝ))

/-- For nonzero `M`, `primRoot M` is a primitive Mth root of unity. -/
theorem isPrimitiveRoot_primRoot (hM : M ≠ 0) : IsPrimitiveRoot (primRoot M) M := by
  unfold primRoot
  exact Complex.isPrimitiveRoot_exp M hM

/-- The Fourier root `primRoot M` is nonzero for every natural `M`. -/
theorem primRoot_ne_zero (M : ℕ) : primRoot M ≠ 0 := Complex.exp_ne_zero _

/-- The Fourier root `primRoot M` has complex norm one. -/
theorem norm_primRoot (M : ℕ) : ‖primRoot M‖ = 1 := by
  have h : primRoot M = Complex.exp ((Complex.ofReal (2 * Real.pi / (M : ℝ))) * Complex.I) := by
    unfold primRoot
    rw [show (2 * Real.pi * Complex.I / (M : ℝ))
          = (Complex.ofReal (2 * Real.pi / (M : ℝ))) * Complex.I by
      push_cast
      field_simp]
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- For positive `M`, an integer power of `primRoot M` equals one exactly when `M` divides the
exponent. -/
theorem primRoot_zpow_eq_one_iff (hM : 0 < M) (c : ℤ) :
    primRoot M ^ c = 1 ↔ (M : ℤ) ∣ c :=
  (isPrimitiveRoot_primRoot (Nat.pos_iff_ne_zero.mp hM)).zpow_eq_one_iff_dvd c

/-- For positive `M`, raising `primRoot M` to the integer exponent `M` gives one. -/
theorem primRoot_zpow_natCast_eq_one (hM : 0 < M) : primRoot M ^ ((M : ℤ)) = 1 :=
  (isPrimitiveRoot_primRoot (Nat.pos_iff_ne_zero.mp hM)).zpow_eq_one

/-- Complex conjugation negates the integer exponent of a power of `primRoot`. -/
theorem primRoot_conj_zpow (M : ℕ) (c : ℤ) :
    (starRingEnd ℂ) (primRoot M ^ c) = primRoot M ^ (-c) := by
  have hconj : (starRingEnd ℂ) (primRoot M) = (primRoot M)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, norm_primRoot, one_pow]
    norm_num
  rw [map_zpow₀ (starRingEnd ℂ) (primRoot M) c, hconj, _root_.inv_zpow, ← _root_.zpow_neg]

/-- If `M` divides the integer frequency, the sum of its Fourier character over `Fin M` equals
`M`. -/
theorem sum_primRoot_zpow_of_dvd (hM : 0 < M) {c : ℤ} (hc : (M : ℤ) ∣ c) :
    ∑ y : Fin M, primRoot M ^ (c * (y : ℤ)) = (M : ℂ) := by
  obtain ⟨q, rfl⟩ := hc
  have hone : ∀ y : Fin M, primRoot M ^ (((M : ℤ) * q) * (y : ℤ)) = 1 := by
    intro y
    rw [mul_assoc, _root_.zpow_mul, primRoot_zpow_natCast_eq_one hM, _root_.one_zpow]
  rw [Finset.sum_congr rfl (fun y _ => hone y), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- A Fourier character with frequency not divisible by the positive size `M` sums to zero over
`Fin M`. -/
theorem sum_primRoot_zpow (hM : 0 < M) {c : ℤ} (hc : ¬ (M : ℤ) ∣ c) :
    ∑ y : Fin M, primRoot M ^ (c * (y : ℤ)) = 0 := by
  have hξne : primRoot M ^ c ≠ 1 := fun h => hc ((primRoot_zpow_eq_one_iff hM c).mp h)
  have hξM : (primRoot M ^ c) ^ M = 1 := by
    rw [← zpow_natCast (primRoot M ^ c) M, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      primRoot_zpow_natCast_eq_one hM, _root_.one_zpow]
  have hterm : ∀ i : ℕ, i ∈ Finset.range M →
      primRoot M ^ (c * (i : ℤ)) = (primRoot M ^ c) ^ i := by
    intro i _
    rw [← zpow_natCast (primRoot M ^ c) i, _root_.zpow_mul, zpow_natCast]
  rw [Fin.sum_univ_eq_sum_range (fun i => primRoot M ^ (c * ((i : ℤ)))) M,
    Finset.sum_congr rfl (fun i hi => hterm i hi),
    geom_sum_eq hξne M, hξM, sub_self, zero_div]

/-- The normalized discrete Fourier matrix on `Fin M`, built from powers of `primRoot M`. See
[Kitaev1995]. -/
noncomputable def QFTMatrix (M : ℕ) : Matrix (Fin M) (Fin M) ℂ :=
  Matrix.of fun x y => (Real.sqrt (M : ℝ) : ℂ)⁻¹ * primRoot M ^ (((x.val : ℤ) * (y.val : ℤ)))

/-- Each Fourier matrix entry is the corresponding root-of-unity power scaled by the inverse
square root of `M`. -/
theorem qftMatrix_apply (M : ℕ) (x y : Fin M) :
    QFTMatrix M x y = (Real.sqrt (M : ℝ) : ℂ)⁻¹ * primRoot M ^ (((x.val : ℤ) * (y.val : ℤ))) :=
  rfl

/-- For positive `M`, the product of two complex inverse square-root normalization factors
equals the inverse of `M`. -/
theorem inv_sqrt_mul_inv_sqrt (hM : 0 < M) :
    (Real.sqrt (M : ℝ) : ℂ)⁻¹ * (Real.sqrt (M : ℝ) : ℂ)⁻¹ = (M : ℂ)⁻¹ := by
  have hsq : ((Real.sqrt (M : ℝ) : ℂ)) ^ 2 = (M : ℂ) :=
    by exact_mod_cast Real.sq_sqrt (by exact_mod_cast hM.le)
  rw [← mul_inv, ← sq, hsq]

/-- The normalized Fourier matrix is unitary when its size is positive. -/
theorem qftMatrix_unitary (hM : 0 < M) : QFTMatrix M ∈ Matrix.unitaryGroup (Fin M) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext x x'
  simp only [Matrix.mul_apply]
  have hcast : ∀ a b : ℕ, ((a * b : ℕ) : ℤ) = ((a : ℤ) * (b : ℤ)) := by
    intro a b; push_cast; ring
  have hconjentry : ∀ a b : Fin M,
      (starRingEnd ℂ) (QFTMatrix M a b)
        = (Real.sqrt (M : ℝ) : ℂ)⁻¹ * primRoot M ^ (-((a.val : ℤ) * (b.val : ℤ))) := by
    intro a b
    rw [qftMatrix_apply, map_mul, map_inv₀, Complex.conj_ofReal,
      primRoot_conj_zpow]
  have hterm : ∀ k : Fin M,
      ((QFTMatrix M)ᴴ x k * QFTMatrix M k x')
        = (M : ℂ)⁻¹ * primRoot M ^ (((x'.val : ℤ) - x.val) * (k : ℤ)) := by
    intro k
    simp only [Matrix.conjTranspose_apply, RCLike.star_def]
    rw [hconjentry k x, qftMatrix_apply,
      show (Real.sqrt (M : ℝ) : ℂ)⁻¹ * primRoot M ^ (-((k.val : ℤ) * (x.val : ℤ)))
          * ((Real.sqrt (M : ℝ) : ℂ)⁻¹ * primRoot M ^ ((k.val : ℤ) * (x'.val : ℤ)))
        = primRoot M ^ (-((k.val : ℤ) * (x.val : ℤ)))
            * primRoot M ^ ((k.val : ℤ) * (x'.val : ℤ)) * ((M : ℂ)⁻¹) from by
        rw [← inv_sqrt_mul_inv_sqrt hM]; ring,
      ← zpow_add₀ (primRoot_ne_zero M), mul_comm]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum]
  by_cases hxx' : x = x'
  · subst hxx'
    rw [sub_self, sum_primRoot_zpow_of_dvd hM (Int.dvd_zero _),
      inv_mul_cancel₀ (by exact_mod_cast hM.ne')]
    simp
  · have hndvd : ¬ (M : ℤ) ∣ ((x'.val : ℤ) - x.val) := by
      intro hdvd
      apply hxx'
      have hxlt : (x.val : ℤ) < (M : ℤ) := by exact_mod_cast x.isLt
      have hx'lt : (x'.val : ℤ) < (M : ℤ) := by exact_mod_cast x'.isLt
      have habs : |((x'.val : ℤ) - x.val)| < (M : ℤ) :=
        abs_sub_lt_iff.mpr ⟨by omega, by omega⟩
      obtain ⟨q, hq⟩ := hdvd
      rw [hq, abs_mul, abs_of_nonneg (by omega)] at habs
      have hMpos : (0 : ℤ) < M := by exact_mod_cast hM
      have hd0 : (x'.val : ℤ) - x.val = 0 := by
        rcases eq_or_ne q 0 with hq0 | hq0
        · rw [hq0, mul_zero] at hq; exact hq
        · exfalso
          have h1 : (1 : ℤ) ≤ |q| := by
            rw [Int.abs_eq_natAbs]
            exact_mod_cast Int.natAbs_pos.mpr hq0
          have hle : (M : ℤ) ≤ (M : ℤ) * |q| := le_mul_of_one_le_right hMpos.le h1
          linarith
      have hval : x'.val = x.val := by omega
      exact Fin.ext hval.symm
    rw [sum_primRoot_zpow hM hndvd, mul_zero, Matrix.one_apply, if_neg hxx']

/-- The normalized Fourier character state with frequency `k` on `Fin M`. -/
noncomputable def PhaseState (M : ℕ) (k : ℕ) : QState (Fin M) :=
  fun y => (Real.sqrt (M : ℝ) : ℂ)⁻¹ * primRoot M ^ (((k : ℤ) * (y.val : ℤ)))

/-- Evaluate a Fourier phase state at a basis label. -/
theorem phaseState_apply (M : ℕ) (k : ℕ) (y : Fin M) :
    PhaseState M k y = (Real.sqrt (M : ℝ) : ℂ)⁻¹ * primRoot M ^ (((k : ℤ) * (y.val : ℤ))) :=
  rfl

/-- Every integer power of the Fourier root has complex norm one. -/
theorem norm_primRoot_zpow (M : ℕ) (c : ℤ) : ‖primRoot M ^ c‖ = 1 := by
  rw [norm_zpow _ c, norm_primRoot, _root_.one_zpow]

/-- For positive `M`, every Fourier phase state is normalized. -/
theorem phaseState_normalized (hM : 0 < M) (k : ℕ) : Normalized (PhaseState M k) := by
  unfold Normalized
  have hterm : ∀ y : Fin M, ‖PhaseState M k y‖ ^ 2 = (M : ℝ)⁻¹ := by
    intro y
    have h1 : ((Real.sqrt (M : ℝ) : ℂ)⁻¹) = ((Real.sqrt (M : ℝ))⁻¹ : ℝ) := by
      rw [Complex.ofReal_inv]
    have hMle : (0 : ℝ) ≤ M := by exact_mod_cast hM.le
    rw [phaseState_apply, norm_mul, mul_pow, norm_primRoot_zpow, one_pow, h1,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_pow,
      Real.sq_sqrt hMle, mul_one]
  rw [Finset.sum_congr rfl (fun y _ => hterm y), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast hM.ne' : (M : ℝ) ≠ 0)

/-- The inverse Fourier matrix sends the phase state of a grid label to its basis ket. -/
theorem qftMatrix_conjTranspose_mulVec_phaseState (hM : 0 < M) (j : Fin M) :
    ApplyGate (QFTMatrix M)ᴴ (PhaseState M j.val) = Ket j := by
  have hconjentry : ∀ a b : Fin M,
      (starRingEnd ℂ) (QFTMatrix M a b)
        = (Real.sqrt (M : ℝ) : ℂ)⁻¹ * primRoot M ^ (-((a.val : ℤ) * (b.val : ℤ))) := by
    intro a b
    rw [qftMatrix_apply, map_mul, map_inv₀, Complex.conj_ofReal, primRoot_conj_zpow]
  funext x
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, RCLike.star_def]
  have hterm : ∀ y : Fin M,
      ((starRingEnd ℂ) (QFTMatrix M y x) * PhaseState M j.val y)
        = (M : ℂ)⁻¹ * primRoot M ^ (((j.val : ℤ) - (x : ℤ)) * (y : ℤ)) := by
    intro y
    rw [hconjentry y x, phaseState_apply,
      show (Real.sqrt (M : ℝ) : ℂ)⁻¹ * primRoot M ^ (-((y.val : ℤ) * (x.val : ℤ)))
          * ((Real.sqrt (M : ℝ) : ℂ)⁻¹ * primRoot M ^ (((j.val : ℤ) * (y.val : ℤ))))
        = primRoot M ^ (-((y.val : ℤ) * (x.val : ℤ)))
            * primRoot M ^ (((j.val : ℤ) * (y.val : ℤ))) * ((M : ℂ)⁻¹) from by
        rw [← inv_sqrt_mul_inv_sqrt hM]; ring,
      ← zpow_add₀ (primRoot_ne_zero M), mul_comm]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun y _ => hterm y), ← Finset.mul_sum]
  by_cases hxj : x = j
  · subst hxj
    rw [sub_self, sum_primRoot_zpow_of_dvd hM (Int.dvd_zero _),
      inv_mul_cancel₀ (by exact_mod_cast hM.ne')]
    simp [Ket]
  · have hndvd : ¬ (M : ℤ) ∣ ((j.val : ℤ) - x.val) := by
      intro hdvd
      apply hxj
      have hjlt : (j.val : ℤ) < (M : ℤ) := by exact_mod_cast j.isLt
      have hxlt : (x.val : ℤ) < (M : ℤ) := by exact_mod_cast x.isLt
      have habs : |((j.val : ℤ) - x.val)| < (M : ℤ) :=
        abs_sub_lt_iff.mpr ⟨by omega, by omega⟩
      obtain ⟨q, hq⟩ := hdvd
      rw [hq, abs_mul, abs_of_nonneg (by exact_mod_cast hM.le)] at habs
      have hMpos : (0 : ℤ) < M := by exact_mod_cast hM
      have hd0 : (j.val : ℤ) - x.val = 0 := by
        rcases eq_or_ne q 0 with hq0 | hq0
        · rw [hq0, mul_zero] at hq; exact hq
        · exfalso
          have h1 : (1 : ℤ) ≤ |q| := by
            rw [Int.abs_eq_natAbs]
            exact_mod_cast Int.natAbs_pos.mpr hq0
          have hle : (M : ℤ) ≤ (M : ℤ) * |q| := le_mul_of_one_le_right hMpos.le h1
          linarith
      have hval : j.val = x.val := by omega
      exact Fin.ext hval.symm
    rw [sum_primRoot_zpow hM hndvd, mul_zero, Ket]
    simp [hxj]

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The controlled operator applying `U^x` in the control block labeled by `x`. This is the
phase-kickback operator used in [Kitaev1995]. -/
noncomputable def ControlledPowers (U : Matrix I I ℂ) (M : ℕ) :
    Matrix (Fin M × I) (Fin M × I) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then (U ^ (q.1.val : ℕ)) p.2 q.2 else 0

/-- Every natural power of a matrix satisfying `Uᴴ*U = 1` satisfies the same identity. -/
theorem conjTranspose_mul_self_pow (U : Matrix I I ℂ)
    (hU : Uᴴ * U = 1) (k : ℕ) : (U ^ k)ᴴ * U ^ k = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Matrix.conjTranspose_mul,
      show (Uᴴ * (U ^ k)ᴴ) * (U ^ k * U) = Uᴴ * (((U ^ k)ᴴ * U ^ k) * U) from by
        noncomm_ring,
      ih, one_mul, hU]

/-- The controlled-powers matrix is the block-diagonal matrix with blocks `U^x`. -/
theorem controlledPowers_eq_blockDiag (U : Matrix I I ℂ) (M : ℕ) :
    ControlledPowers U M = BlockDiag fun x : Fin M => U ^ (x.val : ℕ) := rfl

/-- Controlled powers of a unitary matrix form a unitary matrix. -/
theorem controlledPowers_unitary (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    ControlledPowers U M ∈ Matrix.unitaryGroup (Fin M × I) ℂ := by
  rw [controlledPowers_eq_blockDiag]
  exact blockDiag_unitary _ fun x => pow_mem hU _

/-- An eigenvector with eigenvalue `lam` is an eigenvector of every natural matrix power with
eigenvalue `lam^k`. -/
theorem mulVec_pow_of_eigen {U : Matrix I I ℂ} {ψ : QState I} {lam : ℂ}
    (hψ : U *ᵥ ψ = lam • ψ) : ∀ k : ℕ, (U ^ k) *ᵥ ψ = lam ^ k • ψ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, hψ, Matrix.mulVec_smul, ih, smul_smul, pow_succ]
    exact congrArg (fun c => c • ψ) (mul_comm _ _)

/-- On an eigenvector with grid eigenvalue, controlled powers turn the uniform control state
into the corresponding `PhaseState` and preserve the data vector. See [Kitaev1995]. -/
theorem controlledPowers_kickback {U : Matrix I I ℂ} {ψ : QState I} {k : ℕ}
    (hψ : U *ᵥ ψ = (primRoot M ^ ((k : ℤ))) • ψ) :
    ControlledPowers U M *ᵥ TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) ψ
      = TensorState (PhaseState M k) ψ := by
  have hev := mulVec_pow_of_eigen hψ
  funext p
  obtain ⟨x, i⟩ := p
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ControlledPowers,
    Matrix.of_apply, TensorState, PhaseState]
  rw [Finset.sum_eq_single x]
  · have hsum : (∑ j : I, (U ^ (x.val : ℕ)) i j * ((Real.sqrt (M : ℝ) : ℂ)⁻¹ * ψ j))
        = ((Real.sqrt (M : ℝ) : ℂ)⁻¹) * ((U ^ (x.val : ℕ)) *ᵥ ψ) i := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [if_true]
    rw [hsum, hev, Pi.smul_apply, ← zpow_natCast, ← _root_.zpow_mul]
    ring
  · intro m _ hm
    simp [show x ≠ m from fun e => hm e.symm]
  · intro hcon
    exact absurd (Finset.mem_univ x) hcon

/-- For a normalized eigenstate with grid eigenphase `j`, controlled powers followed by inverse
Fourier transform produce `Ket j` tensored with the eigenstate, and label `j` has
probability one. See [Kitaev1995]. -/
theorem qpe_exact_readout (hM : 0 < M) {U : Matrix I I ℂ}
    {ψ : QState I} (hψn : Normalized ψ) (j : Fin M)
    (hψ : U *ᵥ ψ = (primRoot M ^ ((j.val : ℤ))) • ψ) :
    ApplyGate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix I I ℂ))
        (ControlledPowers U M *ᵥ TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) ψ)
      = TensorState (Ket j) ψ ∧
    MeasureProb (ApplyGate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix I I ℂ))
        (ControlledPowers U M *ᵥ TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) ψ))
        ({j} ×ˢ (Finset.univ : Finset I)) = 1 := by
  constructor
  · rw [controlledPowers_kickback hψ, applyGate_tensorGate, applyGate_one,
      qftMatrix_conjTranspose_mulVec_phaseState hM j]
  · rw [controlledPowers_kickback hψ, applyGate_tensorGate, applyGate_one,
      qftMatrix_conjTranspose_mulVec_phaseState hM j, measureProb_tensorState_prod]
    have h1 : MeasureProb (Ket j) ({j} : Finset (Fin M)) = 1 := by
      unfold MeasureProb
      rw [Finset.sum_singleton, bornProb_ket, if_pos rfl]
    rw [h1, measureProb_univ hψn, mul_one]

/-- Controlled powers and inverse Fourier transform coherently attach each grid phase label to a
finite linear combination of eigenvectors. See [MagniezNayakRolandSantha2011]. -/
theorem qpe_exact_readout_linear (M : ℕ) (hM : 0 < M) (U : Matrix I I ℂ)
    {Idx : Type*} [Fintype Idx] (c : Idx → ℂ) (ψ : Idx → QState I) (k : Idx → Fin M)
    (heig : ∀ i, U *ᵥ (ψ i) = (primRoot M ^ (((k i).val : ℤ))) • (ψ i)) :
    ApplyGate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix I I ℂ))
        (ControlledPowers U M *ᵥ (∑ i, c i • TensorState
          (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) (ψ i)))
      = ∑ i, c i • TensorState (Ket (k i)) (ψ i) := by
  have hkick : ∀ i, ControlledPowers U M *ᵥ (c i • TensorState
        (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) (ψ i))
      = c i • TensorState (PhaseState M (k i).val) (ψ i) := by
    intro i
    rw [mulVec_smul, controlledPowers_kickback (heig i)]
  rw [show ControlledPowers U M *ᵥ (∑ i, c i • TensorState
        (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) (ψ i))
      = ∑ i, ControlledPowers U M *ᵥ (c i • TensorState
        (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) (ψ i)) from mulVec_sum _ _ _]
  rw [Finset.sum_congr rfl fun i _ => hkick i]
  rw [show ApplyGate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix I I ℂ))
        (∑ i, c i • TensorState (PhaseState M (k i).val) (ψ i))
      = ∑ i, ApplyGate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix I I ℂ))
        (c i • TensorState (PhaseState M (k i).val) (ψ i)) from mulVec_sum _ _ _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show ApplyGate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix I I ℂ))
        (c i • TensorState (PhaseState M (k i).val) (ψ i))
      = c i • ApplyGate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix I I ℂ))
        (TensorState (PhaseState M (k i).val) (ψ i)) from mulVec_smul _ _ _]
  rw [applyGate_tensorGate, qftMatrix_conjTranspose_mulVec_phaseState hM (k i),
    applyGate_one]

end Qatlib.Concepts.SpectralFilter.PhaseReadout

open Matrix Set
open scoped Matrix.Norms.L2Operator ComplexOrder Classical

set_option autoImplicit false

variable {I : Type} [Fintype I] [DecidableEq I]
namespace Qatlib.Concepts.SpectralFilter.PhaseReadout

/-- Express an integer power of `primRoot M` as a complex exponential with phase `c/M`. -/
theorem primRoot_zpow_eq_exp (M : ℕ) (c : ℤ) :
    primRoot M ^ c = Complex.exp (2 * Real.pi * Complex.I * ((c : ℝ) / (M : ℝ))) := by
  unfold primRoot
  have h := Complex.exp_int_mul (2 * Real.pi * Complex.I / (M : ℝ)) c
  rw [← h]
  congr 1
  push_cast
  ring

/-- The complex number `2*π*I*t` has real part zero for real `t`. -/
theorem re_two_pi_I_mul (t : ℝ) : (2 * Real.pi * Complex.I * t : ℂ).re = 0 := by
  simp only [Complex.mul_re]
  ring_nf
  simp [Complex.ofReal_im, Complex.I_im, Complex.ofReal_re, Complex.I_re]

/-- The complex exponential of a number with zero real part has norm one. -/
theorem norm_exp_of_re_zero {w : ℂ} (hw : w.re = 0) : ‖Complex.exp w‖ = 1 := by
  rw [Complex.norm_exp, hw, Real.exp_zero]

/-- A complex exponential with real phase `2*π*t` has norm one. -/
theorem norm_exp_two_pi_I (t : ℝ) : ‖Complex.exp (2 * Real.pi * Complex.I * t)‖ = 1 :=
  norm_exp_of_re_zero (re_two_pi_I_mul t)

/-- The complex exponential at `2*π*I` equals one. -/
theorem exp_two_pi_I : Complex.exp ((2 : ℂ) * Real.pi * Complex.I) = 1 := by
  have hrw : (2 : ℂ) * Real.pi * Complex.I = (2 * Real.pi : ℂ) * Complex.I := by ring
  rw [hrw, Complex.exp_mul_I]
  norm_num

/-- The complex exponential at an integer multiple of `2*π*I` equals one. -/
theorem exp_two_pi_I_int (c : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (c : ℝ)) = 1 := by
  have hid : 2 * Real.pi * Complex.I * (c : ℝ)
      = ((c : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
  rw [hid, Complex.exp_int_mul, exp_two_pi_I, _root_.one_zpow]

/-- A phase given by a natural number times an integer has complex exponential one. -/
theorem exp_two_pi_I_nat_int (y : ℕ) (c : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * ((y : ℝ) * (c : ℝ))) = 1 := by
  have hrw : 2 * Real.pi * Complex.I * ((y : ℝ) * (c : ℝ))
      = ((y : ℕ) : ℂ) * (2 * Real.pi * Complex.I * (c : ℝ)) := by
    push_cast
    ring
  rw [hrw, Complex.exp_nat_mul, exp_two_pi_I_int, _root_.one_pow]

/-- Adding an integer to a phase leaves its complex exponential unchanged after multiplication
by a natural frequency. -/
theorem exp_two_pi_I_mul_int (φ : ℝ) (y : ℕ) (c : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * ((y : ℝ) * (φ + (c : ℝ))))
      = Complex.exp (2 * Real.pi * Complex.I * ((y : ℝ) * φ)) := by
  have hone : Complex.exp (2 * Real.pi * Complex.I * ((y : ℝ) * (c : ℝ))) = 1 :=
    exp_two_pi_I_nat_int y c
  calc
    _ = Complex.exp (2 * Real.pi * Complex.I * ((y : ℝ) * φ)
          + 2 * Real.pi * Complex.I * ((y : ℝ) * (c : ℝ))) := by
        congr 1
        push_cast
        ring
    _ = Complex.exp (2 * Real.pi * Complex.I * ((y : ℝ) * φ))
          * Complex.exp (2 * Real.pi * Complex.I * ((y : ℝ) * (c : ℝ))) :=
      Complex.exp_add _ _
    _ = _ := by simp only [hone, mul_one]

/-- For positive `M`, multiplying a complex number by two inverse square-root normalization
factors scales it by `M⁻¹`. -/
theorem mul_inv_sqrt (M : ℕ) (hM : 0 < M) (c : ℂ) :
    (Real.sqrt (M : ℝ) : ℂ)⁻¹ * c * (Real.sqrt (M : ℝ) : ℂ)⁻¹ = (M : ℂ)⁻¹ * c := by
  rw [show (Real.sqrt (M : ℝ) : ℂ)⁻¹ * c * (Real.sqrt (M : ℝ) : ℂ)⁻¹
      = ((Real.sqrt (M : ℝ) : ℂ)⁻¹ * (Real.sqrt (M : ℝ) : ℂ)⁻¹) * c by ring]
  rw [inv_sqrt_mul_inv_sqrt hM]

/-- For positive `M`, the Fourier matrix sends the zero basis ket to the uniform state. -/
theorem qftMatrix_ket_zero (M : ℕ) (hM : 0 < M) :
    ApplyGate (QFTMatrix M) (Ket (⟨0, hM⟩ : Fin M)) =
      fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹ := by
  funext x
  simp [ApplyGate, Matrix.mulVec, dotProduct, Ket, qftMatrix_apply]
end Qatlib.Concepts.SpectralFilter.PhaseReadout
