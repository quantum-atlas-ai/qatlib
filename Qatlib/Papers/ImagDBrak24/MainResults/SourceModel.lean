/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Source model for *Double-bracket quantum algorithms for quantum imaginary-time evolution*

Fixed paper version: arXiv:2412.04554v2 (2 Jul 2025), QAtlas paper `340`.

This module introduces the finite-dimensional vocabulary shared by every
paper-layer statement of `ImagDBrak24`:

* `vdot` — the Dirac bracket `⟨x|y⟩ = ∑ i, conj (x i) * y i`;
* `normSq` — `‖x‖²`;  `twoNorm` — `‖x‖`;
* `IsState` — `‖x‖² = 1`;
* `basisVec i` — the eigenstate `|λ_i⟩` of the Hamiltonian's eigen-basis;
* `expVal A x` — the expectation `⟨x|A|x⟩` (Definition of `E_k`, Table II);
* `pureState x` — the rank-one projector `|x⟩⟨x|`;
* `weight ψ i` — the spectral probability `p_i = ‖ψ_i‖²`;
* `expectedEnergy lam ψ` — `E = Σ_i λ_i p_i`;
* `secondMoment lam ψ` — `Σ_i λ_i² p_i`;
* `energyVariance lam ψ` — `V = ⟨Ĥ²⟩ - E²` (Eq. (60));
* `hsNormSq A`, `hsNorm A` — the Hilbert–Schmidt norm squared/norm (Eq. (27));
* `commutator A B = A * B - B * A`;
* `nestedCommutator X n Y` — Eq. (62) `[(X)^n, Y]`;
* `diagHam lam` — the Hamiltonian `Ĥ = Σ_j λ_j |λ_j⟩⟨λ_j|` in its eigen-basis;
* `IsUnitary U` — `U† U = U U† = 1`.

The paper writes a Hamiltonian in spectral form `Ĥ = Σ_j λ_j |λ_j⟩⟨λ_j|`
(Table II, p.12); `diagHam lam` is exactly that operator in the eigen-basis
`{|λ_j⟩}`, where the state vector component `ψ j` is the amplitude on `|λ_j⟩`.
This module is definitions plus elementary identities only.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.ImagDBrak24.MainResults

open Matrix
open scoped BigOperators ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Dirac bracket `⟨x|y⟩ = ∑ i, conj (x i) * y i`. -/
def vdot (x y : ι → ℂ) : ℂ := ∑ i, star (x i) * y i

/-- The squared Euclidean norm `‖x‖² = ∑ i, ‖x i‖²` of a state vector. -/
def normSq (x : ι → ℂ) : ℝ := ∑ i, Complex.normSq (x i)

/-- The Euclidean (2-)norm `‖x‖` of a state vector. -/
def twoNorm (x : ι → ℂ) : ℝ := Real.sqrt (normSq x)

/-- A normalized state vector, `‖x‖² = 1`. -/
def IsState (x : ι → ℂ) : Prop := normSq x = 1

/-- The `i`-th standard basis vector; in the eigen-basis of the Hamiltonian this
is the eigenstate `|λ_i⟩`. -/
def basisVec (i : ι) : ι → ℂ := fun j => if j = i then (1 : ℂ) else 0

/-- The expectation value `⟨x|A|x⟩` of an operator `A` in a state vector `x`
(this is the complex number whose real part is `E_k = ⟨ω_k|Ĥ|ω_k⟩`). -/
def expVal (A : Matrix ι ι ℂ) (x : ι → ℂ) : ℂ := vdot x (A *ᵥ x)

/-- The rank-one projector `|x⟩⟨x|` associated with a state vector. -/
def pureState (x : ι → ℂ) : Matrix ι ι ℂ := fun i j => x i * star (x j)

/-- The Hilbert–Schmidt (Frobenius) norm squared `‖A‖_HS² = ∑ i j, ‖A i j‖²`,
matching `Tr((A-B)†(A-B))` of Eq. (27). -/
def hsNormSq (A : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (A i j)

/-- The Hilbert–Schmidt norm `‖A‖_HS`. -/
def hsNorm (A : Matrix ι ι ℂ) : ℝ := Real.sqrt (hsNormSq A)

/-- The commutator `[A,B] = A * B - B * A`. -/
def commutator (A B : Matrix ι ι ℂ) : Matrix ι ι ℂ := A * B - B * A

/-- The nested commutator `[(X)^n, Y]` of Eq. (62):
`[(X)^0, Y] = Y` and `[(X)^{n+1}, Y] = [X, [(X)^n, Y]]`. -/
def nestedCommutator (X : Matrix ι ι ℂ) : ℕ → Matrix ι ι ℂ → Matrix ι ι ℂ
  | 0, Y => Y
  | n + 1, Y => commutator X (nestedCommutator X n Y)

/-- The diagonal Hamiltonian in its eigen-basis, `Ĥ = diag λ`, i.e.
`Ĥ = Σ_j λ_j |λ_j⟩⟨λ_j|` with `|λ_j⟩` the `j`-th standard basis vector. -/
def diagHam (lam : ι → ℝ) : Matrix ι ι ℂ := Matrix.diagonal (fun i => (lam i : ℂ))

/-- A unitary operator, `U† U = U U† = 1`. -/
def IsUnitary (U : Matrix ι ι ℂ) : Prop := Uᴴ * U = 1 ∧ U * Uᴴ = 1

/-! ## Spectral energy vocabulary (Table II p.3 and Eq. (60) p.17) -/

/-- The probability weight `p_i = ‖ψ_i‖²` of the `i`-th eigen-component. -/
def weight (ψ : ι → ℂ) (i : ι) : ℝ := Complex.normSq (ψ i)

/-- The expected energy `E = Σ_i λ_i p_i` of the state `ψ`
(`E_k = ⟨ω_k|Ĥ|ω_k⟩`). -/
def expectedEnergy (lam : ι → ℝ) (ψ : ι → ℂ) : ℝ := ∑ i, lam i * weight ψ i

/-- The second moment `Σ_i λ_i² p_i = ⟨ψ|Ĥ²|ψ⟩`. -/
def secondMoment (lam : ι → ℝ) (ψ : ι → ℂ) : ℝ := ∑ i, lam i ^ 2 * weight ψ i

/-- The energy variance `V = ⟨ψ|Ĥ²|ψ⟩ - E²` (Eq. (60)). -/
def energyVariance (lam : ι → ℝ) (ψ : ι → ℂ) : ℝ :=
  secondMoment lam ψ - (expectedEnergy lam ψ) ^ 2

/-! ## Basic identities for the model -/

theorem weight_nonneg (ψ : ι → ℂ) (i : ι) : 0 ≤ weight ψ i :=
  Complex.normSq_nonneg _

/-- The summation identity for `weight`. -/
theorem sum_weight (ψ : ι → ℂ) : ∑ i, weight ψ i = normSq ψ := rfl

/-- The star mul self eq norm Sq property in the paper model. -/
theorem star_mul_self_eq_normSq (z : ℂ) : star z * z = (Complex.normSq z : ℂ) := by
  rw [show star z = (starRingEnd ℂ) z from rfl, mul_comm]
  exact Complex.mul_conj z

/-- The vdot self property in the paper model. -/
@[simp] theorem vdot_self (x : ι → ℂ) : vdot x x = (normSq x : ℂ) := by
  unfold vdot normSq
  push_cast
  exact Finset.sum_congr rfl (fun i _ => star_mul_self_eq_normSq (x i))

/-- The quantity `normSq` is nonnegative. -/
theorem normSq_nonneg (x : ι → ℂ) : 0 ≤ normSq x := by
  unfold normSq
  exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)

/-- The basis Vec apply self property in the paper model. -/
theorem basisVec_apply_self (i : ι) : basisVec i i = 1 := by
  simp [basisVec]

/-- The basis Vec apply ne property in the paper model. -/
theorem basisVec_apply_ne {i j : ι} (h : j ≠ i) : basisVec i j = 0 := by
  simp [basisVec, h]

/-- The norm Sq basis Vec property in the paper model. -/
theorem normSq_basisVec (i : ι) : normSq (basisVec i) = 1 := by
  have h : ∀ j, Complex.normSq (basisVec i j) = if j = i then (1 : ℝ) else 0 := by
    intro j
    by_cases hj : j = i
    · simp [basisVec, hj]
    · simp [basisVec, hj]
  unfold normSq
  rw [Finset.sum_congr rfl (fun j _ => h j)]
  simp

/-- The pure State apply property in the paper model. -/
theorem pureState_apply (x y : ι → ℂ) (i : ι) :
    (pureState x *ᵥ y) i = x i * vdot x y := by
  simp only [pureState, vdot, Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The pure State mul Vec property in the paper model. -/
theorem pureState_mulVec (x y : ι → ℂ) : pureState x *ᵥ y = vdot x y • x := by
  ext i
  rw [pureState_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- The pure State mul Vec self property in the paper model. -/
theorem pureState_mulVec_self {x : ι → ℂ} (hx : IsState x) : pureState x *ᵥ x = x := by
  rw [pureState_mulVec, vdot_self, hx]
  simp

/-- The pure State is Hermitian property in the paper model. -/
theorem pureState_isHermitian (x : ι → ℂ) : (pureState x).IsHermitian := by
  ext i j
  unfold pureState
  rw [conjTranspose_apply]
  simp only [star_mul, star_star]

/-- `|x⟩⟨x| · |x⟩⟨x| = ⟨x|x⟩ • |x⟩⟨x|`. -/
theorem pureState_mul_self' (x : ι → ℂ) :
    pureState x * pureState x = vdot x x • pureState x := by
  ext i k
  simp only [pureState, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    ∑ j, x i * star (x j) * (x j * star (x k))
        = ∑ j, (star (x j) * x j) * (x i * star (x k)) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = (∑ j, star (x j) * x j) * (x i * star (x k)) := by rw [Finset.sum_mul]
    _ = (vdot x x) * (x i * star (x k)) := by
          rw [show (∑ j, star (x j) * x j) = vdot x x from rfl]

/-- The pure State mul self property in the paper model. -/
theorem pureState_mul_self {x : ι → ℂ} (hx : IsState x) :
    pureState x * pureState x = pureState x := by
  rw [pureState_mul_self', vdot_self, hx]
  simp

/-- The vdot smul property in the paper model. -/
theorem vdot_smul (x : ι → ℂ) (c : ℂ) (y : ι → ℂ) :
    vdot x (c • y) = c * vdot x y := by
  unfold vdot
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- `⟨x| (|y⟩⟨y|) z⟩ = ⟨x|y⟩ ⟨y|z⟩`. -/
theorem vdot_pureState (x y z : ι → ℂ) :
    vdot x (pureState y *ᵥ z) = vdot x y * vdot y z := by
  rw [pureState_mulVec, vdot_smul]
  ring

end Qatlib.Papers.ImagDBrak24.MainResults
