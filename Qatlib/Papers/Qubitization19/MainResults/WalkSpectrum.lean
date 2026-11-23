/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Tactic
public import Qatlib.Papers.Qubitization19.MainResults.SignalRotation

@[expose] public section

/-!
# Qubitization walk spectrum on an eigenbranch

This module proves the two-dimensional eigenbranch form of the qubitization
iterate in [LowChuang2019], Theorem 2 and Corollary 9, the eigenphase and
Chebyshev description of its powers in Eqs. (4)–(7), and the phased-iterate
conjugation in [LowChuang2019], Lemma 11 ([arXiv:1610.06546v3](https://arxiv.org/abs/1610.06546v3)).

On the ordered branch basis `(|G_λ⟩, |G_λ^⊥⟩)` an eigenvalue `λ = cos θ` of a
Hermitian signal operator is encoded by a Hermitian involution whose
`(|G_λ⟩, |G_λ⟩)` entry is `λ`.  Multiplying that oracle by the reflection
`2|G_λ⟩⟨G_λ| - I` gives a plane rotation.  The rotation, its powers, its two
eigenvectors with eigenphases `exp (θ * I)` and `exp (-θ * I)`, and its
conjugation by the partial reflections of Lemma 11 are proved explicitly.

For an interior eigenvalue, the rotation and its powers act in the
orthonormal frame constructed from the oracle's two Eq. (17) corner identities.
At `λ = ±1`, the explicit two-by-two model has coincident phases, and makes
no claim about the dimension of a branch in the original workspace.
The results are stated on one eigenbranch.  They do not assemble the branches
into a global direct-sum circuit, do not construct `PREPARE`/`SELECT`
oracles, and do not by themselves give gate or query costs for a general
Hamiltonian input model.

[LowChuang2019]: Guang Hao Low and Isaac L. Chuang, “Hamiltonian Simulation
by Qubitization”, Quantum 3, 163 (2019), DOI 10.22331/q-2019-07-12-163.
-/

set_option autoImplicit false

open Matrix

namespace Qatlib.Papers.Qubitization19.MainResults

/-- The plane rotation on an eigenbranch, in the ordered basis
`(|G_λ⟩, |G_λ^⊥⟩)` with `λ = cos θ`: this is the signal rotation
`exp (-i * θ * Y)` form of the qubitization iterate in [LowChuang2019], Eq. (6),
transported to the real rotation
`!![cos θ, -sin θ; sin θ, cos θ]`. -/
noncomputable def branchRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos θ : ℂ), -(Real.sin θ : ℂ);
     (Real.sin θ : ℂ), (Real.cos θ : ℂ)]

/-- The reflection `2|G_λ⟩⟨G_λ| - I` on an eigenbranch: it is `+1` on the
signal state `|G_λ⟩` and `-1` on its orthogonal branch vector. -/
def branchReflection : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- A Hermitian involutive signal oracle on an eigenbranch whose encoded
entry is `cos θ`.  In the branch basis it is
`!![cos θ, -sin θ; -sin θ, -cos θ]`; the sign of the second basis vector is
the phase convention for `|G_λ^⊥⟩` for which the reflection times the oracle
is exactly `branchRotation θ`. -/
noncomputable def branchOracle (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos θ : ℂ), -(Real.sin θ : ℂ);
     -(Real.sin θ : ℂ), -(Real.cos θ : ℂ)]

/-- The partial reflection `Z_φ = diag (exp (-φ * I), -1)` on an eigenbranch:
the `((1 + exp (-φ * I)) |G_λ⟩⟨G_λ| - I)` operator of [LowChuang2019],
Lemma 11, Eq. (20), written in the branch basis. -/
noncomputable def partialReflection (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-(Complex.I * (φ : ℂ))), 0; 0, -1]

/-- The phased iterate of [LowChuang2019], Lemma 11:
`W_φ = Z_{φ + π / 2} W Z_{-φ - π / 2}` on one eigenbranch, where `W` is
`branchRotation θ`. -/
noncomputable def phasedWalk (φ θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  partialReflection (φ + Real.pi / 2) * branchRotation θ *
    partialReflection (-φ - Real.pi / 2)

/-- The encoded entry of the branch oracle is the signal eigenvalue:
`(branchOracle θ) 0 0 = cos θ`.  This is the `⟨G_λ| Û |G_λ⟩ = λ` corner of
the standard-form encoding in [LowChuang2019], Definition 1. -/
theorem branchOracle_apply_zero_zero (θ : ℝ) :
    branchOracle θ 0 0 = (Real.cos θ : ℂ) := by
  simp [branchOracle]

/-- The branch oracle is an involution, `Û² = I` on the eigenbranch.  This is
the hypothesis `Û² = Î` of [LowChuang2019], Corollary 9, in branch form. -/
theorem branchOracle_mul_self (θ : ℝ) :
    branchOracle θ * branchOracle θ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [branchOracle, Matrix.mul_apply, Fin.sum_univ_two] <;>
    rw [Complex.ext_iff] <;>
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re] <;>
    first
      | linear_combination Real.cos_sq_add_sin_sq θ
      | ring

/-- The branch oracle is Hermitian: together with
`branchOracle_mul_self`, it is a Hermitian unitary signal oracle as used for
a Hermitian signal operator in [LowChuang2019], Corollary 9. -/
theorem branchOracle_isHermitian (θ : ℝ) :
    (branchOracle θ).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [branchOracle, Matrix.conjTranspose_apply, Complex.ext_iff]

/-- Qubitization by a reflection on one eigenbranch: multiplying the
involutive signal oracle by `2|G_λ⟩⟨G_λ| - I` gives exactly the plane
rotation `branchRotation θ`.  This is the branch identity behind
[LowChuang2019], Theorem 2 and Corollary 9. -/
theorem branchReflection_mul_branchOracle (θ : ℝ) :
    branchReflection * branchOracle θ = branchRotation θ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [branchReflection, branchOracle, branchRotation, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- The qubitization walk on an eigenbranch is unitary.  This is the
unitarity of the iterate `Ŵ` in [LowChuang2019], Theorem 2, on the invariant
two-dimensional branch. -/
theorem branchRotation_mem_unitaryGroup (θ : ℝ) :
    branchRotation θ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [branchRotation, Matrix.mul_apply, Fin.sum_univ_two] <;>
    rw [Complex.ext_iff] <;>
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re] <;>
    first
      | linear_combination Real.cos_sq_add_sin_sq θ
      | ring

/-- Branch rotations compose by adding their angles:
`W_α W_β = W_{α + β}`. -/
theorem branchRotation_mul (α β : ℝ) :
    branchRotation α * branchRotation β = branchRotation (α + β) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [branchRotation, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add,
      Real.sin_add] <;> ring

/-- Powers of the qubitization walk rotate by multiples of the branch angle:
`(W_θ)^n = W_{nθ}`.  Each factor is one use of the iterate, so this is the
spectral content of applying the walk `n` times. -/
theorem branchRotation_pow (θ : ℝ) (n : ℕ) :
    (branchRotation θ) ^ n = branchRotation ((n : ℝ) * θ) := by
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp [branchRotation]
  | succ k ih =>
      rw [pow_succ, ih, branchRotation_mul]
      congr 1
      push_cast
      ring

/-- The encoded corner of the `n`-th power of the walk is the Chebyshev
polynomial of the first kind evaluated at the signal eigenvalue:
`⟨G_λ| Ŵ^n |G_λ⟩ = T_n (λ)` with `λ = cos θ`.  This is the polynomial action
underlying quantum signal processing on the qubitized walk. -/
theorem branchRotation_pow_apply_zero_zero (θ : ℝ) (n : ℕ) :
    ((branchRotation θ) ^ n) 0 0 =
      (((Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (Real.cos θ) : ℝ) : ℂ) := by
  rw [branchRotation_pow]
  simp [branchRotation, Polynomial.Chebyshev.T_real_cos]

/-- The lower branch entry of the `n`-th power of the walk is
`sin θ * U_{n-1} (cos θ)`, where `U` is the Chebyshev polynomial of the
second kind.  For `n = 0` this uses `U_{-1} = 0` in the same formula. -/
theorem branchRotation_pow_apply_one_zero (θ : ℝ) (n : ℕ) :
    ((branchRotation θ) ^ n) 1 0 =
      ((Real.sin θ *
        (Polynomial.Chebyshev.U ℝ ((n : ℤ) - 1)).eval (Real.cos θ) : ℝ) : ℂ) := by
  rw [branchRotation_pow]
  have h := Polynomial.Chebyshev.U_real_cos θ ((n : ℤ) - 1)
  push_cast at h
  have hn : ((n : ℝ) - 1 + 1) = (n : ℝ) := by ring
  rw [hn] at h
  have hentry : (branchRotation ((n : ℝ) * θ)) 1 0 =
      ((Real.sin ((n : ℝ) * θ) : ℝ) : ℂ) := by
    simp [branchRotation]
  rw [hentry, ← h]
  push_cast
  ring

/-- The vector `|G_λ⟩ - i |G_λ^⊥⟩` (written `![1, -I]`) is an eigenvector of
the branch walk with eigenphase `exp (θ * I)`.  Together with
`branchRotation_mulVec_eigen_minus`, this gives the eigenphases
`±θ_λ = ±arccos λ` of [LowChuang2019], Eq. (7). -/
theorem branchRotation_mulVec_eigen_plus (θ : ℝ) :
    branchRotation θ *ᵥ ![1, -Complex.I] =
      Complex.exp ((θ : ℂ) * Complex.I) • ![1, -Complex.I] := by
  funext i
  fin_cases i
  · simp [branchRotation, Matrix.mulVec, Complex.exp_ofReal_mul_I]
  · simp [branchRotation, Matrix.mulVec, Complex.exp_ofReal_mul_I]
    rw [Complex.ext_iff]
    simp

/-- The vector `|G_λ⟩ + i |G_λ^⊥⟩` (written `![1, I]`) is an eigenvector of
the branch walk with eigenphase `exp (-θ * I)`. -/
theorem branchRotation_mulVec_eigen_minus (θ : ℝ) :
    branchRotation θ *ᵥ ![1, Complex.I] =
      Complex.exp (-(θ : ℂ) * Complex.I) • ![1, Complex.I] := by
  have harg : -((θ : ℂ) * Complex.I) =
      (((-θ : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  have hre : (Complex.exp (-((θ : ℂ) * Complex.I))).re = Real.cos θ := by
    rw [harg, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  have him : (Complex.exp (-((θ : ℂ) * Complex.I))).im =
      -Real.sin θ := by
    rw [harg, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  funext i
  fin_cases i <;>
    simp [branchRotation, Matrix.mulVec] <;>
    rw [Complex.ext_iff] <;> simp [hre, him, Complex.cos_ofReal_re,
      Complex.sin_ofReal_re]

/-- Both branch eigenvectors are nonzero, so the two eigenphase conclusions
for the walk are non-vacuous. -/
theorem branch_eigenvectors_ne_zero :
    (![1, -Complex.I] : Fin 2 → ℂ) ≠ 0 ∧
      (![1, Complex.I] : Fin 2 → ℂ) ≠ 0 := by
  constructor <;> intro h <;>
    have := congrFun h 0 <;> simp at this

/-- For every real signal eigenvalue `λ ∈ [-1, 1]` there is a branch angle
`θ = arccos λ` whose oracle encodes `λ`, whose walk has encoded `n`-th-power
corner `T_n (λ)`, and whose two eigenphases are `exp (±θ * I)`.  This is the
eigenbranch spectral package of [LowChuang2019], Eqs. (4)–(7), applied to an
arbitrary Hermitian eigenvalue in the encoded range. -/
theorem exists_branch_walk_of_mem_Icc {lam : ℝ} (hlam : lam ∈ Set.Icc (-1) 1) :
    ∃ θ : ℝ, Real.cos θ = lam ∧ branchOracle θ 0 0 = (lam : ℂ) ∧
      (∀ n : ℕ, ((branchRotation θ) ^ n) 0 0 =
        (((Polynomial.Chebyshev.T ℝ (n : ℤ)).eval lam : ℝ) : ℂ)) ∧
      branchRotation θ *ᵥ ![1, -Complex.I] =
        Complex.exp ((θ : ℂ) * Complex.I) • ![1, -Complex.I] ∧
      branchRotation θ *ᵥ ![1, Complex.I] =
        Complex.exp (-(θ : ℂ) * Complex.I) • ![1, Complex.I] := by
  refine ⟨Real.arccos lam, Real.cos_arccos hlam.1 hlam.2, ?_, ?_,
    branchRotation_mulVec_eigen_plus _, branchRotation_mulVec_eigen_minus _⟩
  · rw [branchOracle_apply_zero_zero, Real.cos_arccos hlam.1 hlam.2]
  · intro n
    rw [branchRotation_pow_apply_zero_zero, Real.cos_arccos hlam.1 hlam.2]

/-- A partial reflection composed with its opposite phase is the identity:
`Z_φ Z_{-φ} = I`.  In particular `Z_{-φ}` is the inverse of `Z_φ`, because
the second branch entry `-1` is its own inverse. -/
theorem partialReflection_mul_neg (φ : ℝ) :
    partialReflection φ * partialReflection (-φ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [partialReflection, Matrix.mul_apply, Fin.sum_univ_two,
      ← Complex.exp_add]

/-- The opposite order of the same partial-reflection inverse identity:
`Z_{-φ} Z_φ = I`. -/
theorem partialReflection_neg_mul (φ : ℝ) :
    partialReflection (-φ) * partialReflection φ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [partialReflection, Matrix.mul_apply, Fin.sum_univ_two,
      ← Complex.exp_add]

/-- The phased iterate in explicit branch form.  Conjugation by the partial
reflections preserves the encoded corner `cos θ` and only dresses the two
off-diagonal entries by opposite phases, as in [LowChuang2019], Lemma 11,
Eq. (20). -/
theorem phasedWalk_eq (φ θ : ℝ) :
    phasedWalk φ θ =
      !![(Real.cos θ : ℂ),
          Complex.exp (-(Complex.I * ((φ + Real.pi / 2 : ℝ) : ℂ))) *
            (Real.sin θ : ℂ);
         -(Complex.exp (Complex.I * ((φ + Real.pi / 2 : ℝ) : ℂ))) *
            (Real.sin θ : ℂ),
          (Real.cos θ : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [phasedWalk, partialReflection, branchRotation, Matrix.mul_apply,
      Fin.sum_univ_two]
    have hprod : Complex.exp (-(Complex.I * (φ : ℂ)) +
          Complex.I * (Real.pi : ℂ) * (-1 / 2)) *
        Complex.exp (Complex.I * (φ : ℂ) +
          Complex.I * (Real.pi : ℂ) * (1 / 2)) = 1 := by
      rw [← Complex.exp_add]
      have hz : (-(Complex.I * (φ : ℂ)) +
            Complex.I * (Real.pi : ℂ) * (-1 / 2)) +
          (Complex.I * (φ : ℂ) +
            Complex.I * (Real.pi : ℂ) * (1 / 2)) = 0 := by ring
      rw [hz]
      exact Complex.exp_zero
    have e1 : Complex.exp (-(Complex.I * ((φ : ℂ) + (Real.pi : ℂ) / 2))) =
        Complex.exp (-(Complex.I * (φ : ℂ)) +
          Complex.I * (Real.pi : ℂ) * (-1 / 2)) := by
      congr 1
      ring
    have e2 : Complex.exp (-(Complex.I * (-(φ : ℂ) - (Real.pi : ℂ) / 2))) =
        Complex.exp (Complex.I * (φ : ℂ) +
          Complex.I * (Real.pi : ℂ) * (1 / 2)) := by
      congr 1
      ring
    rw [e1, e2]
    linear_combination (Complex.cos (θ : ℂ)) * hprod
  · simp [phasedWalk, partialReflection, branchRotation, Matrix.mul_apply,
      Fin.sum_univ_two]
  · simp [phasedWalk, partialReflection, branchRotation, Matrix.mul_apply,
      Fin.sum_univ_two]
    have e2 : Complex.exp (-(Complex.I * (-(φ : ℂ) - (Real.pi : ℂ) / 2))) =
        Complex.exp (Complex.I * ((φ : ℂ) + (Real.pi : ℂ) / 2)) := by
      congr 1
      ring
    rw [e2]
    ring
  · simp [phasedWalk, partialReflection, branchRotation, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- Powers of a conjugate are conjugates of powers. This algebraic step
transports the walk spectrum to the phased iterate. -/
theorem conj_pow {Z Zinv R : Matrix (Fin 2) (Fin 2) ℂ}
    (hinv : Zinv * Z = 1) (hinv' : Z * Zinv = 1) (n : ℕ) :
    (Z * R * Zinv) ^ n = Z * R ^ n * Zinv := by
  induction n with
  | zero => simp [hinv']
  | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      calc Z * R ^ k * Zinv * (Z * R * Zinv)
          = Z * R ^ k * (Zinv * Z) * R * Zinv := by noncomm_ring
        _ = Z * (R ^ k * R) * Zinv := by
            rw [hinv]
            noncomm_ring

/-- Powers of the phased iterate are the same partial-reflection conjugation
applied to powers of the unphased walk:
`(W_φ)^n = Z_{φ + π/2} W^n Z_{-φ - π/2}`.  Hence the phased iterate has the
same Chebyshev encoded corner and the same eigenphases as `W`. -/
theorem phasedWalk_pow (φ θ : ℝ) (n : ℕ) :
    (phasedWalk φ θ) ^ n =
      partialReflection (φ + Real.pi / 2) * (branchRotation θ) ^ n *
        partialReflection (-φ - Real.pi / 2) := by
  have harg : -φ - Real.pi / 2 = -(φ + Real.pi / 2) := by ring
  have hinv : partialReflection (-φ - Real.pi / 2) *
        partialReflection (φ + Real.pi / 2) = 1 := by
    rw [harg]
    exact partialReflection_neg_mul _
  have hinv' : partialReflection (φ + Real.pi / 2) *
        partialReflection (-φ - Real.pi / 2) = 1 := by
    rw [harg]
    exact partialReflection_mul_neg _
  exact conj_pow hinv hinv' n

/-- Conjugation by a partial reflection does not change the encoded
`(0, 0)` entry of a branch operator: the two opposite phases at the signal
entry cancel. -/
theorem partialReflection_conj_apply_zero_zero (φ : ℝ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (partialReflection φ * M * partialReflection (-φ)) 0 0 = M 0 0 := by
  have hprod : Complex.exp (-(Complex.I * (φ : ℂ))) *
      Complex.exp (-(Complex.I * ((-φ : ℝ) : ℂ))) = 1 := by
    rw [← Complex.exp_add]
    have hz : -(Complex.I * (φ : ℂ)) +
        -(Complex.I * ((-φ : ℝ) : ℂ)) = 0 := by
      push_cast
      ring
    rw [hz]
    exact Complex.exp_zero
  have e1 := (Matrix.two_mul_expl (partialReflection φ * M)
    (partialReflection (-φ))).1
  have e2 := (Matrix.two_mul_expl (partialReflection φ) M).1
  have e3 := (Matrix.two_mul_expl (partialReflection φ) M).2.1
  rw [e1, e2, e3]
  simp only [partialReflection, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  linear_combination (M 0 0) * hprod

/-- The encoded corner of a power of the phased iterate equals the Chebyshev
corner of the unphased walk: conjugation by a diagonal partial reflection
does not change the `(0, 0)` entry. -/
theorem phasedWalk_pow_apply_zero_zero (φ θ : ℝ) (n : ℕ) :
    ((phasedWalk φ θ) ^ n) 0 0 =
      (((Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (Real.cos θ) : ℝ) : ℂ) := by
  have harg : -φ - Real.pi / 2 = -(φ + Real.pi / 2) := by ring
  rw [phasedWalk_pow, harg, partialReflection_conj_apply_zero_zero,
    branchRotation_pow_apply_zero_zero]

/-- The conjugated branch eigenvector is an eigenvector of the phased
iterate with the same eigenphase `exp (θ * I)`: if `v` is the
`exp (θ * I)` eigenvector of `W`, then `Z_{φ + π/2} v` is the corresponding
eigenvector of `W_φ`. -/
theorem phasedWalk_mulVec_conj_eigen_plus (φ θ : ℝ) :
    phasedWalk φ θ *ᵥ
        (partialReflection (φ + Real.pi / 2) *ᵥ ![1, -Complex.I]) =
      Complex.exp ((θ : ℂ) * Complex.I) •
        (partialReflection (φ + Real.pi / 2) *ᵥ ![1, -Complex.I]) := by
  have harg : -φ - Real.pi / 2 = -(φ + Real.pi / 2) := by ring
  have hinv : partialReflection (-φ - Real.pi / 2) *
        partialReflection (φ + Real.pi / 2) = 1 := by
    rw [harg]
    exact partialReflection_neg_mul _
  rw [phasedWalk, Matrix.mulVec_mulVec, Matrix.mul_assoc, hinv,
    Matrix.mul_one, ← Matrix.mulVec_mulVec,
    branchRotation_mulVec_eigen_plus, Matrix.mulVec_smul]

open Qatlib.Foundations.PureStateMath in
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding in
/-- The actual reflected oracle and all its powers act as `branchRotation`
in the same orthonormal frame on an interior eigenbranch. The two Eq. (17)
corners are assumed for the input oracle, as in the sufficient direction
of [LowChuang2019], Lemma 8. -/
theorem eq17_branch_rotation_powers {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (U : Matrix (J × I) (J × I) ℂ) (hU : U ∈ Matrix.unitaryGroup (J × I) ℂ)
    (j₀ : J) (A : Matrix I I ℂ) (hc : BlockCorner U j₀ = A)
    (h2 : BlockCorner (U * U) j₀ = 1) (ψ : QState I) (hψ : Normalized ψ)
    (x : ℝ) (hx : |x| < 1) (hAψ : A *ᵥ ψ = (x : ℂ) • ψ) :
    ∃ E : Matrix (J × I) (Fin 2) ℂ,
      E.col 0 = TensorState (Ket j₀) ψ ∧ Normalized (E.col 0) ∧
      Normalized (E.col 1) ∧ Inner (E.col 0) (E.col 1) = 0 ∧
      ∀ n : ℕ, (FiberReflection j₀ * U) ^ n * E =
        E * (branchRotation (Real.arccos x)) ^ n := by
  obtain ⟨χ, hσ, hχ, horth, _, h0, h1⟩ :=
    eq17_rotation_vectors U hU j₀ A hc h2 ψ hψ x hx hAψ
  let E : Matrix (J × I) (Fin 2) ℂ := Matrix.of fun k => ![TensorState (Ket j₀) ψ k, χ k]
  refine ⟨E, rfl, hσ, hχ, horth, ?_⟩
  have hstep : (FiberReflection j₀ * U) * E = E * branchRotation (Real.arccos x) := by
    have hcos := Real.cos_arccos (abs_lt.mp hx).1.le (abs_lt.mp hx).2.le
    ext k j
    fin_cases j
    · have hh := congrFun h0 k
      simpa [E, branchRotation, hcos, Real.sin_arccos, Matrix.mul_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm] using hh
    · have hh := congrFun h1 k
      simpa [E, branchRotation, hcos, Real.sin_arccos, Matrix.mul_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm] using hh
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' (FiberReflection j₀ * U), Matrix.mul_assoc, ih,
      ← Matrix.mul_assoc, hstep, Matrix.mul_assoc, ← pow_succ']

end Qatlib.Papers.Qubitization19.MainResults
