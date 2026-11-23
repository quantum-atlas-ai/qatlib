/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Qatlib.Foundations.PureStateMath.Qubit
public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

@[expose] public section

/-!
# Hadamard-test autocorrelation readout

Appendix D of [FillionGourdeauMacLeanLaflamme2017] estimates the autocorrelation of Eq. (D1)
using the finite-register circuit in Fig. 9. The Hadamard and controlled evolution prepare
the state of Eq. (D4). Separate measurements of `σₓ` and `σ_y` on the ancilla give the real and
imaginary parts of the discretized autocorrelation in Eqs. (D5) and (D6).

On the register `Fin 2 × Fin d` (ancilla tensor system) the circuit word is
`controlledEvolution U * (hadamardAncilla ⊗ₖ I)`, applied to `|0⟩ ⊗ ψ`. The module proves that
the output state is `(1/√2)(|0⟩ ⊗ ψ + |1⟩ ⊗ Uψ)`, that the ancilla expectations of `σₓ` and
`σ_y` are the real and imaginary parts of `C = Inner ψ (U *ᵥ ψ)` (so `σₓ + iσ_y` reads `C`,
Eq. (D5)). The corresponding spectral projectors have Born probabilities
`(1 ± Re C) / 2` and `(1 ± Im C) / 2`.

## Main statements

* `autoCorrWord_mulVec`: the circuit word maps `|0⟩ ⊗ ψ` to the Eq. (D4) state.
* `inner_corrState_kron_one`: master identity reducing ancilla-bilinear forms to the branch
  inner products with the constant `2⁻¹` outside the sum.
* `expect_sigmaX` / `expect_sigmaY`: `⟨σₓ⟩ = (C + C̄)/2`, `⟨σ_y⟩ = (C̄ - C)·i/2`.
* `expect_sigmaX_add_i_mul_sigmaY`: `⟨σₓ + iσ_y⟩ = C`, Eq. (D5).
* `expect_sigmaX_euclidean`: the Euclidean-space form of the `σₓ` expectation.
* `born_sigmaX_plus` / `born_sigmaX_minus`: Born probabilities `(1 ± Re C) / 2`.
* `corrState_norm`: the readout state has Euclidean norm one.

## References

* [Fillion-Gourdeau et al., 2017][FillionGourdeauMacLeanLaflamme2017]
-/

set_option autoImplicit false

open Matrix
open scoped Matrix BigOperators Matrix.Norms.L2Operator Kronecker ComplexConjugate

namespace Qatlib.Papers.DiracEquation16.AutoCorrel

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

variable {d : ℕ}

/-- The norm squared of `(√2)⁻¹ • z` is `(1/2) ‖z‖²`. -/
theorem norm_mul_sqrtTwo_inv (z : ℂ) :
    ‖((Real.sqrt 2)⁻¹ : ℂ) * z‖ ^ 2 = (2⁻¹ : ℝ) * ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_mul, show ((Real.sqrt 2)⁻¹ : ℂ) = (↑(Real.sqrt 2) : ℂ)⁻¹
    from rfl, Complex.normSq_inv, Complex.normSq_ofReal,
    Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num), ← Complex.sq_norm]

/-- The norm squared of `(1/2) • z` is `(1/2)² ‖z‖²`. -/
theorem norm_mul_twoInv (z : ℂ) :
    ‖(2⁻¹ : ℂ) * z‖ ^ 2 = (2⁻¹:ℝ) ^ 2 * ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_mul, show (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) by norm_num,
    Complex.normSq_ofReal, show (2⁻¹:ℝ) * (2⁻¹:ℝ) = (2⁻¹:ℝ) ^ 2 by ring, ← Complex.sq_norm]

/-- The norm squared of `(i/2) • z` is `(1/2)² ‖z‖²`. -/
theorem norm_mul_I_twoInv (z : ℂ) :
    ‖(2⁻¹ : ℂ) * Complex.I * z‖ ^ 2 = (2⁻¹:ℝ) ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one, show (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) by norm_num,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ) ≤ 2⁻¹ by norm_num), mul_pow]

/-- Multiplication by `i` preserves the complex norm. -/
theorem norm_mul_I (z : ℂ) : ‖Complex.I * z‖ = ‖z‖ := by
  rw [norm_mul, Complex.norm_I, one_mul]

/-- The ancilla Hadamard gate `(1/√2) [[1, 1], [1, -1]]` of Fig. 9. -/
noncomputable def hadamardAncilla : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) • !![1, 1; 1, -1]

/-- The ancilla Pauli-X matrix. -/
def sigmaX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The ancilla Pauli-Y matrix. -/
def sigmaY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The controlled-evolution operator `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U` of Fig. 9. -/
noncomputable def controlledEvolution (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ :=
  Matrix.of fun (b, i) (b', i') =>
    (if b = 0 then (1 : Matrix (Fin d) (Fin d) ℂ) else U) i i' * (if b = b' then (1 : ℂ) else 0)

/-- The autocorrelation readout state of Eq. (D4) after the controlled evolution. -/
noncomputable def corrState (U : Matrix (Fin d) (Fin d) ℂ) (ψ : QState (Fin d)) :
    QState (Fin 2 × Fin d) :=
  fun p => ((Real.sqrt 2)⁻¹ : ℂ) * (if p.1 = 0 then ψ p.2 else (U *ᵥ ψ) p.2)

/-- The autocorrelation amplitude `C = ⟨ψ, Uψ⟩` of Eqs. (D1) and (D5). -/
noncomputable def corr (U : Matrix (Fin d) (Fin d) ℂ) (ψ : QState (Fin d)) : ℂ :=
  Inner ψ (U *ᵥ ψ)

/-- Sum of the two readout branches. -/
theorem corrState_add (U : Matrix (Fin d) (Fin d) ℂ) (ψ : QState (Fin d)) (i : Fin d) :
    corrState U ψ (0, i) + corrState U ψ (1, i)
      = ((Real.sqrt 2)⁻¹ : ℂ) * (ψ i + (U *ᵥ ψ) i) := by
  simp [corrState]
  ring

/-- Difference of the two readout branches. -/
theorem corrState_sub (U : Matrix (Fin d) (Fin d) ℂ) (ψ : QState (Fin d)) (i : Fin d) :
    corrState U ψ (0, i) - corrState U ψ (1, i)
      = ((Real.sqrt 2)⁻¹ : ℂ) * (ψ i - (U *ᵥ ψ) i) := by
  simp [corrState]
  ring

/-- The `|0⟩` branch minus `i` times the `|1⟩` branch. -/
theorem corrState_sub_I (U : Matrix (Fin d) (Fin d) ℂ) (ψ : QState (Fin d)) (i : Fin d) :
    corrState U ψ (0, i) - Complex.I * corrState U ψ (1, i)
      = ((Real.sqrt 2)⁻¹ : ℂ) * (ψ i - Complex.I * (U *ᵥ ψ) i) := by
  simp [corrState]
  ring

/-- The `|0⟩` branch plus `i` times the `|1⟩` branch. -/
theorem corrState_add_I (U : Matrix (Fin d) (Fin d) ℂ) (ψ : QState (Fin d)) (i : Fin d) :
    corrState U ψ (0, i) + Complex.I * corrState U ψ (1, i)
      = ((Real.sqrt 2)⁻¹ : ℂ) * (ψ i + Complex.I * (U *ᵥ ψ) i) := by
  simp [corrState]
  ring

/-- The full ancilla circuit word of Fig. 9: controlled evolution after the ancilla
Hadamard. -/
noncomputable def autoCorrWord (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ :=
  controlledEvolution U * (hadamardAncilla ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))

/-- Conjugation fixes the real amplitude `(√2)⁻¹`. -/
theorem conj_sqrtTwo_inv : conj ((Real.sqrt 2)⁻¹ : ℂ) = ((Real.sqrt 2)⁻¹ : ℂ) := by
  rw [show ((Real.sqrt 2)⁻¹ : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ from rfl, map_inv₀,
    Complex.conj_ofReal]

/-- The squared Hadamard amplitude is `1/2`. -/
theorem sqrtTwo_inv_mul_self : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = (2⁻¹ : ℂ) := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- Pointwise action of `A ⊗ₖ I` on the product register: only the ancilla index mixes. -/
theorem kron_one_mulVec_apply (A : Matrix (Fin 2) (Fin 2) ℂ) (v : QState (Fin 2 × Fin d))
    (b : Fin 2) (i : Fin d) :
    ((A ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ v) (b, i) = ∑ b' : Fin 2, A b b' * v (b', i) := by
  show ∑ q ∈ Finset.univ ×ˢ Finset.univ, (A ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) (b, i) q * v q =
    ∑ b' : Fin 2, A b b' * v (b', i)
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun b' _ => ?_
  show ∑ i' : Fin d, (A b b' * (1 : Matrix (Fin d) (Fin d) ℂ) i i') * v (b', i') = A b b' * v (b', i)
  rw [Finset.sum_congr rfl fun i' _ => (by ring : (A b b' * (1 : Matrix (Fin d) (Fin d) ℂ) i i') *
      v (b', i') = A b b' * ((1 : Matrix (Fin d) (Fin d) ℂ) i i' * v (b', i'))), ← Finset.mul_sum]
  congr 1
  simp [Matrix.one_apply]

/-- The ancilla Hadamard tensor identity maps `|0⟩ ⊗ ψ` to `(1/√2) (|0⟩ + |1⟩) ⊗ ψ`, since
every entry of its first column is `(√2)⁻¹`. -/
theorem kron_hadamard_one_mulVec_tensor (ψ : QState (Fin d)) (b' : Fin 2) (i' : Fin d) :
    ((hadamardAncilla ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ TensorState (Ket (0 : Fin 2)) ψ)
        (b', i')
      = ((Real.sqrt 2)⁻¹ : ℂ) * ψ i' := by
  show ∑ q ∈ Finset.univ ×ˢ Finset.univ,
      (hadamardAncilla ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) (b', i') q *
        TensorState (Ket (0 : Fin 2)) ψ q = _
  rw [Finset.sum_product]
  show (∑ b'' : Fin 2, ∑ i'' : Fin d,
      (hadamardAncilla b' b'' * (1 : Matrix (Fin d) (Fin d) ℂ) i' i'') *
        ((Ket (0 : Fin 2)) b'' * ψ i'')) = _
  rw [Finset.sum_congr rfl fun b'' _ => (by
    show (∑ i'' : Fin d, (hadamardAncilla b' b'' * (1 : Matrix (Fin d) (Fin d) ℂ) i' i'') *
        ((Ket (0 : Fin 2)) b'' * ψ i'')) =
      hadamardAncilla b' b'' * ((Ket (0 : Fin 2)) b'') * ψ i'
    rw [Finset.sum_congr rfl fun i'' _ => (by ring : (hadamardAncilla b' b'' *
        (1 : Matrix (Fin d) (Fin d) ℂ) i' i'') * ((Ket (0 : Fin 2)) b'' * ψ i'') =
      (hadamardAncilla b' b'' * (Ket (0 : Fin 2)) b'') *
        ((1 : Matrix (Fin d) (Fin d) ℂ) i' i'' * ψ i'')), ← Finset.mul_sum]
    congr 1
    simp [Matrix.one_apply])]
  rw [Fin.sum_univ_two]
  fin_cases b' <;> simp [hadamardAncilla, Matrix.smul_apply, Ket]

/-- The circuit word of Fig. 9 applied to `|0⟩ ⊗ ψ` produces the state of Eq. (D4). -/
theorem autoCorrWord_mulVec (U : Matrix (Fin d) (Fin d) ℂ) (ψ : QState (Fin d)) :
    autoCorrWord U *ᵥ TensorState (Ket (0 : Fin 2)) ψ = corrState U ψ := by
  funext p
  obtain ⟨b, i⟩ := p
  simp only [autoCorrWord]
  rw [← Matrix.mulVec_mulVec]
  have hH : ((hadamardAncilla ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ
      TensorState (Ket (0 : Fin 2)) ψ) = fun q : Fin 2 × Fin d =>
        ((Real.sqrt 2)⁻¹ : ℂ) * ψ q.2 :=
    funext fun q => by obtain ⟨b', i'⟩ := q; exact kron_hadamard_one_mulVec_tensor ψ b' i'
  rw [hH]
  show (∑ q ∈ Finset.univ ×ˢ Finset.univ, controlledEvolution U (b, i) q *
      (((Real.sqrt 2)⁻¹ : ℂ) * ψ q.2)) = ((Real.sqrt 2)⁻¹ : ℂ) *
    (if b = 0 then ψ i else (U *ᵥ ψ) i)
  rw [Finset.sum_product]
  fin_cases b
  · show (∑ x : Fin 2, ∑ i' : Fin d, controlledEvolution U (0, i) (x, i') *
        (((Real.sqrt 2)⁻¹ : ℂ) * ψ i')) = ((Real.sqrt 2)⁻¹ : ℂ) * ψ i
    rw [Fin.sum_univ_two]
    simp [controlledEvolution, Matrix.one_apply, Finset.sum_ite_eq,
       mul_comm, mul_left_comm]
  · show (∑ x : Fin 2, ∑ i' : Fin d, controlledEvolution U (1, i) (x, i') *
        (((Real.sqrt 2)⁻¹ : ℂ) * ψ i')) = ((Real.sqrt 2)⁻¹ : ℂ) * (U *ᵥ ψ) i
    rw [Fin.sum_univ_two]
    simp [controlledEvolution, Matrix.mulVec_apply,
       mul_comm, mul_left_comm]
    rw [Finset.sum_congr rfl fun x _ => (by ring : U i x * (ψ x * ((Real.sqrt 2)⁻¹ : ℂ))
      = (U i x * ψ x) * ((Real.sqrt 2)⁻¹ : ℂ)), ← Finset.sum_mul]
    exact rfl

/-- Master identity: ancilla-bilinear forms on the readout state reduce to the branch inner
products with the uniform Hadamard factor `2⁻¹` outside the sum. -/
theorem inner_corrState_kron_one (A : Matrix (Fin 2) (Fin 2) ℂ) (U : Matrix (Fin d) (Fin d) ℂ)
    (ψ : QState (Fin d)) :
    Inner (corrState U ψ) (ApplyGate (A ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) (corrState U ψ))
      = (2⁻¹ : ℂ) * ∑ b : Fin 2, ∑ b' : Fin 2, A b b' *
        Inner (if b = 0 then ψ else U *ᵥ ψ) (if b' = 0 then ψ else U *ᵥ ψ) := by
  rw [inner_apply]
  show (∑ p : Fin 2 × Fin d, (starRingEnd ℂ) (corrState U ψ p) *
      ApplyGate (A ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) (corrState U ψ) p) = _
  simp only [ApplyGate]
  have hstep : (∑ p : Fin 2 × Fin d, (starRingEnd ℂ) (corrState U ψ p) *
        ((A ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) p)
      = ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) *
        (∑ b : Fin 2, ∑ b' : Fin 2, A b b' *
          Inner (if b = 0 then ψ else U *ᵥ ψ) (if b' = 0 then ψ else U *ᵥ ψ)) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    have h1 : (∑ y : Fin d, (starRingEnd ℂ) (corrState U ψ (b, y)) *
          ((A ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) (b, y))
        = ∑ i : Fin d, ∑ b' : Fin 2, (starRingEnd ℂ) (corrState U ψ (b, i)) *
            (A b b' * corrState U ψ (b', i)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [kron_one_mulVec_apply A (corrState U ψ) b i, Finset.mul_sum]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [inner_apply, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [corrState, map_mul, conj_sqrtTwo_inv, ite_apply]
    ring
  rw [hstep, sqrtTwo_inv_mul_self]

/-- The `σₓ` expectation on the readout state is the real part `(C + C̄)/2` of the
autocorrelation. -/
theorem expect_sigmaX (U : Matrix (Fin d) (Fin d) ℂ) (ψ : QState (Fin d)) :
    Inner (corrState U ψ) (ApplyGate (sigmaX ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) (corrState U ψ))
      = (corr U ψ + (starRingEnd ℂ) (corr U ψ)) / 2 := by
  rw [inner_corrState_kron_one]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp [sigmaX]
  rw [show Inner (U *ᵥ ψ) ψ = (starRingEnd ℂ) (corr U ψ) from by
    rw [corr]; exact BornBridge.inner_conj_symm (U *ᵥ ψ) ψ]
  simp only [corr]
  ring

/-- The `σ_y` expectation on the readout state is `(C̄ - C)·i/2`, the imaginary part of the
autocorrelation. -/
theorem expect_sigmaY (U : Matrix (Fin d) (Fin d) ℂ) (ψ : QState (Fin d)) :
    Inner (corrState U ψ) (ApplyGate (sigmaY ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) (corrState U ψ))
      = ((starRingEnd ℂ) (corr U ψ) - corr U ψ) * Complex.I / 2 := by
  rw [inner_corrState_kron_one]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp [sigmaY]
  rw [show Inner (U *ᵥ ψ) ψ = (starRingEnd ℂ) (corr U ψ) from by
    rw [corr]; exact BornBridge.inner_conj_symm (U *ᵥ ψ) ψ]
  simp only [corr]
  ring

/-- The combined ancilla measurement of Eq. (D5): `⟨(σₓ + iσ_y) ⊗ I⟩ = C`. -/
theorem expect_sigmaX_add_i_mul_sigmaY (U : Matrix (Fin d) (Fin d) ℂ) (ψ : QState (Fin d)) :
    Inner (corrState U ψ) (ApplyGate ((sigmaX + Complex.I • sigmaY) ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ)) (corrState U ψ))
      = corr U ψ := by
  have hsplit : (sigmaX + Complex.I • sigmaY) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)
      = sigmaX ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ) +
        Complex.I • (sigmaY ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp [Matrix.kroneckerMap_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_add,
      mul_comm, mul_left_comm]
  rw [hsplit]
  simp only [ApplyGate, Matrix.add_mulVec, Matrix.smul_mulVec]
  have key : Inner (corrState U ψ) ((sigmaX ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ +
      Complex.I • ((sigmaY ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ))
      = Inner (corrState U ψ) ((sigmaX ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ)
        + Complex.I * Inner (corrState U ψ)
          ((sigmaY ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) := by
    show (∑ i, (starRingEnd ℂ) (corrState U ψ i) *
        (((sigmaX ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) i +
          Complex.I * ((sigmaY ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) i))
      = (∑ i, (starRingEnd ℂ) (corrState U ψ i) *
          ((sigmaX ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) i) + Complex.I *
        (∑ i, (starRingEnd ℂ) (corrState U ψ i) *
          ((sigmaY ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) i)
    rw [Finset.sum_congr rfl fun i _ => (by ring : (starRingEnd ℂ) (corrState U ψ i) *
        (((sigmaX ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) i +
          Complex.I * ((sigmaY ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) i) =
      (starRingEnd ℂ) (corrState U ψ i) * ((sigmaX ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ
        corrState U ψ) i + (starRingEnd ℂ) (corrState U ψ i) *
        (Complex.I * ((sigmaY ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) i)),
      Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [key]
  rw [show (sigmaX ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ
      = ApplyGate (sigmaX ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) (corrState U ψ) from rfl,
    show (sigmaY ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ
      = ApplyGate (sigmaY ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) (corrState U ψ) from rfl]
  rw [expect_sigmaX, expect_sigmaY]
  have h2 : Complex.I * (((starRingEnd ℂ) (corr U ψ) - corr U ψ) * Complex.I / 2)
      = (corr U ψ - (starRingEnd ℂ) (corr U ψ)) / 2 := by
    rw [show Complex.I * (((starRingEnd ℂ) (corr U ψ) - corr U ψ) * Complex.I / 2)
        = ((starRingEnd ℂ) (corr U ψ) - corr U ψ) * (Complex.I * Complex.I) / 2 from by ring,
      Complex.I_mul_I]
    ring
  rw [h2]
  ring

/-- The Euclidean-space form of the `σₓ` expectation: the true EuclideanSpace inner product
with the `σₓ ⊗ I` action reproduces `(C + C̄)/2`. -/
theorem expect_sigmaX_euclidean (U : Matrix (Fin d) (Fin d) ℂ) (ψ : QState (Fin d)) :
    inner ℂ (toEuclidean_fromVec (corrState U ψ))
      ((Matrix.toEuclideanCLM : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ ≃⋆ₐ[ℂ]
        (EuclideanSpace ℂ (Fin 2 × Fin d) →L[ℂ] EuclideanSpace ℂ (Fin 2 × Fin d)))
        (sigmaX ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) (toEuclidean_fromVec (corrState U ψ)))
      = (corr U ψ + (starRingEnd ℂ) (corr U ψ)) / 2 := by
  rw [toEuclideanCLM_applyGate, inner_euclidean_fromVec, expect_sigmaX]

/-- The Euclidean-space form of the `σ_y` expectation. -/
theorem expect_sigmaY_euclidean (U : Matrix (Fin d) (Fin d) ℂ) (ψ : QState (Fin d)) :
    inner ℂ (toEuclidean_fromVec (corrState U ψ))
      ((Matrix.toEuclideanCLM : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ ≃⋆ₐ[ℂ]
        (EuclideanSpace ℂ (Fin 2 × Fin d) →L[ℂ] EuclideanSpace ℂ (Fin 2 × Fin d)))
        (sigmaY ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) (toEuclidean_fromVec (corrState U ψ)))
      = ((starRingEnd ℂ) (corr U ψ) - corr U ψ) * Complex.I / 2 := by
  rw [toEuclideanCLM_applyGate, inner_euclidean_fromVec, expect_sigmaY]

/-- The Euclidean-space form of Eq. (D5): `⟨(σₓ + iσ_y) ⊗ I⟩ = C`. -/
theorem expect_readout_euclidean (U : Matrix (Fin d) (Fin d) ℂ) (ψ : QState (Fin d)) :
    inner ℂ (toEuclidean_fromVec (corrState U ψ))
      ((Matrix.toEuclideanCLM : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ ≃⋆ₐ[ℂ]
        (EuclideanSpace ℂ (Fin 2 × Fin d) →L[ℂ] EuclideanSpace ℂ (Fin 2 × Fin d)))
        ((sigmaX + Complex.I • sigmaY) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))
        (toEuclidean_fromVec (corrState U ψ)))
      = corr U ψ := by
  rw [toEuclideanCLM_applyGate, inner_euclidean_fromVec, expect_sigmaX_add_i_mul_sigmaY]

/-- The spectral projector `(I + σₓ)/2` onto the `σₓ`-eigenvalue `+1`, with entries `1/2`. -/
noncomputable def projSigmaXPlus : Matrix (Fin 2) (Fin 2) ℂ := !![2⁻¹, 2⁻¹; 2⁻¹, 2⁻¹]

/-- The spectral projector `(I - σₓ)/2` onto the `σₓ`-eigenvalue `-1`. -/
noncomputable def projSigmaXMinus : Matrix (Fin 2) (Fin 2) ℂ := !![2⁻¹, -2⁻¹; -2⁻¹, 2⁻¹]

/-- The spectral projector `(I + σ_y)/2` onto the `σ_y`-eigenvalue `+1`. -/
noncomputable def projSigmaYPlus : Matrix (Fin 2) (Fin 2) ℂ :=
  !![2⁻¹, -(Complex.I / 2); Complex.I / 2, 2⁻¹]

/-- The spectral projector `(I - σ_y)/2` onto the `σ_y`-eigenvalue `-1`. -/
noncomputable def projSigmaYMinus : Matrix (Fin 2) (Fin 2) ℂ :=
  !![2⁻¹, Complex.I / 2; -(Complex.I / 2), 2⁻¹]

/-- Pointwise action of the `σₓ` `+1`-projector on the readout state. -/
theorem projSigmaXPlus_apply (U : Matrix (Fin d) (Fin d) ℂ) (ψ : QState (Fin d)) (b : Fin 2)
    (i : Fin d) :
    ((projSigmaXPlus ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) (b, i)
      = (2⁻¹ : ℂ) * (corrState U ψ (0, i) + corrState U ψ (1, i)) := by
  rw [kron_one_mulVec_apply]
  fin_cases b <;> simp [projSigmaXPlus] <;> ring

/-- Pointwise action of the `σₓ` `-1`-projector on the `|0⟩` ancilla branch. -/
theorem projSigmaXMinus_apply_zero (U : Matrix (Fin d) (Fin d) ℂ) (ψ : QState (Fin d))
    (i : Fin d) :
    ((projSigmaXMinus ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) (0, i)
      = (2⁻¹ : ℂ) * (corrState U ψ (0, i) - corrState U ψ (1, i)) := by
  rw [kron_one_mulVec_apply]
  simp [projSigmaXMinus]
  ring

/-- Pointwise action of the `σₓ` `-1`-projector on the `|1⟩` ancilla branch. -/
theorem projSigmaXMinus_apply_one (U : Matrix (Fin d) (Fin d) ℂ) (ψ : QState (Fin d))
    (i : Fin d) :
    ((projSigmaXMinus ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) (1, i)
      = (2⁻¹ : ℂ) * -(corrState U ψ (0, i) - corrState U ψ (1, i)) := by
  rw [kron_one_mulVec_apply]
  simp [projSigmaXMinus]
  ring

/-- Pointwise action of the `σ_y` `+1`-projector on the `|0⟩` ancilla branch. -/
theorem projSigmaYPlus_apply_zero (U : Matrix (Fin d) (Fin d) ℂ) (ψ : QState (Fin d))
    (i : Fin d) :
    ((projSigmaYPlus ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) (0, i)
      = (2⁻¹ : ℂ) * (corrState U ψ (0, i) - Complex.I * corrState U ψ (1, i)) := by
  rw [kron_one_mulVec_apply]
  simp [projSigmaYPlus]
  ring

/-- Pointwise action of the `σ_y` `+1`-projector on the `|1⟩` ancilla branch. -/
theorem projSigmaYPlus_apply_one (U : Matrix (Fin d) (Fin d) ℂ) (ψ : QState (Fin d))
    (i : Fin d) :
    ((projSigmaYPlus ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) (1, i)
      = (2⁻¹ : ℂ) * Complex.I * (corrState U ψ (0, i) - Complex.I * corrState U ψ (1, i)) := by
  rw [kron_one_mulVec_apply]
  simp [projSigmaYPlus, Fin.sum_univ_two, mul_add, mul_comm,
    mul_left_comm, mul_assoc, sub_eq_add_neg, mul_neg]
  rw [show Complex.I * (Complex.I * ((2⁻¹ : ℂ) * corrState U ψ (1, i)))
      = -((2⁻¹ : ℂ) * corrState U ψ (1, i)) from by
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]]
  ring

/-- Pointwise action of the `σ_y` `-1`-projector on the `|0⟩` ancilla branch. -/
theorem projSigmaYMinus_apply_zero (U : Matrix (Fin d) (Fin d) ℂ) (ψ : QState (Fin d))
    (i : Fin d) :
    ((projSigmaYMinus ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) (0, i)
      = (2⁻¹ : ℂ) * (corrState U ψ (0, i) + Complex.I * corrState U ψ (1, i)) := by
  rw [kron_one_mulVec_apply]
  simp [projSigmaYMinus]
  ring

/-- Pointwise action of the `σ_y` `-1`-projector on the `|1⟩` ancilla branch. -/
theorem projSigmaYMinus_apply_one (U : Matrix (Fin d) (Fin d) ℂ) (ψ : QState (Fin d))
    (i : Fin d) :
    ((projSigmaYMinus ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) (1, i)
      = (2⁻¹ : ℂ) * (Complex.I * -(corrState U ψ (0, i) + Complex.I * corrState U ψ (1, i))) := by
  rw [kron_one_mulVec_apply]
  simp [projSigmaYMinus, Fin.sum_univ_two, mul_add,
    mul_left_comm, mul_neg, neg_mul]
  rw [show Complex.I * (Complex.I * ((2⁻¹ : ℂ) * corrState U ψ (1, i)))
      = -((2⁻¹ : ℂ) * corrState U ψ (1, i)) from by
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]]
  ring

/-- The sum of squared norms of a two-branch combination on the system register, in terms of
the branch inner products. -/
theorem normSq_branch_add (g h : QState (Fin d)) :
    (∑ i : Fin d, ‖g i + h i‖ ^ 2 : ℝ)
      = (∑ i : Fin d, ‖g i‖ ^ 2 : ℝ) + (∑ i : Fin d, ‖h i‖ ^ 2 : ℝ)
        + 2 * ((Inner g h).re : ℝ) := by
  have e : ∀ i : Fin d, ‖g i + h i‖ ^ 2
      = ‖g i‖ ^ 2 + ‖h i‖ ^ 2 + 2 * ((starRingEnd ℂ) (g i) * h i).re := fun i => by
    rw [Complex.sq_norm, Complex.normSq_add, Complex.sq_norm, Complex.sq_norm]
    congr 1
    rw [← Complex.conj_re, map_mul, Complex.conj_conj]
  rw [Finset.sum_congr rfl fun i _ => e i]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Complex.re_sum]
  congr 1

/-- The norm squared of the readout state is the average of the squared branch norms. -/
theorem normSq_corrState (U : Matrix (Fin d) (Fin d) ℂ) (ψ : QState (Fin d)) :
    (∑ p : Fin 2 × Fin d, ‖corrState U ψ p‖ ^ 2 : ℝ)
      = (2⁻¹ : ℝ) * ((∑ i : Fin d, ‖ψ i‖ ^ 2 : ℝ) + (∑ i : Fin d, ‖(U *ᵥ ψ) i‖ ^ 2 : ℝ)) := by
  rw [← Finset.univ_product_univ, Finset.sum_product, Fin.sum_univ_two]
  have e : ∀ b : Fin 2, (∑ i : Fin d, ‖corrState U ψ (b, i)‖ ^ 2 : ℝ)
      = ((Real.sqrt 2)⁻¹ ^ 2 : ℝ) * (∑ i : Fin d, ‖(if b = 0 then ψ i else (U *ᵥ ψ) i)‖ ^ 2 : ℝ) := by
    intro b
    fin_cases b
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [corrState, Complex.norm_real, Real.norm_eq_abs,
         mul_pow, inv_pow,
        Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [corrState, Complex.norm_real, Real.norm_eq_abs,
         mul_pow, inv_pow,
        Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  rw [e 0, e 1, inv_pow, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  simp
  ring

/-- The readout state is normalized whenever `ψ` is normalized and `U` is unitary. -/
theorem corrState_norm (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (ψ : QState (Fin d)) (hψ : Normalized ψ) :
    ‖toEuclidean_fromVec (corrState U ψ)‖ = 1 := by
  have h1 : (∑ i : Fin d, ‖ψ i‖ ^ 2 : ℝ) = 1 := hψ
  have h2 : (∑ i : Fin d, ‖(U *ᵥ ψ) i‖ ^ 2 : ℝ) = 1 := by
    have hnorm : Normalized (ApplyGate U ψ) := normalized_applyGate hU hψ
    simpa [Normalized, ApplyGate] using hnorm
  have h3 : ‖toEuclidean_fromVec (corrState U ψ)‖ ^ 2 = 1 := by
    rw [norm_toEuclidean_fromVec_sq, normSq_corrState, h1, h2]
    norm_num
  rcases _root_.sq_eq_one_iff.mp h3 with h | h
  · exact h
  · exact absurd h (by have := norm_nonneg (toEuclidean_fromVec (corrState U ψ)); linarith)

/-- The Born probability of the `σₓ = +1` outcome equals `(1 + Re C) / 2`. -/
theorem born_sigmaX_plus (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (ψ : QState (Fin d)) (hψ : Normalized ψ) :
    ‖toEuclidean_fromVec ((projSigmaXPlus ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ
        corrState U ψ)‖ ^ 2 = (1 + (corr U ψ).re) / 2 := by
  rw [norm_toEuclidean_fromVec_sq]
  rw [← Finset.univ_product_univ, Finset.sum_product, Fin.sum_univ_two]
  have key : ∀ b : Fin 2, (∑ i : Fin d,
        ‖((projSigmaXPlus ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) (b, i)‖ ^ 2 : ℝ)
      = (2⁻¹:ℝ) ^ 2 * (∑ i : Fin d, ‖corrState U ψ (0, i) + corrState U ψ (1, i)‖ ^ 2 : ℝ) := by
    intro b
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [projSigmaXPlus_apply, norm_mul_twoInv]
  rw [key 0, key 1]
  have hsum : (∑ i : Fin d, ‖corrState U ψ (0, i) + corrState U ψ (1, i)‖ ^ 2 : ℝ)
      = (2⁻¹ : ℝ) * (∑ i : Fin d, ‖ψ i + (U *ᵥ ψ) i‖ ^ 2 : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [corrState_add, norm_mul_sqrtTwo_inv]
  rw [hsum]
  have hbr : (∑ i : Fin d, ‖ψ i + (U *ᵥ ψ) i‖ ^ 2 : ℝ) = 2 + 2 * (corr U ψ).re := by
    have h1 : (∑ i : Fin d, ‖(U *ᵥ ψ) i‖ ^ 2 : ℝ) = 1 := by
      have hnorm : Normalized (ApplyGate U ψ) := normalized_applyGate hU hψ
      simpa [Normalized, ApplyGate] using hnorm
    have h2 := normSq_branch_add ψ (U *ᵥ ψ)
    rw [h1] at h2
    have h3 : (∑ i : Fin d, ‖ψ i‖ ^ 2 : ℝ) = 1 := hψ
    rw [h2, h3, corr]
    ring
  rw [hbr]
  ring

/-- The Born probability of the `σₓ = -1` outcome equals `(1 - Re C) / 2`. -/
theorem born_sigmaX_minus (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (ψ : QState (Fin d)) (hψ : Normalized ψ) :
    ‖toEuclidean_fromVec ((projSigmaXMinus ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ
        corrState U ψ)‖ ^ 2 = (1 - (corr U ψ).re) / 2 := by
  rw [norm_toEuclidean_fromVec_sq]
  rw [← Finset.univ_product_univ, Finset.sum_product, Fin.sum_univ_two]
  have key0 : (∑ i : Fin d,
        ‖((projSigmaXMinus ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) (0, i)‖ ^ 2 : ℝ)
      = (2⁻¹:ℝ) ^ 2 * (∑ i : Fin d, ‖corrState U ψ (0, i) - corrState U ψ (1, i)‖ ^ 2 : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [projSigmaXMinus_apply_zero, norm_mul_twoInv]
  have key1 : (∑ i : Fin d,
        ‖((projSigmaXMinus ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) (1, i)‖ ^ 2 : ℝ)
      = (2⁻¹:ℝ) ^ 2 * (∑ i : Fin d, ‖corrState U ψ (0, i) - corrState U ψ (1, i)‖ ^ 2 : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [projSigmaXMinus_apply_one, norm_mul_twoInv, norm_neg]
  rw [key0, key1]
  have hsum : (∑ i : Fin d, ‖corrState U ψ (0, i) - corrState U ψ (1, i)‖ ^ 2 : ℝ)
      = (2⁻¹ : ℝ) * (∑ i : Fin d, ‖ψ i - (U *ᵥ ψ) i‖ ^ 2 : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [corrState_sub, norm_mul_sqrtTwo_inv]
  rw [hsum]
  have hbr : (∑ i : Fin d, ‖ψ i - (U *ᵥ ψ) i‖ ^ 2 : ℝ) = 2 - 2 * (corr U ψ).re := by
    have h1 : (∑ i : Fin d, ‖(U *ᵥ ψ) i‖ ^ 2 : ℝ) = 1 := by
      have hnorm : Normalized (ApplyGate U ψ) := normalized_applyGate hU hψ
      simpa [Normalized, ApplyGate] using hnorm
    have hs : (∑ i : Fin d, ‖ψ i - (U *ᵥ ψ) i‖ ^ 2 : ℝ)
        = (∑ i : Fin d, ‖ψ i + (-(U *ᵥ ψ)) i‖ ^ 2 : ℝ) := by
      simp [Pi.neg_apply, sub_eq_add_neg]
    rw [hs, normSq_branch_add]
    have hneg : (∑ i : Fin d, ‖(-(U *ᵥ ψ)) i‖ ^ 2 : ℝ) = (∑ i : Fin d, ‖(U *ᵥ ψ) i‖ ^ 2 : ℝ) := by
      simp [Pi.neg_apply]
    rw [hneg, h1]
    have h3 : (∑ i : Fin d, ‖ψ i‖ ^ 2 : ℝ) = 1 := hψ
    have h5 : (Inner ψ (-(U *ᵥ ψ))).re = -(corr U ψ).re := by
      simp [Qatlib.Foundations.PureStateMath.Inner, corr, Complex.neg_re]
    rw [h3, h5, corr]
    ring
  rw [hbr]
  ring

/-- The Born probability of the `σ_y = +1` outcome equals `(1 + Im C) / 2`. -/
theorem born_sigmaY_plus (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (ψ : QState (Fin d)) (hψ : Normalized ψ) :
    ‖toEuclidean_fromVec ((projSigmaYPlus ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ
        corrState U ψ)‖ ^ 2 = (1 + (corr U ψ).im) / 2 := by
  rw [norm_toEuclidean_fromVec_sq]
  rw [← Finset.univ_product_univ, Finset.sum_product, Fin.sum_univ_two]
  have key0 : (∑ i : Fin d,
        ‖((projSigmaYPlus ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) (0, i)‖ ^ 2 : ℝ)
      = (2⁻¹:ℝ) ^ 2 *
        (∑ i : Fin d, ‖corrState U ψ (0, i) - Complex.I * corrState U ψ (1, i)‖ ^ 2 : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [projSigmaYPlus_apply_zero, norm_mul_twoInv]
  have key1 : (∑ i : Fin d,
        ‖((projSigmaYPlus ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) (1, i)‖ ^ 2 : ℝ)
      = (2⁻¹:ℝ) ^ 2 *
        (∑ i : Fin d, ‖corrState U ψ (0, i) - Complex.I * corrState U ψ (1, i)‖ ^ 2 : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [projSigmaYPlus_apply_one, norm_mul_I_twoInv]
  rw [key0, key1]
  have hsum : (∑ i : Fin d, ‖corrState U ψ (0, i) - Complex.I * corrState U ψ (1, i)‖ ^ 2 : ℝ)
      = (2⁻¹ : ℝ) *
        (∑ i : Fin d, ‖ψ i - Complex.I * (U *ᵥ ψ) i‖ ^ 2 : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [corrState_sub_I, norm_mul_sqrtTwo_inv]
  rw [hsum]
  have hbr : (∑ i : Fin d, ‖ψ i - Complex.I * (U *ᵥ ψ) i‖ ^ 2 : ℝ) = 2 + 2 * (corr U ψ).im := by
    have h1 : (∑ i : Fin d, ‖(U *ᵥ ψ) i‖ ^ 2 : ℝ) = 1 := by
      have hnorm : Normalized (ApplyGate U ψ) := normalized_applyGate hU hψ
      simpa [Normalized, ApplyGate] using hnorm
    have hs : (∑ i : Fin d, ‖ψ i - Complex.I * (U *ᵥ ψ) i‖ ^ 2 : ℝ)
        = (∑ i : Fin d, ‖ψ i + (-(Complex.I • (U *ᵥ ψ))) i‖ ^ 2 : ℝ) := by
      simp [Pi.neg_apply, sub_eq_add_neg]
    rw [hs, normSq_branch_add]
    have hneg : (∑ i : Fin d, ‖(-(Complex.I • (U *ᵥ ψ))) i‖ ^ 2 : ℝ)
        = (∑ i : Fin d, ‖(U *ᵥ ψ) i‖ ^ 2 : ℝ) := by
      simp [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    rw [hneg, h1]
    have h3 : (∑ i : Fin d, ‖ψ i‖ ^ 2 : ℝ) = 1 := hψ
    have h5 : (Inner ψ (-(Complex.I • (U *ᵥ ψ)))).re = (corr U ψ).im := by
      simp [Qatlib.Foundations.PureStateMath.Inner, corr, Complex.mul_re,
         Complex.neg_re, Complex.I_re, Complex.I_im]
    rw [h3, h5]
    ring
  rw [hbr]
  ring

/-- The Born probability of the `σ_y = -1` outcome equals `(1 - Im C) / 2`. -/
theorem born_sigmaY_minus (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (ψ : QState (Fin d)) (hψ : Normalized ψ) :
    ‖toEuclidean_fromVec ((projSigmaYMinus ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ
        corrState U ψ)‖ ^ 2 = (1 - (corr U ψ).im) / 2 := by
  rw [norm_toEuclidean_fromVec_sq]
  rw [← Finset.univ_product_univ, Finset.sum_product, Fin.sum_univ_two]
  have key0 : (∑ i : Fin d,
        ‖((projSigmaYMinus ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) (0, i)‖ ^ 2 : ℝ)
      = (2⁻¹:ℝ) ^ 2 *
        (∑ i : Fin d, ‖corrState U ψ (0, i) + Complex.I * corrState U ψ (1, i)‖ ^ 2 : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [projSigmaYMinus_apply_zero, norm_mul_twoInv]
  have key1 : (∑ i : Fin d,
        ‖((projSigmaYMinus ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ corrState U ψ) (1, i)‖ ^ 2 : ℝ)
      = (2⁻¹:ℝ) ^ 2 *
        (∑ i : Fin d, ‖corrState U ψ (0, i) + Complex.I * corrState U ψ (1, i)‖ ^ 2 : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [projSigmaYMinus_apply_one, ← mul_assoc, norm_mul_I_twoInv, norm_neg]
  rw [key0, key1]
  have hsum : (∑ i : Fin d, ‖corrState U ψ (0, i) + Complex.I * corrState U ψ (1, i)‖ ^ 2 : ℝ)
      = (2⁻¹ : ℝ) *
        (∑ i : Fin d, ‖ψ i + Complex.I * (U *ᵥ ψ) i‖ ^ 2 : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [corrState_add_I, norm_mul_sqrtTwo_inv]
  rw [hsum]
  have hbr : (∑ i : Fin d, ‖ψ i + Complex.I * (U *ᵥ ψ) i‖ ^ 2 : ℝ) = 2 - 2 * (corr U ψ).im := by
    have h1 : (∑ i : Fin d, ‖(U *ᵥ ψ) i‖ ^ 2 : ℝ) = 1 := by
      have hnorm : Normalized (ApplyGate U ψ) := normalized_applyGate hU hψ
      simpa [Normalized, ApplyGate] using hnorm
    rw [normSq_branch_add]
    have hneg : (∑ i : Fin d, ‖Complex.I * (U *ᵥ ψ) i‖ ^ 2 : ℝ)
        = (∑ i : Fin d, ‖(U *ᵥ ψ) i‖ ^ 2 : ℝ) := by
      simp [ Complex.norm_I, one_mul]
    rw [hneg, h1]
    have h3 : (∑ i : Fin d, ‖ψ i‖ ^ 2 : ℝ) = 1 := hψ
    rw [h3]
    have key_i : ∀ i : Fin d, ((starRingEnd ℂ) (ψ i) * (Complex.I * (U *ᵥ ψ) i)).re
        + ((starRingEnd ℂ) (ψ i) * (U *ᵥ ψ) i).im = 0 := by
      intro i
      rw [show (starRingEnd ℂ) (ψ i) * (Complex.I * (U *ᵥ ψ) i)
          = (starRingEnd ℂ) (ψ i) * (U *ᵥ ψ) i * Complex.I from by ring, Complex.mul_I_re]
      simp
    have h5 : (Inner ψ (fun i : Fin d => Complex.I * (U *ᵥ ψ) i)).re + (corr U ψ).im = 0 := by
      rw [inner_apply, corr, inner_apply, Complex.re_sum, Complex.im_sum]
      show (∑ i : Fin d, ((starRingEnd ℂ) (ψ i) * (Complex.I * (U *ᵥ ψ) i)).re)
          + ∑ i : Fin d, ((starRingEnd ℂ) (ψ i) * (U *ᵥ ψ) i).im = 0
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun i _ => key_i i]
      simp
    linarith
  rw [hbr]
  ring

end Qatlib.Papers.DiracEquation16.AutoCorrel
