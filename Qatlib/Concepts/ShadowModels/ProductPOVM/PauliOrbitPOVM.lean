/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ProductPOVM.TensorPauliTwirl
import QuantumInfo.ForMathlib.HermitianMat.Unitary

/-!
# Pauli orbit measurements

`pauliUnitary` and `pauliObservable` package Pauli word matrices as unitaries and Hermitian
observables. The density twirl identity constructs `pauliOrbitPOVM` from the Pauli conjugates of
any state, with uniform effect traces and conjugation signs given by the symplectic form. See
[XuEtAl2026] for background.

## Main statements

* `pauli_density_twirl`: the sum of Pauli conjugates of a density matrix is dimension times
  identity.
* `pauliOrbitPOVM`: the normalized measurement obtained from a Pauli orbit.
* `pauli_conjugation_sign`: the symplectic sign of Pauli conjugation.

## References

* [Xu et al., 2026][XuEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ShadowModels.ProductPOVM
open scoped Classical BigOperators RealInnerProductSpace
open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Foundations.PureStateMath

/-- The unitary matrix represented by an `n`-qubit Pauli word. -/
def pauliUnitary (n : ℕ) (w : PauliWord n) : Matrix.unitaryGroup (Reg n) ℂ :=
  ⟨pauliWordOp n w,pauliWordOp_unitary n w⟩

/-- The Hermitian observable represented by an `n`-qubit Pauli word. -/
def pauliObservable (n : ℕ) (w : PauliWord n) : HermitianMat (Reg n) ℂ :=
  ⟨pauliWordOp n w,pauliWordOp_herm n w⟩

/-- The real-valued Hilbert space dimension `2^n` of an `n`-qubit register. -/
def qubitDimension (n : ℕ) : ℝ := (2:ℝ)^n

/-- The dimension `qubitDimension n` is strictly positive. -/
theorem qubitDimension_pos (n : ℕ) : 0<qubitDimension n := pow_pos (by norm_num) n

/-- Summing all Pauli conjugates of a density matrix gives `qubitDimension n` times the
identity, yielding the orbit normalization used in [XuEtAl2026]. -/
theorem pauli_density_twirl (n : ℕ) (ρ : MState (Reg n)) :
    (∑ w : PauliWord n,ρ.M.conj (pauliUnitary n w).val)=qubitDimension n • (1 : HermitianMat (Reg n) ℂ) := by
  apply HermitianMat.ext
  simp only [HermitianMat.mat_finset_sum,HermitianMat.conj_apply_mat]
  change (∑ w : PauliWord n,pauliWordOp n w*ρ.M.mat*(pauliWordOp n w)ᴴ)=_
  rw [tensor_pauli_twirl]
  have ht : ρ.M.mat.trace=(1:ℂ) := ρ.tr'
  rw [ht,mul_one]
  ext i j
  simp [qubitDimension,Complex.real_smul]

/-- The POVM whose effects are Pauli conjugates of `ρ`, each scaled by the inverse register
dimension. -/
def pauliOrbitPOVM (n : ℕ) (ρ : MState (Reg n)) : POVM (PauliWord n) (Reg n) where
  mats w := (qubitDimension n)⁻¹ • ρ.M.conj (pauliUnitary n w).val
  nonneg w := smul_nonneg (inv_nonneg.mpr (qubitDimension_pos n).le)
    (HermitianMat.conj_nonneg _ ρ.nonneg)
  normalized := by
    rw [← Finset.smul_sum,pauli_density_twirl,smul_smul,inv_mul_cancel₀ (qubitDimension_pos n).ne',one_smul]

/-- Every effect of the Pauli orbit POVM has trace equal to the inverse register dimension. -/
theorem pauliOrbit_trace (n : ℕ) (ρ : MState (Reg n)) (w : PauliWord n) :
    ((pauliOrbitPOVM n ρ).mats w).trace=(qubitDimension n)⁻¹ := by
  change ((qubitDimension n)⁻¹ • ρ.M.conj (pauliUnitary n w).val).trace=_
  rw [HermitianMat.trace_smul,HermitianMat.trace_conj_unitary,ρ.tr,mul_one]

/-- Conjugation of a Pauli observable by a Pauli unitary multiplies it by the sign determined by
their binary symplectic pairing. -/
theorem pauli_conjugation_sign (n : ℕ) (q w : PauliWord n) :
    (pauliObservable n w).conj (pauliUnitary n q).val=
      ((-1:ℝ)^(symplecticForm (symplecticX q,symplecticZ q) (symplecticX w,symplecticZ w)).val) • pauliObservable n w := by
  apply HermitianMat.ext
  simp only [HermitianMat.conj_apply_mat,pauliUnitary,pauliObservable,HermitianMat.mat_mk,HermitianMat.mat_smul]
  rw [pauliWordOp_herm,pauliWordOp_symplectic,smul_mul_assoc,mul_assoc]
  have hq : pauliWordOp n q*pauliWordOp n q=1 := by
    have h := (pauliUnitary n q).property.1
    simpa only [pauliUnitary,Matrix.star_eq_conjTranspose,pauliWordOp_herm] using h
  rw [hq,mul_one]
  ext i j
  simp [Complex.real_smul]

end Qatlib.Concepts.ShadowModels.ProductPOVM
