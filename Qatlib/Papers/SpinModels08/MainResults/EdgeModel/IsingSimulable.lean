/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpinModels08.MainResults.EdgeModel.UniversalGateSet

/-!
# Ising weights and rotation gate identities

This module specializes edge weights to two values according to spin equality and expresses the
resulting gates using the Pauli X and ZZ matrices. It also transfers a supplied
partition-function evaluation to a circuit matrix element, providing algebraic ingredients for
the Ising-model correspondence in [VanDenNestEtAl2009].

## Main statements

* `isingWeight_diag_decomp`: the diagonal edge gate is a linear combination of the identity and
  ZZ.
* `rotation_evaluator_identity`: an evaluator for the specified rotation weights equals the
  circuit matrix element.

## References

* [Van den Nest et al., 2009][VanDenNestEtAl2009]
-/

set_option warningAsError false

noncomputable section

open scoped BigOperators Matrix

namespace Qatlib.Papers.SpinModels08.MainResults.EdgeModel.IsingSimulable

open Qatlib.Papers.SpinModels08.MainResults
open Qatlib.Papers.SpinModels08.MainResults.EdgeModel
open Qatlib.Papers.SpinModels08.MainResults.EdgeModel.UniversalGateSet

/-- The two-spin weight equal to `a` for matching spins and `b` for distinct spins. -/
def isingWeight (a b : ℂ) : EdgeW 2 := fun i j => if i = j then a else b

/-- The Ising weight on the spin pair `(0, 0)` is `a`. -/
theorem isingWeight_00 (a b : ℂ) : isingWeight a b 0 0 = a := by
  simp [isingWeight]

/-- The Ising weight on the spin pair `(1, 1)` is `a`. -/
theorem isingWeight_11 (a b : ℂ) : isingWeight a b 1 1 = a := by
  simp [isingWeight]

/-- The Ising weight on the spin pair `(0, 1)` is `b`. -/
theorem isingWeight_01 (a b : ℂ) : isingWeight a b 0 1 = b := by
  simp [isingWeight]

/-- The Ising weight on the spin pair `(1, 0)` is `b`. -/
theorem isingWeight_10 (a b : ℂ) : isingWeight a b 1 0 = b := by
  simp [isingWeight]

/-- The Ising weights agree on the two equal-spin pairs and on the two unequal-spin pairs. -/
theorem isingWeight_free_field (a b : ℂ) :
    isingWeight a b 0 0 = isingWeight a b 1 1 ∧
      isingWeight a b 0 1 = isingWeight a b 1 0 :=
  ⟨(isingWeight_00 a b).trans (isingWeight_11 a b).symm,
    (isingWeight_01 a b).trans (isingWeight_10 a b).symm⟩

/-- The single-qubit matrix with diagonal entries `cos α` and off-diagonal entries `I * sin α`. -/
def rotX2 (α : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  singleQubitGate (isingWeight ((Real.cos α : ℂ)) (Complex.I * (Real.sin α : ℂ)))

/-- The entries of `rotX2 α` are `cos α` on the diagonal and `I * sin α` elsewhere. -/
theorem rotX2_apply (α : ℝ) (i j : Fin 2) :
    rotX2 α i j = if i = j then (Real.cos α : ℂ) else Complex.I * (Real.sin α : ℂ) :=
  rfl

/-- The X rotation matrix is the single-qubit edge gate for the corresponding trigonometric
Ising weights. -/
theorem rotX2_eq_edgeGate (α : ℝ) :
    rotX2 α =
      singleQubitGate
        (isingWeight ((Real.cos α : ℂ)) (Complex.I * (Real.sin α : ℂ))) := rfl

/-- The Pauli X matrix, which interchanges the two computational basis states. -/
def sigmaX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The single-qubit Ising edge gate is `a` times the identity plus `b` times Pauli X. -/
theorem isingWeight_singleQubit_eq (a b : ℂ) :
    singleQubitGate (isingWeight a b) =
      a • (1 : Matrix (Fin 2) (Fin 2) ℂ) + b • sigmaX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [singleQubitGate, isingWeight, sigmaX, Matrix.add_apply, Matrix.smul_apply]

/-- The diagonal two-qubit ZZ matrix, with eigenvalue one for equal spins and minus one for
unequal spins. -/
def zzGate : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun (i, j) (k, l) => if i = k ∧ j = l then (if i = j then 1 else -1) else 0

/-- The ZZ matrix has the stated equal-spin signs on the diagonal and zero off the diagonal. -/
theorem zzGate_apply (i j k l : Fin 2) :
    zzGate (i, j) (k, l) = if i = k ∧ j = l then (if i = j then 1 else -1) else 0 := rfl

/-- The diagonal two-qubit matrix with phase `exp (I * β)` on equal spins and the opposite phase
on unequal spins. -/
def rotZZ (β : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  diagTwoQubitGate
    (isingWeight (Complex.exp ((β : ℂ) * Complex.I))
      (Complex.exp (-((β : ℂ) * Complex.I))))

/-- The entries of `rotZZ β` are the specified Ising phases on the diagonal and zero elsewhere. -/
theorem rotZZ_apply (β : ℝ) (i j k l : Fin 2) :
    rotZZ β (i, j) (k, l) =
      if i = k ∧ j = l then
        (if i = j then Complex.exp ((β : ℂ) * Complex.I)
          else Complex.exp (-((β : ℂ) * Complex.I)))
      else 0 := rfl

/-- The ZZ rotation matrix is the diagonal edge gate for its exponential Ising weights. -/
theorem rotZZ_eq_edgeGate (β : ℝ) :
    rotZZ β = diagTwoQubitGate
      (isingWeight (Complex.exp ((β : ℂ) * Complex.I))
        (Complex.exp (-((β : ℂ) * Complex.I)))) := rfl

/-- The diagonal Ising edge gate is the sum of the identity and ZZ components with coefficients
`(a + b) / 2` and `(a - b) / 2`, respectively; see [VanDenNestEtAl2009]. -/
theorem isingWeight_diag_decomp (a b : ℂ) :
    diagTwoQubitGate (isingWeight a b) =
      ((a + b) / 2) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) +
        ((a - b) / 2) • zzGate := by
  ext x y
  obtain ⟨i, j⟩ := x
  obtain ⟨k, l⟩ := y
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [diagTwoQubitGate, isingWeight, zzGate, Matrix.add_apply, Matrix.smul_apply] <;> ring

/-- An evaluator agreeing with the partition contraction for the supplied Ising weights also
agrees with the circuit matrix element. -/
theorem ising_evaluator_identity {N : ℕ} (M : ℕ)
    (hW vW : Fin M → Fin N → EdgeW 2)
    (_hhW : ∀ c r, ∃ a b : ℂ, hW c r = isingWeight a b)
    (_hvW : ∀ c r, ∃ a b : ℂ, vW c r = isingWeight a b)
    (Zval : Config 2 N → Config 2 N → ℂ)
    (hZ : ∀ L R, Zval L R = emPartition0 M hW vW L R) :
    ∀ L R, Zval L R = matElem (emCircuit M hW vW) L R := by
  intro L R
  rw [hZ L R, matElem_eq_apply, emPartition0_eq_emCircuit]

/-- An evaluator agreeing with the partition contraction for the specified X and ZZ rotation
weights agrees with the corresponding circuit matrix element [VanDenNestEtAl2009]. -/
theorem rotation_evaluator_identity {N : ℕ} (M : ℕ)
    (α : Fin M → Fin N → ℝ) (β : Fin M → Fin N → ℝ)
    (Zval : Config 2 N → Config 2 N → ℂ)
    (hZ : ∀ L R, Zval L R =
      emPartition0 M
        (fun c r => isingWeight ((Real.cos (α c r) : ℂ))
          (Complex.I * (Real.sin (α c r) : ℂ)))
        (fun c r => isingWeight (Complex.exp (((β c r : ℝ) : ℂ) * Complex.I))
          (Complex.exp (-(((β c r : ℝ) : ℂ) * Complex.I)))) L R) :
    ∀ L R, Zval L R = matElem
      (emCircuit M
        (fun c r => isingWeight ((Real.cos (α c r) : ℂ))
          (Complex.I * (Real.sin (α c r) : ℂ)))
        (fun c r => isingWeight (Complex.exp (((β c r : ℝ) : ℂ) * Complex.I))
          (Complex.exp (-(((β c r : ℝ) : ℂ) * Complex.I))))) L R :=
  ising_evaluator_identity M _ _
    (fun _ _ => ⟨_, _, rfl⟩) (fun _ _ => ⟨_, _, rfl⟩) Zval hZ

end Qatlib.Papers.SpinModels08.MainResults.EdgeModel.IsingSimulable
