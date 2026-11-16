/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.ParentBridge
public import Qatlib.Concepts.GibbsSource.CkgBounds.CKGWeight

@[expose] public section


/-! Exact matrix-unit entries of a finite thermal parent factor.
The two nonzero row and column contributions retain their opposite Gibbs coefficients. -/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Matrix

namespace Qatlib.Concepts.GibbsSource.SourceForms

variable {D : ℕ}

/-- Left multiplication by a matrix unit selects its source row. -/
theorem matUnit_mulL_apply (i j : Fin D) (O : Operator D) (m n : Fin D) :
    (matUnit i j (1 : ℂ) * O) m n = if m = i then O j n else 0 := by
  by_cases hm : m = i
  · simp [Matrix.mul_apply, matUnit_apply, hm]
  · simp [Matrix.mul_apply, matUnit_apply, hm]

/-- Right multiplication by a matrix unit selects its source column. -/
theorem matUnit_mulR_apply (i j : Fin D) (O : Operator D) (m n : Fin D) :
    (O * matUnit i j (1 : ℂ)) m n = if n = j then O m i else 0 := by
  by_cases hn : n = j
  · simp [Matrix.mul_apply, matUnit_apply, hn]
  · simp [Matrix.mul_apply, matUnit_apply, hn]

/-- The matrix-unit parent factor has the two actual thermal row/column coefficients. -/
theorem parentFactor_matUnit_entry (lam : Fin D → ℝ) (β : ℝ) (i j : Fin D)
    (O : Operator D) (m n : Fin D) :
    (parentFactor (gibbsDiag lam β) (matUnit i j (1 : ℂ)) O) m n
      = (if m = i then ((Real.exp (-(β * (lam i - lam j)) / 4) : ℝ) : ℂ) * O j n else 0)
        - (if n = j then ((Real.exp (β * (lam i - lam j) / 4) : ℝ) : ℂ) * O m i else 0) := by
  rw [parentFactor_apply, sharp_matUnit lam β i j (1 : ℂ),
    flat_matUnit lam β i j (1 : ℂ), Matrix.sub_apply, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
    matUnit_mulL_apply, matUnit_mulR_apply, mul_ite, mul_ite]
  simp only [MulZeroClass.mul_zero]


end Qatlib.Concepts.GibbsSource.SourceForms
