/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Pi
import Qatlib.Foundations.PureStateMath.Qubit

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Papers.HamLCUSim12.TaylorBounds

open scoped Matrix.Norms.L2Operator

noncomputable def expProductGenerator {I : Type} [Fintype I] [DecidableEq I] {M : ℕ}
    (a : Fin M → ℝ) (H : Fin M → Matrix I I ℂ) (j : Fin M) : Matrix I I ℂ :=
  (-(Complex.I * (a j : ℂ))) • H j

noncomputable def expProductMul {I : Type} [Fintype I] [DecidableEq I] {M : ℕ}
    (A : Fin M → Matrix I I ℂ) : Matrix I I ℂ :=
  (List.ofFn fun j => A j).prod

noncomputable def expProductTaylor {I : Type} [Fintype I] [DecidableEq I] {M : ℕ}
    (A : Fin M → Matrix I I ℂ) (t : ℝ) (ℓ : ℕ) : Matrix I I ℂ :=
  ∑ p ∈ (Fintype.piFinset fun _ : Fin M => Finset.range (ℓ + 1)).filter
      (fun p => (∑ j, p j) ≤ ℓ),
    ((t ^ (∑ j, p j) : ℝ) : ℂ) • expProductMul (fun j => ((p j).factorial : ℂ)⁻¹ • A j ^ (p j))

end Qatlib.Papers.HamLCUSim12.TaylorBounds
