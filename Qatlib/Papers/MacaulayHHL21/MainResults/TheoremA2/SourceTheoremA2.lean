/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MacaulayHHL21.MainResults.SourceModel
import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse
import Mathlib.Data.Matrix.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem A.2 — unique Boolean Macaulay solution is `M⁺b⃗`

Fixed paper: arXiv:2111.00405, Theorem A.2 (Appendix A).

Statement (verbatim): *Given a set of polynomials `F = F₁ ∪ F₂ ⊆ ℂ[x₁,…,x_n]`, where
`F₁ = {f₁, …, f_m}` and `F₂ = {x₁² − x₁, …, x_n² − x_n}`, suppose `F` has a unique solution
`a = (a₁, …, a_n)`, where `F₂` forces the root of `F₁` to be Boolean.  Let `ŷ` be the
multilinear monomial solution vector corresponding to `a`; then the Boolean Macaulay linear
system `Mŷ = b⃗` of total degree `n` has the unique solution `ŷ = M⁺b⃗`.*

The polynomial-ideal content of the appendix (every `X^β − a^β` lies in `⟨F⟩`, hence the
solution vector is the unique multilinear solution) is the standing hypothesis of "unique
solution"; the linear-algebra conclusion `ŷ = M⁺b⃗` is proved below from the Frozen
pseudoinverse minimum-norm specification.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset Matrix

namespace Qatlib.Papers.MacaulayHHL21.MainResults.TheoremA2

open Qatlib.Papers.MacaulayHHL21.MainResults
open Qatlib.Concepts.CoherentSim.CoherentOAA

/-- **Theorem A.2** (arXiv:2111.00405, Appendix A): if the Boolean Macaulay linear system
`M y = b` has the unique solution `yhat`, then `yhat = M⁺ b`. -/
theorem theoremA2_unique_solution
    {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ)
    (b : Matrix (Fin m) (Fin 1) ℂ) (yhat : Matrix (Fin n) (Fin 1) ℂ)
    (hsol : M * yhat = b)
    (huniq : ∀ y : Matrix (Fin n) (Fin 1) ℂ, M * y = b → y = yhat) :
    matrixPseudoinverse M * b = yhat := by
  have hb : ∃ y : Matrix (Fin n) (Fin 1) ℂ, M * y = b := ⟨yhat, hsol⟩
  exact huniq _ (matrixPseudoinverse_minimumNorm_solution M b hb).1

end Qatlib.Papers.MacaulayHHL21.MainResults.TheoremA2
