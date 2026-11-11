/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero

set_option backward.isDefEq.respectTransparency false

/-!
# Appendix A.1 — generalized-eigenspace dimension (Non-Hermitian Physics)

Fixed arXiv:2006.01837v3 (Adv. Phys. review, 2020). Theorem A.1, Eq. (A13), p.150.

For a matrix `M ∈ ℂ^{n×n}` with distinct eigenvalues `λ_j` and algebraic multiplicities
`m_jᵃ`, the generalized eigenspace `Ṽ_M(λ_j) = ker((M - λ_j I)^{m_jᵃ - m_jᵍ + 1})` has
`dim Ṽ_M(λ_j) = m_jᵃ`, hence `ℂⁿ = ⊕_j Ṽ_M(λ_j)`.

We state this coordinate-free for an endomorphism of a finite-dimensional complex vector
space. The paper's `Ṽ_M(λ)` is the *maximal* generalized eigenspace (it stabilises at
`ker((M - λI)^{mᵃ - mᵍ + 1})`, Mathlib's `Module.End.maxGenEigenspace`), and `m_jᵃ` is the
root multiplicity of `λ_j` in the characteristic polynomial.

Reuse:
* `LinearMap.finrank_maxGenEigenspace_eq` — the dimension equals `rootMultiplicity`.
* `Module.End.independent_maxGenEigenspace` — distinct generalized eigenspaces are
  independent.
* `Module.End.iSup_maxGenEigenspace_eq_top` — over an algebraically closed field the
  maximal generalized eigenspaces span the whole space.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NonHermitian20.MatrixJordan

open Module

/-- Fixed arXiv:2006.01837v3, Theorem A.1, Eq. (A13), p.150. Coordinate-free matrix form.

For an endomorphism `φ` of a finite-dimensional complex vector space (the paper's
`M ∈ ℂ^{n×n}`) and any eigenvalue `λ`:
* the maximal generalized eigenspace `Ṽ_φ(λ)` has dimension equal to the algebraic
  multiplicity `mᵃ(λ)` (`= φ.charpoly.rootMultiplicity λ`), and
* the maximal generalized eigenspaces over all `λ` form an internal direct-sum
  decomposition of the whole space (`ℂⁿ = ⊕_λ Ṽ_φ(λ)`).

The paper restricts to distinct eigenvalues `λ_j`; summing over all `λ` is harmless because
`maxGenEigenspace φ λ = ⊥` for non-eigenvalues, so those terms contribute nothing. -/
theorem theorem_A1_generalized_eigenspace_dim (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (φ : Module.End ℂ V) (mu : ℂ) :
    finrank ℂ (φ.maxGenEigenspace mu) = φ.charpoly.rootMultiplicity mu ∧
      iSupIndep φ.maxGenEigenspace ∧ ⨆ (μ : ℂ), φ.maxGenEigenspace μ = ⊤ := by
  refine ⟨LinearMap.finrank_maxGenEigenspace_eq φ mu, ?_, ?_⟩
  · exact Module.End.independent_maxGenEigenspace φ
  · exact Module.End.iSup_maxGenEigenspace_eq_top φ

end Qatlib.Papers.NonHermitian20.MatrixJordan
