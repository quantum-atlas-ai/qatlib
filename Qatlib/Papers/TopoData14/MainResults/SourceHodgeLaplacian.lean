/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Complex.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceHodgeLaplacian — Hodge theory of the combinatorial Laplacian

Lloyd--Garnerone--Zanardi, *Quantum algorithms for topological and geometric analysis of
big data*, fixed arXiv:1408.3106v1 (2014).

Section 2, Eq. (7) and Section 3, Eqs. (9)--(10) (PDF p. 12--14): the combinatorial
Laplacian on the `k`-simplex space `C_k` is
`Δ_k = ∂_k† ∂_k + ∂_{k+1} ∂_{k+1}†`,
where `∂_k : C_k → C_{k-1}` is the boundary map. Hodge theory states that the kernel of
`Δ_k` is isomorphic to the `k`-th homology group, hence
`dim Ker Δ_k = β_k = dim Ker ∂_k − dim Im ∂_{k+1}`. This is the identity the paper uses
to read the Betti number off the kernel of the (Dirac-square) Laplacian.

In this file `f : E → F` plays the role of `∂_k` (`E = C_k`, `F = C_{k-1}`) and
`g : G → E` the role of `∂_{k+1}` (`G = C_{k+1}`). The paper's Eq. (7) is the last
theorem, `hodge_betti_eq_kernel_add_kernel_sub`.

Boundary: the file proves the kernel identity and the dimension identity of Hodge
theory, plus symmetry and positivity of `Δ_k`. It does not construct the concrete
simplicial boundary maps of Eq. (5), nor any quantum phase-estimation procedure.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TopoData14.MainResults

open scoped InnerProduct ComplexOrder
open ComplexConjugate

variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

/-- Fixed arXiv:1408.3106v1, Eq. (10) (PDF p. 14): the combinatorial Laplacian on the
`k`-simplex space, `Δ_k = ∂_k† ∂_k + ∂_{k+1} ∂_{k+1}†`. In the local notation `f = ∂_k`
and `g = ∂_{k+1}`. -/
def combinatorialLaplacian (f : E →ₗ[ℂ] F) (g : G →ₗ[ℂ] E) : E →ₗ[ℂ] E :=
  f.adjoint ∘ₗ f + g ∘ₗ g.adjoint

/-- Fixed arXiv:1408.3106v1, Section 3, PDF p. 14: the combinatorial Laplacian is
self-adjoint, so the quantum phase-estimation algorithm (which requires Hermitian
input) applies to `Δ_k` and to its Dirac square root. -/
theorem combinatorialLaplacian_adjoint_eq (f : E →ₗ[ℂ] F) (g : G →ₗ[ℂ] E) :
    (combinatorialLaplacian f g).adjoint = combinatorialLaplacian f g := by
  simp only [combinatorialLaplacian, map_add, LinearMap.adjoint_comp,
    LinearMap.adjoint_adjoint]

/-- Fixed arXiv:1408.3106v1, Section 3, PDF p. 14: the combinatorial Laplacian is
positive semi-definite (as a sum of `∂†∂` and `∂∂†`). -/
theorem combinatorialLaplacian_isPositive (f : E →ₗ[ℂ] F) (g : G →ₗ[ℂ] E) :
    (combinatorialLaplacian f g).IsPositive :=
  (LinearMap.isPositive_adjoint_comp_self f).add (LinearMap.isPositive_self_comp_adjoint g)

/-- Fixed arXiv:1408.3106v1, Eq. (10) and Hodge theory (PDF p. 14): the kernel of the
combinatorial Laplacian is the intersection of the kernel of `∂_k` with the kernel of
`∂_{k+1}†`; equivalently (by `orthogonal_range`) it is the subspace of `∂_k`-cycles
orthogonal to the `∂_{k+1}`-boundaries.

Proof: `Δ x = 0` implies
`0 = ⟪x, Δx⟫ = ⟪∂_k x, ∂_k x⟫ + ⟪∂_{k+1}† x, ∂_{k+1}† x⟫`;
both inner products have nonnegative real part, so both vanish, giving
`∂_k x = 0` and `∂_{k+1}† x = 0` by `inner_self_eq_zero`. -/
theorem ker_combinatorialLaplacian (f : E →ₗ[ℂ] F) (g : G →ₗ[ℂ] E) :
    LinearMap.ker (combinatorialLaplacian f g) =
      LinearMap.ker f ⊓ LinearMap.ker g.adjoint := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    have h0 : combinatorialLaplacian f g x = 0 := hx
    have hinner : inner ℂ x (combinatorialLaplacian f g x) = 0 := by
      rw [h0, inner_zero_right]
    have hexp : inner ℂ x (combinatorialLaplacian f g x) =
        inner ℂ (f x) (f x) + inner ℂ (g.adjoint x) (g.adjoint x) := by
      unfold combinatorialLaplacian
      simp only [LinearMap.add_apply, LinearMap.comp_apply, inner_add_right]
      rw [LinearMap.adjoint_inner_right (A := f) (x := x) (y := f x)]
      rw [← LinearMap.adjoint_inner_left (A := g) (x := g.adjoint x) (y := x)]
    have hsum : inner ℂ (f x) (f x) + inner ℂ (g.adjoint x) (g.adjoint x) = 0 := by
      rw [← hexp, hinner]
    have hre : (inner ℂ (f x) (f x)).re +
        (inner ℂ (g.adjoint x) (g.adjoint x)).re = 0 := by
      have := congrArg Complex.re hsum
      simpa using this
    have hn1 : (0 : ℝ) ≤ (inner ℂ (f x) (f x)).re := by
      simpa using inner_self_nonneg (𝕜 := ℂ) (x := f x)
    have hn2 : (0 : ℝ) ≤ (inner ℂ (g.adjoint x) (g.adjoint x)).re := by
      simpa using inner_self_nonneg (𝕜 := ℂ) (x := g.adjoint x)
    have h1 : inner ℂ (f x) (f x) = 0 := by
      apply Complex.ext
      · show (inner ℂ (f x) (f x)).re = 0
        linarith
      · simpa using inner_self_im (𝕜 := ℂ) (x := f x)
    have h2 : inner ℂ (g.adjoint x) (g.adjoint x) = 0 := by
      apply Complex.ext
      · show (inner ℂ (g.adjoint x) (g.adjoint x)).re = 0
        linarith
      · simpa using inner_self_im (𝕜 := ℂ) (x := g.adjoint x)
    exact Submodule.mem_inf.mpr
      ⟨LinearMap.mem_ker.mpr (inner_self_eq_zero.mp h1),
        LinearMap.mem_ker.mpr (inner_self_eq_zero.mp h2)⟩
  · intro hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨h1, h2⟩ := hx
    rw [LinearMap.mem_ker] at h1 h2 ⊢
    unfold combinatorialLaplacian
    simp only [LinearMap.add_apply, LinearMap.comp_apply, h1, h2, map_zero, add_zero]

/-- Fixed arXiv:1408.3106v1, Hodge theory (PDF p. 14): the `k`-th Betti number is the
dimension of the kernel of the combinatorial Laplacian,
`dim Ker Δ_k = dim Ker ∂_k − dim Im ∂_{k+1}`.

Proof: `dim Ker Δ_k = dim (Ker ∂_k ⊓ Ker ∂_{k+1}†)` by the previous theorem,
`Ker ∂_{k+1}† = (Im ∂_{k+1})ᗮ` by `orthogonal_range`, and
`Submodule.finrank_add_inf_finrank_orthogonal` with `Im ∂_{k+1} ≤ Ker ∂_k` (chain
condition `∂_k ∂_{k+1} = 0`) gives
`dim Im ∂_{k+1} + dim (Ker ∂_k ⊓ (Im ∂_{k+1})ᗮ) = dim Ker ∂_k`. -/
theorem finrank_ker_combinatorialLaplacian_eq_betti
    (f : E →ₗ[ℂ] F) (g : G →ₗ[ℂ] E) (hchain : f ∘ₗ g = 0) :
    Module.finrank ℂ (LinearMap.ker (combinatorialLaplacian f g)) =
      Module.finrank ℂ (LinearMap.ker f) -
        Module.finrank ℂ (LinearMap.range g) := by
  rw [ker_combinatorialLaplacian]
  have horth : LinearMap.ker g.adjoint = (LinearMap.range g)ᗮ :=
    (LinearMap.orthogonal_range g).symm
  rw [horth, inf_comm]
  have hle : LinearMap.range g ≤ LinearMap.ker f := by
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hchain, LinearMap.zero_apply]
  have hdim := Submodule.finrank_add_inf_finrank_orthogonal (𝕜 := ℂ)
    (K₁ := LinearMap.range g) (K₂ := LinearMap.ker f) hle
  omega

/-- Fixed arXiv:1408.3106v1, Eq. (7) (PDF p. 12) combined with Hodge theory: the
Betti number of the `k`-th complex is
`dim Ker ∂_k + dim Ker ∂_{k+1} − dim H^ε_{k+1}`, and it equals the dimension of the
kernel of the combinatorial Laplacian `Δ_k = ∂_k†∂_k + ∂_{k+1}∂_{k+1}†`.

Here `H^ε_{k+1} = G` is the space of `(k+1)`-simplices at grouping scale `ε`. -/
theorem hodge_betti_eq_kernel_add_kernel_sub
    (f : E →ₗ[ℂ] F) (g : G →ₗ[ℂ] E) (hchain : f ∘ₗ g = 0) :
    Module.finrank ℂ (LinearMap.ker (combinatorialLaplacian f g)) =
      Module.finrank ℂ (LinearMap.ker f) +
        Module.finrank ℂ (LinearMap.ker g) - Module.finrank ℂ G := by
  have hrn : Module.finrank ℂ (LinearMap.range g) +
      Module.finrank ℂ (LinearMap.ker g) = Module.finrank ℂ G :=
    LinearMap.finrank_range_add_finrank_ker g
  have h := finrank_ker_combinatorialLaplacian_eq_betti f g hchain
  omega

end Qatlib.Papers.TopoData14.MainResults

end
