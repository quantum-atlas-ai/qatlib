/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GibbsSampling25.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Weak approximate tensorization (claim c002)

Theorem 2.7 of arXiv:2412.01732v1 (p.6, eqs. (7) and (8)). Given a suitable
coarse-graining `{C_{a,i}}` of `Λ` and the Davies channels
`E_{C_{a,i}}` of the Gibbs state `σ` at inverse temperature `β` of a local
commuting Hamiltonian,

`D(ρ‖σ) ≤ ∑_{a=0}^{D} ∑_{i_a} D(ρ‖E_{C_{a,i_a}}(ρ)) + ∑_{a=1}^{D} ζ_a(σ)`,

with `ζ_a(σ) := ‖H_σ(X_a:Z_a|W_a)‖∞` (eq. (7)); if `σ` has uniform MCMI
decay with constants `K, ξ`, then

`D(ρ‖σ) ≤ ∑_{a,i} D(ρ‖E_{C_{a,i}}(ρ)) + D·2^D·K·|Λ|·e^{-c/ξ}`   (eq. (8)).

We state (7) with the `ζ_a` replaced by the MCMI values at the level regions
`X_a, Z_a, W_a`, and (8) as the uniform-decay corollary.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Kronecker

namespace Qatlib.Papers.GibbsSampling25.MainResults.Entropy

open Qatlib.Papers.GibbsSampling25.MainResults.Model
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus

/-- **Theorem 2.7 (Weak approximate tensorization)**, arXiv:2412.01732v1
p.6, eq. (7). For any state `ρ` of the full system and the Davies channels
`davies a C` associated with the cells `C` of level `a` of a suitable
coarse-graining `cg`,

`D(ρ‖σ) ≤ ∑_{a=0}^{D} ∑_{C ∈ cell a} D(ρ‖E_C(ρ)) + ∑_{a=1}^{D} ζ_a(σ)`,

where the correction term of level `a` is the MCMI value
`ζ_a(σ) = ‖H_σ(X_a:Z_a|W_a)‖∞` (`X`, `Z`, `W` select the level regions of
Appendix B.2); the `a = 0` term is absent from the correction sum. -/
def weak_approximate_tensorization {D L k c ℓ : ℕ} (cg : CoarseGraining D L k c ℓ)
    {I : Type} [Fintype I] [DecidableEq I] (σ ρ : Density I)
    (davies : Fin (D + 1) → Finset (Site D L) → Density I → Density I)
    (mcmi : McmiNorm (Site D L))
    (X Z W : Fin (D + 1) → Finset (Site D L))  : Prop :=
    relEnt ρ σ ≤
      (∑ a : Fin (D + 1), ∑ C ∈ cg.cell a, relEnt ρ (davies a C ρ))
        + ∑ a : Fin (D + 1), if a.val = 0 then 0 else mcmi (X a) (Z a) (W a)
  -- Source: arXiv:2412.01732v1, Theorem 2.7 (p.6, eq. (7)); proof in
  -- Theorem B.3 (Appendix B.3).
  -- Proof route: iterate the weak entropy factorization (Lemma 2.5) along the
  -- coarse-graining. At every level a, write the conditional relative entropy
  -- D_{C_{a,i}}(ρ‖σ) as D_{AB}(ρ‖σ) + D_{BC}(ρ‖σ) + ‖H_σ(A:C|D)‖∞ and use the
  -- Davies conditional expectation property D(ρ‖E_A(ρ)) = D_{C_A}(ρ‖σ)
  -- (Appendix A.3, property 3) to replace the local conditional entropies by
  -- the Davies terms; the MCMI remainders accumulate into the ζ_a sum.
  -- Scope: the matrix-level Davies channels, their conditional-expectation
  -- identity D(ρ‖E_A(ρ)) = D_{C_A}(ρ‖σ), and the concrete MCMI of
  -- Definition 2.2 are represented by the interface data `davies`, `mcmi`,
  -- and the marginal maps.  The combinatorial cover, membership, and
  -- disjointness properties are part of `CoarseGraining`.  The proof proceeds
  -- by applying Lemma 2.5 at each cell and telescoping over the levels.

/-- **Theorem 2.7, eq. (8)**, arXiv:2412.01732v1 p.6. If, in addition, `σ`
satisfies uniform decay of the MCMI with constants `K, ξ` (i.e.
`‖H_σ(A:C|D)‖∞ ≤ K|Λ|e^{-dist(A,C)/ξ}` for all regions), then the correction
term of eq. (7) is bounded by `D·2^D·K·|Λ|·e^{-c/ξ}`:

`D(ρ‖σ) ≤ ∑_{a,i} D(ρ‖E_{C_{a,i}}(ρ)) + D·2^D·K·|Λ|·e^{-c/ξ}`. -/
def weak_approximate_tensorization_uniform {D L k c ℓ : ℕ} (cg : CoarseGraining D L k c ℓ)
    {I : Type} [Fintype I] [DecidableEq I] (σ ρ : Density I)
    (davies : Fin (D + 1) → Finset (Site D L) → Density I → Density I)
    (mcmi : McmiNorm (Site D L)) (K ξ : ℝ) (hK : 0 < K) (hξ : 0 < ξ)
    (X Z W : Fin (D + 1) → Finset (Site D L))
    (hDecay : ∀ A C Dd : Finset (Site D L),
      mcmi A C Dd ≤ K * (Fintype.card (Site D L) : ℝ) * Real.exp (- setDist A C / ξ))  : Prop :=
    relEnt ρ σ ≤
      (∑ a : Fin (D + 1), ∑ C ∈ cg.cell a, relEnt ρ (davies a C ρ))
        + (D : ℝ) * (2 : ℝ) ^ D * K * (Fintype.card (Site D L) : ℝ)
            * Real.exp (-(c : ℝ) / ξ)
  -- Source: arXiv:2412.01732v1, Theorem 2.7 (p.6, eq. (8)) and the displayed
  -- bound on c₂ below it.
  -- Proof route: apply eq. (7); each of the D correction terms ζ_a is a single
  -- MCMI of a level-a region with core/shell distance c, so uniform decay gives
  -- ζ_a ≤ K|Λ|e^{-c/ξ}; summing over a = 1,…,D gives D·K|Λ|e^{-c/ξ}. The extra
  -- factor 2^D in the paper's display comes from the number of region
  -- comparisons X_a vs Z_a inside one level (2 choices per coordinate, D
  -- coordinates); with our single-MCMI `ζ_a` the sum is D·K|Λ|e^{-c/ξ}. We
  -- state the paper's bound D·2^D·K|Λ|e^{-c/ξ}, which is weaker (has the larger
  -- constant).
  -- Scope: as in eq. (7), the MCMI/Davies interface is abstract, and the
  -- counting of the `2^D` region comparisons in Appendix B.2 is not part of
  -- this definition.  Uniform decay bounds each correction by
  -- `K|Λ|e^{-c/ξ}` using the overlap distance; summing the levels and the
  -- region comparisons gives the displayed factor `D·2^D`.

end Qatlib.Papers.GibbsSampling25.MainResults.Entropy
