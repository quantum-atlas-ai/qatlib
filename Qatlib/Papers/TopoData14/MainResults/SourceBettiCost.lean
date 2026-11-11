/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# SourceBettiCost — the reconstruction time of Eq. (8)

Lloyd--Garnerone--Zanardi, *Quantum algorithms for topological and geometric analysis of
big data*, fixed arXiv:1408.3106v1 (2014).

Section 2, Eq. (8) (PDF p. 13, text line 504): after Eq. (7) the paper states that the
`k`-th Betti number is reconstructed to multiplicative accuracy `δ` in time

  `max( O(n³ / (η_k^ε δ)),  O(n² (ζ_k^ε)^{-1/2}) )`,

where `η_k^ε = dim (Ker ∂_k) / |S_k^ε|` is the probability that the quantum phase
algorithm projects onto the kernel of `B_k` (Eq. (6)), and `ζ_k^ε` is the accuracy to
which the simplex state is constructed. The text explains that the complexity "is
dominated either by the quantum phase algorithm and the probability that one identifies
an eigenstate in the kernel of B_k (first term in the max), or by the construction of the
simplex state (second term in the max)."

This file formalises that cost model and proves the paper's dominance decomposition:

* `kernelIdentificationCost n η δ = n³ / (η δ)` — the first term of the max;
* `simplexStateConstructionCost n ζ = n² ζ^{-1/2}` — the second term;
* `bettiReconstructionCost n η ζ δ = max` of the two;
* the dominance theorems: the reconstruction cost equals the kernel term when the
  simplex term is dominated (and dually), which is exactly the "dominated either
  by … or by …" sentence;
* `kernelIdentificationCost` in the paper's dimension form
  `n³ · |S_k^ε| / (dim (Ker ∂_k) · δ)` under `η_k^ε = dim (Ker ∂_k) / |S_k^ε|`.

Boundary: this is an arithmetic cost model for Eq. (8). It does not implement the quantum
phase estimation, the kernel projection, or the simplex-state preparation themselves;
those are separate algorithmic objects. It records the numeraire and the max structure of
the published bound.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TopoData14.MainResults

/-- First term of Eq. (8), fixed arXiv:1408.3106v1 (PDF p. 13): the quantum phase
algorithm cost `O(n³ / (η_k^ε δ))`, where `η_k^ε` is the kernel-projection probability
of Eq. (6). -/
def kernelIdentificationCost (n η δ : ℝ) : ℝ := n ^ 3 / (η * δ)

/-- Second term of Eq. (8), fixed arXiv:1408.3106v1 (PDF p. 13): the simplex-state
construction cost `O(n² (ζ_k^ε)^{-1/2})`. -/
def simplexStateConstructionCost (n ζ : ℝ) : ℝ := n ^ 2 / Real.sqrt ζ

/-- Eq. (8), fixed arXiv:1408.3106v1 (PDF p. 13): the Betti-number reconstruction time
`max(O(n³/(η_k^ε δ)), O(n² (ζ_k^ε)^{-1/2}))`. -/
def bettiReconstructionCost (n η ζ δ : ℝ) : ℝ :=
  max (kernelIdentificationCost n η δ) (simplexStateConstructionCost n ζ)

/-- Fixed arXiv:1408.3106v1, Eq. (8) (PDF p. 13): the reconstruction cost is literally
the maximum of the printed first and second terms. -/
theorem bettiReconstructionCost_eq_source (n η ζ δ : ℝ) :
    bettiReconstructionCost n η ζ δ =
      max (n ^ 3 / (η * δ)) (n ^ 2 / Real.sqrt ζ) := rfl

/-- Fixed arXiv:1408.3106v1, Eq. (8) (PDF p. 13): the second term is printed with
`(ζ_k^ε)^{-1/2}`; this is the same number as `n² / √ζ`. -/
theorem simplexStateConstructionCost_eq_inv_sqrt (n ζ : ℝ) :
    simplexStateConstructionCost n ζ = n ^ 2 * (Real.sqrt ζ)⁻¹ := by
  unfold simplexStateConstructionCost
  rw [div_eq_mul_inv]

/-- Fixed arXiv:1408.3106v1, Eq. (8) (PDF p. 13): the reconstruction cost in the exact
printed form `max(n³/(η δ), n² · ζ^{-1/2})`, with the inverse square root written
multiplicatively. -/
theorem bettiReconstructionCost_eq_max_inv_sqrt (n η ζ δ : ℝ) :
    bettiReconstructionCost n η ζ δ =
      max (n ^ 3 / (η * δ)) (n ^ 2 * (Real.sqrt ζ)⁻¹) := by
  unfold bettiReconstructionCost kernelIdentificationCost
  rw [simplexStateConstructionCost_eq_inv_sqrt]

/-! ## Dominance decomposition (the sentence after Eq. (8)) -/

/-- Fixed arXiv:1408.3106v1, PDF p. 13: the phase-estimation term never exceeds the
reconstruction cost. -/
theorem kernelIdentificationCost_le_bettiReconstructionCost (n η ζ δ : ℝ) :
    kernelIdentificationCost n η δ ≤ bettiReconstructionCost n η ζ δ :=
  le_max_left _ _

/-- Fixed arXiv:1408.3106v1, PDF p. 13: the simplex-state construction term never
exceeds the reconstruction cost. -/
theorem simplexStateConstructionCost_le_bettiReconstructionCost (n η ζ δ : ℝ) :
    simplexStateConstructionCost n ζ ≤ bettiReconstructionCost n η ζ δ :=
  le_max_right _ _

/-- Fixed arXiv:1408.3106v1, PDF p. 13 ("the computational complexity is dominated
either by the quantum phase algorithm … or by the construction of the simplex state"):
if the simplex-state term is no larger than the phase-estimation term, the reconstruction
cost is exactly the phase-estimation term. -/
theorem bettiReconstructionCost_eq_kernel_of_le
    (n η ζ δ : ℝ) (h : simplexStateConstructionCost n ζ ≤ kernelIdentificationCost n η δ) :
    bettiReconstructionCost n η ζ δ = kernelIdentificationCost n η δ := by
  unfold bettiReconstructionCost
  exact le_antisymm (max_le le_rfl h) (le_max_left _ _)

/-- Fixed arXiv:1408.3106v1, PDF p. 13: dually, if the phase-estimation term is no
larger than the simplex-state term, the reconstruction cost is exactly the simplex-state
term. -/
theorem bettiReconstructionCost_eq_simplex_of_le
    (n η ζ δ : ℝ) (h : kernelIdentificationCost n η δ ≤ simplexStateConstructionCost n ζ) :
    bettiReconstructionCost n η ζ δ = simplexStateConstructionCost n ζ := by
  unfold bettiReconstructionCost
  rw [max_eq_right h]

/-! ## Nonnegativity and the dimension form of `η` -/

/-- Supports Eq. (8), fixed arXiv:1408.3106v1 (PDF p. 13): the phase-estimation term is
nonnegative for nonnegative parameters. -/
theorem kernelIdentificationCost_nonneg (n η δ : ℝ) (hn : 0 ≤ n) (hη : 0 ≤ η)
    (hδ : 0 ≤ δ) : 0 ≤ kernelIdentificationCost n η δ := by
  unfold kernelIdentificationCost
  exact div_nonneg (pow_nonneg hn 3) (mul_nonneg hη hδ)

/-- Supports Eq. (8), fixed arXiv:1408.3106v1 (PDF p. 13): the simplex-state term is
nonnegative for every `n` and `ζ ≥ 0`. -/
theorem simplexStateConstructionCost_nonneg (n ζ : ℝ) :
    0 ≤ simplexStateConstructionCost n ζ := by
  unfold simplexStateConstructionCost
  exact div_nonneg (sq_nonneg n) (Real.sqrt_nonneg ζ)

/-- Fixed arXiv:1408.3106v1, PDF p. 13: `η_k^ε = dim (Ker ∂_k) / |S_k^ε|`, the
probability that the phase algorithm projects the `k`-simplex state onto the kernel of
`B_k`. -/
def kernelProjectionProbability (dker dS : ℕ) : ℝ := (dker : ℝ) / (dS : ℝ)

/-- Fixed arXiv:1408.3106v1, Eq. (8) with `η_k^ε = dim (Ker ∂_k) / |S_k^ε|`: the
phase-estimation term in the paper's dimension form,
`n³ · |S_k^ε| / (dim (Ker ∂_k) · δ)`. -/
theorem kernelIdentificationCost_eq_dimension_form
    (n δ : ℝ) (dker dS : ℕ) (hker : (dker : ℝ) ≠ 0) (hS : (dS : ℝ) ≠ 0) (hδ : δ ≠ 0) :
    kernelIdentificationCost n (kernelProjectionProbability dker dS) δ =
      n ^ 3 * (dS : ℝ) / ((dker : ℝ) * δ) := by
  unfold kernelIdentificationCost kernelProjectionProbability
  field_simp

end Qatlib.Papers.TopoData14.MainResults

end
