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
# SourceDiracSpectrum — cost and spectral dimensions of the Dirac-operator QPE

Lloyd--Garnerone--Zanardi, *Quantum algorithms for topological and geometric analysis of
big data*, fixed arXiv:1408.3106v1 (2014).

Section 3 (PDF p. 14): after Eq. (10) the paper applies the quantum phase algorithm to the
Dirac operator `B^ε` of Eq. (9). The published statements are:

* "the quantum phase algorithm … can project the simplex states `|ψ⟩^ε_k` onto the
  eigenspaces of the Dirac operator `B^ε` and find corresponding eigenvalues to accuracy
  `δ` in time `O(n⁵ δ⁻¹ ζ^{-1/2})`" (text line 609--610);
* "the algorithm also identifies the dimension of the eigenspaces in time
  `O(n⁵ δ⁻¹ ζ^{-1/2} η_ℓ^{-1/2})`, where `η_ℓ` is equal to the dimension `d_ℓ` of the
  `ℓ`th eigenspace divided by `|S|_k`, the dimension of the `k`-simplex space"
  (text line 612--614);
* "the probability of yielding a particular eigenvalue is proportional to the dimension
  of the corresponding eigenspace" (text line 604);
* "the additional factor of `n²` compared with the algorithm for finding the Betti
  numbers alone comes from the need to project onto the simplicial subspace each stage
  of the computation" (text line 618--620).

This file formalises that cost model:

* `diracQPEcost n δ ζ = n⁵ δ⁻¹ ζ^{-1/2}` — the eigenvalue-estimation time;
* `eigenspaceDimensionCost n δ ζ η = diracQPEcost · η^{-1/2}` — the eigenspace-dimension
  time, with the paper's `η_ℓ^{-1/2}` amplification;
* `eigenspaceProbability dℓ dS = d_ℓ / |S|_k` — the spectral probability of measuring an
  eigenspace, with `eigenspaceProbability_le_one`;
* `diracQPEcost_eq_nsq_mul_bettiTerm`: the `n⁵` is `n² · n³`, the paper's statement that
  the extra `n²` comes from applying the projectors `P^ε` at every stage;
* `√`-inverse source forms of both costs.

The kernel statement `dim Ker ∆_k = β_k` that converts these spectral dimensions into
Betti numbers is proved in `SourceHodgeLaplacian.lean`
(`hodge_betti_eq_kernel_add_kernel_sub`).

Boundary: this is an arithmetic cost/spectral-dimension model. It does not implement the
quantum phase estimation circuit, its eigenvalue precision analysis, or the projectors
`P^ε`; it records the published numeraire and the relations between the printed bounds.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TopoData14.MainResults

/-- Fixed arXiv:1408.3106v1, Section 3 (PDF p. 14): the time for the quantum phase
algorithm to project onto the eigenspaces of the Dirac operator `B^ε` and find
eigenvalues to accuracy `δ`, `O(n⁵ δ⁻¹ ζ^{-1/2})`. -/
def diracQPEcost (n δ ζ : ℝ) : ℝ := n ^ 5 / (δ * Real.sqrt ζ)

/-- Fixed arXiv:1408.3106v1, Section 3 (PDF p. 14): the time to identify the dimension of
the `ℓ`th eigenspace, `O(n⁵ δ⁻¹ ζ^{-1/2} η_ℓ^{-1/2})`. -/
def eigenspaceDimensionCost (n δ ζ η : ℝ) : ℝ :=
  n ^ 5 / (δ * Real.sqrt ζ * Real.sqrt η)

/-- Fixed arXiv:1408.3106v1, Section 3 (PDF p. 14): `η_ℓ = d_ℓ / |S|_k`, the dimension
`d_ℓ` of the `ℓ`th eigenspace divided by the dimension `|S|_k` of the `k`-simplex space;
this is the probability that the phase algorithm yields the corresponding eigenvalue. -/
def eigenspaceProbability (dℓ dS : ℕ) : ℝ := (dℓ : ℝ) / (dS : ℝ)

/-- Fixed arXiv:1408.3106v1, Section 3 (PDF p. 14): the eigenvalue-estimation cost is
`n⁵ · δ⁻¹ · ζ^{-1/2}` in the printed multiplicative form. -/
theorem diracQPEcost_eq_source (n δ ζ : ℝ) :
    diracQPEcost n δ ζ = n ^ 5 * δ⁻¹ * (Real.sqrt ζ)⁻¹ := by
  unfold diracQPEcost
  rw [div_eq_mul_inv, mul_inv]
  simp [mul_assoc]

/-- Fixed arXiv:1408.3106v1, Section 3 (PDF p. 14): the eigenspace-dimension cost is
`n⁵ · δ⁻¹ · ζ^{-1/2} · η^{-1/2}` in the printed multiplicative form. -/
theorem eigenspaceDimensionCost_eq_source (n δ ζ η : ℝ) :
    eigenspaceDimensionCost n δ ζ η =
      n ^ 5 * δ⁻¹ * (Real.sqrt ζ)⁻¹ * (Real.sqrt η)⁻¹ := by
  unfold eigenspaceDimensionCost
  rw [div_eq_mul_inv, mul_inv, mul_inv]
  simp [mul_assoc]

/-- Fixed arXiv:1408.3106v1, Section 3 (PDF p. 14): identifying the eigenspace dimension
costs the eigenvalue-estimation time multiplied by the spectral amplification
`η_ℓ^{-1/2}`. -/
theorem eigenspaceDimensionCost_eq_diracQPEcost_mul_inv_sqrt
    (n δ ζ η : ℝ) (hδ : δ ≠ 0) (hζ : Real.sqrt ζ ≠ 0) (hη : Real.sqrt η ≠ 0) :
    eigenspaceDimensionCost n δ ζ η = diracQPEcost n δ ζ * (Real.sqrt η)⁻¹ := by
  unfold eigenspaceDimensionCost diracQPEcost
  field_simp

/-- Fixed arXiv:1408.3106v1, Section 3 (PDF p. 14): "the additional factor of `n²`
compared with the algorithm for finding the Betti numbers alone comes from the need to
project onto the simplicial subspace each stage of the computation". Formally, the `n⁵`
of the Dirac QPE cost is `n²` times the `n³` of the Betti-number phase-estimation term
(with `ζ^{-1/2}` in place of `δ`). -/
theorem diracQPEcost_eq_nsq_mul_bettiTerm
    (n δ ζ : ℝ) (hδ : δ ≠ 0) (hζ : Real.sqrt ζ ≠ 0) :
    diracQPEcost n δ ζ = n ^ 2 * (n ^ 3 / (δ * Real.sqrt ζ)) := by
  unfold diracQPEcost
  field_simp

/-- Supports the Section 3 cost model, fixed arXiv:1408.3106v1 (PDF p. 14): the
eigenvalue-estimation cost is nonnegative for nonnegative parameters. -/
theorem diracQPEcost_nonneg (n δ ζ : ℝ) (hn : 0 ≤ n) (hδ : 0 ≤ δ) :
    0 ≤ diracQPEcost n δ ζ := by
  unfold diracQPEcost
  exact div_nonneg (pow_nonneg hn 5) (mul_nonneg hδ (Real.sqrt_nonneg ζ))

/-- Supports the Section 3 cost model, fixed arXiv:1408.3106v1 (PDF p. 14): the
eigenspace-dimension cost is nonnegative for nonnegative parameters. -/
theorem eigenspaceDimensionCost_nonneg (n δ ζ η : ℝ) (hn : 0 ≤ n) (hδ : 0 ≤ δ) :
    0 ≤ eigenspaceDimensionCost n δ ζ η := by
  unfold eigenspaceDimensionCost
  exact div_nonneg (pow_nonneg hn 5)
    (mul_nonneg (mul_nonneg hδ (Real.sqrt_nonneg ζ)) (Real.sqrt_nonneg η))

/-! ## Spectral probabilities -/

/-- Fixed arXiv:1408.3106v1, Section 3 (PDF p. 14): the probability of yielding a
particular eigenvalue is the dimension of the eigenspace divided by the dimension of the
`k`-simplex space. -/
theorem eigenspaceProbability_eq_source (dℓ dS : ℕ) :
    eigenspaceProbability dℓ dS = (dℓ : ℝ) / (dS : ℝ) := rfl

/-- Supports Section 3, fixed arXiv:1408.3106v1 (PDF p. 14): the spectral probability is
nonnegative. -/
theorem eigenspaceProbability_nonneg (dℓ dS : ℕ) : 0 ≤ eigenspaceProbability dℓ dS := by
  unfold eigenspaceProbability
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Fixed arXiv:1408.3106v1, Section 3 (PDF p. 14): an eigenspace whose dimension `d_ℓ`
does not exceed the simplex-space dimension `|S|_k` has spectral probability at most one
(it is an honest probability). -/
theorem eigenspaceProbability_le_one (dℓ dS : ℕ) (h : dℓ ≤ dS) (hdS : 0 < dS) :
    eigenspaceProbability dℓ dS ≤ 1 := by
  unfold eigenspaceProbability
  rw [div_le_one (by exact_mod_cast hdS : (0 : ℝ) < (dS : ℝ))]
  exact_mod_cast h

/-- Fixed arXiv:1408.3106v1, Section 3 (PDF p. 14): in the dimension form
`η_ℓ = d_ℓ / |S|_k`, the eigenspace-dimension cost is
`n⁵ / (δ · ζ^{-1/2} · √(d_ℓ/|S|_k))`. -/
theorem eigenspaceDimensionCost_probability_form
    (n δ ζ : ℝ) (dℓ dS : ℕ) :
    eigenspaceDimensionCost n δ ζ (eigenspaceProbability dℓ dS) =
      n ^ 5 / (δ * Real.sqrt ζ * Real.sqrt ((dℓ : ℝ) / (dS : ℝ))) := rfl

end Qatlib.Papers.TopoData14.MainResults

end
