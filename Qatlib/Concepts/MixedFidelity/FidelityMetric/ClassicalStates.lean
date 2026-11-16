/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import QuantumInfo.States.Mixed.Fidelity
public import Mathlib.Tactic.Ring

@[expose] public section


/-! # Classical-state root fidelity

These identities connect Physlib classical embeddings to the unsquared
Bhattacharyya coefficient. They support the finite-copy classical restriction
of fidelity testing, without asserting any copy-complexity bound.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric
open scoped BigOperators
variable {d : Type*} [Fintype d] [DecidableEq d]

section Classical

open scoped ComplexOrder

/-!
### Square roots of classical states

Through the pin's `MState.ofClassical_pow`, the matrix square root of a
classical (diagonal) state stays diagonal with entrywise real square roots.
This keeps the classical world closed under the pin's fidelity functional
calculus, and makes `MState.ofClassical` injective.
-/

/-- The square root of a diagonal Hermitian matrix is the entrywise real
square root, in the diagonal form of the pin's `HermitianMat.rpow_diagonal`,
via `HermitianMat.sqrt_eq_cfc_rpow_half`. -/
theorem sqrt_diagonal (h : d → ℝ) :
    (HermitianMat.diagonal ℂ h).sqrt
      = HermitianMat.diagonal ℂ (fun i ↦ (h i) ^ (1 / 2 : ℝ)) := by
  rw [show (HermitianMat.diagonal ℂ h).sqrt = (HermitianMat.diagonal ℂ h) ^ (1 / 2 : ℝ) from by
      rw [HermitianMat.sqrt_eq_cfc_rpow_half, ← HermitianMat.rpow_eq_cfc],
    HermitianMat.rpow_diagonal]

/-- Square roots of classical states are classical: the square root of
`MState.ofClassical p` is the diagonal state with entries `Real.sqrt (p i)`
(written as real powers, per the pin's `MState.ofClassical_pow`). -/
theorem sqrt_ofClassical (p : ProbDistribution d) :
    (MState.ofClassical p).M.sqrt
      = HermitianMat.diagonal ℂ (fun i ↦ (p i : ℝ) ^ (1 / 2 : ℝ)) := by
  rw [MState.coe_ofClassical, sqrt_diagonal]

/-- `MState.ofClassical` is injective: the diagonal of a classical state
determines its distribution. -/
theorem ofClassical_inj (p q : ProbDistribution d) :
    MState.ofClassical p = MState.ofClassical q ↔ p = q := by
  constructor
  · intro h
    have hM : (MState.ofClassical p).M.mat = (MState.ofClassical q).M.mat :=
      congrArg (fun ρ ↦ ρ.M.mat) h
    rw [MState.coe_ofClassical, MState.coe_ofClassical, HermitianMat.diagonal_mat,
      HermitianMat.diagonal_mat] at hM
    refine ProbDistribution.ext (fun x => ?_)
    exact Prob.ext (by simpa [Matrix.diagonal_apply] using congrFun₂ hM x x)
  · intro h
    rw [h]

/-!
### The classical Bhattacharyya connection

The root fidelity of two classical states is exactly the Bhattacharyya
coefficient of their distributions.  The two promise-boundary facts of the
bounds `MState.fidelity_le_one` and `MState.fidelity_eq_one_iff_self`
transport through this identity.
-/

/-- **Classical Bhattacharyya connection.**  The root fidelity of two
classical states is exactly the Bhattacharyya coefficient of their
distributions, `F(ofClassical p, ofClassical q) = ∑ x, √(p x * q x)`.  With
the root-fidelity convention this is the *unsquared* coefficient.  Proof: square roots stay diagonal
(`sqrt_ofClassical`), conjugating one diagonal state by the other's square
root multiplies entries (`HermitianMat.diagonal_conj_diagonal`), the outer
square root is again entrywise (`sqrt_diagonal`), and the trace of a diagonal
state sums its entries (`HermitianMat.trace_diagonal`). -/
theorem fidelity_ofClassical_eq_bhattacharyya (p q : ProbDistribution d) :
    MState.fidelity (MState.ofClassical p) (MState.ofClassical q)
      = ∑ x, Real.sqrt ((p x : ℝ) * (q x : ℝ)) := by
  show ((MState.ofClassical q).M.conj (MState.ofClassical p).M.sqrt.mat).sqrt.trace = _
  rw [sqrt_ofClassical, MState.coe_ofClassical, HermitianMat.diagonal_conj_diagonal]
  have key : (fun i ↦ ((q i : ℝ) * (((p i : ℝ)) ^ (1 / 2 : ℝ)) ^ 2))
      = (fun i ↦ ((p i : ℝ) * (q i : ℝ))) := by
    funext i
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt Prob.zero_le_coe]
    ring
  rw [key, sqrt_diagonal, HermitianMat.trace_diagonal]
  simp only [Real.sqrt_eq_rpow]

/-- The Bhattacharyya coefficient of two distributions is at most `1`, by the
pin's `MState.fidelity_le_one` through the connection above. -/
theorem bhattacharyya_le_one (p q : ProbDistribution d) :
    (∑ x, Real.sqrt ((p x : ℝ) * (q x : ℝ))) ≤ 1 := by
  rw [← fidelity_ofClassical_eq_bhattacharyya]
  exact MState.fidelity_le_one _ _

/-- The Bhattacharyya coefficient characterizes distribution equality, by the
pin's `MState.fidelity_eq_one_iff_self` through the connection above.  This is
the classical collapse of the `H₀` boundary: on classical states, coefficient
`1` already forces `p = q`. -/
theorem bhattacharyya_eq_one_iff (p q : ProbDistribution d) :
    (∑ x, Real.sqrt ((p x : ℝ) * (q x : ℝ))) = 1 ↔ p = q := by
  rw [← fidelity_ofClassical_eq_bhattacharyya, MState.fidelity_eq_one_iff_self]
  exact ofClassical_inj p q


end Classical

end Qatlib.Concepts.MixedFidelity.FidelityMetric
