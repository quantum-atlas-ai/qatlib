/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.GramReadout
import Qatlib.Papers.QuantumSVM13.GramDensity

/-!
# The kernel matrix as a quantum density matrix (QuantumSVM13, claim c002)

Source: P. Rebentrost, M. Mohseni, S. Lloyd, "Quantum support vector machine for
big data classification", arXiv:1307.0471v3 (10 Jul 2014), p. 2, left column:
the preparation of `|χ⟩ = 1/√Nχ ∑_i |x_i| |i⟩ |x_i⟩` and the partial trace
`tr₂{|χ⟩⟨χ|} = K/tr K` with `K_ij = x_i · x_j` and `Nχ = ∑_i |x_i|²`.

The weighted-Gram identity is the Frozen result
`QuantumAlgorithm.Concepts.CopyEvolution.GramReadout.gramFirstRegisterDensity`.
This file only bridges the paper's data-dependent normalisation to it: the
data vectors are real `x_i ∈ ℝ^N`, their norms `|x_i| = sqrt(∑_k x_{ik}²)`
supply the weights `w_i = |x_i| / sqrt(Nχ)`, and the partial trace is exactly
the paper's normalised kernel matrix `K / tr K`. No preparation oracle is
asserted here; only the algebraic density-matrix identity is formalised.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Matrix
open scoped BigOperators Classical ComplexOrder

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.QuantumSVM13.GramDensity

open Qatlib.Papers.QuantumSVM13.GramDensity

open Qatlib.Concepts.CopyEvolution.GramReadout

variable {M N : ℕ}

/-- The native Gram weights are nonnegative actual real amplitudes. -/
theorem dataWeight_nonneg (x : Fin M → Fin N → ℝ) (i : Fin M) :
    0 ≤ dataWeight x i := by
  unfold dataWeight
  exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- Under the native nonzero-row hypothesis every Gram weight is strictly
positive. -/
theorem dataWeight_pos (x : Fin M → Fin N → ℝ) (hM : 0 < M)
    (hx : ∀ i, 0 < ∑ k, (x i k) ^ 2) (i : Fin M) :
    0 < dataWeight x i := by
  unfold dataWeight
  apply div_pos
  · exact Real.sqrt_pos.2 (hx i)
  · exact Real.sqrt_pos.2 (dataNormSq_pos x hM hx)

/-- Every individual Gram weight has squared mass at most one. -/
theorem dataWeight_sq_le_one (x : Fin M → Fin N → ℝ) (hM : 0 < M)
    (hx : ∀ i, 0 < ∑ k, (x i k) ^ 2) (i : Fin M) :
    (dataWeight x i) ^ 2 ≤ 1 := by
  have hsum := dataWeight_sq_sum x hM hx
  have hi : (dataWeight x i) ^ 2 ≤ ∑ j, (dataWeight x j) ^ 2 := by
    exact Finset.single_le_sum (fun j hj => sq_nonneg (dataWeight x j))
      (Finset.mem_univ i)
  simpa [hsum] using hi

/-- Every native Gram amplitude lies in the unit interval. -/
theorem dataWeight_mem_Icc_one (x : Fin M → Fin N → ℝ) (hM : 0 < M)
    (hx : ∀ i, 0 < ∑ k, (x i k) ^ 2) (i : Fin M) :
    dataWeight x i ∈ Set.Icc 0 1 := by
  refine ⟨dataWeight_nonneg x i, ?_⟩
  have hsq := dataWeight_sq_le_one x hM hx i
  nlinarith [dataWeight_nonneg x i]

/-- Under the native nonzero-row hypothesis every Gram weight is nonzero. -/
theorem dataWeight_ne_zero (x : Fin M → Fin N → ℝ) (hM : 0 < M)
    (hx : ∀ i, 0 < ∑ k, (x i k) ^ 2) (i : Fin M) :
    dataWeight x i ≠ 0 :=
  (ne_of_gt (dataWeight_pos x hM hx i))

end Qatlib.Papers.QuantumSVM13.GramDensity
