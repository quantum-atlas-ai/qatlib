/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LaplaceEigen24.MainResults.Discretization
public import Qatlib.Concepts.BlockEncoding.Basic

@[expose] public section


set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.LaplaceEigen24.MainResults

open Qatlib.Papers.LaplaceEigen24.MainResults

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The paper's `A`-query count expression (60), without the suppressed `O(·)`
constant: `α_A K T + log(‖f‖_{L¹}‖g‖_{L¹}/ε)`. -/
noncomputable def queryCountA (αA K T ε : ℝ) (f : ℂ → ℂ) (g : ℝ → ℂ) : ℝ :=
  αA * K * T + Real.log (l1Norm (boundaryTrace f) Set.univ * l1Norm g (Set.Ioi (0 : ℝ)) / ε)

/-- Theorem 6 of arXiv:2411.04010 (printed p.16, Eqs. (59)–(60)), numerical
content: suppose the truncation/grid parameters are chosen as in Lemma 5 (so
that the Riemann sum is `ε`-close to `h(A)` in operator norm), and suppose the
LCU of the Hamiltonian-simulation blocks and coefficient preparation unitaries
gives a `(α, 0)`-block encoding of that Riemann sum with factor
`α ≤ 2‖f‖_{L¹(ℝ)}‖g‖_{L¹(ℝ₊)}`.  Then `h(A)` itself admits the same
`(α, ε)`-block encoding, and the factor obeys the printed bound (59).

The block-encoding data `U, L, R` are the LCU circuit of §3.4 (Eqs. (61)–(65));
its construction and the query count (60) are recorded in the module docstring
and are not mechanized here.

Proof: the printed triangle inequality (63)–(65) is exactly
`BlockEncoding.perturb` applied with the exact Riemann-sum encoding, since
`ε₁ = 0` corresponds to exact Hamiltonian simulation blocks. -/
theorem lap_lchs_block_encoding
    (f : ℂ → ℂ) (g : ℝ → ℂ) (L H : Matrix I I ℂ)
    (K T : ℝ) (Mk Mt : ℕ) {α ε : ℝ}
    (U : Matrix (Fin 2 × I) (Fin 2 × I) ℂ)
    (Lm Rm : Matrix (Fin 2 × I) I ℂ)
    (hfactor : α ≤ 2 * l1Norm (boundaryTrace f) Set.univ * l1Norm g (Set.Ioi (0 : ℝ)))
    (hsum : Qatlib.Concepts.BlockEncoding.BlockEncoding
      (riemannSum f g L H K T Mk Mt) U Lm Rm α 0)
    (happrox : ‖matrixLaplace g (cartesianMatrix L H) - riemannSum f g L H K T Mk Mt‖ ≤ ε)
    (hε : 0 ≤ ε) :
    Qatlib.Concepts.BlockEncoding.BlockEncoding
        (matrixLaplace g (cartesianMatrix L H)) U Lm Rm α ε ∧
      α ≤ 2 * l1Norm (boundaryTrace f) Set.univ * l1Norm g (Set.Ioi (0 : ℝ)) := by
  refine ⟨?_, hfactor⟩
  have h := hsum.perturb hε happrox
  simpa using h

/-- Theorem 6, item 2 of arXiv:2411.04010 (printed p.16): combining the two
error bounds of Lemma 5 with the exact LCU encoding.  If the truncated
quadrature sum is `ε`-close to `h(A)` and the block encoding of the Riemann sum
has precision `ε`, the resulting block encoding of `h(A)` has precision `2ε`.

This is the printed "bound the quadrature error by `O(ε)` and the simulation
error by `O(ε/‖f‖₁‖g‖₁)`" decomposition (Eqs. (63)–(66)), stated with explicit
`ε`-budgets. -/
theorem lap_lchs_block_encoding_two_source_error
    (f : ℂ → ℂ) (g : ℝ → ℂ) (L H : Matrix I I ℂ)
    (K T : ℝ) (Mk Mt : ℕ) {α ε : ℝ}
    (U : Matrix (Fin 2 × I) (Fin 2 × I) ℂ)
    (Lm Rm : Matrix (Fin 2 × I) I ℂ)
    (hfactor : α ≤ 2 * l1Norm (boundaryTrace f) Set.univ * l1Norm g (Set.Ioi (0 : ℝ)))
    (hsum : Qatlib.Concepts.BlockEncoding.BlockEncoding
      (riemannSum f g L H K T Mk Mt) U Lm Rm α ε)
    (happrox : ‖matrixLaplace g (cartesianMatrix L H) - riemannSum f g L H K T Mk Mt‖ ≤ ε)
    (hε : 0 ≤ ε) :
    Qatlib.Concepts.BlockEncoding.BlockEncoding
          (matrixLaplace g (cartesianMatrix L H)) U Lm Rm α (ε + ε) ∧
      α ≤ 2 * l1Norm (boundaryTrace f) Set.univ * l1Norm g (Set.Ioi (0 : ℝ)) := by
  refine ⟨?_, hfactor⟩
  exact hsum.perturb hε happrox

end Qatlib.Papers.LaplaceEigen24.MainResults
