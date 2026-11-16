/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LaplaceEigen24.MainResults.SourceModel
public import Qatlib.Papers.LaplaceEigen24.MainResults.Representation.LaplaceRepresentation

@[expose] public section


set_option autoImplicit false
noncomputable section
set_option linter.unusedVariables false

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.LaplaceEigen24.MainResults

open Qatlib.Papers.LaplaceEigen24.MainResults

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Boundary trace `k ↦ f(k)` of a function on the complex plane: the function
whose `L¹(ℝ)` and `L∞(ℝ)` norms appear in Lemma 5 (the boundary values of the
Hardy-space function `f` on the real line). -/
noncomputable def boundaryTrace (f : ℂ → ℂ) : ℝ → ℂ := fun k => f (k : ℂ)

/-- Uniform `k`-grid node `k_j = -K + j·(2K/Mk)` of Eq. (33)–(34). -/
noncomputable def kNode (K : ℝ) (Mk : ℕ) (j : ℕ) : ℝ :=
  -K + (j : ℝ) * (2 * K / (Mk : ℝ))

/-- Uniform `t`-grid node `t_l = l·(T/Mt)` of Eq. (33)–(34). -/
noncomputable def tNode (T : ℝ) (Mt : ℕ) (l : ℕ) : ℝ :=
  (l : ℝ) * (T / (Mt : ℝ))

/-- Step size `h_k = 2K/Mk`. -/
noncomputable def kStep (K : ℝ) (Mk : ℕ) : ℝ := 2 * K / (Mk : ℝ)

/-- Step size `h_t = T/Mt`. -/
noncomputable def tStep (T : ℝ) (Mt : ℕ) : ℝ := T / (Mt : ℝ)

/-- Quadrature coefficient `c_j = h_k f(k_j)/(1-i k_j)`. -/
noncomputable def cCoeff (f : ℂ → ℂ) (K : ℝ) (Mk : ℕ) (j : ℕ) : ℂ :=
  (kStep K Mk : ℂ) * laplaceKernel f (kNode K Mk j)

/-- Quadrature coefficient `ĉ_l = h_t g(t_l)`. -/
noncomputable def tCoeff (g : ℝ → ℂ) (T : ℝ) (Mt : ℕ) (l : ℕ) : ℂ :=
  (tStep T Mt : ℂ) * g (tNode T Mt l)

/-- The truncated double integral of Eq. (33). -/
noncomputable def truncatedIntegral (f : ℂ → ℂ) (g : ℝ → ℂ) (L H : Matrix I I ℂ)
    (K T : ℝ) : Matrix I I ℂ :=
  ∫ t in Set.Ioc (0 : ℝ) T, ∫ k in Set.Icc (-K) K,
    (g t * laplaceKernel f k) • lchsKernelEvolution L H k t

/-- The Riemann-sum approximation of Eq. (34). -/
noncomputable def riemannSum (f : ℂ → ℂ) (g : ℝ → ℂ) (L H : Matrix I I ℂ)
    (K T : ℝ) (Mk Mt : ℕ) : Matrix I I ℂ :=
  ∑ j ∈ Finset.range Mk, ∑ l ∈ Finset.range Mt,
    (cCoeff f K Mk j * tCoeff g T Mt l) • lchsKernelEvolution L H (kNode K Mk j) (tNode T Mt l)

/-- Lemma 5, part 3, Eqs. (37)–(38) of arXiv:2411.04010 (printed p.12): once
the truncation and quadrature errors are each at most half of the tolerance,
the total approximation error is at most `ε`.

Printed statement: to bound `‖h(A) - Σ_{j,l} c_j ĉ_l U(k_j,t_l)‖` by `ε` it
suffices to choose `K, T` with
`‖g‖_{L¹((T,∞))} = O(ε/‖f‖_{L¹(ℝ)})` and
`‖f‖_{L¹(ℝ∖[-K,K])} = O(ε/‖g‖_{L¹(ℝ₊)})`, and grid numbers
`Mk = O(K²T/ε · (‖f‖∞‖tg‖∞‖A‖ + ‖f'‖∞ + ‖f‖∞‖g‖∞))`,
`Mt = O(KT²/ε · (‖f‖∞‖g‖∞‖A‖ + ‖f‖∞‖g'‖∞))`.
The two `O`-constants in (37)–(38) are not printed, so the Lean statement takes
the two numeric error bounds as hypotheses and concludes the combined bound by
the triangle inequality; the printed tail/grid conditions are recorded above. -/
theorem truncation_error_total_le
    (f : ℂ → ℂ) (g : ℝ → ℂ) (L H : Matrix I I ℂ) (K T : ℝ) (Mk Mt : ℕ) {ε : ℝ}
    (htrunc : ‖matrixLaplace g (cartesianMatrix L H) - truncatedIntegral f g L H K T‖ ≤ ε / 2)
    (hquad : ‖truncatedIntegral f g L H K T - riemannSum f g L H K T Mk Mt‖ ≤ ε / 2) :
    ‖matrixLaplace g (cartesianMatrix L H) - riemannSum f g L H K T Mk Mt‖ ≤ ε := by
  have hsplit : matrixLaplace g (cartesianMatrix L H) - riemannSum f g L H K T Mk Mt
      = (matrixLaplace g (cartesianMatrix L H) - truncatedIntegral f g L H K T)
        + (truncatedIntegral f g L H K T - riemannSum f g L H K T Mk Mt) := by
    abel
  rw [hsplit]
  linarith [norm_add_le (matrixLaplace g (cartesianMatrix L H) - truncatedIntegral f g L H K T)
    (truncatedIntegral f g L H K T - riemannSum f g L H K T Mk Mt)]

end Qatlib.Papers.LaplaceEigen24.MainResults
