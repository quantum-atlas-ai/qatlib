/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.LchsRep.GeneralAnalyticLchsKernel
import Qatlib.Concepts.LchsSimulation.StaticLchs.StaticNoncommutingLCHS
import Qatlib.Concepts.QspSimulation.Achievability.MatrixExponentialApproximation
import Qatlib.Concepts.BlockEncoding.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option backward.isDefEq.respectTransparency false

/-!
# LaplaceEigen24 — shared source model

An, Childs, Lin, Ying, *Laplace transform based quantum eigenvalue transformation
via linear combination of Hamiltonian simulation*, fixed arXiv:2411.04010.
PDF and text were read from the prefetched assets
`prove/assets/2411.04010.{pdf,txt}`.

This module fixes the objects used by every paper-layer statement so that the
claim modules speak about the same matrix-exponential, Laplace-transform and
block-encoding objects as the paper:

* `cartesianEvolution` — `e^{-tA}` with `A = L + iH` (Eq. (22)–(23));
* `lchsKernelEvolution` — the LCHS integrand `U(k,t) = e^{-it(kL+H)}` (Eq. (31));
* `matrixLaplace` / `scalarLaplace` — the matrix and scalar Laplace transforms
  of Eq. (3)–(4);
* `laplaceKernel` — the LCHS weight `f(k)/(1-ik)`;
* `l1Norm` / `linfNorm` — the `L¹` set integral and the `L∞` supremum norm used
  in Lemma 5 and Theorem 6;
* `IsMatrixFunction` — the eigenvalue-transform functional calculus (used for
  `h(A)` in the application corollaries, cf. `MatrixFunc24`);
* `preparesState` — the semantic post-selected state-preparation guarantee used
  by Corollaries 7–13.

Query/gate counts of the paper are, as in the rest of the paper layer, recorded
in the docstrings of the corresponding theorems; the matrix-semantics layer does
not carry a circuit word or gate count.  This module asserts no source result.
-/

set_option autoImplicit false
noncomputable section

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.LaplaceEigen24.MainResults

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The Cartesian matrix `A = L + iH` of Eq. (22). -/
noncomputable def cartesianMatrix (L H : Matrix I I ℂ) : Matrix I I ℂ :=
  L + Complex.I • H

/-- The actual matrix exponential `e^{-tA}` of the dissipative evolution, with
`A = L + iH` (Eq. (22)–(23)).  This is `NormedSpace.exp` of the matrix algebra,
not a scalar sampling. -/
noncomputable def cartesianEvolution (L H : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  NormedSpace.exp ((-(t : ℂ)) • cartesianMatrix L H)

/-- The LCHS integrand `U(k,t) = e^{-it(kL+H)}` of Eq. (31). -/
noncomputable def lchsKernelEvolution (L H : Matrix I I ℂ) (k t : ℝ) : Matrix I I ℂ :=
  NormedSpace.exp ((-Complex.I * (t : ℂ)) • ((k : ℂ) • L + H))

/-- The matrix Laplace transform `h(A) = ∫₀^∞ g(t) e^{-tA} dt` of Eq. (3)–(4),
with the Bochner integral over `(0,∞)`. -/
noncomputable def matrixLaplace (g : ℝ → ℂ) (A : Matrix I I ℂ) : Matrix I I ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), g t • NormedSpace.exp ((-(t : ℂ)) • A)

/-- The scalar Laplace transform `h(z) = ∫₀^∞ g(t) e^{-zt} dt` of Eq. (3). -/
noncomputable def scalarLaplace (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), g t * Complex.exp (-(z * (t : ℂ)))

/-- The LCHS kernel weight `f(k)/(1-ik)` of Eq. (25)/(27). -/
noncomputable def laplaceKernel (f : ℂ → ℂ) (k : ℝ) : ℂ :=
  f (k : ℂ) / (1 - Complex.I * (k : ℂ))

/-- The double-integral integrand of Theorem 4, Eq. (27), over a pair
`(t,k) : ℝ × ℝ`. -/
noncomputable def laplaceDoubleIntegrand (f : ℂ → ℂ) (g : ℝ → ℂ)
    (L H : Matrix I I ℂ) (p : ℝ × ℝ) : Matrix I I ℂ :=
  (g p.1 * laplaceKernel f p.2) • lchsKernelEvolution L H p.2 p.1

/-- `L¹` norm on a set: `∫_s ‖f‖`. -/
noncomputable def l1Norm (f : ℝ → ℂ) (s : Set ℝ) : ℝ :=
  ∫ x in s, ‖f x‖

/-- `L∞` (supremum) norm.  For a function that is not essentially bounded the
value is the junk value `sSup` of an unbounded set; every statement using it
carries a boundedness hypothesis. -/
noncomputable def linfNorm (f : ℝ → ℂ) : ℝ :=
  sSup (Set.range fun x : ℝ => ‖f x‖)

/-- The eigenvalue-transform matrix functional calculus: `B = f(A)` when `A` is
unitarily diagonalized and `f` is applied entrywise to the eigenvalues. -/
def IsMatrixFunction (f : ℂ → ℂ) (A B : Matrix I I ℂ) : Prop :=
  ∃ (U : Matrix I I ℂ) (lam : I → ℂ),
    U ∈ Matrix.unitaryGroup I ℂ ∧
      A = U * Matrix.diagonal lam * Uᴴ ∧
      B = U * Matrix.diagonal (fun i => f (lam i)) * Uᴴ

/-- Euclidean (ℓ²) norm of a bare amplitude vector `I → ℂ`. -/
noncomputable def vecNorm {I : Type*} [Fintype I] (v : I → ℂ) : ℝ :=
  ‖(WithLp.toLp 2 v : EuclideanSpace ℂ I)‖

/-- Semantic post-selected state preparation: for a flag ancilla `F`, the
all-zero flag component `w` of `U (|f₀⟩ ⊗ ψ)` succeeds with probability at
least `1/2`, and its normalized system part is `ε`-close (in ℓ² norm) to
`target`.  This captures the "`ε`-approximation with `Ω(1)` success probability
and a flag indicating success" wording of Corollaries 7–13. -/
def preparesState {F I : Type*} [Fintype F] [DecidableEq F] [Fintype I] [DecidableEq I]
    (U : Matrix (F × I) (F × I) ℂ) (f₀ : F) (ψ target : I → ℂ) (ε : ℝ) : Prop :=
  let v : F × I → ℂ := U *ᵥ (fun x => if x.1 = f₀ then ψ x.2 else 0)
  let w : I → ℂ := fun i => v (f₀, i)
  (1 / 2 : ℝ) ≤ vecNorm w ^ 2 ∧
    vecNorm (fun i => w i / (vecNorm w : ℂ) - target i) ≤ ε

end Qatlib.Papers.LaplaceEigen24.MainResults
