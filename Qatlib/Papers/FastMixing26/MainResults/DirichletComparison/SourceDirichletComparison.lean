/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FastMixing26.MainResults.ClusterExpansion.SourceClusterExpansion
import Qatlib.Foundations.DirichletForm.KmsDirichlet.Basic
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCoreDefs
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupDirichlet
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# FastMixing26.MainResults.DirichletComparison — Section 5

Bergamaschi, *Fast mixing of all-to-all quantum systems at high temperatures*,
arXiv:2606.26090v2.

Scope note: this module imports the vocabulary for the multiscale Dirichlet-form
comparison in Section 5.  Theorem 5.1 and Lemmas 5.4/5.5 (claims c015–c017), whose
proofs use that comparison, are outside the scope of this file.

The CKG Lindbladian `L` is `Qatlib.Concepts.LindbladFlow.GkslSemigroup.gkslHeisenbergMap`
(the trace dual of the Schrödinger generator); its Dirichlet form is
`kmsDirichlet`. The Pauli generator `K = Σ_a K_a` is `kmsGeneratorFam`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators MatrixOrder ComplexOrder
open MeasureTheory Finset Matrix
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.FastMixing26.MainResults.DirichletComparison

open Qatlib.Papers.FastMixing26.MainResults
open Qatlib.Papers.FastMixing26.MainResults.ClusterExpansion
open Qatlib.Foundations.DirichletForm.KmsDirichlet
open Qatlib.Concepts.LindbladFlow.GkslSemigroup

/-- The `g`-Dirichlet form of (110)/(112): for a jump family `A` and Hamiltonian `H`,
`C[O] = Σ_a ∫_ℝ (β cosh(2πt/β))^{-1} ‖[A_a(t), O]‖²_ρ dt`, where
`A_a(t) = e^{iHt}A_a e^{-iHt}` is `complexTimeEvolve H (A a) (t : ℂ)`. -/
noncomputable def gDirichlet {D : ℕ} {ι : Type} [Fintype ι] (ρ : Operator D) (β : ℝ)
    (H : Operator D) (A : ι → Operator D) (O : Operator D) : ℝ :=
  ∑ a, ∫ t : ℝ,
    (1 / (β * Real.cosh (2 * Real.pi * t / β))) *
      (kmsNorm ρ (complexTimeEvolve H (A a) (t : ℂ) * O
        - O * complexTimeEvolve H (A a) (t : ℂ))) ^ 2

end Qatlib.Papers.FastMixing26.MainResults.DirichletComparison
