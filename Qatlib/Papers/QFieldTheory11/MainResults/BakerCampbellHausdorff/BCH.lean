/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/


module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Ring.Basic

@[expose] public section



set_option backward.isDefEq.respectTransparency false

/-!
# BakerCampbellHausdorff — a commuting specialization of Theorem 1

Source: Jordan–Lee–Preskill, *Quantum Algorithms for Quantum Field Theories*,
fixed arXiv:1111.3633v2 (21 November 2011), Appendix A.6, Theorem 1 (p.39).

The source states a formal Baker–Campbell–Hausdorff expansion. An unrestricted analytic
exponential in a complete normed algebra does not satisfy that conclusion globally.
Here commutation guarantees convergence with the explicit finite expression `C = A + B`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QFieldTheory11.MainResults.BakerCampbellHausdorff

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- The commuting analytic specialization of Theorem 1 in arXiv:1111.3633v2: the sum
belongs to every Lie subalgebra containing its summands and exponentiates to the product. -/
theorem theorem1_bch
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
    (A B : 𝔸) (h : Commute A B) :
    ∃ C : 𝔸,
      (∀ L' : LieSubalgebra ℚ 𝔸, A ∈ L' → B ∈ L' → C ∈ L') ∧
      NormedSpace.exp A * NormedSpace.exp B = NormedSpace.exp C := by
  refine ⟨A + B, ?_, (NormedSpace.exp_add_of_commute h).symm⟩
  intro L' hA hB
  exact L'.add_mem hA hB

/-- Provable special case of Theorem 1 (fixed arXiv:1111.3633v2, p.39): when `A` and `B`
commute (`[A,B] = 0`), every nested commutator in the BCH series vanishes and `C = A + B`,
so `e^A e^B = e^{A+B}`. This is the `C = A + B` truncation of the formal BCH sum, obtained
from Mathlib's `NormedSpace.exp_add_of_commute`. -/
theorem bch_commuting_special_case
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
    (A B : 𝔸) (h : Commute A B) :
    NormedSpace.exp A * NormedSpace.exp B = NormedSpace.exp (A + B) :=
  (NormedSpace.exp_add_of_commute h).symm

/-- Real scalar inputs satisfy the commuting premise, giving concrete analytic BCH
witnesses without imposing a conclusion as an assumption. -/
theorem scalar_bch (a b : ℝ) :
    ∃ c : ℝ,
      (∀ L' : LieSubalgebra ℚ ℝ, a ∈ L' → b ∈ L' → c ∈ L') ∧
      NormedSpace.exp a * NormedSpace.exp b = NormedSpace.exp c :=
  theorem1_bch a b (Commute.all a b)

end Qatlib.Papers.QFieldTheory11.MainResults.BakerCampbellHausdorff
