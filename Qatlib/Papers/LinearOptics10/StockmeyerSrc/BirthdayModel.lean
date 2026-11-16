/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.BosonFock.BosonOperators.Pigeonhole
public import Qatlib.Concepts.BosonFock.BosonOperators.BosonPermanent
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section


/-! # Fixed-source birthday definitions and genuine unitary averaging

Aaronson--Arkhipov, arXiv:1011.3245v1, Appendix 13. The historical
`HaarLaw` predicate is retained exactly for diagnosis: permutation
invariance alone does not specify Haar measure or support on unitaries.
The source averaged Corollary 70 target is proved without mistaking it
for the paper's stronger fixed-state probability conclusion.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.BirthdayModel
open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib.Concepts.BosonFock.BosonOperators

/-- The actual first n columns of the input mode matrix. -/
def colMat {m n : ℕ} (U : Fin m → Fin m → ℂ) (hn : n ≤ m) :
    Matrix (Fin m) (Fin n) ℂ := fun i j => U i (Fin.castLE hn j)

/-- The historical permutation-invariance predicate, without a unitary-support assertion. -/
def HaarLaw (m : ℕ) (μ : Measure (Fin m → Fin m → ℂ)) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ σ : Equiv.Perm (Fin m),
    Measure.map (fun U i j => U (σ i) (σ j)) μ = μ

/-- The entire original P0075 averaged target follows from genuine unitarity and normalized weights. -/
theorem mixtureBound (M : ℕ) {ι : Type} [Fintype ι]
    (V : ι → Matrix (Fin M) (Fin M) ℂ) (w : ι → ℝ)
    (hw : ∀ t, 0 ≤ w t) (hw1 : ∑ t, w t = 1)
    (hV : ∀ t, V t ∈ Matrix.unitaryGroup (Fin M) ℂ) (G B : Finset (Fin M)) :
    (∑ t, w t * (∑ x ∈ G, ∑ y ∈ B, Complex.normSq (V t x y))) / (G.card : ℝ)
      ≤ (B.card : ℝ) / (G.card : ℝ) :=
  Pigeonhole.mixtureMass V w hw hw1 hV G B

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.BirthdayModel
