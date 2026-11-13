/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

/-!
# Orbit Fourier vectors and uniform Born weights

This module defines translation matrices `orbitRegMatrix`, normalized character vectors
`orbitFourierVec`, and their Born masses at the identity. The masses define `fourierBornDist`, a
distribution assigning every character the reciprocal of the group cardinality. [Kitaev1995]

## Main statements

* `fourierBornMass_eq`: computes the Born mass of each Fourier vector at zero.
* `fourierBornDist_apply`: identifies the character distribution as uniform.

## References

* [Kitaev, 1995][Kitaev1995]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

open Matrix
open scoped Classical BigOperators

variable (E : Type) [AddCommGroup E] [Fintype E] [DecidableEq E]

/-- The permutation matrix for translation by `g₀` in the finite abelian group `E`. -/
noncomputable def orbitRegMatrix (g₀ : E) : Matrix E E ℂ :=
  permMatrix (fun x => x + g₀)

/-- The character vector with coordinate `χ g / sqrt(card E)` at each group element `g`. -/
noncomputable def orbitFourierVec (χ : AddChar E ℂ) : QState E :=
  fun g => (Real.sqrt ((Fintype.card E : ℝ)))⁻¹ * (χ g)

/-- The Born probability at the identity element for the Fourier vector indexed by `χ`. -/
noncomputable def fourierBornMass (χ : AddChar E ℂ) : ℝ :=
  BornProb (orbitFourierVec E χ) 0

omit [DecidableEq E] in

/-- The Born mass at zero of every normalized character vector equals the reciprocal of the
group cardinality. -/
theorem fourierBornMass_eq (χ : AddChar E ℂ) :
    fourierBornMass E χ = (Fintype.card E : ℝ)⁻¹ := by
  have hq0 : 0 ≤ (Fintype.card E : ℝ) := by exact_mod_cast Nat.zero_le _
  have hχ0 : (χ 0 : ℂ) = 1 := by simp
  unfold fourierBornMass BornProb orbitFourierVec
  rw [hχ0, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), inv_pow, Real.sq_sqrt hq0]

/-- The finite distribution on complex additive characters given by their Fourier vector Born
masses at zero. -/
noncomputable def fourierBornDist : FinDist (AddChar E ℂ) where
  prob χ := fourierBornMass E χ
  nonneg χ := bornProb_nonneg _ _
  sum_one := by
    have hcard : Fintype.card (AddChar E ℂ) = Fintype.card E := AddChar.card_eq
    have hq : ((Fintype.card E : ℝ)) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    calc ∑ χ : AddChar E ℂ, fourierBornMass E χ
        = ∑ _χ : AddChar E ℂ, (Fintype.card E : ℝ)⁻¹ :=
          Finset.sum_congr rfl fun _χ _ => fourierBornMass_eq E _χ
      _ = (Fintype.card (AddChar E ℂ) : ℝ) * (Fintype.card E : ℝ)⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ = 1 := by
          rw [show (Fintype.card (AddChar E ℂ) : ℝ) = (Fintype.card E : ℝ) from by
              exact_mod_cast hcard, mul_inv_cancel₀ hq]

/-- Every character has probability equal to the reciprocal of the group cardinality under
`fourierBornDist`. -/
@[simp] theorem fourierBornDist_apply (χ : AddChar E ℂ) :
    (fourierBornDist E).prob χ = (Fintype.card E : ℝ)⁻¹ := fourierBornMass_eq E χ

end Qatlib.Concepts.HspRecovery.AbelianSampling
