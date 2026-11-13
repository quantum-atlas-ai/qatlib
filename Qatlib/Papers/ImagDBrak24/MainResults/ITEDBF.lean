/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
import Qatlib.Papers.ImagDBrak24.MainResults.SourceDynamics
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Star

set_option backward.isDefEq.respectTransparency false

/-!
# Imaginary-Time Evolution as a Double-Bracket Flow (Propositions 4--5)

This module formalizes Propositions 4 and 5 (Equations (33) and (41),
pp. 13--14) of Gluza, Son, Tiang, and Ng, proving that normalized imaginary-time
evolution `∂_τ |Ψ⟩ = -(Ĥ - E(τ))|Ψ⟩` satisfies Brockett's double-bracket flow
`∂_τ Ψ = [[Ψ, Ĥ], Ψ]` and the exact fluctuation-refrigeration identity
`∂_τ E(τ) = -2 V(τ)`.

## Main statements

* `proposition4_iteDBF`: Proposition 4, `HasDerivAt` double-bracket flow
  equation for `pureState (ψ τ)`.
* `proposition5_iteFluctuationRefrigeration`: Proposition 5, `HasDerivAt`
  energy-variance cooling law `∂_τ E(τ) = -2 V(τ)`.

## References

* [Gluza, Son, Tiang, and Ng, 2024][GluzaEtAl2024ImagDBrak], Propositions 4--5,
  Equations (33) and (41), pp. 13--14.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.ImagDBrak24.MainResults

open Matrix
open scoped BigOperators ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem ite_coordinate_deriv
    (lam : ι → ℝ) (ψ : ℝ → ι → ℂ) (τ : ℝ)
    (hψ : HasDerivAt ψ
      (fun i => -(((diagHam lam) *ᵥ ψ τ) i -
        (expectedEnergy lam (ψ τ) : ℂ) * ψ τ i)) τ) (i : ι) :
    HasDerivAt (fun σ => ψ σ i)
      (((expectedEnergy lam (ψ τ) - lam i : ℝ) : ℂ) * ψ τ i) τ := by
  have hi := (hasDerivAt_pi.mp hψ) i
  convert hi using 1
  simp [diagHam, Matrix.mulVec_diagonal, sub_mul]

private theorem double_commutator_pureState_entry
    (lam : ι → ℝ) (x : ι → ℂ) (hx : IsState x) (i j : ι) :
    commutator (commutator (pureState x) (diagHam lam)) (pureState x) i j =
      (((2 * expectedEnergy lam x - lam i - lam j : ℝ) : ℂ)) *
        x i * star (x j) := by
  have hnorm : (∑ k, (weight x k : ℂ)) = 1 := by
    exact_mod_cast hx
  have henergy : (∑ k, (lam k : ℂ) * (weight x k : ℂ)) =
      (expectedEnergy lam x : ℂ) := by
    simp only [expectedEnergy, Complex.ofReal_sum, Complex.ofReal_mul]
  have hcomm (a b : ι) :
      commutator (pureState x) (diagHam lam) a b =
        ((lam b : ℂ) - (lam a : ℂ)) * x a * star (x b) := by
    simp only [commutator, Matrix.sub_apply, diagHam, Matrix.mul_diagonal,
      Matrix.diagonal_mul, pureState]
    ring
  change ((commutator (pureState x) (diagHam lam) * pureState x) i j -
    (pureState x * commutator (pureState x) (diagHam lam)) i j) = _
  simp only [Matrix.mul_apply, hcomm, pureState]
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ k, (2 * (lam k : ℂ) - ((lam i : ℂ) + (lam j : ℂ))) *
        (weight x k : ℂ) * (x i * star (x j)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [weight, ← star_mul_self_eq_normSq]
      ring
    _ = (2 * (∑ k, (lam k : ℂ) * (weight x k : ℂ)) -
        ((lam i : ℂ) + (lam j : ℂ)) * (∑ k, (weight x k : ℂ))) *
        (x i * star (x j)) := by
      rw [← Finset.sum_mul]
      congr 1
      simp only [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = _ := by
      rw [hnorm, henergy]
      push_cast
      ring

/-- **Proposition 4** (ITE is a solution to a DBF, Eq. (33), p.13).
The ITE pure state `Ψ(τ) = |Ψ(τ)⟩⟨Ψ(τ)|` — here any norm-preserving
imaginary-time flow `∂_τ |Ψ⟩ = -(Ĥ - E(τ))|Ψ⟩` — is a solution of Brockett's
double-bracket flow equation
`∂_τ Ψ(τ) = [[Ψ(τ), Ĥ], Ψ(τ)]`. -/
theorem proposition4_iteDBF
    (lam : ι → ℝ) (ψ : ℝ → ι → ℂ)
    (hstate : ∀ τ, IsState (ψ τ))
    (hite : ∀ τ, HasDerivAt ψ
      (fun i => -(((diagHam lam) *ᵥ ψ τ) i - (expectedEnergy lam (ψ τ) : ℂ) * ψ τ i)) τ) :
    ∀ τ, HasDerivAt (fun σ : ℝ => pureState (ψ σ))
      (commutator (commutator (pureState (ψ τ)) (diagHam lam)) (pureState (ψ τ))) τ := by
  intro τ
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hi := ite_coordinate_deriv lam ψ τ (hite τ) i
  have hj := ite_coordinate_deriv lam ψ τ (hite τ) j
  convert hi.mul hj.star using 1
  · rfl
  · rw [double_commutator_pureState_entry lam (ψ τ) (hstate τ) i j]
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring

/-- **Proposition 5** (ITE fluctuation–refrigeration relation, Eq. (41), p.14).
The derivative of the average energy `E(τ) = ⟨Ψ(τ)|Ĥ|Ψ(τ)⟩` of the
imaginary-time flow with respect to the inverse temperature `τ` is
`∂_τ E(τ) = -2 V(τ)`, where `V(τ) = ⟨Ψ(τ)|Ĥ²|Ψ(τ)⟩ - E(τ)²`. -/
theorem proposition5_iteFluctuationRefrigeration
    (lam : ι → ℝ) (ψ : ℝ → ι → ℂ)
    (hstate : ∀ τ, IsState (ψ τ))
    (hite : ∀ τ, HasDerivAt ψ
      (fun i => -(((diagHam lam) *ᵥ ψ τ) i - (expectedEnergy lam (ψ τ) : ℂ) * ψ τ i)) τ) :
    ∀ τ, HasDerivAt (fun σ : ℝ => expectedEnergy lam (ψ σ))
      (-2 * energyVariance lam (ψ τ)) τ := by
  intro τ
  by_cases _htriv : IsState (ψ τ) ∧ (0 : ℕ) ≤ Fintype.card ι
  swap
  · exact False.elim (_htriv ⟨hstate τ, Nat.zero_le _⟩)
  have hweight (i : ι) : HasDerivAt (fun σ => weight (ψ σ) i)
      (2 * (expectedEnergy lam (ψ τ) - lam i) * weight (ψ τ) i) τ := by
    have hi := ite_coordinate_deriv lam ψ τ (hite τ) i
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt τ hi
    have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt τ hi
    convert (hre.mul hre).add (him.mul him) using 1
    · rfl
    · simp [weight, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
      ring
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (hweight i).const_mul (lam i))
  convert hsum using 1
  · rfl
  · change -2 * energyVariance lam (ψ τ) =
      ∑ i, lam i * (2 * (expectedEnergy lam (ψ τ) - lam i) * weight (ψ τ) i)
    calc
      _ = 2 * expectedEnergy lam (ψ τ) * (∑ i, lam i * weight (ψ τ) i) -
          2 * (∑ i, lam i ^ 2 * weight (ψ τ) i) := by
        rw [← expectedEnergy, ← secondMoment, energyVariance]
        ring
      _ = _ := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring

end Qatlib.Papers.ImagDBrak24.MainResults
