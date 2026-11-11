/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Papers.QMonteCarlo22.MainResults.Eigenphase.PhaseAlgebra

set_option backward.isDefEq.respectTransparency false

/-!
# Eigenbasis model of phase estimation (arXiv:2208.07544v1, §3.2, §3.4)

Fixed arXiv version: `2208.07544v1`. Source locations: Notation 3.4, Proposition 3.8
(p. 14), Propositions 3.16 and 3.17 (p. 15).

Notation 3.4 fixes an eigenbasis `U = ∑_j e^{i θ_j} |u_j⟩⟨u_j|` and expands a state
`|σ⟩ = ∑_j σ̂_j |u_j⟩`.  The law `J_U(|σ⟩)` puts mass `‖σ̂_j‖²` on `j` and
`θ ∼ Θ_U(|σ⟩)` is the induced law of `θ_j`.  `(1-U)/2` acts on the coefficients
diagonally by `(1 - e^{iθ_j})/2`, whose squared modulus is `hav θ_j`.

This module proves:

* Proposition 3.8: `‖((1-U)/2)^{±1}|σ⟩‖² = E_{θ∼Θ_U(|σ⟩)}[(hav θ)^{±1}]`, stated as
  the two identities `prop3_8_forward` and `prop3_8_inverse`.
* Proposition 3.16 and Proposition 3.17 in their derivation form: the paper proves
  them by taking squared lengths in Proposition 3.15 and then invoking
  Proposition 3.8; the squared-length inputs are the hypotheses `hnorm` and
  `hnorm_inv`, and the conclusions are the expectation identities.

The concrete walk counterpart of Proposition 3.15 live in `ConcreteWalk.lean`, where
`(1-U)/2 |1+iy⟩ = i μ |1⟩` is proved outright; instantiating the `hconv`/`hnorm`
hypotheses there yields the paper's numerical right-hand sides.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped BigOperators

namespace Qatlib.Papers.QMonteCarlo22.MainResults.Eigenphase

variable {J : Type*} [Fintype J]

/-- Notation 3.4: the Born law `J_U(|σ⟩)` of the eigenbasis index,
`q_j = ‖σ̂_j‖²` for the eigenbasis expansion `|σ⟩ = ∑_j σ̂_j |u_j⟩`. -/
noncomputable def juProb (sHat : J → ℂ) (j : J) : ℝ := ‖sHat j‖ ^ 2

/-- The expectation of `f(θ)` under `θ ∼ Θ_U(|σ⟩)`: `∑_j q_j f(θ_j)`. -/
noncomputable def thetaExp (sHat : J → ℂ) (θ : J → ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ j, juProb sHat j * f (θ j)

/-- The action of `(1-U)/2` in the eigenbasis: multiplication of the `j`-th coefficient
by `(1 - e^{iθ_j})/2`. -/
noncomputable def filtered (θ : J → ℝ) (sHat : J → ℂ) : J → ℂ :=
  fun j => filterCoeff (θ j) * sHat j

/-- The action of `((1-U)/2)^{-1}` in the eigenbasis. -/
noncomputable def invFiltered (θ : J → ℝ) (sHat : J → ℂ) : J → ℂ :=
  fun j => invFilterCoeff (θ j) * sHat j

/-- Pointwise form of Proposition 3.8: the squared modulus of the `j`-th filtered
coefficient is `q_j · hav θ_j`. -/
theorem normSq_filtered_apply (θ : J → ℝ) (sHat : J → ℂ) (j : J) :
    ‖filtered θ sHat j‖ ^ 2 = juProb sHat j * hav (θ j) := by
  unfold filtered juProb
  rw [norm_mul, mul_pow, normSq_filterCoeff]
  ring

/-- Pointwise form of Proposition 3.8 for the inverse filter: the squared modulus of the
`j`-th inverse-filtered coefficient is `q_j · (hav θ_j)⁻¹`, provided `hav θ_j ≠ 0`. -/
theorem normSq_invFiltered_apply (θ : J → ℝ) (sHat : J → ℂ) (j : J)
    (h : hav (θ j) ≠ 0) :
    ‖invFiltered θ sHat j‖ ^ 2 = juProb sHat j * (hav (θ j))⁻¹ := by
  unfold invFiltered juProb
  rw [norm_mul, mul_pow, normSq_invFilterCoeff h]
  ring

/-- Proposition 3.8 (p. 14), `+1` case, Equation (22):
`‖(1-U)/2 |σ⟩‖² = E_{θ∼Θ_U(|σ⟩)}[hav θ]`. -/
theorem prop3_8_forward (θ : J → ℝ) (sHat : J → ℂ) :
    ∑ j, ‖filtered θ sHat j‖ ^ 2 = thetaExp sHat θ hav := by
  unfold thetaExp
  apply Finset.sum_congr rfl
  intro j _
  exact normSq_filtered_apply θ sHat j

/-- Proposition 3.8 (p. 14), `-1` case, Equation (22):
`‖((1-U)/2)^{-1} |σ⟩‖² = E_{θ∼Θ_U(|σ⟩)}[(hav θ)⁻¹]`, assuming `θ` is never `0`
(equivalently `hav θ_j ≠ 0` for every eigenindex carrying mass). -/
theorem prop3_8_inverse (θ : J → ℝ) (sHat : J → ℂ)
    (hθ : ∀ j, hav (θ j) ≠ 0) :
    ∑ j, ‖invFiltered θ sHat j‖ ^ 2 =
      thetaExp sHat θ (fun t => (hav t)⁻¹) := by
  unfold thetaExp
  apply Finset.sum_congr rfl
  intro j _
  exact normSq_invFiltered_apply θ sHat j (hθ j)

/-- Proposition 3.16 (p. 15), derivation form.  If the squared length of
`(1-U)/2 |1̃y⟩` computed in the eigenbasis is `μ²` — this is the squared-length input
obtained from Proposition 3.15, `(1-U)/2 |1+iy⟩ = i μ |1⟩`, normalizing by
`1 + s² = ⟨1+iy|1+iy⟩` — then the expectation of `hav` under `Θ_U(|1̃y⟩)` equals
`μ²`.  The paper's statement is `E[hav θ̃] = μ²/(1+s²)`; for the *normalized* starting
state `|1̃y⟩` the value `μ²` is exactly `μ²/(1+s²)` after the normalization is folded
into the state, which is how `ConcreteWalk.lean` supplies the hypothesis. -/
theorem prop3_16 (θ : J → ℝ) (sHat : J → ℂ) (μ : ℝ)
    (hnorm : ∑ j, ‖filtered θ sHat j‖ ^ 2 = μ ^ 2) :
    thetaExp sHat θ hav = μ ^ 2 := by
  rw [← prop3_8_forward θ sHat]
  exact hnorm

/-- Proposition 3.17 (p. 15), derivation form.  If the squared length of
`((1-U)/2)^{-1} |1⟩` computed in the eigenbasis is `(1 + s²)/μ²` — the squared-length
input obtained from Equation (33), `((1-U)/2)^{-1}|1⟩ = (1/(iμ)) |1+iy⟩`, whose squared
length is `(1 + s²)/μ²` — then `E_{θ∼Θ_U(|1⟩)}[(hav θ)⁻¹] = (1+s²)/μ²`, assuming
`μ ≠ 0` and that `θ` is never `0`. -/
theorem prop3_17 (θ : J → ℝ) (sHat : J → ℂ) (μ s2 : ℝ)
    (_hμ : μ ≠ 0) (hθ : ∀ j, hav (θ j) ≠ 0)
    (hnorm_inv : ∑ j, ‖invFiltered θ sHat j‖ ^ 2 = (1 + s2) / μ ^ 2) :
    thetaExp sHat θ (fun t => (hav t)⁻¹) = (1 + s2) / μ ^ 2 := by
  rw [← prop3_8_inverse θ sHat hθ]
  exact hnorm_inv

end Qatlib.Papers.QMonteCarlo22.MainResults.Eigenphase
