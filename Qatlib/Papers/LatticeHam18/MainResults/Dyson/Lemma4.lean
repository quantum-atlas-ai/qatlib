/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Qatlib.Papers.LatticeHam18.MainResults.Model.LatticeModel
import Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel

set_option backward.isDefEq.respectTransparency false

/-!
# Interaction-Picture Dyson Equation and Perturbation Stability

This module formalizes Lemma 4 of Haah, Hastings, Kothari, and Low: for continuous
Hermitian Hamiltonians `A_t` and `B_t`, the interaction propagator
`W_t = (U_t^B)ᴴ U_t^A` is the unique solution of
`i ∂_t W_t = ((U_t^B)ᴴ (A_t - B_t) U_t^B) W_t` with `W_0 = 1`, and satisfies the
time-dependent operator-norm stability estimate `‖U_t^A - U_t^B‖ ≤ t δ` whenever
`‖A_s - B_s‖ ≤ δ` on `[0, t]`.

## Main statements

* `lemma4_i_dyson_equation`: initial value, interaction-picture ODE, and ODE
  uniqueness for `(U_t^B)ᴴ U_t^A`.
* `lemma4_ii_norm_bound`: time-dependent propagator perturbation bound
  `‖U_t^A - U_t^B‖ ≤ t * δ`.
* `lemma4_ii_constant_generator_bridge`: specialization to constant Hermitian
  generators.

## References

* [Haah et al., 2018][HaahHastingsKothariLow2018], Section 2, Lemma 4, p. 8.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.LatticeHam18.MainResults.Dyson

variable {I : Type} [Fintype I] [DecidableEq I]

open Qatlib.Papers.LatticeHam18.MainResults.Model
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

/-- **Lemma 4(i)**: for continuous Hermitian `A_t` and `B_t`, `U_0^A = 1` and
`W_t = (U_t^B)ᴴ U_t^A` is the unique solution of
`∂_t W_t = -i ((U_t^B)ᴴ (A_t - B_t) U_t^B) W_t` with `W_0 = 1`. -/
theorem lemma4_i_dyson_equation
    (A B : ℝ → Matrix I I ℂ) (hA : Continuous A) (hB : Continuous B)
    (hAh : ∀ s, (A s).IsHermitian) (hBh : ∀ s, (B s).IsHermitian) :
    Qatlib.Papers.LatticeHam18.MainResults.Model.evolution A 0 = 1 ∧
    (∀ t : ℝ, HasDerivAt
      (fun u => (Qatlib.Papers.LatticeHam18.MainResults.Model.evolution B u)ᴴ *
        Qatlib.Papers.LatticeHam18.MainResults.Model.evolution A u)
      (-(Complex.I • ((Qatlib.Papers.LatticeHam18.MainResults.Model.evolution B t)ᴴ *
            (A t - B t) *
            Qatlib.Papers.LatticeHam18.MainResults.Model.evolution B t) *
          ((Qatlib.Papers.LatticeHam18.MainResults.Model.evolution B t)ᴴ *
            Qatlib.Papers.LatticeHam18.MainResults.Model.evolution A t))) t) ∧
    ∀ Z : ℝ → Matrix I I ℂ, Z 0 = 1 →
      (∀ t : ℝ, HasDerivAt Z
        (-(Complex.I • ((Qatlib.Papers.LatticeHam18.MainResults.Model.evolution B t)ᴴ *
              (A t - B t) *
              Qatlib.Papers.LatticeHam18.MainResults.Model.evolution B t) *
            Z t)) t) →
      Z = fun t => (Qatlib.Papers.LatticeHam18.MainResults.Model.evolution B t)ᴴ *
        Qatlib.Papers.LatticeHam18.MainResults.Model.evolution A t := by
  refine And.left ⟨?_, hAh⟩
  have hzero (H : ℝ → Matrix I I ℂ) : evolution H 0 = 1 :=
    orderedEvolution_self _ _
  have hder (H : ℝ → Matrix I I ℂ) (hH : Continuous H) (t : ℝ) :
      HasDerivAt (evolution H) (-(Complex.I • H t * evolution H t)) t :=
    orderedEvolution_hasDerivAt (fun s => Complex.I • H s) (hH.const_smul Complex.I) 0 t
  have hunit (t : ℝ) : evolution B t * (evolution B t)ᴴ = 1 :=
    (ordered_evolution_hermitian_unitary I B hB hBh 0 t).2
  have hstar (t : ℝ) : HasDerivAt (fun u => (evolution B u)ᴴ)
      ((evolution B t)ᴴ * (Complex.I • B t)) t := by
    simpa [star_neg, star_mul, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_smul, (hBh t).eq] using (hder B hB t).star
  have hW (t : ℝ) : HasDerivAt
      (fun u => (evolution B u)ᴴ * evolution A u)
      (-(Complex.I • ((evolution B t)ᴴ * (A t - B t) * evolution B t) *
        ((evolution B t)ᴴ * evolution A t))) t := by
    convert (hstar t).mul (hder A hA t) using 1
    simp only [smul_mul_assoc, mul_smul_comm, mul_assoc,
      ← mul_assoc (evolution B t) (evolution B t)ᴴ, hunit t, one_mul,
      mul_sub, sub_mul, smul_sub, mul_neg]
    abel
  refine ⟨hzero A, hW, ?_⟩
  intro Z hZzero hZ
  have hcont : Continuous (evolution B) :=
    continuous_iff_continuousAt.mpr fun t => (hder B hB t).continuousAt
  exact ordered_matrix_ode_unique
    (fun t => Complex.I • ((evolution B t)ᴴ * (A t - B t) * evolution B t))
    (((hcont.matrix_conjTranspose.mul (hA.sub hB)).mul hcont).const_smul Complex.I)
    Z (fun t => (evolution B t)ᴴ * evolution A t) 0
    (by simpa only [hzero, Matrix.conjTranspose_one, one_mul] using hZzero) hZ hW

/-- **Lemma 4(ii)**: if `‖A_s - B_s‖ ≤ δ` for all `s ∈ [0, t]`, then
`‖U_t^A - U_t^B‖ ≤ t * δ`. -/
theorem lemma4_ii_norm_bound
    (A B : ℝ → Matrix I I ℂ) (hA : Continuous A) (hB : Continuous B)
    (hAh : ∀ s, (A s).IsHermitian) (hBh : ∀ s, (B s).IsHermitian)
    (δ t : ℝ) (ht : 0 ≤ t) (hδ : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖A s - B s‖ ≤ δ) :
    ‖Qatlib.Papers.LatticeHam18.MainResults.Model.evolution A t -
      Qatlib.Papers.LatticeHam18.MainResults.Model.evolution B t‖ ≤ t * δ := by
  have hunit (H : ℝ → Matrix I I ℂ) (hH : Continuous H)
      (hHh : ∀ s, (H s).IsHermitian) (s : ℝ) :
      evolution H s ∈ Matrix.unitaryGroup I ℂ :=
    ordered_evolution_hermitian_unitary I H hH hHh 0 s
  let W := fun s => (evolution B s)ᴴ * evolution A s
  let D := fun s =>
    -(Complex.I • ((evolution B s)ᴴ * (A s - B s) * evolution B s) * W s)
  have hder : ∀ s, HasDerivAt W (D s) s :=
    (lemma4_i_dyson_equation A B hA hB hAh hBh).2.1
  have hbound (s : ℝ) (hs : s ∈ Set.Ico 0 t) : ‖D s‖ ≤ δ := by
    have hBunit := hunit B hB hBh s
    have hAunit := hunit A hA hAh s
    have hcancel : evolution B s * (evolution B s)ᴴ = 1 := hBunit.2
    have hnorm : ‖D s‖ = ‖A s - B s‖ := by
      dsimp only [D, W]
      simp only [norm_neg, smul_mul_assoc, norm_smul, Complex.norm_I, one_mul,
        mul_assoc, ← mul_assoc (evolution B s) (evolution B s)ᴴ, hcancel]
      change ‖star (evolution B s) * ((A s - B s) * evolution A s)‖ = _
      rw [CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hBunit),
        CStarRing.norm_mul_mem_unitary _ hAunit]
    rw [hnorm]
    exact hδ s ⟨hs.1, hs.2.le⟩
  have hmean := norm_image_sub_le_of_norm_deriv_right_le_segment
    (continuous_iff_continuousAt.mpr (fun s => (hder s).continuousAt)).continuousOn
    (fun s _ => (hder s).hasDerivWithinAt) hbound t ⟨ht, le_rfl⟩
  have hzero : W 0 = 1 := by simp [W, evolution]
  have hdiff : evolution A t - evolution B t = evolution B t * (W t - 1) := by
    have hcancel : evolution B t * (evolution B t)ᴴ = 1 := (hunit B hB hBh t).2
    dsimp only [W]
    rw [mul_sub, ← mul_assoc, hcancel, one_mul, mul_one]
  rw [hdiff, CStarRing.norm_mem_unitary_mul _ (hunit B hB hBh t)]
  simpa only [hzero, sub_zero, mul_comm δ t] using hmean

/-- **Lemma 4(ii) (constant generators)**: for Hermitian `H₁, H₂` with
`‖H₁ - H₂‖ ≤ δ` and `t ≥ 0`, `‖U_t^{H₁} - U_t^{H₂}‖ ≤ t * δ`. -/
theorem lemma4_ii_constant_generator_bridge
    (H₁ H₂ : Matrix I I ℂ) (h₁ : H₁.IsHermitian) (h₂ : H₂.IsHermitian)
    (δ : ℝ) (hδ : ‖H₁ - H₂‖ ≤ δ) {t : ℝ} (ht : 0 ≤ t) :
    ‖Qatlib.Papers.LatticeHam18.MainResults.Model.evolution (fun _ => H₁) t -
      Qatlib.Papers.LatticeHam18.MainResults.Model.evolution (fun _ => H₂) t‖ ≤
      t * δ := by
  have hE (H : Matrix I I ℂ) :
      Qatlib.Papers.LatticeHam18.MainResults.Model.evolution (fun _ => H) t =
        Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution
          (Complex.I • H) t := by
    rw [Qatlib.Papers.LatticeHam18.MainResults.Model.evolution,
      Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution_eq_ordered]
  have hpsd (H : Matrix I I ℂ) (hH : H.IsHermitian) :
      ((Complex.I • H) + (Complex.I • H)ᴴ).PosSemidef := by
    have h0 : (Complex.I • H) + (Complex.I • H)ᴴ = 0 := by
      rw [Matrix.conjTranspose_smul, hH.eq, ← add_smul]
      simp
    rw [h0]
    exact Matrix.PosSemidef.zero
  have hnorm : ‖Complex.I • H₁ - Complex.I • H₂‖ = ‖H₁ - H₂‖ := by
    rw [← smul_sub, norm_smul, Complex.norm_I, one_mul]
  rw [hE H₁, hE H₂]
  calc
    ‖Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution
          (Complex.I • H₁) t -
        Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution
          (Complex.I • H₂) t‖
        ≤ t * ‖Complex.I • H₁ - Complex.I • H₂‖ :=
          Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.norm_evolution_sub_le
            _ _ (hpsd H₁ h₁) (hpsd H₂ h₂) ht
    _ = t * ‖H₁ - H₂‖ := by rw [hnorm]
    _ ≤ t * δ := mul_le_mul_of_nonneg_left hδ ht

end Qatlib.Papers.LatticeHam18.MainResults.Dyson
