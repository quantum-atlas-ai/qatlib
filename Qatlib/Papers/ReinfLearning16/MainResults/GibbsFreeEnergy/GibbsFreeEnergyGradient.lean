/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixExpTrace.ExpPerturbation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Matrix.Trace

set_option backward.isDefEq.respectTransparency false

/-!
# Clamped Quantum Boltzmann Machine: Gibbs Objects and Free-Energy Gradient

This module formalizes the equilibrium Gibbs objects and the free-energy gradient identity of
[Crawford et al., 2016][CrawfordEtAl2016] (§§2.7–2.8, Eq. (13), p. 12).

For a clamped quantum Boltzmann machine with Hermitian Hamiltonian `H` on a finite Hilbert
space `I` and inverse temperature `β ≠ 0`:

* `partitionFunction`: `Z = Re tr(e^{-βH}) > 0` (`partitionFunction_pos`),
* `gibbsState`: `ρ = Z⁻¹ e^{-βH}` with unit trace (`gibbsState_trace_eq_one`),
* `gibbsExpectation`: `⟨X⟩ = Z⁻¹ Re tr(e^{-βH} X)`, linear over real scalars
  (`gibbsExpectation_add`, `gibbsExpectation_smul`),
* `freeEnergy`: `F = -(1/β) ln Z`.

The central calculus result `freeEnergy_hasDerivAt_gibbsExpectation` proves the noncommutative
free-energy gradient identity `d/dw F(β, H + w • A)|_{w=0} = ⟨A⟩` by combining the product-path
derivative (`hasDerivAt_product_path`), trace cyclicity, and noncommuting exponential trace
duality (`trace_duality_exp_consumer`).

## Main statements

* `partitionFunction_pos`
* `gibbsState_trace_eq_one`
* `hasDerivAt_re_trace_exp_add_smul`
* `freeEnergy_hasDerivAt_gibbsExpectation`

## References

* [Crawford et al., 2016][CrawfordEtAl2016]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.ReinfLearning16.MainResults.GibbsFreeEnergy

variable {I : Type} [Fintype I] [DecidableEq I]

/-! ## Objects of Eq (13) -/

/-- A negated real number, read in `ℂ`, is self-adjoint.  Used to keep a real scalar
(e.g. `-β`, `-v`, `-1`) self-adjoint when rescaling a Hermitian Hamiltonian. -/
theorem isSelfAdjoint_neg_real (r : ℝ) : IsSelfAdjoint (-(r : ℂ)) := by
  rw [IsSelfAdjoint]
  simp [RCLike.star_def]

/-- The complex partition function `tr(e^{-β H_v})` of Eq (13) (p.12).  For Hermitian
`H_v` it is a positive real; keeping it complex avoids a reality side-condition in
the normalisation statements. -/
def partitionFunctionC (β : ℝ) (H : Matrix I I ℂ) : ℂ :=
  Matrix.trace (NormedSpace.exp (-(β : ℂ) • H))

/-- The partition function `Z_v = tr(e^{-β H_v})` of Eq (13) (p.12), read in the
reals (`tr(e^{-βH})` is positive real for Hermitian `H`). -/
def partitionFunction (β : ℝ) (H : Matrix I I ℂ) : ℝ :=
  (partitionFunctionC β H).re

/-- The Gibbs density matrix `ρ_v = Z_v^{-1} e^{-β H_v}` of Eq (13) (p.12). -/
def gibbsState (β : ℝ) (H : Matrix I I ℂ) : Matrix I I ℂ :=
  (partitionFunctionC β H)⁻¹ • NormedSpace.exp (-(β : ℂ) • H)

/-- The Gibbs expectation `⟨X⟩ = Z_v^{-1} tr(e^{-β H_v} X)` of Eq (13) (p.12),
read in the reals.  For Hermitian `X` (every Pauli observable used in the paper)
this is a real number. -/
def gibbsExpectation (β : ℝ) (H X : Matrix I I ℂ) : ℝ :=
  (partitionFunction β H)⁻¹ *
    (Matrix.trace (NormedSpace.exp (-(β : ℂ) • H) * X)).re

/-- The equilibrium free energy `F(v) = -(1/β) ln Z_v` of Eq (13) (p.12). -/
def freeEnergy (β : ℝ) (H : Matrix I I ℂ) : ℝ :=
  -(1 / β) * Real.log (partitionFunction β H)

/-! ## Elementary structure of the Gibbs objects -/

/-- **Linearity of the Gibbs expectation in the observable** (used throughout the
derivation of Eqs (14)–(15)): `⟨A + B⟩ = ⟨A⟩ + ⟨B⟩`.  Pure linearity of the trace. -/
theorem gibbsExpectation_add (β : ℝ) (H A B : Matrix I I ℂ) :
    gibbsExpectation β H (A + B) = gibbsExpectation β H A + gibbsExpectation β H B := by
  unfold gibbsExpectation
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re, mul_add]

/-- **Homogeneity of the Gibbs expectation** in a real scalar: `⟨c • A⟩ = c ⟨A⟩`.
This is the step turning the Pauli coefficient `-v` in `∂H/∂w_vh = -v σ^z_h`
into the factor `v` of Eq (14). -/
theorem gibbsExpectation_smul (β : ℝ) (H : Matrix I I ℂ) (c : ℝ) (A : Matrix I I ℂ) :
    gibbsExpectation β H ((c : ℂ) • A) = c * gibbsExpectation β H A := by
  unfold gibbsExpectation
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  have hre :
      (↑c * Matrix.trace (NormedSpace.exp (-(β : ℂ) • H) * A)).re
        = c * (Matrix.trace (NormedSpace.exp (-(β : ℂ) • H) * A)).re := by
    rw [Complex.mul_re]
    simp
  rw [hre]
  ring

/-- Negation form of homogeneity: `⟨-A⟩ = -⟨A⟩`. -/
theorem gibbsExpectation_neg (β : ℝ) (H A : Matrix I I ℂ) :
    gibbsExpectation β H (-A) = -gibbsExpectation β H A := by
  simpa using gibbsExpectation_smul β H (-1) A

/-- **Normalisation of the Gibbs state** (the `Z_v` in Eq (13) is exactly the trace
of the unnormalised Gibbs matrix): `tr ρ_v = 1`. -/
theorem gibbsState_trace_eq_one (β : ℝ) (H : Matrix I I ℂ)
    (hZ : partitionFunctionC β H ≠ 0) :
    Matrix.trace (gibbsState β H) = 1 := by
  unfold gibbsState at *
  unfold partitionFunctionC at hZ ⊢
  rw [Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ hZ]

/-- The partition function of a Hermitian Hamiltonian is strictly positive on a
nonempty Hilbert space: `Z_v > 0` (Eq (13), p.12).  Obtained by reusing the Frozen
foundation lemma `MatrixExpTrace.ExpPerturbation.exp_trace_eq_sum`
(`tr(e^{-βH}) = Σ_i e^{λ_i}`). -/
theorem partitionFunction_pos [Nonempty I] (β : ℝ) (H : Matrix I I ℂ)
    (hH : H.IsHermitian) : 0 < partitionFunction β H := by
  unfold partitionFunction partitionFunctionC
  have hH' : (-(β : ℂ) • H).IsHermitian :=
    hH.smul (isSelfAdjoint_neg_real β)
  rw [Qatlib.Concepts.MatrixExpTrace.ExpPerturbation.exp_trace_eq_sum
    (-(β : ℂ) • H) hH']
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

/-! ## The free-energy gradient (Eq (13) differentiated): `∂F/∂w = ⟨∂H/∂w⟩` -/

section TraceExpDeriv
open scoped Matrix.Norms.L2Operator Topology

/-- Directional derivative of `w ↦ Re tr(exp(M + w • B))` at `w = 0` for Hermitian matrices
`M` and `B`. -/
theorem hasDerivAt_re_trace_exp_add_smul [Nonempty I]
    (M B : Matrix I I ℂ) (hM : M.IsHermitian) (hB : B.IsHermitian) :
    HasDerivAt (fun w : ℝ => (Matrix.trace (NormedSpace.exp (M + w • B))).re)
      (Matrix.trace (NormedSpace.exp M * B)).re 0 := by
  let T : Matrix I I ℂ →L[ℝ] ℝ :=
    Complex.reCLM.comp (Matrix.traceLinearMap I ℝ ℂ).toContinuousLinearMap
  let HM : HermitianMat I ℂ := ⟨M, hM⟩
  let HB : HermitianMat I ℂ := ⟨B, hB⟩
  let g : ℝ → ℝ := fun s =>
    ‖NormedSpace.exp ((1 - s) • M) * B‖ * (Matrix.trace (NormedSpace.exp (s • M))).re
  have hg_cont : Continuous g := by
    have hexpM : Continuous (fun s : ℝ => NormedSpace.exp (s • M)) :=
      continuous_iff_continuousAt.mpr fun s =>
        (hasDerivAt_exp_smul_const' (𝕂 := ℝ) M s).continuousAt
    have h1 : Continuous (fun s : ℝ => ‖NormedSpace.exp ((1 - s) • M) * B‖) :=
      (((hexpM.comp (continuous_const.sub continuous_id)).mul continuous_const)).norm
    have h2 : Continuous (fun s : ℝ => T (NormedSpace.exp (s • M))) :=
      T.continuous.comp hexpM
    exact h1.mul h2
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hg_cont.continuousOn
  let C₀ : ℝ := max C₁ 0
  have hC₀_nn : 0 ≤ C₀ := le_max_right C₁ 0
  have hdiff_bound : ∀ w : ℝ,
      ‖T (NormedSpace.exp (M + w • B)) - T (NormedSpace.exp M) -
          w * T (NormedSpace.exp M * B)‖ ≤
        |w| * C₀ * (Real.exp (|w| * ‖B‖) - 1) := by
    intro w
    let Kw : Matrix I I ℂ := M + w • B
    let HKw : HermitianMat I ℂ := HM + w • HB
    have hKw_eq : HKw.mat = Kw := rfl
    let φ : ℝ → ℝ := fun s =>
      T (NormedSpace.exp ((1 - s) • M) * NormedSpace.exp (s • Kw)) -
        s * (w * T (NormedSpace.exp M * B))
    let φ' : ℝ → ℝ := fun s =>
      T (NormedSpace.exp ((1 - s) • M) * (Kw - M) * NormedSpace.exp (s • Kw)) -
        w * T (NormedSpace.exp M * B)
    have hφ_deriv : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt φ (φ' s) (Set.Icc 0 1) s := by
      intro s _
      have hP := T.hasFDerivAt.comp_hasDerivAt s
        (Qatlib.Concepts.MatrixExpTrace.ExpPerturbation.hasDerivAt_product_path M Kw s)
      have hL : HasDerivAt (fun u : ℝ => u * (w * T (NormedSpace.exp M * B)))
          (w * T (NormedSpace.exp M * B)) s := by
        simpa using (hasDerivAt_id s).mul_const (w * T (NormedSpace.exp M * B))
      exact (hP.sub hL).hasDerivWithinAt
    have hφ_bound : ∀ s ∈ Set.Ico (0 : ℝ) 1,
        ‖φ' s‖ ≤ |w| * C₀ * (Real.exp (|w| * ‖B‖) - 1) := by
      intro s hs
      have hs0 : 0 ≤ s := hs.1
      have hs1 : s ≤ 1 := hs.2.le
      have hcyc : T (NormedSpace.exp ((1 - s) • M) * B * NormedSpace.exp (s • M)) =
          T (NormedSpace.exp M * B) := by
        change (Matrix.trace ((NormedSpace.exp ((1 - s) • M) * B) * NormedSpace.exp (s • M))).re =
          (Matrix.trace (NormedSpace.exp M * B)).re
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
        have hexp_prod : NormedSpace.exp (s • M) * NormedSpace.exp ((1 - s) • M) =
            NormedSpace.exp M := by
          let q : ℝ → Matrix I I ℂ :=
            fun u => NormedSpace.exp ((1 - u) • M) * NormedSpace.exp (u • M)
          have hq : ∀ u : ℝ, HasDerivAt q 0 u := fun u => by
            simpa using
              Qatlib.Concepts.MatrixExpTrace.ExpPerturbation.hasDerivAt_product_path M M u
          have hconst := is_const_of_deriv_eq_zero (fun u => (hq u).differentiableAt)
            (fun u => (hq u).deriv) (1 - s) 1
          simpa [q] using hconst
        rw [hexp_prod]
      have hKw_sub : Kw - M = w • B := add_sub_cancel_left M (w • B)
      have hφ'_eq : φ' s =
          w * T ((NormedSpace.exp ((1 - s) • M) * B) *
            (NormedSpace.exp (s • Kw) - NormedSpace.exp (s • M))) := by
        dsimp [φ']
        rw [hKw_sub, ← hcyc]
        have hsmul : NormedSpace.exp ((1 - s) • M) * (w • B) * NormedSpace.exp (s • Kw) =
            w • (NormedSpace.exp ((1 - s) • M) * B * NormedSpace.exp (s • Kw)) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
        rw [hsmul, map_smul, smul_eq_mul, ← mul_sub, ← map_sub, Matrix.mul_sub]
      rw [hφ'_eq, Real.norm_eq_abs, abs_mul]
      have hsM : (s • M).IsHermitian := (s • HM).H
      have hsKw : (s • Kw).IsHermitian := by
        have h1 : (s • HKw).mat = s • Kw := rfl
        exact h1 ▸ (s • HKw).H
      have htr_neg :
          ‖Matrix.trace ((NormedSpace.exp ((1 - s) • M) * B) *
              (NormedSpace.exp (s • Kw) - NormedSpace.exp (s • M)))‖ =
            ‖Matrix.trace ((NormedSpace.exp ((1 - s) • M) * B) *
              (NormedSpace.exp (s • M) - NormedSpace.exp (s • Kw)))‖ := by
        have hneg :
            Matrix.trace ((NormedSpace.exp ((1 - s) • M) * B) *
                (NormedSpace.exp (s • Kw) - NormedSpace.exp (s • M))) =
              -Matrix.trace ((NormedSpace.exp ((1 - s) • M) * B) *
                (NormedSpace.exp (s • M) - NormedSpace.exp (s • Kw))) := by
          rw [← Matrix.trace_neg, ← Matrix.mul_neg, neg_sub]
        rw [hneg, norm_neg]
      have hdual :=
        Qatlib.Concepts.MatrixExpTrace.ExpPerturbation.trace_duality_exp_consumer.2
          I (s • M) (s • Kw) (NormedSpace.exp ((1 - s) • M) * B) hsM hsKw
      have habs_le :
          |T ((NormedSpace.exp ((1 - s) • M) * B) *
              (NormedSpace.exp (s • Kw) - NormedSpace.exp (s • M)))| ≤
            ‖NormedSpace.exp ((1 - s) • M) * B‖ *
              (Real.exp ‖s • M - s • Kw‖ - 1) *
                (Matrix.trace (NormedSpace.exp (s • M))).re := by
        calc |T ((NormedSpace.exp ((1 - s) • M) * B) *
                (NormedSpace.exp (s • Kw) - NormedSpace.exp (s • M)))|
            ≤ ‖Matrix.trace ((NormedSpace.exp ((1 - s) • M) * B) *
                (NormedSpace.exp (s • Kw) - NormedSpace.exp (s • M)))‖ :=
              Complex.abs_re_le_norm _
          _ = ‖Matrix.trace ((NormedSpace.exp ((1 - s) • M) * B) *
                (NormedSpace.exp (s • M) - NormedSpace.exp (s • Kw)))‖ := htr_neg
          _ ≤ ‖NormedSpace.exp ((1 - s) • M) * B‖ *
                (Real.exp ‖s • M - s • Kw‖ - 1) *
                  (Matrix.trace (NormedSpace.exp (s • M))).re := hdual
      have hnorm_diff : ‖s • M - s • Kw‖ ≤ |w| * ‖B‖ := by
        have hsub : s • M - s • Kw = -(s • (w • B)) := by
          dsimp [Kw]
          rw [smul_add, sub_add_eq_sub_sub, sub_self, zero_sub]
        rw [hsub, norm_neg, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hs0]
        exact mul_le_of_le_one_left (mul_nonneg (abs_nonneg w) (norm_nonneg B)) hs1
      have hexp_diff : Real.exp ‖s • M - s • Kw‖ - 1 ≤ Real.exp (|w| * ‖B‖) - 1 :=
        sub_le_sub_right (Real.exp_le_exp.mpr hnorm_diff) 1
      have hexp_nn : 0 ≤ Real.exp ‖s • M - s • Kw‖ - 1 := by
        linarith [Real.one_le_exp (norm_nonneg (s • M - s • Kw))]
      have hexp_nn2 : 0 ≤ Real.exp (|w| * ‖B‖) - 1 := le_trans hexp_nn hexp_diff
      have hZ_pos : 0 ≤ (Matrix.trace (NormedSpace.exp (s • M))).re :=
        (Qatlib.Concepts.MatrixExpTrace.ExpPerturbation.exp_trace_pos (s • HM)).le
      have hg_nn : 0 ≤ g s := mul_nonneg (norm_nonneg _) hZ_pos
      have hg_le : g s ≤ C₀ := by
        have hc := hC₁ s ⟨hs0, hs1⟩
        rw [Real.norm_eq_abs, abs_of_nonneg hg_nn] at hc
        exact hc.trans (le_max_left C₁ 0)
      have hprod_le :
          ‖NormedSpace.exp ((1 - s) • M) * B‖ *
              (Real.exp ‖s • M - s • Kw‖ - 1) *
                (Matrix.trace (NormedSpace.exp (s • M))).re ≤
            C₀ * (Real.exp (|w| * ‖B‖) - 1) := by
        calc ‖NormedSpace.exp ((1 - s) • M) * B‖ *
              (Real.exp ‖s • M - s • Kw‖ - 1) *
                (Matrix.trace (NormedSpace.exp (s • M))).re
            = g s * (Real.exp ‖s • M - s • Kw‖ - 1) := by dsimp [g]; ring
          _ ≤ g s * (Real.exp (|w| * ‖B‖) - 1) := mul_le_mul_of_nonneg_left hexp_diff hg_nn
          _ ≤ C₀ * (Real.exp (|w| * ‖B‖) - 1) := mul_le_mul_of_nonneg_right hg_le hexp_nn2
      calc |w| * |T ((NormedSpace.exp ((1 - s) • M) * B) *
              (NormedSpace.exp (s • Kw) - NormedSpace.exp (s • M)))|
          ≤ |w| * (C₀ * (Real.exp (|w| * ‖B‖) - 1)) :=
            mul_le_mul_of_nonneg_left (habs_le.trans hprod_le) (abs_nonneg w)
        _ = |w| * C₀ * (Real.exp (|w| * ‖B‖) - 1) := by ring
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01' hφ_deriv hφ_bound
    have hφ10 : φ 1 - φ 0 =
        T (NormedSpace.exp (M + w • B)) - T (NormedSpace.exp M) -
          w * T (NormedSpace.exp M * B) := by
      dsimp [φ, Kw]
      simp only [sub_self, zero_smul, one_smul, NormedSpace.exp_zero, one_mul, mul_one,
        zero_mul, sub_zero]
      ring
    rwa [hφ10] at hmvt
  rw [hasDerivAt_iff_tendsto]
  have hupper_tendsto :
      Filter.Tendsto (fun w : ℝ => C₀ * (Real.exp (|w| * ‖B‖) - 1)) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun w : ℝ => C₀ * (Real.exp (|w| * ‖B‖) - 1)) :=
      continuous_const.mul
        ((Real.continuous_exp.comp (continuous_abs.mul continuous_const)).sub continuous_const)
    simpa only [abs_zero, zero_mul, Real.exp_zero, sub_self, mul_zero] using hcont.tendsto 0
  refine squeeze_zero (fun w => by positivity) (fun w => ?_) hupper_tendsto
  by_cases hw : w = 0
  · subst hw
    simp
  · have hw_pos : 0 < |w| := abs_pos.mpr hw
    have hb := hdiff_bound w
    have hnorm_w : ‖w - 0‖ = |w| := by simp [Real.norm_eq_abs]
    have harg : (fun w' : ℝ => (Matrix.trace (NormedSpace.exp (M + w' • B))).re) w -
        (fun w' : ℝ => (Matrix.trace (NormedSpace.exp (M + w' • B))).re) 0 -
        (w - 0) • (Matrix.trace (NormedSpace.exp M * B)).re =
        T (NormedSpace.exp (M + w • B)) - T (NormedSpace.exp M) -
          w * T (NormedSpace.exp M * B) := by
      simp [T, smul_eq_mul]
    rw [hnorm_w, harg]
    calc |w|⁻¹ * ‖T (NormedSpace.exp (M + w • B)) - T (NormedSpace.exp M) -
            w * T (NormedSpace.exp M * B)‖
        ≤ |w|⁻¹ * (|w| * C₀ * (Real.exp (|w| * ‖B‖) - 1)) :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hw_pos.le)
      _ = C₀ * (Real.exp (|w| * ‖B‖) - 1) := by
          field_simp [hw_pos.ne']

end TraceExpDeriv

/-- **Free-energy gradient identity** ([Crawford et al., 2016][CrawfordEtAl2016], p. 12,
between Eq. (13) and Eq. (14)). For a Hermitian Hamiltonian `H` and a Hermitian weight
direction `A`, the directional derivative of the equilibrium free energy `F(β, H + w • A)`
at `w = 0` equals the Gibbs expectation `⟨A⟩`:

`d/dw [ -(1/β) ln tr(e^{-β(H + wA)}) ]|_{w=0} = Z⁻¹ tr(e^{-βH} A) = ⟨A⟩`. -/
theorem freeEnergy_hasDerivAt_gibbsExpectation [Nonempty I]
    (β : ℝ) (hβ : β ≠ 0) (H A : Matrix I I ℂ) (hH : H.IsHermitian) (hA : A.IsHermitian) :
    HasDerivAt (fun w : ℝ => freeEnergy β (H + w • A)) (gibbsExpectation β H A) 0 := by
  let M : Matrix I I ℂ := -(β : ℂ) • H
  let Kdir : Matrix I I ℂ := -(β : ℂ) • A
  have hM : M.IsHermitian := hH.smul (isSelfAdjoint_neg_real β)
  have hKdir : Kdir.IsHermitian := hA.smul (isSelfAdjoint_neg_real β)
  have hZ_eq : ∀ w : ℝ, partitionFunction β (H + w • A) =
      (Matrix.trace (NormedSpace.exp (M + w • Kdir))).re := by
    intro w
    unfold partitionFunction partitionFunctionC
    congr 3
    dsimp [M, Kdir]
    rw [smul_add, smul_comm]
  have hZ_deriv0 : HasDerivAt (fun w : ℝ => partitionFunction β (H + w • A))
      (Matrix.trace (NormedSpace.exp M * Kdir)).re 0 := by
    simp_rw [hZ_eq]
    exact hasDerivAt_re_trace_exp_add_smul M Kdir hM hKdir
  have hZ0_pos : 0 < partitionFunction β H := partitionFunction_pos β H hH
  have hZ0_eq : partitionFunction β (H + (0 : ℝ) • A) = partitionFunction β H := by simp
  have hZ0_ne : partitionFunction β (H + (0 : ℝ) • A) ≠ 0 := by
    rw [hZ0_eq]
    exact hZ0_pos.ne'
  have hlog : HasDerivAt (fun w : ℝ => Real.log (partitionFunction β (H + w • A)))
      ((Matrix.trace (NormedSpace.exp M * Kdir)).re /
        partitionFunction β (H + (0 : ℝ) • A)) 0 :=
    hZ_deriv0.log hZ0_ne
  unfold freeEnergy
  convert hlog.const_mul (-(1 / β)) using 1
  rw [hZ0_eq]
  have htr : (Matrix.trace (NormedSpace.exp M * Kdir)).re =
      -β * (Matrix.trace (NormedSpace.exp (-(β : ℂ) • H) * A)).re := by
    dsimp [M, Kdir]
    have hsmul : NormedSpace.exp (-(β : ℂ) • H) * (-(β : ℂ) • A) =
        ((-β : ℝ) : ℂ) • (NormedSpace.exp (-(β : ℂ) • H) * A) := by
      rw [Matrix.mul_smul]
      push_cast
      rfl
    rw [hsmul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re]
    simp
  rw [htr]
  unfold gibbsExpectation
  have hZ0_ne' : partitionFunction β H ≠ 0 := hZ0_pos.ne'
  field_simp [hβ, hZ0_ne']

end Qatlib.Papers.ReinfLearning16.MainResults.GibbsFreeEnergy
