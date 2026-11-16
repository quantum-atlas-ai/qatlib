/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ThermalDrift26.ThermalSampling.Model

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Lemma S11 — stability of the normalized Gibbs state under a Hermitian perturbation

Source: arXiv:2602.05912v2, Lemma S11, Eq. (C.21), page 17.

For Hermitian matrices `A, E` (with `A(t) = A + tE`), the normalized
exponential states satisfy
`‖ e^{A+E}/Tr[e^{A+E}] − e^A/Tr[e^A] ‖_1 ≤ 2 ‖E‖_∞`.

The paper derives this by differentiating `ρ(t) = e^{A(t)}/Z(t)` with the
Fréchet derivative of the matrix exponential (Lemma S1), bounding both the
sandwiched derivative `F(t) = ∫_0^1 ρ(t)^s E ρ(t)^{1-s} ds` and its trace by
`‖E‖_∞` via Lemma S2, and integrating the resulting `2‖E‖_∞` derivative
bound over `t ∈ [0,1]`.

The reusable Gibbs-normalization development gives the exponential estimate
`2(e^{‖H−K‖} − 1)`. Applying it along `n` equally spaced points of the
Hermitian segment from `A` to `A+E` gives
`2n(e^{‖E‖/n} − 1)`. The scalar exponential derivative at zero shows that
this converges to `2‖E‖`, proving the sharp bound without requiring a
matrix-valued differentiation theorem.
-/

set_option autoImplicit false
noncomputable section

open Matrix Filter
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.ThermalDrift26.ThermalSampling
open Qatlib.Papers.ThermalDrift26.ThermalSampling

/-- Bridge: on a positive-partition-function input, the paper's `gibbsState`
coincides with the Frozen normalized positive branch
`LwePhaseSieve.SieveLaw.normalizedPositiveBranch`
applied to `e^A`. This connects the paper notation to the reusable Frozen API. -/
theorem gibbsState_eq_normalizedPositiveBranch {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ)
    (h : 0 < (Matrix.trace (NormedSpace.exp A)).re) :
    gibbsState A =
      Qatlib.Concepts.HspRecovery.SieveLaw.normalizedPositiveBranch
        (NormedSpace.exp A) := by
  simp only [gibbsState,
    Qatlib.Concepts.HspRecovery.SieveLaw.normalizedPositiveBranch,
    ite_eq_left h]

/-- Frozen reuse (weaker than Lemma S11): the Frozen normalized Gibbs
perturbation bound is exactly the distance between the two `gibbsState`s when
both partition functions are positive, with the `2(e^{‖H−K‖}−1)` right-hand
side. Uniform subdivision and the derivative of the scalar exponential
recover the sharp bound in Lemma S11 below. -/
theorem normalized_gibbs_branch_traceNorm_bridge {I : Type} [Fintype I]
    [DecidableEq I] [Nonempty I] (H K : Matrix I I ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    Matrix.traceNorm (gibbsState H - gibbsState K) ≤
      2 * (Real.exp ‖H - K‖ - 1) := by
  have hp : 0 < (Matrix.trace (NormedSpace.exp H)).re :=
    Qatlib.Concepts.MatrixExpTrace.GibbsNorm.exp_trace_re_pos H hH
  have hq : 0 < (Matrix.trace (NormedSpace.exp K)).re :=
    Qatlib.Concepts.MatrixExpTrace.GibbsNorm.exp_trace_re_pos K hK
  rw [gibbsState_eq_normalizedPositiveBranch H hp,
    gibbsState_eq_normalizedPositiveBranch K hq]
  exact (Qatlib.Concepts.MatrixExpTrace.GibbsNorm.normalized_gibbs_branch_traceNorm_le
    H K hH (fun _ => hK)).2.2.2.2

/-- Lemma S11 (arXiv:2602.05912v2, Eq. (C.21), p. 17): for Hermitian `A, E`,
`‖ e^{A+E}/Tr[e^{A+E}] − e^A/Tr[e^A] ‖_1 ≤ 2 ‖E‖_∞`.

Subdivide the perturbation into equally spaced Hermitian increments, apply
the exponential perturbation bound to each increment, and take the limit
using the derivative of the scalar exponential at zero. -/
theorem lemmaS11_normalized_gibbs_stability {I : Type} [Fintype I] [DecidableEq I]
    (A E : Matrix I I ℂ) (hA : A.IsHermitian) (hE : E.IsHermitian) :
    Matrix.traceNorm (gibbsState (A + E) - gibbsState A) ≤ 2 * ‖E‖ := by
  classical
  cases isEmpty_or_nonempty I with
  | inl h =>
    let := h
    have hz : E = 0 := Subsingleton.elim _ _
    simp [hz, Matrix.traceNorm_zero]
  | inr h =>
    let := h
    by_cases hE0 : E = 0
    · simp [hE0, Matrix.traceNorm_zero]
    have hc : 0 < ‖E‖ := norm_pos_iff.mpr hE0
    have hfinite (n : ℕ) (hn : 0 < n) :
        Matrix.traceNorm (gibbsState (A + E) - gibbsState A) ≤
          2 * (n : ℝ) * (Real.exp (‖E‖ / n) - 1) := by
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      let D : Matrix I I ℂ := (1 / (n : ℝ)) • E
      let X (k : ℕ) : Matrix I I ℂ := A + (k : ℝ) • D
      have hD : D.IsHermitian := hE.smul (isSelfAdjoint_iff.mpr rfl)
      have hX (k : ℕ) : (X k).IsHermitian :=
        hA.add (hD.smul (isSelfAdjoint_iff.mpr rfl))
      have hstep (k : ℕ) : X (k + 1) - X k = D := by
        simp only [X, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
        abel
      have hbound (k : ℕ) :
          Matrix.traceNorm (gibbsState (X k) - gibbsState A) ≤
            (k : ℝ) * (2 * (Real.exp ‖D‖ - 1)) := by
        induction k with
        | zero => simp [X, Matrix.traceNorm_zero]
        | succ k ih =>
          have ht := normalized_gibbs_branch_traceNorm_bridge
            (X (k + 1)) (X k) (hX _) (hX _)
          rw [hstep] at ht
          have heq : gibbsState (X (k + 1)) - gibbsState A =
              (gibbsState (X (k + 1)) - gibbsState (X k)) +
                (gibbsState (X k) - gibbsState A) := by abel
          rw [heq]
          have htri := Matrix.traceNorm_add_le
            (gibbsState (X (k + 1)) - gibbsState (X k))
            (gibbsState (X k) - gibbsState A)
          push_cast
          linarith
      have hDn : ‖D‖ = ‖E‖ / n := by
        simp [D, norm_smul, div_eq_mul_inv, mul_comm]
      have hXn : X n = A + E := by
        simp [X, D, smul_smul, hnR.ne']
      simpa [hXn, hDn, mul_assoc, mul_left_comm, mul_comm] using hbound n
    let u (n : ℕ) : ℝ := ‖E‖ / (n + 1 : ℕ)
    have hu0 : Filter.Tendsto u Filter.atTop (nhds (0 : ℝ)) := by
      exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp
        (Filter.tendsto_add_atTop_nat 1))
    have hu : Filter.Tendsto u Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hu0, ?_⟩
      exact Filter.Eventually.of_forall fun n => div_pos hc (by positivity)
    have hexp : Filter.Tendsto (fun n => (Real.exp (u n) - 1) / u n)
        Filter.atTop (nhds (1 : ℝ)) := by
      simpa only [Function.comp_def, zero_add, Real.exp_zero, smul_eq_mul,
        div_eq_mul_inv, mul_comm]
        using (Real.hasDerivAt_exp 0).tendsto_slope_zero_right.comp hu
    have hlim : Filter.Tendsto
        (fun n => (2 * ‖E‖) * ((Real.exp (u n) - 1) / u n))
        Filter.atTop (nhds (2 * ‖E‖)) := by
      simpa using tendsto_const_nhds.mul hexp
    have hle (n : ℕ) :
        Matrix.traceNorm (gibbsState (A + E) - gibbsState A) ≤
          (2 * ‖E‖) * ((Real.exp (u n) - 1) / u n) := by
      have hb := hfinite (n + 1) (Nat.succ_pos n)
      have hnR : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      convert hb using 1
      dsimp [u]
      field_simp [hc.ne', hnR]
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall hle)

end Qatlib.Papers.ThermalDrift26.ThermalSampling
