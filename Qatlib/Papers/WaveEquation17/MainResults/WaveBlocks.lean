/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.WaveEquation17.MainResults.PerturbationCore
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Wave perturbation in source block form

In the bounded Hilbert-space model of arXiv:1711.05394v4, represent the
state of Eq. (59) as the Hilbert sum of the field and the auxiliary
components. The signs of Eq. (61) give anticommutation with Eq. (60) when
the constituent spatial operators commute with `D`.
-/

set_option autoImplicit false

noncomputable section

open Qatlib.Papers.WaveEquation17.MainResults

namespace Qatlib.Papers.WaveEquation17.MainResults

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The field at coordinate zero and the auxiliary components at the successor coordinates. -/
abbrev WaveState (d : ℕ) (E : Type*) := PiLp 2 (fun _ : Fin (d + 1) => E)

/-- Assemble bounded component maps into a bounded operator on the Hilbert sum. -/
def blockOperator {d : ℕ} (rows : Fin (d + 1) → WaveState d E →L[ℂ] E) :
    WaveState d E →L[ℂ] WaveState d E :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (d + 1) => E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi rows)

/-- Applying the assembled operator at a coordinate returns that row's value. -/
theorem blockOperator_apply {d : ℕ} (rows : Fin (d + 1) → WaveState d E →L[ℂ] E)
    (x : WaveState d E) (i : Fin (d + 1)) : blockOperator rows x i = rows i x := rfl

/-- The undamped block operator of Eq. (60) for bounded spatial operators. -/
def waveUndamped {d : ℕ} (A : Fin d → E →L[ℂ] E) : WaveState d E →L[ℂ] WaveState d E :=
  blockOperator (Fin.cases
    (∑ j, (A j).comp (PiLp.proj 2 (fun _ : Fin (d + 1) => E) j.succ))
    (fun j => -((A j).comp (PiLp.proj 2 (fun _ : Fin (d + 1) => E) 0))))

/-- The perturbation of Eq. (61) applies `D` to the field and `-D` to every auxiliary component. -/
def signedPerturbation (d : ℕ) (D : E →L[ℂ] E) : WaveState d E →L[ℂ] WaveState d E :=
  blockOperator (Fin.cases
    (D.comp (PiLp.proj 2 (fun _ : Fin (d + 1) => E) 0))
    (fun j => -(D.comp (PiLp.proj 2 (fun _ : Fin (d + 1) => E) j.succ))))

/-- The field row of the undamped operator sums the spatial terms. -/
theorem waveUndamped_zero {d : ℕ} (A : Fin d → E →L[ℂ] E) (x : WaveState d E) :
    (waveUndamped A x) 0 = ∑ j, A j (x j.succ) := by
  simp [waveUndamped, blockOperator_apply, PiLp.proj_apply]

/-- Each auxiliary row of the undamped operator is minus its spatial operator on the field. -/
theorem waveUndamped_succ {d : ℕ} (A : Fin d → E →L[ℂ] E) (x : WaveState d E) (j : Fin d) :
    waveUndamped A x j.succ = -(A j (x 0)) := by
  simp [waveUndamped, blockOperator_apply, PiLp.proj_apply]

/-- The field row of the signed perturbation. -/
theorem signedPerturbation_zero {d : ℕ} (D : E →L[ℂ] E) (x : WaveState d E) :
    signedPerturbation d D x 0 = D (x 0) := by
  simp [signedPerturbation, blockOperator_apply, PiLp.proj_apply]

/-- The auxiliary rows of the signed perturbation. -/
theorem signedPerturbation_succ {d : ℕ} (D : E →L[ℂ] E) (x : WaveState d E) (j : Fin d) :
    signedPerturbation d D x j.succ = -(D (x j.succ)) := by
  simp [signedPerturbation, blockOperator_apply, PiLp.proj_apply]

/-- Skew-adjoint spatial operators give a self-adjoint undamped block matrix. -/
theorem waveUndamped_selfAdjoint {d : ℕ} (A : Fin d → E →L[ℂ] E)
    (hA : ∀ (j : Fin d) (x y : E), inner ℂ (A j x) y = -inner ℂ x (A j y)) :
    IsSelfAdjointCLM (waveUndamped A) := by
  intro x y
  simp only [PiLp.inner_apply, Fin.sum_univ_succ, waveUndamped_zero, waveUndamped_succ,
    sum_inner, inner_sum, inner_neg_left, inner_neg_right, hA, neg_neg]
  exact add_comm _ _

/-- The signed block perturbation is self-adjoint whenever `D` is. -/
theorem signedPerturbation_selfAdjoint (d : ℕ) (D : E →L[ℂ] E) (hD : IsSelfAdjointCLM D) :
    IsSelfAdjointCLM (signedPerturbation d D) := by
  intro x y
  have hD' (a b : E) : inner ℂ (D a) b = inner ℂ a (D b) := hD a b
  simp only [PiLp.inner_apply, Fin.sum_univ_succ, signedPerturbation_zero, signedPerturbation_succ,
    inner_neg_left, inner_neg_right, hD']

/-- The signs in Eq. (61) turn commutation of the spatial operators with `D`
into anticommutation of the two block operators. -/
theorem waveBlocks_anticommute {d : ℕ} (A : Fin d → E →L[ℂ] E) (D : E →L[ℂ] E)
    (hcom : ∀ (j : Fin d) (x : E), D (A j x) = A j (D x)) (x : WaveState d E) :
    signedPerturbation d D (waveUndamped A x) =
      -(waveUndamped A (signedPerturbation d D x)) := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [signedPerturbation_zero, waveUndamped_zero, PiLp.neg_apply, map_sum, hcom,
      signedPerturbation_succ, map_neg, Finset.sum_neg_distrib, neg_neg]
  · simp only [signedPerturbation_succ, waveUndamped_succ, PiLp.neg_apply, map_neg, hcom,
      signedPerturbation_zero, neg_neg]

/-- Under anticommutation, applying the perturbation to the reference trajectory
gives the flow generated by the negative undamped operator. Its norm is constant. -/
theorem norm_comp_const_of_anticommute (H0 HD : E →L[ℂ] E) (hH0 : IsSelfAdjointCLM H0)
    (hanti : ∀ x, HD (H0 x) = -(H0 (HD x)))
    (S : ℝ → E) (hS : ∀ t, HasDerivAt S (-(Complex.I) • H0 (S t)) t) :
    ∀ t, ‖HD (S t)‖ = ‖HD (S 0)‖ := by
  have hneg : IsSelfAdjointCLM (-H0) := by
    intro x y
    simp only [neg_apply, inner_neg_left, inner_neg_right, hH0 x y]
  have hT : ∀ t, HasDerivAt (fun s => HD (S s)) (-(Complex.I) • (-H0) (HD (S t))) t := by
    intro t
    have h := HasFDerivAt.comp_hasDerivAt (l := fun x : E => HD x)
      (l' := HD.restrictScalars ℝ) t (ContinuousLinearMap.hasFDerivAt (HD.restrictScalars ℝ)) (hS t)
    change HasDerivAt (fun s => HD (S s)) (HD (-(Complex.I) • H0 (S t))) t at h
    simpa only [map_smul, hanti, neg_apply] using h
  exact norm_eq_of_norm_sq_eq _ (norm_sq_const_of_deriv_zero _ (-H0) hneg hT)

/-- Separate the time factor from the quarter root in Eq. (57). -/
private theorem sqrt_product_fourth_root (s a b : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (s * a * b) = Real.sqrt s * (a ^ 2 * b ^ 2) ^ ((1 : ℝ) / 4) := by
  rw [mul_assoc, Real.sqrt_mul hs, ← mul_pow,
    ← Real.rpow_natCast_mul (mul_nonneg ha hb), Real.sqrt_eq_rpow (a * b)]
  norm_num

/-- Eq. (57) in aggregate norms under the commutation hypothesis of the existing abstract bound. -/
theorem theorem2_paper_form {H0 HD : E →L[ℂ] E}
    (hH0 : IsSelfAdjointCLM H0) (hHD : IsSelfAdjointCLM HD)
    (hcomm : ∀ x, H0 (HD x) = HD (H0 x))
    {Sε S0 : ℝ → E} {ε t : ℝ}
    (hSε : ∀ τ, HasDerivAt Sε (-(Complex.I) • (H0 (Sε τ) + (ε : ℂ) • HD (Sε τ))) τ)
    (hS0 : ∀ τ, HasDerivAt S0 (-(Complex.I) • H0 (S0 τ)) τ)
    (hinit : Sε 0 = S0 0) (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    ‖Sε t - S0 t‖ ≤ Real.sqrt (2 * t * ε) *
      (‖Sε 0‖ ^ 2 * ‖HD (S0 0)‖ ^ 2) ^ ((1 : ℝ) / 4) := by
  rw [← sqrt_product_fourth_root _ _ _ (by positivity) (norm_nonneg _) (norm_nonneg _)]
  exact theorem2_wave_perturbation hH0 hHD hcomm hSε hS0 hinit hε ht

omit [InnerProductSpace ℂ E] in
/-- The two norm sums in Eq. (57) use the Hilbert norm of the full state. -/
theorem waveState_norm_sq {d : ℕ} (x : WaveState d E) :
    ‖x‖ ^ 2 = ‖x 0‖ ^ 2 + ∑ j : Fin d, ‖x j.succ‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]

/-- The signs of the auxiliary rows do not change the perturbation norm. -/
theorem signedPerturbation_norm_sq {d : ℕ} (D : E →L[ℂ] E) (x : WaveState d E) :
    ‖signedPerturbation d D x‖ ^ 2 =
      ‖D (x 0)‖ ^ 2 + ∑ j : Fin d, ‖D (x j.succ)‖ ^ 2 := by
  simp only [waveState_norm_sq, signedPerturbation_zero, signedPerturbation_succ, norm_neg]

/-- Eq. (57) for the field component, with both block sums and the actual signed operators
of Eqs. (60)–(61) in the bounded Hilbert-space model. -/
theorem theorem2_block_bound {d : ℕ} (A : Fin d → E →L[ℂ] E) (D : E →L[ℂ] E)
    (hA : ∀ (j : Fin d) (x y : E), inner ℂ (A j x) y = -inner ℂ x (A j y))
    (hD : IsSelfAdjointCLM D) (hcom : ∀ (j : Fin d) (x : E), D (A j x) = A j (D x))
    {Sε S0 : ℝ → WaveState d E} {ε t : ℝ}
    (hSε : ∀ τ, HasDerivAt Sε (-(Complex.I) •
      (waveUndamped A (Sε τ) + (ε : ℂ) • signedPerturbation d D (Sε τ))) τ)
    (hS0 : ∀ τ, HasDerivAt S0 (-(Complex.I) • waveUndamped A (S0 τ)) τ)
    (hinit : Sε 0 = S0 0) (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    ‖Sε t 0 - S0 t 0‖ ≤ Real.sqrt (2 * t * ε) *
      ((‖Sε 0 0‖ ^ 2 + ∑ j : Fin d, ‖Sε 0 j.succ‖ ^ 2) *
       (‖D (S0 0 0)‖ ^ 2 + ∑ j : Fin d, ‖D (S0 0 j.succ)‖ ^ 2)) ^ ((1 : ℝ) / 4) := by
  have hH0 := waveUndamped_selfAdjoint A hA
  have hn := norm_comp_const_of_anticommute (waveUndamped A) (signedPerturbation d D)
    hH0 (waveBlocks_anticommute A D hcom) S0 hS0
  have hfull := perturbation_norm_bound hH0 (signedPerturbation_selfAdjoint d D hD)
    hSε hS0 hinit (fun τ _ => le_of_eq (hn τ)) hε ht
  have hcomponent : ‖Sε t 0 - S0 t 0‖ ≤ ‖Sε t - S0 t‖ :=
    PiLp.norm_apply_le (Sε t - S0 t) (0 : Fin (d + 1))
  rw [sqrt_product_fourth_root _ _ _ (by positivity) (norm_nonneg _) (norm_nonneg _),
    waveState_norm_sq (Sε 0), signedPerturbation_norm_sq] at hfull
  exact hcomponent.trans hfull

end Qatlib.Papers.WaveEquation17.MainResults
