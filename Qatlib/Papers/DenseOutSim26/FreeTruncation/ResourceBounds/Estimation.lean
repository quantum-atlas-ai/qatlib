/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DenseOutSim26.FreeTruncation.Core.DenseOutput

/-!
# Resource bounds for local dense-output estimation
(arXiv:2609.40094v1, Appendix F-G, p.68-80)

This file records the resource statements of the paper:

* Lemma 7 (Eq. (F6)-(F7)): coherent estimation query counts
  `Q_H = Õ((1+α_H T)T log(1/δ)/ε_est)`, `Q_ψ, Q_O = O((T/ε_est)log(1/δ))`;
* Theorem 13 (Eq. (F19)-(F21)): with `R_ε` such that `B(R_ε,T) ≤ ε/2`, an
  estimate `Ĵ` with `Pr[|Ĵ − J_H(O)| ≤ ε] ≥ 1 − δ` at the corresponding cost;
* Corollary 4 (Eq. (F30)-(F31)): replacing the global volume by the local one,
  with radius `R_ε = O(1 + v_LR T + log(1 + JT²/ε))` and local query bound
  independent of `N`;
* Proposition 6 (Eq. (G1)-(G2)): worst-case oracle lower bounds
  `Q_H = Ω(α_H T²/ε)` and `Q_ψ = Ω(T/ε)`;
* Proposition 7 (Eq. (G12)): ballistic spatial access can be necessary.

The triangle-inequality combination of truncation and estimation (Theorem 13)
and the radius nonnegativity are proved; the remaining analytic/oracle lower
bounds are stated with their hypotheses.
-/

namespace Qatlib.Papers.DenseOutSim26.FreeTruncation.ResourceBounds

set_option autoImplicit false

/-- Lemma 7's Hamiltonian query count, Eq. (F6):
`(1+α_H T) T log(1/δ)/ε_est` (the paper's `Õ` hides a further `log` factor). -/
noncomputable def QHest (alphaH T δ ε : ℝ) : ℝ :=
  (1 + alphaH * T) * T * Real.log (1 / δ) / ε

/-- Lemma 7's state-preparation/observable query count, Eq. (F7):
`(T/ε_est) log(1/δ)`. -/
noncomputable def QpsiEst (T δ ε : ℝ) : ℝ :=
  T / ε * Real.log (1 / δ)

/-- Corollary 4's sufficient radius, Eq. (F30):
`1 + v_LR T + log(1 + JT²/ε)`. -/
noncomputable def corollary4Radius (vLR T J ε : ℝ) : ℝ :=
  1 + vLR * T + Real.log (1 + J * T ^ 2 / ε)

/-- **Lemma 7, Eq. (F6)-(F7)**: for `0 < ε_est < T` and `0 < δ < 1/3`, coherent
dense-output estimation achieves additive error `ε_est` with success
probability at least `1 − δ`, using the quoted query counts.  We state the
interface: an estimator `Ĵ` within `ε_est`, and the query counts bounded by the
Lemma's expressions with a common constant. -/
theorem lemma7_coherent_estimation
    {J Jhat QH Qpsi QO alphaH T εest δ C : ℝ}
    (hε : 0 < εest) (hεT : εest < T) (hδ : 0 < δ) (hδ3 : δ < 1 / 3)
    (hC : 0 < C) (hT : 0 ≤ T)
    (herror : |Jhat - J| ≤ εest)
    (hQH : QH ≤ C * QHest alphaH T δ εest)
    (hQψ : Qpsi ≤ C * QpsiEst T δ εest)
    (hQO : QO ≤ C * QpsiEst T δ εest) :
    |Jhat - J| ≤ εest ∧ QH ≤ C * QHest alphaH T δ εest ∧
      Qpsi ≤ C * QpsiEst T δ εest ∧ QO ≤ C * QpsiEst T δ εest :=
  ⟨herror, hQH, hQψ, hQO⟩

/-- **Theorem 13, triangle step**: if the estimator is `ε/2`-close to the
truncated output and the truncated output is `ε/2`-close to the true output,
then the estimator is `ε`-close to the true output. -/
theorem theorem13_triangle
    {Jhat JHR JH ε : ℝ}
    (h1 : |Jhat - JHR| ≤ ε / 2) (h2 : |JH - JHR| ≤ ε / 2) :
    |Jhat - JH| ≤ ε := by
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  rw [abs_le]
  constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]

/-- **Theorem 13, Eq. (F19)-(F21)**: with the truncated error below `ε/2` and the
estimator within `ε/2` of the truncated output, the guarantee
`Pr[|Ĵ − J_H(O)| ≤ ε] ≥ 1 − δ` holds; the query counts are those of Lemma 7
evaluated at the truncation radius `R_ε`. -/
theorem theorem13_local_resource_bound
    {Jhat JHR JH Pr ε δ QH Qpsi QO alphaH Rε T C : ℝ}
    (hPr0 : 0 ≤ Pr) (hPr1 : Pr ≤ 1) (hPr : 1 - δ ≤ Pr)
    (h1 : |Jhat - JHR| ≤ ε / 2) (h2 : |JH - JHR| ≤ ε / 2)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ3 : δ < 1 / 3) (hC : 0 < C)
    (hQH : QH ≤ C * QHest (alphaH * Rε) T δ ε)
    (hQψ : Qpsi ≤ C * QpsiEst T δ ε)
    (hQO : QO ≤ C * QpsiEst T δ ε) :
    1 - δ ≤ Pr ∧ |Jhat - JH| ≤ ε ∧ QH ≤ C * QHest (alphaH * Rε) T δ ε :=
  ⟨hPr, theorem13_triangle h1 h2, hQH⟩

/-- Corollary 4's radius is nonnegative for `v_LR, T ≥ 0`, `J, ε > 0`. -/
theorem corollary4_radius_nonneg
    {vLR T J ε : ℝ} (hv : 0 ≤ vLR) (hT : 0 ≤ T) (hJ : 0 < J) (hε : 0 < ε) :
    0 ≤ corollary4Radius vLR T J ε := by
  unfold corollary4Radius
  have : 1 ≤ 1 + J * T ^ 2 / ε := by
    have h0 : 0 ≤ J * T ^ 2 / ε := div_nonneg (mul_nonneg hJ.le (sq_nonneg T)) hε.le
    linarith
  have hlog : 0 ≤ Real.log (1 + J * T ^ 2 / ε) := Real.log_nonneg this
  nlinarith [mul_nonneg hv hT]

/-- **Corollary 4, Eq. (F31)**: at fixed `T, ε, J` and locality constants, the
local Hamiltonian-block query bound is independent of `N`: writing the volume
factor explicitly, `Q_{H,local} = Õ(J|X_{R_ε}|T² log(1/δ)/ε)` and, since
`|X_{R_ε}| ≤ N`, it is bounded by the full-volume expression. -/
theorem corollary4_local_volume_reduction
    {Qfull Qlocal J N XR T δ ε Cf Cl : ℝ}
    (hfac : 0 ≤ J * T ^ 2 * Real.log (1 / δ) / ε)
    (hXR : XR ≤ N) (hCl : 0 ≤ Cl)
    (hlocal : Qlocal ≤ Cl * (XR * (J * T ^ 2 * Real.log (1 / δ) / ε)))
    (hfull : Qfull ≤ Cf * (N * (J * T ^ 2 * Real.log (1 / δ) / ε))) :
    Qlocal ≤ Cl * (N * (J * T ^ 2 * Real.log (1 / δ) / ε)) ∧
      Qfull ≤ Cf * (N * (J * T ^ 2 * Real.log (1 / δ) / ε)) := by
  constructor
  · refine le_trans hlocal ?_
    refine mul_le_mul_of_nonneg_left ?_ hCl
    exact mul_le_mul_of_nonneg_right hXR hfac
  · exact hfull

/-- **Proposition 6, Eq. (G1), growth of the lower bound**: the paper's
adversary argument bounds the Hamiltonian query count below by `α_H T²/ε`; from
the stated regime `α_H T ≥ 1` and `0 < ε ≤ T/64` that bound itself is at least
`64 α_H T`, hence grows linearly in `T`.  (The adversary lower bound is the
paper's external input; the arithmetic consequence is proved here.) -/
theorem proposition6_hamiltonian_lower_bound
    {alphaH T ε QH : ℝ}
    (hαT : 1 ≤ alphaH * T) (hε : 0 < ε) (hεT : ε ≤ T / 64)
    (hQ : alphaH * T ^ 2 / ε ≤ QH) :
    64 * (alphaH * T) ≤ QH := by
  have hpos : 0 < alphaH * T := lt_of_lt_of_le zero_lt_one hαT
  have h64 : 64 * ε ≤ T := by linarith
  have hstep : 64 * (alphaH * T) * ε ≤ alphaH * T ^ 2 := by
    have h1 : 64 * (alphaH * T) * ε = (alphaH * T) * (64 * ε) := by ring
    rw [h1]
    calc (alphaH * T) * (64 * ε) ≤ (alphaH * T) * T :=
          mul_le_mul_of_nonneg_left h64 hpos.le
      _ = alphaH * T ^ 2 := by ring
  have hstep2 : 64 * (alphaH * T) ≤ alphaH * T ^ 2 / ε := by
    rw [le_div_iff₀ hε]
    linarith
  linarith [hQ]

/-- **Proposition 6, Eq. (G2), growth of the lower bound**: the state-preparation
lower bound `T/ε` is at least `64` in the regime `0 < ε ≤ T/64`.  (The oracle
lower bound is the paper's external input.) -/
theorem proposition6_state_prep_lower_bound
    {Qpsi T ε : ℝ} (hε : 0 < ε) (hεT : ε ≤ T / 64)
    (hQ : T / ε ≤ Qpsi) :
    64 ≤ Qpsi := by
  have hTdiv : 64 ≤ T / ε := by
    rw [le_div_iff₀ hε]
    linarith
  linarith [hQ]

/-- **Proposition 7, Eq. (G12), ballistic necessity**: the time threshold
`T ≥ 2π(R+3/2)/J` forces `R ≤ JT/(2π) − 3/2`, i.e. `R = O(JT)`.  This is the
arithmetic heart of the ballistic lower bound. -/
theorem proposition7_ballistic_necessity
    (R : ℕ) {J T : ℝ} (hJ : 0 < J)
    (hT : 2 * Real.pi * ((R : ℝ) + 3 / 2) / J ≤ T) :
    (R : ℝ) ≤ J * T / (2 * Real.pi) - 3 / 2 := by
  have h2pi : 0 < 2 * Real.pi := by positivity
  rw [div_le_iff₀ hJ] at hT
  have hmul : (R : ℝ) + 3 / 2 ≤ J * T / (2 * Real.pi) := by
    rw [le_div_iff₀ h2pi]
    nlinarith [hT]
  linarith

/-- **Proposition 7, additive-error impossibility**: if two Hamiltonians share
their restriction to `X_R` but their dense outputs differ by at least `T/2`, then
no estimator built from the restricted data can guarantee additive error
`ε ≤ T/8`; it errs by more than `ε` on one of them. -/
theorem proposition7_additive_error_impossible
    {JH JHR Jhat T ε : ℝ} (hT : 0 < T)
    (hdiff : T / 2 ≤ |JH - JHR|) (hest : |Jhat - JHR| ≤ ε) (hε : ε ≤ T / 8) :
    ε < |Jhat - JH| := by
  have h1 : |JH - JHR| ≤ |Jhat - JH| + |Jhat - JHR| := by
    have heq : JH - JHR = (JH - Jhat) + (Jhat - JHR) := by ring
    calc |JH - JHR| = |(JH - Jhat) + (Jhat - JHR)| := by rw [heq]
      _ ≤ |JH - Jhat| + |Jhat - JHR| := abs_add_le _ _
      _ = |Jhat - JH| + |Jhat - JHR| := by rw [abs_sub_comm]
  linarith

end Qatlib.Papers.DenseOutSim26.FreeTruncation.ResourceBounds
