/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.Lemma5DysonSourceParametersHami
import Qatlib.Concepts.InteractionEvo.DysonGrid.DysonTruncationGrid
import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid

/-!
# DysonTruncation — Lemma 5, Lemma 11, Lemma 12 of InteractPic18

Low--Wiebe, *Hamiltonian Simulation in the Interaction Picture*,
fixed arXiv:1805.00675v2.

* Lemma 5 (Section III.C p. 6, Appendix A p. 21): joint truncation and
  discretization error of the truncated ordered Euler grid sum.
* Lemma 11 (Appendix A p. 17, Eqs. (A2)--(A3)): the explicit factorial-tail
  truncation error of the Dyson series.
* Lemma 12 (Appendix A p. 18): the Riemann-sum (grid) replacement error.

Paper notation introduced here: `timeOrderedExponential H t` is
`T[e^{-i ∫_0^t H(s) ds}]`, `dysonTaylorSum H t K` is `Σ_{k=0}^K (-i)^k D_k`,
and `riemannGridSum H t M K` is `Σ_{k=0}^K (-it/M)^k B_k`.

Boundary: exact matrix-norm bounds only. No oracle, gate, qubit or
failure-probability accounting is asserted; the printed closed-form
truncation order of Lemma 5/Lemma 11 is handled through the explicit
factorial-tail hypothesis (see the note on `lemma11_prefix_truncation`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Matrix
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.InteractionEvo
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Qatlib.Concepts.InteractionEvo.DysonGrid
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.InteractPic18.MainResults.DysonTruncation

/-- Paper notation: the time-ordered operator exponential
`T[e^{-i ∫_0^t H(s) ds}]`. -/
noncomputable def timeOrderedExponential {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  orderedEvolution (fun u => Complex.I • H u) 0 t

/-- Paper notation: the truncated Dyson series `Σ_{k=0}^K (-i)^k D_k`. -/
noncomputable def dysonTaylorSum {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (K : ℕ) : Matrix I I ℂ :=
  dysonPrefix (fun u => Complex.I • H u) 0 t K

/-- Paper notation: the truncated Riemann grid sum
`Σ_{k=0}^K (-it/M)^k B_k` with `B_k = Σ_{0 ≤ m_1 < … < m_k < M}
H(m_k t/M) ⋯ H(m_1 t/M)`. -/
noncomputable def riemannGridSum {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M K : ℕ) : Matrix I I ℂ :=
  truncatedDysonGridSum H t M K

/-- `dysonTaylorSum` is the frozen `dysonPrefix` of the generator `-iH`. -/
theorem dysonTaylorSum_eq {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (K : ℕ) :
    dysonTaylorSum H t K = dysonPrefix (fun u => Complex.I • H u) 0 t K := rfl

/-- **Lemma 5** (fixed arXiv:1805.00675v2, Section III.C p. 6, Appendix A):
the `K`-truncated ordered Euler grid sum approximates the time-ordered
exponential within `ε`, under the source's grid-size choice
`M ≥ 16 t²/ε (⟨‖Ḣ‖⟩ + max_s ‖H(s)‖²)` (Lemma 5 condition 3, first branch)
and the explicit factorial-tail hypothesis on `K` (Lemma 5 condition 2,
see the note at `lemma11_prefix_truncation`). -/
theorem lemma5_joint_truncation_discretization {I : Type} [Fintype I] [DecidableEq I]
    (H Hd : ℝ → Matrix I I ℂ) (t Λ ε : ℝ) (K M : ℕ)
    (hH : Continuous H) (hHd : Continuous Hd)
    (hderiv : ∀ u ∈ Set.Icc 0 t, HasDerivAt H (Hd u) u)
    (ht : 0 < t) (hM : 0 < M) (hε : 0 < ε)
    (hbound : ∀ u ∈ Set.Icc 0 t, (H u).IsHermitian ∧ ‖H u‖ ≤ Λ)
    (hlog : Λ * t ≤ Real.log 2)
    (hgrid : 16 * t ^ 2 * ((1 / t) * ∫ u in (0 : ℝ)..t, ‖Hd u‖ + Λ ^ 2) / ε ≤ (M : ℝ))
    (htail : 2 * (Λ * t) ^ (K + 1) / (Nat.factorial (K + 1) : ℝ) ≤ ε / 2) :
    ‖riemannGridSum H t M K - timeOrderedExponential H t‖ ≤ ε :=
  lemma5DysonSourceParameters I H Hd t Λ ε K M hH hHd hderiv ht hM hε hbound hlog hgrid htail

/-- **Lemma 11, Eq. (A3)** (fixed arXiv:1805.00675v2, Appendix A p. 17): the
`K`-truncated Dyson series differs from the full time-ordered exponential by
at most `exp(Λ|t-s|)·(Λ|t-s|)^{K+1}/(K+1)!`. -/
theorem lemma11_prefix_truncation_exponential {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (s t Λ : ℝ) (K : ℕ)
    (hA : Continuous A) (hΛ : 0 ≤ Λ)
    (hbound : ∀ u ∈ Set.uIcc s t, ‖A u‖ ≤ Λ) :
    ‖orderedEvolution A s t - dysonPrefix A s t K‖ ≤
      Real.exp (Λ * |t - s|) * (Λ * |t - s|) ^ (K + 1) /
        (Nat.factorial (K + 1) : ℝ) :=
  dyson_finite_prefix_explicit_factorial_tail I A s t Λ K hA hΛ hbound

/-- **Lemma 11** (fixed arXiv:1805.00675v2, Appendix A p. 17): under
`Λ|t-s| ≤ ln 2` (Lemma 11 condition 2) the factorial tail is at most
`2 (Λ|t-s|)^{K+1}/(K+1)!`. This is the rigorous content of Eq. (A3); the
printed closed-form order `K = ⌈-1 + 2 ln(1/ε₁)/(ln ln(1/ε₁) + 1)⌉`
(condition 1) is *not* derived here — the frozen layer documents that the
printed Appendix A estimate is insufficient for that closed form, so the
truncation order enters through the factorial hypothesis instead. -/
theorem lemma11_prefix_truncation {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (s t Λ : ℝ) (K : ℕ)
    (hA : Continuous A) (hΛ : 0 ≤ Λ)
    (hbound : ∀ u ∈ Set.uIcc s t, ‖A u‖ ≤ Λ)
    (hlog : Λ * |t - s| ≤ Real.log 2) :
    ‖orderedEvolution A s t - dysonPrefix A s t K‖ ≤
      (2 : ℝ) * (Λ * |t - s|) ^ (K + 1) / (Nat.factorial (K + 1) : ℝ) := by
  have h := lemma11_prefix_truncation_exponential A s t Λ K hA hΛ hbound
  have hexp : Real.exp (Λ * |t - s|) ≤ 2 := by
    have hmono := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hmono
  have hbase : 0 ≤ (Λ * |t - s|) ^ (K + 1) :=
    pow_nonneg (mul_nonneg hΛ (abs_nonneg _)) _
  have hfact : 0 ≤ (Nat.factorial (K + 1) : ℝ) := by positivity
  refine h.trans ?_
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hexp hbase) hfact

/-- **Lemma 11** in the paper's own notation: `‖T[e^{-i∫H}] - Σ_{k=0}^K (-i)^k D_k‖
≤ 2(Λt)^{K+1}/(K+1)!` under `Λt ≤ ln 2`. -/
theorem lemma11_taylor_truncation {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t Λ : ℝ) (K : ℕ)
    (hH : Continuous H) (hΛ : 0 ≤ Λ)
    (hbound : ∀ u ∈ Set.Icc 0 t, ‖H u‖ ≤ Λ)
    (hlog : Λ * t ≤ Real.log 2) (ht : 0 ≤ t) :
    ‖timeOrderedExponential H t - dysonTaylorSum H t K‖ ≤
      (2 : ℝ) * (Λ * t) ^ (K + 1) / (Nat.factorial (K + 1) : ℝ) := by
  have hcont : Continuous (fun u => Complex.I • H u) := hH.const_smul Complex.I
  have hb : ∀ u ∈ Set.uIcc (0 : ℝ) t, ‖Complex.I • H u‖ ≤ Λ := by
    intro u hu
    rw [Set.uIcc_of_le ht] at hu
    rw [norm_smul, Complex.norm_I, one_mul]
    exact hbound u hu
  have h := lemma11_prefix_truncation (fun u => Complex.I • H u) 0 t Λ K hcont hΛ hb
    (by simpa [abs_of_nonneg ht] using hlog)
  simpa [timeOrderedExponential, dysonTaylorSum, abs_of_nonneg ht] using h

/-- **Lemma 12** (fixed arXiv:1805.00675v2, Appendix A p. 18): replacing the
truncated Dyson series by its Riemann grid sum changes the operator by at most
`ε`, given the discretization budget (Lemma 12 condition 1 together with
`Λt ≤ ln 2`) and the truncation budget on the factorial tail. The paper's
explicit `M ≥ (t²/ε)(4e^{Λt}⟨‖Ḣ‖⟩ + max‖H‖²)` and `M ≥ K²` choices are
sufficient conditions for the two stated budgets. -/
theorem lemma12_riemann_sum_error {I : Type} [Fintype I] [DecidableEq I]
    (H Hd : ℝ → Matrix I I ℂ) (t Λ ε : ℝ) (M K : ℕ)
    (hH : Continuous H) (ht : 0 ≤ t) (hΛ : 0 ≤ Λ) (hM : 0 < M) (_hε : 0 < ε)
    (hbound : ∀ u ∈ Set.Icc 0 t, (H u).IsHermitian ∧ ‖H u‖ ≤ Λ)
    (hHd : Continuous Hd)
    (hderiv : ∀ u ∈ Set.Icc 0 t, HasDerivAt H (Hd u) u)
    (hlog : Λ * t ≤ Real.log 2)
    (hdisc : Real.exp (Λ * t) * Λ ^ 2 * t ^ 2 / (2 * M)
        + (t / M) * (∫ u in (0 : ℝ)..t, ‖Hd u‖) ≤ ε / 2)
    (htail : 4 * (Λ * t) ^ (K + 1) / (Nat.factorial (K + 1) : ℝ) ≤ ε / 2) :
    ‖dysonTaylorSum H t K - riemannGridSum H t M K‖ ≤ ε := by
  have hfact : 0 < (Nat.factorial (K + 1) : ℝ) := by positivity
  have htail' : (2 : ℝ) * (Λ * t) ^ (K + 1) / (Nat.factorial (K + 1) : ℝ)
      ≤ ε / 4 := by
    rw [div_le_iff₀ hfact] at htail ⊢
    linarith
  -- truncation leg
  have h1 : ‖dysonTaylorSum H t K - timeOrderedExponential H t‖ ≤ ε / 4 := by
    rw [norm_sub_rev]
    exact (lemma11_taylor_truncation H t Λ K hH hΛ (fun u hu => (hbound u hu).2) hlog ht).trans htail'
  -- discretization leg
  have h2 : ‖timeOrderedExponential H t - riemannGridSum H t M K‖ ≤ ε / 2 + ε / 4 := by
    have h3 := dyson_truncated_grid_joint_error I H Hd t Λ M K hH ht hΛ hM hbound hHd hderiv hlog
    have hrev : ‖timeOrderedExponential H t - riemannGridSum H t M K‖
        = ‖riemannGridSum H t M K - timeOrderedExponential H t‖ := norm_sub_rev _ _
    rw [hrev]
    calc ‖riemannGridSum H t M K - timeOrderedExponential H t‖
        ≤ Real.exp (Λ * t) * Λ ^ 2 * t ^ 2 / (2 * M)
            + (t / M) * (∫ u in (0 : ℝ)..t, ‖Hd u‖)
            + 2 * (Λ * t) ^ (K + 1) / (Nat.factorial (K + 1) : ℝ) := h3
      _ ≤ ε / 2 + ε / 4 := by linarith
  -- triangle
  have htri : ‖dysonTaylorSum H t K - riemannGridSum H t M K‖
      ≤ ‖dysonTaylorSum H t K - timeOrderedExponential H t‖
        + ‖timeOrderedExponential H t - riemannGridSum H t M K‖ := by
    have := dist_triangle (dysonTaylorSum H t K) (timeOrderedExponential H t)
      (riemannGridSum H t M K)
    simpa [dist_eq_norm] using this
  linarith [htri, h1, h2]

end Qatlib.Papers.InteractPic18.MainResults.DysonTruncation
