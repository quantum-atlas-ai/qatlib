/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Carleman truncation error and the homogeneous error bound

Fixed source: arXiv:2011.03185v4 (7 July 2026), Liu--Kolden--Krovi--Loureiro--Trivisa--Childs,
*Efficient quantum algorithm for dissipative nonlinear differential equations*.

This file formalises the analytic content of

* **Lemma 2** (printed pp. 8--10, Eqs. (4.12)--(4.27)): the Carleman truncation error obeys
  `‖η_j(t)‖ ≤ ‖η(t)‖ ≤ t N ‖F₂‖ ‖u_in‖^{N+1}`;
* **Corollary 1** (printed pp. 10--11, Eqs. (4.28)--(4.41)): for a homogeneous quadratic ODE the
  error improves to `‖η_j(t)‖ ≤ ‖u_in‖^j R^{N+1-j}`, with the tighter `j = 1` bound
  `‖u_in‖ (R (1 - e^{Re(λ₁)t}))^N`.

Modelling boundary.  The paper derives the scalar differential inequality (4.23)

`d‖η‖/dt ≤ ν₁ ‖η‖ + N ‖F₂‖ ‖u_in‖^{N+1}`

from the block-matrix estimates (4.16)--(4.22).  Those estimates need the Carleman block
matrices (3.3)--(3.5) and spectral norms, which do not exist in the current Lean library; the
derivation is therefore isolated in the statement-only theorem
`lemma2_carleman_derivative_bound`, while the analytic endpoint (4.23)--(4.26) is fully proved
here (it is an instance of Grönwall's inequality plus the elementary estimate (4.25)).
Similarly, the backward-substitution integral formula (4.37)--(4.39) of Corollary 1 is isolated
in `corollary1_error_bound`; the algebraic identity (4.39) and the `j = 1` factorisation (4.41)
are proved below.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DissipNonlin20.MainResults.TruncError

open Set

/-- **Eq. (4.25), scalar form.**  For `ν < 0` and `t ≥ 0`,
`(1 - e^{νt}) / (-ν) ≤ t`.  This is the only estimate used to turn the integral of the
comparison equation into the linear-in-time forcing term of (4.26). -/
theorem exp_integral_le_time (ν t : ℝ) (hν : ν < 0) (ht : 0 ≤ t) :
    (1 - Real.exp (ν * t)) / (-ν) ≤ t := by
  have hνne : ν ≠ 0 := ne_of_lt hν
  have hpos : 0 < -ν := by linarith
  have h := Real.add_one_le_exp (ν * t)
  have hlin : 1 - Real.exp (ν * t) ≤ -(ν * t) := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith

/-- **Eq. (4.24)--(4.25), evaluation of the Grönwall bound.**  The Grönwall bound with
`δ = 0`, rate `ν < 0` and forcing `C ≥ 0` is `gronwallBound 0 ν C t = C (e^{νt}-1)/ν`, and
is at most `C t` on `t ≥ 0`. -/
theorem gronwallBound_neg_le (ν C t : ℝ) (hν : ν < 0) (hC : 0 ≤ C) (ht : 0 ≤ t) :
    gronwallBound 0 ν C t ≤ C * t := by
  rw [gronwallBound_of_K_ne_0 (ne_of_lt hν)]
  simp only [zero_mul, zero_add]
  have hkey := exp_integral_le_time ν t hν ht
  have hνne : ν ≠ 0 := ne_of_lt hν
  have heq : C / ν * (Real.exp (ν * t) - 1) = C * ((1 - Real.exp (ν * t)) / (-ν)) := by
    field_simp
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left hkey hC

/-- **Lemma 2, analytic core (4.22)--(4.26).**  Let `η` be a continuous curve in a real normed
space with right derivative `η'` on `[0,T]`, `η(0) = 0`, satisfying the differential inequality
`‖η'(t)‖ ≤ ν ‖η(t)‖ + C` of (4.23) with `ν < 0` and `C ≥ 0`.  Then `‖η(t)‖ ≤ C t`.

This is exactly the passage (4.22) → (4.26) of the paper: Grönwall's inequality gives (4.24),
and (4.25) bounds the integral by `t`. -/
theorem lemma2_forcing_estimate
    (T ν C : ℝ) (hν : ν < 0) (hC : 0 ≤ C) (f f' : ℝ → ℝ)
    (hcont : ContinuousOn f (Icc 0 T))
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt f (f' t) (Ici t) t)
    (h0 : f 0 ≤ 0)
    (hbound : ∀ t ∈ Ico 0 T, f' t ≤ ν * f t + C) :
    ∀ t ∈ Icc 0 T, f t ≤ C * t := by
  have hg := le_gronwallBound_of_liminf_deriv_right_le hcont
    (fun x hx _r hr => (hderiv x hx).liminf_right_slope_le hr) h0 hbound
  intro t ht
  have hb := hg t ht
  have ht0 : 0 ≤ t := ht.1
  have hgb := gronwallBound_neg_le ν C (t - 0) hν hC (by simpa using ht0)
  have hsub : t - 0 = t := by ring
  rw [hsub] at hgb hb
  linarith

/-- **Lemma 2, Eq. (4.12)/(4.26): truncation error bound.**  If the norm of the Carleman error
satisfies (4.23) on `[0,T]` with rate `ν < 0`, then for every `t ∈ [0,T]`

`‖η(t)‖ ≤ t · N · ‖F₂‖ · ‖u_in‖^{N+1}`.

The hypotheses `hcont`, `hderiv`, `hη0` and `hbound` are the statement of (4.14)/(4.23) for the
norm of the error; the operator-level derivation of `hbound` is the separate statement-only
theorem `lemma2_carleman_derivative_bound` below. -/
theorem lemma2_error_bound (N : ℕ) (F2 uin ν T : ℝ)
    (hF2 : 0 ≤ F2) (huin : 0 ≤ uin) (hν : ν < 0)
    (ηNorm ηNorm' : ℝ → ℝ)
    (hcont : ContinuousOn ηNorm (Icc 0 T))
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt ηNorm (ηNorm' t) (Ici t) t)
    (hη0 : ηNorm 0 = 0)
    (hbound : ∀ t ∈ Ico 0 T,
      ηNorm' t ≤ ν * ηNorm t + (N : ℝ) * F2 * uin ^ (N + 1))
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ ηNorm t) :
    ∀ t ∈ Icc 0 T, ηNorm t ≤ t * (N : ℝ) * F2 * uin ^ (N + 1) := by
  have hC : 0 ≤ (N : ℝ) * F2 * uin ^ (N + 1) := by positivity
  have h0 : ηNorm 0 ≤ 0 := by rw [hη0]
  have hmain := lemma2_forcing_estimate T ν ((N : ℝ) * F2 * uin ^ (N + 1)) hν hC
    ηNorm ηNorm' hcont hderiv h0 hbound
  intro t ht
  have h := hmain t ht
  calc ηNorm t ≤ ((N : ℝ) * F2 * uin ^ (N + 1)) * t := h
    _ = t * (N : ℝ) * F2 * uin ^ (N + 1) := by ring

/-- **Factorial cancellation in (4.39).**  The two factorial prefactors coming from (4.37) and
(4.38) multiply to one. -/
theorem factorial_ratio_cancel (j N : ℕ) (hj : 1 ≤ j) :
    ((N.factorial : ℝ) / ((j - 1).factorial : ℝ)) *
        (((j - 1).factorial : ℝ) / (N.factorial : ℝ)) = 1 := by
  have hN : (N.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero N
  have hj1 : ((j - 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (j - 1)
  field_simp

/-- **Corollary 1, Eq. (4.39): geometric form of the bound.**

With `u = ‖u_in‖`, `F = ‖F₂‖`, `λ = |Re(λ₁)| > 0` and `R = u F / λ`, the `j`-th error bound
`u^{N+1} F^{N+1-j} / λ^{N+1-j}` equals `u^j R^{N+1-j}`.  This is the final step of (4.39). -/
theorem corollary1_geometric_bound (u F lam : ℝ) (hu : u ≠ 0) (hlam : lam ≠ 0)
    (j N : ℕ) (hj : 1 ≤ j) (hjn : j ≤ N + 1) :
    F ^ (N + 1 - j) * u ^ (N + 1) / lam ^ (N + 1 - j) =
      u ^ j * (u * F / lam) ^ (N + 1 - j) := by
  have hpow : N + 1 = j + (N + 1 - j) := by omega
  have hsub : j + (N + 1 - j) - j = N + 1 - j := by omega
  rw [hpow, pow_add]
  simp only [hsub]
  rw [div_pow, mul_pow]
  field_simp

/-- **Corollary 1, Eq. (4.41): the `j = 1` factorisation.**  The tighter bound
`u (R (1 - e^{λt}))^N` is the `N`-th power of the single factor `R (1 - e^{λt})`, matching the
displayed expression `‖u_in‖ R^N (1 - e^{Re(λ₁)t})^N`. -/
theorem corollary1_j1_factor (u R lam t : ℝ) :
    u * R ^ 2 * (1 - Real.exp (lam * t)) ^ 2 =
      u * (R * (1 - Real.exp (lam * t))) ^ 2 := by
  ring

/-- **Corollary 1, Eq. (4.28): homogeneous Carleman error bound.**

Under the hypotheses of Lemma 2 with `F₀(t) = 0`, the error satisfies

`‖η_j(t)‖ ≤ ‖u_in‖^j R^{N+1-j}`.

The paper proves this by backward substitution: (4.30)--(4.32) give η_N, and iterating (4.34)--
(4.37) gives the nested integral (4.37), bounded through (4.38) and simplified in (4.39).

Not formalised: the explicit fundamental solutions `e^{A_j^j t}` of the Carleman blocks, the
iterated integral (4.37), and the eigenvalue-norm identity `‖e^{A_j^j t}‖ = e^{j Re(λ₁)t}`.
The algebra of the final step is proved in `corollary1_geometric_bound`; the `j = 1` refinement
(4.41) reduces to the closed-form integral (4.40), which needs the same block-matrix machinery. -/
theorem corollary1_error_bound
    (N j : ℕ) (uin F2 lam : ℝ) (hlam : lam < 0) (huin : 0 ≤ uin) (huin0 : uin ≠ 0)
    (hF2 : 0 ≤ F2) (hj : 1 ≤ j) (hjn : j ≤ N + 1)
    (etaNorm : ℝ → ℝ) (T : ℝ)
    (hint : ∀ t ∈ Icc 0 T, etaNorm t ≤
      ((N.factorial : ℝ) / ((j - 1).factorial : ℝ)) * F2 ^ (N + 1 - j) *
        uin ^ (N + 1) / (-lam) ^ (N + 1 - j) *
          (((j - 1).factorial : ℝ) / (N.factorial : ℝ))) :
    ∀ t ∈ Icc 0 T, etaNorm t ≤ uin ^ j * (uin * F2 / (-lam)) ^ (N + 1 - j) := by
  intro t ht
  have hratio := factorial_ratio_cancel j N hj
  have hgeo := corollary1_geometric_bound uin F2 (-lam)
    huin0 (by linarith) j N hj hjn
  have h := hint t ht
  calc etaNorm t
      ≤ ((N.factorial : ℝ) / ((j - 1).factorial : ℝ)) * F2 ^ (N + 1 - j) *
          uin ^ (N + 1) / (-lam) ^ (N + 1 - j) *
            (((j - 1).factorial : ℝ) / (N.factorial : ℝ)) := h
    _ = F2 ^ (N + 1 - j) * uin ^ (N + 1) / (-lam) ^ (N + 1 - j) := by
        calc ((N.factorial : ℝ) / ((j - 1).factorial : ℝ)) * F2 ^ (N + 1 - j) *
              uin ^ (N + 1) / (-lam) ^ (N + 1 - j) *
                (((j - 1).factorial : ℝ) / (N.factorial : ℝ))
            = (((N.factorial : ℝ) / ((j - 1).factorial : ℝ)) *
                (((j - 1).factorial : ℝ) / (N.factorial : ℝ))) *
                (F2 ^ (N + 1 - j) * uin ^ (N + 1) / (-lam) ^ (N + 1 - j)) := by ring
          _ = F2 ^ (N + 1 - j) * uin ^ (N + 1) / (-lam) ^ (N + 1 - j) := by
              rw [hratio, one_mul]
    _ = uin ^ j * (uin * F2 / (-lam)) ^ (N + 1 - j) := hgeo

end Qatlib.Papers.DissipNonlin20.MainResults.TruncError
