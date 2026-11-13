/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QDataFit12.SparseHHL.SourceClaims.SourceCostModel
import Qatlib.Papers.QDataFit12.SparseHHL.DataFitting
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option backward.isDefEq.respectTransparency false

/-!
# Claim c003 — Algorithm 1 (Fitting Algorithm), Eqs. (3)–(4) and Appendix A

Fixed paper: Wiebe–Braun–Lloyd, *Quantum Data Fitting*, arXiv:1204.5242v2 (3 Jul 2012).

Source: p.2, §1 "Fitting Algorithm"; Appendix A, pp.5–6.

* Eq. (3): the number of oracle queries is `Õ(log(N)·s³κ⁶/ε)`.
* Eq. (4): with the Childs–Berry simulation method the query complexity is
  `Õ(log(N)·sκ⁶/ε²)`.
* Algorithm 1 output (p.2): a state approximately proportional to the optimal fit
  parameters `λ/|λ|` (Euclidean error `ε`), where by the Moore–Penrose theory the optimal
  parameters are `λ = F⁺ y` (p.2, Eq. below line 87).
* Appendix A: the Moore–Penrose pseudoinverse minimises the least-squares residual
  `‖Fλ − y‖²`; the derivation is A7–A9, with the key normal-equation property A4
  `F†(F F⁺ y − y) = 0`.

The exact cost functions `fitHeadlineCost` (Eq. (3)) and `simulationHeadlineCost`
(Eq. (4)) are already fixed in the reusable model
`Qatlib.Papers.QDataFit12.SparseHHL`.  §1 records them and bridges their
monotonicity to the reusable theorems `clause23_fit_headline_mono`,
`clause23_fit_headline_anti_mono_eps`, `clause23_simulation_headline_mono`,
`clause23_simulation_headline_anti_mono_eps`.  §2 proves the Appendix-A least-squares
optimality statement for an abstract linear map `F` satisfying the normal equations — this
is the exact mathematics of the paper's A7–A9 derivation.

The oracle program realising Eqs. (3)–(4) and the state-preparation bound on `|λ/|λ|⟩`
are outside the scope of this paper-layer model (residuals of the `SparseHHL` block).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QDataFit12.SparseHHL.SourceClaims

open Qatlib.Papers.QDataFit12.SparseHHL

/-! ## §1 Eqs. (3)–(4): the two Algorithm-1 query complexities -/

/-- **c003 Eq. (3) reuse.**  The Algorithm-1 fit query complexity `Õ(log N·s³κ⁶/ε)` is the
library function `fitHeadlineCost`, so the statement of Eq. (3) is definitional. -/
theorem algorithm1_fit_cost_eq (N s κ : ℕ) (ε : ℝ) :
    fitHeadlineCost N s κ ε = Real.log (N + 1) * (s : ℝ) ^ 3 * (κ : ℝ) ^ 6 / ε := rfl

/-- **c003 Eq. (4) reuse.**  The alternative-simulation query complexity
`Õ(log N·sκ⁶/ε²)` is the library function `simulationHeadlineCost`. -/
theorem algorithm1_simulation_cost_eq (N s κ : ℕ) (ε : ℝ) :
    simulationHeadlineCost N s κ ε = Real.log (N + 1) * (s : ℝ) * (κ : ℝ) ^ 6 / ε ^ 2 := rfl

/-- **c003 Eq. (3) monotonicity, by reference.**  Monotone in `N, s, κ` at fixed `ε`.
Reuses the reusable theorem
`Qatlib.Papers.QDataFit12.SparseHHL.clause23_fit_headline_mono`. -/
theorem algorithm1_fit_cost_mono (N N' s s' κ κ' : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hN : N ≤ N') (hs : s ≤ s') (hκ : κ ≤ κ') :
    fitHeadlineCost N s κ ε ≤ fitHeadlineCost N' s' κ' ε :=
  clause23_fit_headline_mono N N' s s' κ κ' ε hε hN hs hκ

/-- **c003 Eq. (3) anti-monotonicity in `ε`, by reference.**  Reuses the reusable theorem
`Qatlib.Papers.QDataFit12.SparseHHL.clause23_fit_headline_anti_mono_eps`. -/
theorem algorithm1_fit_cost_anti_mono_eps (N s κ : ℕ) (ε ε' : ℝ) (hε : 0 < ε)
    (hle : ε ≤ ε') :
    fitHeadlineCost N s κ ε' ≤ fitHeadlineCost N s κ ε :=
  clause23_fit_headline_anti_mono_eps N s κ ε ε' hε hle

/-- **c003 Eq. (4) monotonicity, by reference.**  Reuses the reusable theorem
`Qatlib.Papers.QDataFit12.SparseHHL.clause23_simulation_headline_mono`. -/
theorem algorithm1_simulation_cost_mono (N N' s s' κ κ' : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hN : N ≤ N') (hs : s ≤ s') (hκ : κ ≤ κ') :
    simulationHeadlineCost N s κ ε ≤ simulationHeadlineCost N' s' κ' ε :=
  clause23_simulation_headline_mono N N' s s' κ κ' ε hε hN hs hκ

/-- **c003 Eq. (4) anti-monotonicity in `ε`, by reference.**  Reuses the reusable theorem
`Qatlib.Papers.QDataFit12.SparseHHL.clause23_simulation_headline_anti_mono_eps`. -/
theorem algorithm1_simulation_cost_anti_mono_eps (N s κ : ℕ) (ε ε' : ℝ) (hε : 0 < ε)
    (hle : ε ≤ ε') :
    simulationHeadlineCost N s κ ε' ≤ simulationHeadlineCost N s κ ε :=
  clause23_simulation_headline_anti_mono_eps N s κ ε ε' hε hle

/-! ## §2 Appendix A: the pseudoinverse minimises the least-squares residual -/

/-- **c003 Appendix-A residual decomposition (Eqs. A7–A9).**  Write `z = F⁺ y` and suppose
the normal-equation property (A4) `F†(Fz − y) = 0`.  Then for every parameter vector `λ`,
`‖Fλ − y‖² = ‖Fz − y‖² + ‖F(λ − z)‖²`: the cross term in the binomial expansion of
A8 vanishes by (A4). -/
theorem leastSquares_residual_decomposition
    {U W : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (F : U →L[ℂ] W) (y : W) (z : U)
    (h : (ContinuousLinearMap.adjoint F) (F z - y) = 0) :
    ∀ a : U, ‖F a - y‖ ^ 2 = ‖F z - y‖ ^ 2 + ‖F (a - z)‖ ^ 2 := by
  intro a
  have hsum : F a - y = F (a - z) + (F z - y) := by
    rw [map_sub]; abel
  have hcross : RCLike.re (inner ℂ (F (a - z)) (F z - y)) = 0 := by
    have h1 : inner ℂ (F (a - z)) (F z - y)
        = inner ℂ (a - z) ((ContinuousLinearMap.adjoint F) (F z - y)) :=
      (ContinuousLinearMap.adjoint_inner_right F (a - z) (F z - y)).symm
    rw [h1, h, inner_zero_right]; simp
  rw [hsum, norm_add_sq (𝕜 := ℂ), hcross]
  ring

/-- **c003 Appendix A (Eq. A9): the pseudoinverse minimises the least-squares error.**
Any `z` satisfying the normal equation (A4) — in particular `z = F⁺ y` — gives a residual
no larger than that of any other parameter vector `λ`: `‖Fz − y‖² ≤ ‖Fλ − y‖²`. -/
theorem leastSquares_pseudoinverse_optimal
    {U W : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (F : U →L[ℂ] W) (y : W) (z : U)
    (h : (ContinuousLinearMap.adjoint F) (F z - y) = 0) :
    ∀ a : U, ‖F z - y‖ ^ 2 ≤ ‖F a - y‖ ^ 2 := by
  intro a
  rw [leastSquares_residual_decomposition F y z h a]
  nlinarith [sq_nonneg ‖F (a - z)‖]

/-- **c003 Appendix A: existence of a least-squares minimiser.**  If some parameter vector
satisfies the normal equations (A4) — the defining property of the Moore–Penrose solution
`F⁺ y` — then a least-squares minimiser of `‖Fλ − y‖²` exists. -/
theorem exists_leastSquares_minimiser
    {U W : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (F : U →L[ℂ] W) (y : W)
    (h : ∃ z : U, (ContinuousLinearMap.adjoint F) (F z - y) = 0) :
    ∃ z : U, ∀ a : U, ‖F z - y‖ ^ 2 ≤ ‖F a - y‖ ^ 2 := by
  obtain ⟨z, hz⟩ := h
  exact ⟨z, leastSquares_pseudoinverse_optimal F y z hz⟩

/-! ## §3 The claim statement -/

/-- **c003 (Algorithm 1, Fitting Algorithm) — Eqs. (3)–(4), arXiv:1204.5242v2 p.2, and
Appendix A pp.5–6.**

* The fit query complexity is Eq. (3), `log(N)·s³κ⁶/ε`, monotone in `N, s, κ` and
  non-increasing in `ε`.
* The alternative-simulation query complexity is Eq. (4), `log(N)·sκ⁶/ε²`, monotone in
  `N, s, κ` and non-increasing in `ε`.
* The fit parameters are the Moore–Penrose pseudoinverse `λ = F⁺ y`, which — via the
  normal equation (A4) — minimises the least-squares residual `‖Fλ − y‖²` (Appendix A,
  Eqs. A7–A9), with the residual decomposition `‖Fλ − y‖² = ‖Fz − y‖² + ‖F(λ − z)‖²`.

*Proved:* all of the above (Eqs. (3)–(4) via the `clause23_*` theorems; Appendix A's
A7–A9 derivation from the normal equation). — *Not modelled here:* the sparse-oracle
program realising Eqs. (3)–(4) and the Euclidean-norm state-preparation bound on
`|λ/|λ|⟩` (residuals of the `SparseHHL` block). -/
theorem claim_c003 :
    (∀ (N s κ : ℕ) (ε : ℝ),
        fitHeadlineCost N s κ ε = Real.log (N + 1) * (s : ℝ) ^ 3 * (κ : ℝ) ^ 6 / ε) ∧
      (∀ (N s κ : ℕ) (ε : ℝ),
        simulationHeadlineCost N s κ ε
          = Real.log (N + 1) * (s : ℝ) * (κ : ℝ) ^ 6 / ε ^ 2) ∧
      (∀ (N N' s s' κ κ' : ℕ) (ε : ℝ), 0 < ε →
        N ≤ N' → s ≤ s' → κ ≤ κ' →
          fitHeadlineCost N s κ ε ≤ fitHeadlineCost N' s' κ' ε) ∧
      (∀ (N s κ : ℕ) (ε ε' : ℝ), 0 < ε → ε ≤ ε' →
          fitHeadlineCost N s κ ε' ≤ fitHeadlineCost N s κ ε) ∧
      (∀ (N N' s s' κ κ' : ℕ) (ε : ℝ), 0 < ε →
        N ≤ N' → s ≤ s' → κ ≤ κ' →
          simulationHeadlineCost N s κ ε ≤ simulationHeadlineCost N' s' κ' ε) ∧
      (∀ (N s κ : ℕ) (ε ε' : ℝ), 0 < ε → ε ≤ ε' →
          simulationHeadlineCost N s κ ε' ≤ simulationHeadlineCost N s κ ε) ∧
      (∀ {U W : Type*}
        [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
        [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
        (F : U →L[ℂ] W) (y : W) (z : U),
          (ContinuousLinearMap.adjoint F) (F z - y) = 0 →
            ∀ a : U, ‖F a - y‖ ^ 2 = ‖F z - y‖ ^ 2 + ‖F (a - z)‖ ^ 2) ∧
      (∀ {U W : Type*}
        [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
        [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
        (F : U →L[ℂ] W) (y : W),
          (∃ z : U, (ContinuousLinearMap.adjoint F) (F z - y) = 0) →
            ∃ z : U, ∀ a : U, ‖F z - y‖ ^ 2 ≤ ‖F a - y‖ ^ 2) := by
  refine ⟨algorithm1_fit_cost_eq, algorithm1_simulation_cost_eq,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N N' s s' κ κ' ε hε hN hs hκ
    exact algorithm1_fit_cost_mono N N' s s' κ κ' ε hε hN hs hκ
  · intro N s κ ε ε' hε hle
    exact algorithm1_fit_cost_anti_mono_eps N s κ ε ε' hε hle
  · intro N N' s s' κ κ' ε hε hN hs hκ
    exact algorithm1_simulation_cost_mono N N' s s' κ κ' ε hε hN hs hκ
  · intro N s κ ε ε' hε hle
    exact algorithm1_simulation_cost_anti_mono_eps N s κ ε ε' hε hle
  · intro U W _ _ _ _ _ _ F y z h a
    exact leastSquares_residual_decomposition F y z h a
  · intro U W _ _ _ _ _ _ F y h
    exact exists_leastSquares_minimiser F y h

end Qatlib.Papers.QDataFit12.SparseHHL.SourceClaims
